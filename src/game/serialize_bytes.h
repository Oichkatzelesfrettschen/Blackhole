/**
 * @file serialize_bytes.h
 * @brief Little-endian field-by-field byte writers and the FNV-1a digest shared
 *        by every deterministic game core.
 *
 * Deterministic serialization writes each field at an explicit width rather than
 * memcpy-ing a struct, so padding bytes never reach the digest and -0.0 hashes
 * equal to +0.0. Both the single-hole CampaignState and the multi-system
 * Constellation serialize through these writers, so their byte formats agree
 * primitive-for-primitive and a shared scenario expressed either way digests the
 * same. Keeping one copy is what lets the two cores converge rather than drift.
 */

#ifndef BLACKHOLE_GAME_SERIALIZE_BYTES_H
#define BLACKHOLE_GAME_SERIALIZE_BYTES_H

#include <algorithm>
#include <bit>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string_view>
#include <vector>

namespace game::serial {

inline void appendU8(std::vector<std::uint8_t> &out, std::uint8_t value) { out.push_back(value); }

inline void appendU32(std::vector<std::uint8_t> &out, std::uint32_t value) {
  for (int byteIndex = 0; byteIndex < 4; ++byteIndex) {
    out.push_back(static_cast<std::uint8_t>((value >> (8 * byteIndex)) & 0xFFU));
  }
}

inline void appendU64(std::vector<std::uint8_t> &out, std::uint64_t value) {
  for (int byteIndex = 0; byteIndex < 8; ++byteIndex) {
    out.push_back(static_cast<std::uint8_t>((value >> (8 * byteIndex)) & 0xFFU));
  }
}

inline void appendI64(std::vector<std::uint8_t> &out, std::int64_t value) {
  appendU64(out, static_cast<std::uint64_t>(value));
}

inline void appendI32(std::vector<std::uint8_t> &out, std::int32_t value) {
  appendU32(out, static_cast<std::uint32_t>(value));
}

inline void appendF64(std::vector<std::uint8_t> &out, double value) {
  assert(std::isfinite(value));
  if (value == 0.0) {
    // Canonicalize both zero signs to the positive-zero encoding.
    appendU64(out, 0);
    return;
  }
  appendU64(out, std::bit_cast<std::uint64_t>(value));
}

/** @brief Length-prefixed (u32) byte string. */
inline void appendString(std::vector<std::uint8_t> &out, std::string_view text) {
  appendU32(out, static_cast<std::uint32_t>(text.size()));
  std::ranges::transform(text, std::back_inserter(out),
                         [](char character) { return static_cast<std::uint8_t>(character); });
}

/** @brief FNV-1a 64-bit over a byte serialization -- a cheap comparison aid,
 *         not a security or sole-equality mechanism. */
inline std::uint64_t fnv1a64(const std::vector<std::uint8_t> &bytes) {
  std::uint64_t hash = 14695981039346656037ULL;
  for (const std::uint8_t byte : bytes) {
    hash ^= byte;
    hash *= 1099511628211ULL;
  }
  return hash;
}

/**
 * @brief Bounds-checked little-endian reader, the inverse of the writers.
 *
 * Every read returns false and leaves the output untouched once the input is
 * exhausted, and the reader stays failed afterwards, so a parser can read a
 * whole section and check ok() once.
 */
class ByteReader {
public:
  ByteReader(const std::uint8_t *data, std::size_t size) : data_(data), size_(size) {}

  bool readU8(std::uint8_t &value) {
    if (!take(1)) {
      return false;
    }
    value = data_[offset_ - 1];
    return true;
  }

  bool readU32(std::uint32_t &value) {
    std::uint64_t wide = 0;
    if (!readLittleEndian(4, wide)) {
      return false;
    }
    value = static_cast<std::uint32_t>(wide);
    return true;
  }

  bool readU64(std::uint64_t &value) { return readLittleEndian(8, value); }

  bool readI32(std::int32_t &value) {
    std::uint32_t bits = 0;
    if (!readU32(bits)) {
      return false;
    }
    value = static_cast<std::int32_t>(bits);
    return true;
  }

  bool readI64(std::int64_t &value) {
    std::uint64_t bits = 0;
    if (!readU64(bits)) {
      return false;
    }
    value = static_cast<std::int64_t>(bits);
    return true;
  }

  /** @brief Reads a double; a non-finite value fails the reader, since the
   *         writer never emits one. */
  bool readF64(double &value) {
    std::uint64_t bits = 0;
    if (!readU64(bits)) {
      return false;
    }
    const auto decoded = std::bit_cast<double>(bits);
    if (!std::isfinite(decoded)) {
      failed_ = true;
      return false;
    }
    value = decoded;
    return true;
  }

  /** @brief Skips `count` bytes. */
  bool skip(std::size_t count) { return take(count); }

  [[nodiscard]] bool ok() const { return !failed_; }
  [[nodiscard]] std::size_t remaining() const { return failed_ ? 0 : size_ - offset_; }
  [[nodiscard]] std::size_t offset() const { return offset_; }

private:
  bool take(std::size_t count) {
    if (failed_ || size_ - offset_ < count) {
      failed_ = true;
      return false;
    }
    offset_ += count;
    return true;
  }

  bool readLittleEndian(std::size_t width, std::uint64_t &value) {
    if (!take(width)) {
      return false;
    }
    std::uint64_t result = 0;
    for (std::size_t byteIndex = 0; byteIndex < width; ++byteIndex) {
      result |= static_cast<std::uint64_t>(data_[offset_ - width + byteIndex]) << (8 * byteIndex);
    }
    value = result;
    return true;
  }

  const std::uint8_t *data_;
  std::size_t size_;
  std::size_t offset_ = 0;
  bool failed_ = false;
};

} // namespace game::serial

#endif // BLACKHOLE_GAME_SERIALIZE_BYTES_H
