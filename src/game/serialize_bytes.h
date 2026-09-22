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

#include <bit>
#include <cassert>
#include <cmath>
#include <cstdint>
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

} // namespace game::serial

#endif // BLACKHOLE_GAME_SERIALIZE_BYTES_H
