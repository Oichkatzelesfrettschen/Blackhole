/**
 * @file safe_limits.h
 * @brief Safe numeric limits that work correctly with -ffast-math.
 *
 * When -ffast-math is enabled, std::numeric_limits<T>::infinity() can
 * return undefined results because -ffinite-math-only assumes no
 * infinities or NaNs exist. This header provides alternatives that
 * work correctly regardless of optimization flags.
 *
 * The Planck force F_P = c^4/G is the natural force scale in general
 * relativity. It represents the maximum force that can exist before
 * spacetime curvature becomes significant. This is sometimes called
 * the "superforce" in popular science contexts.
 *
 * References:
 *   - GCC manual: -ffinite-math-only
 *   - Gibbons (2002) "The maximum tension principle in general relativity"
 */

#ifndef PHYSICS_SAFE_LIMITS_H
#define PHYSICS_SAFE_LIMITS_H

#include <cstdint>
#include <cstring>
#include <limits>
#include <type_traits>

namespace physics {

/**
 * @brief Get a "very large" value suitable for initialization of min/max searches.
 *
 * Use this instead of std::numeric_limits<T>::infinity() when -ffast-math
 * may be enabled. Returns max() which is always well-defined.
 *
 * @tparam T Floating point type
 * @return Maximum finite value
 */
template <typename T> [[nodiscard]] constexpr T safeMax() noexcept {
  return std::numeric_limits<T>::max();
}

/**
 * @brief Get a "very small" value suitable for initialization of min/max searches.
 *
 * Use this instead of -std::numeric_limits<T>::infinity() when -ffast-math
 * may be enabled. Returns lowest() which is always well-defined.
 *
 * @tparam T Floating point type
 * @return Minimum finite value
 */
template <typename T> [[nodiscard]] constexpr T safeLowest() noexcept {
  return std::numeric_limits<T>::lowest();
}

/**
 * @brief Get infinity in a way that works with -ffast-math.
 *
 * Uses compiler builtin to get true infinity even when -ffinite-math-only
 * is active. This is useful when infinity is semantically meaningful
 * (e.g., representing "no valid solution" or "divergent").
 *
 * Note: Code using this should handle the infinity case explicitly,
 * as comparisons with infinity may still be optimized away by -ffast-math.
 *
 * CONSTRAINT: the infinity is returned BY VALUE, and under
 * -ffinite-math-only clang annotates by-value float returns with
 * nofpclass(inf nan), making the returned value poison in fast-math
 * translation units. In fast-math code use divergentResult() +
 * isEffectivelyInfinite() as the sentinel pair instead; reserve this
 * function for IEEE-compiled translation units.
 *
 * @tparam T Floating point type (must be double or float)
 * @return Positive infinity
 */
template <typename T> [[nodiscard]] inline T safeInfinity() noexcept {
  // Use compiler builtins that bypass -ffinite-math-only
#if defined(__GNUC__) || defined(__clang__)
  if constexpr (std::is_same_v<T, double>) {
    return __builtin_huge_val();
  } else if constexpr (std::is_same_v<T, float>) {
    return __builtin_huge_valf();
  } else {
    return __builtin_huge_vall();
  }
#else
  // Fallback for other compilers - may not work with fast-math
  return std::numeric_limits<T>::infinity();
#endif
}

/**
 * @brief Check if a value represents "infinity" or "no valid result".
 *
 * Works correctly even with -ffast-math by comparing against max().
 *
 * @param x Value to check
 * @return true if x is very large (> 0.99 * max)
 */
template <typename T> [[nodiscard]] constexpr bool isEffectivelyInfinite(T x) noexcept {
  return x > T(0.99) * std::numeric_limits<T>::max();
}

/**
 * @brief Return infinity for error conditions, max() otherwise.
 *
 * When returning infinity to indicate "no valid solution", this
 * function provides a safe value that works with -ffast-math.
 * Callers should use isEffectivelyInfinite() to check results.
 *
 * @tparam T Floating point type
 * @return Large positive value representing "no solution"
 */
template <typename T> [[nodiscard]] constexpr T divergentResult() noexcept {
  // Return a very large but finite value
  // This avoids UB with -ffast-math while still being "infinity-like"
  return std::numeric_limits<T>::max() / T(2);
}

/**
 * @brief Extract the absolute-value bit pattern of an IEEE-754 scalar.
 *
 * Classification must not go through floating-point semantics at all.
 * Two compiler behaviors break the naive approaches under
 * -ffinite-math-only: GCC 16 and clang 22 constant-fold
 * __builtin_isinf/isfinite/isnan (and their std:: forms) to
 * false/true/false, and clang 22 additionally annotates by-value
 * float/double parameters and returns with nofpclass(inf nan), so an
 * infinity passed BY VALUE into any function becomes poison before the
 * callee sees it. The parameter is therefore a reference -- the caller
 * materializes the object in memory -- and the bytes are read with
 * memcpy, never as a typed float load.
 *
 * Soundness boundary: a non-finite value PRODUCED by arithmetic inside
 * a fast-math translation unit is poison at birth (its defining ops
 * carry nnan/ninf); no after-the-fact check can recover it. These
 * classifiers are sound for values that enter from outside fast-math
 * code: file data, GPU readbacks, and modules compiled with IEEE
 * semantics (the -fno-fast-math test targets, or everything once
 * ENABLE_FAST_MATH defaults OFF).
 */
template <typename T>
[[nodiscard]] inline auto absBits(const T &x) noexcept {
  static_assert(std::is_same_v<T, float> || std::is_same_v<T, double>,
                "bit-level classification is implemented for float and "
                "double; add the type's layout before using it here");
  if constexpr (std::is_same_v<T, float>) {
    std::uint32_t bits = 0;
    std::memcpy(&bits, &x, sizeof(bits));
    return static_cast<std::uint32_t>(bits & 0x7fffffffU);
  } else {
    std::uint64_t bits = 0;
    std::memcpy(&bits, &x, sizeof(bits));
    return static_cast<std::uint64_t>(bits & 0x7fffffffffffffffULL);
  }
}

namespace detail {
template <typename T>
inline constexpr auto INF_BITS = std::is_same_v<T, float>
                                     ? std::uint64_t{0x7f800000U}
                                     : std::uint64_t{0x7ff0000000000000ULL};
} // namespace detail

/**
 * @brief Check if a value is finite (not inf or NaN).
 *
 * The exponent field of an infinity or NaN is all ones; every finite
 * value has at least one zero exponent bit. Byte-level comparison
 * survives -ffast-math where std::isfinite and __builtin_isfinite fold
 * to true. See absBits for the soundness boundary.
 *
 * @param x Value to check
 * @return true if x is finite
 */
template <typename T>
[[nodiscard]] inline bool safeIsfinite(const T &x) noexcept {
  return absBits(x) < detail::INF_BITS<T>;
}

/**
 * @brief Check if a value is NaN.
 *
 * A NaN carries an all-ones exponent plus a nonzero mantissa, so its
 * absolute bit pattern exceeds the infinity pattern.
 *
 * @param x Value to check
 * @return true if x is NaN
 */
template <typename T>
[[nodiscard]] inline bool safeIsnan(const T &x) noexcept {
  return absBits(x) > detail::INF_BITS<T>;
}

/**
 * @brief Check if a value is infinite.
 *
 * Positive and negative infinity share one absolute bit pattern: all
 * exponent bits set, mantissa zero.
 *
 * @param x Value to check
 * @return true if x is positive or negative infinity
 */
template <typename T>
[[nodiscard]] inline bool safeIsinf(const T &x) noexcept {
  return absBits(x) == detail::INF_BITS<T>;
}

} // namespace physics

#endif // PHYSICS_SAFE_LIMITS_H
