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

#include <cmath>
#include <limits>

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
template<typename T>
[[nodiscard]] constexpr T safe_max() noexcept {
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
template<typename T>
[[nodiscard]] constexpr T safe_lowest() noexcept {
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
 * @tparam T Floating point type (must be double or float)
 * @return Positive infinity
 */
template<typename T>
[[nodiscard]] inline T safe_infinity() noexcept {
    // Use compiler builtins that bypass -ffinite-math-only
#if defined(__GNUC__) || defined(__clang__)
    if constexpr (std::is_same_v<T, double>) {
        return __builtin_huge_val();
    } else if constexpr (std::is_same_v<T, float>) {
        return __builtin_huge_valf();
    } else if constexpr (std::is_same_v<T, long double>) {
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
template<typename T>
[[nodiscard]] constexpr bool is_effectively_infinite(T x) noexcept {
    return x > T(0.99) * std::numeric_limits<T>::max();
}

/**
 * @brief Return infinity for error conditions, max() otherwise.
 *
 * When returning infinity to indicate "no valid solution", this
 * function provides a safe value that works with -ffast-math.
 * Callers should use is_effectively_infinite() to check results.
 *
 * @tparam T Floating point type
 * @return Large positive value representing "no solution"
 */
template<typename T>
[[nodiscard]] constexpr T divergent_result() noexcept {
    // Return a very large but finite value
    // This avoids UB with -ffast-math while still being "infinity-like"
    return std::numeric_limits<T>::max() / T(2);
}

// Clang warns about infinity/NaN checks even when using builtins with -ffast-math.
// We deliberately want to check for these edge cases, so locally disable the warning.
#if defined(__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wnan-infinity-disabled"
#endif

/**
 * @brief Check if a value is finite (not inf or NaN).
 *
 * Works correctly even with -ffast-math by using compiler builtins.
 * With -ffinite-math-only, std::isfinite can be optimized to always
 * return true, which defeats its purpose.
 *
 * @param x Value to check
 * @return true if x is finite
 */
template<typename T>
[[nodiscard]] inline bool safe_isfinite(T x) noexcept {
#if defined(__GNUC__) || defined(__clang__)
    // Use builtin that bypasses -ffinite-math-only optimization
    if constexpr (std::is_same_v<T, double>) {
        return __builtin_isfinite(x);
    } else if constexpr (std::is_same_v<T, float>) {
        return __builtin_isfinite(x);
    } else if constexpr (std::is_same_v<T, long double>) {
        return __builtin_isfinite(x);
    }
#else
    return std::isfinite(x);
#endif
}

/**
 * @brief Check if a value is NaN.
 *
 * Works correctly even with -ffast-math.
 *
 * @param x Value to check
 * @return true if x is NaN
 */
template<typename T>
[[nodiscard]] inline bool safe_isnan(T x) noexcept {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_isnan(x);
#else
    return std::isnan(x);
#endif
}

/**
 * @brief Check if a value is infinite.
 *
 * Works correctly even with -ffast-math.
 *
 * @param x Value to check
 * @return true if x is positive or negative infinity
 */
template<typename T>
[[nodiscard]] inline bool safe_isinf(T x) noexcept {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_isinf(x);
#else
    return std::isinf(x);
#endif
}

#if defined(__clang__)
#pragma clang diagnostic pop
#endif

} // namespace physics

#endif // PHYSICS_SAFE_LIMITS_H
