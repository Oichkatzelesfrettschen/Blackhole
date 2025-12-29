/**
 * @file compat.h
 * @brief C++ version compatibility layer with fallbacks.
 *
 * Provides unified interface for C++23/20/17 features with graceful degradation.
 * Include this header instead of directly using version-specific features.
 *
 * Detected at compile time via BLACKHOLE_CXX23, BLACKHOLE_CXX20, BLACKHOLE_CXX17
 */

#ifndef BLACKHOLE_COMPAT_H
#define BLACKHOLE_COMPAT_H

// ============================================================================
// Version Detection
// ============================================================================

// Fallback detection if CMake didn't set macros
#ifndef BLACKHOLE_CXX_STANDARD
#if __cplusplus >= 202302L
#define BLACKHOLE_CXX_STANDARD 23
#define BLACKHOLE_CXX23 1
#define BLACKHOLE_CXX20 1
#define BLACKHOLE_CXX17 1
#elif __cplusplus >= 202002L
#define BLACKHOLE_CXX_STANDARD 20
#define BLACKHOLE_CXX20 1
#define BLACKHOLE_CXX17 1
#elif __cplusplus >= 201703L
#define BLACKHOLE_CXX_STANDARD 17
#define BLACKHOLE_CXX17 1
#else
#error "Blackhole requires at least C++17"
#endif
#endif

// ============================================================================
// Feature Test Macros
// ============================================================================

// Check for specific library features
#ifdef __has_include
#define BLACKHOLE_HAS_INCLUDE(x) __has_include(x)
#else
#define BLACKHOLE_HAS_INCLUDE(x) 0
#endif

#ifdef __cpp_concepts
#define BLACKHOLE_HAS_CONCEPTS 1
#else
#define BLACKHOLE_HAS_CONCEPTS 0
#endif

#ifdef __cpp_lib_expected
#define BLACKHOLE_HAS_EXPECTED 1
#else
#define BLACKHOLE_HAS_EXPECTED 0
#endif

#ifdef __cpp_lib_ranges
#define BLACKHOLE_HAS_RANGES 1
#else
#define BLACKHOLE_HAS_RANGES 0
#endif

#ifdef __cpp_lib_format
#define BLACKHOLE_HAS_FORMAT 1
#else
#define BLACKHOLE_HAS_FORMAT 0
#endif

#ifdef __cpp_lib_span
#define BLACKHOLE_HAS_SPAN 1
#else
#define BLACKHOLE_HAS_SPAN 0
#endif

#ifdef __cpp_constexpr
#if __cpp_constexpr >= 202211L
#define BLACKHOLE_CONSTEXPR23 constexpr
#elif __cpp_constexpr >= 201907L
#define BLACKHOLE_CONSTEXPR23 constexpr
#else
#define BLACKHOLE_CONSTEXPR23 inline
#endif
#else
#define BLACKHOLE_CONSTEXPR23 inline
#endif

// ============================================================================
// Standard Library Includes with Fallbacks
// ============================================================================

#include <cmath>
#include <limits>
#include <optional>
#include <type_traits>
#include <utility>

// std::expected (C++23) or fallback
#if BLACKHOLE_HAS_EXPECTED
#include <expected>
namespace blackhole {
template <typename T, typename E>
using expected = std::expected<T, E>;
template <typename E>
using unexpected = std::unexpected<E>;
} // namespace blackhole
#else
// Simple fallback implementation
#include <variant>
namespace blackhole {

template <typename E>
class unexpected {
public:
  explicit unexpected(E e) : error_(std::move(e)) {}
  const E &error() const & { return error_; }
  E &error() & { return error_; }
  E &&error() && { return std::move(error_); }

private:
  E error_;
};

template <typename T, typename E>
class expected {
public:
  using value_type = T;
  using error_type = E;

  expected() : data_(T{}) {}
  expected(const T &val) : data_(val) {}
  expected(T &&val) : data_(std::move(val)) {}
  expected(const unexpected<E> &err) : data_(err.error()) {}
  expected(unexpected<E> &&err) : data_(std::move(err).error()) {}

  bool has_value() const { return std::holds_alternative<T>(data_); }
  explicit operator bool() const { return has_value(); }

  T &value() & { return std::get<T>(data_); }
  const T &value() const & { return std::get<T>(data_); }
  T &&value() && { return std::get<T>(std::move(data_)); }

  E &error() & { return std::get<E>(data_); }
  const E &error() const & { return std::get<E>(data_); }

  T &operator*() & { return value(); }
  const T &operator*() const & { return value(); }
  T *operator->() { return &value(); }
  const T *operator->() const { return &value(); }

  template <typename U>
  T value_or(U &&default_value) const & {
    return has_value() ? value() : static_cast<T>(std::forward<U>(default_value));
  }

private:
  std::variant<T, E> data_;
};
} // namespace blackhole
#endif

// std::span (C++20) or fallback
#if BLACKHOLE_HAS_SPAN
#include <span>
namespace blackhole {
template <typename T, std::size_t Extent = std::dynamic_extent>
using span = std::span<T, Extent>;
} // namespace blackhole
#else
namespace blackhole {
inline constexpr std::size_t dynamic_extent = static_cast<std::size_t>(-1);

template <typename T, std::size_t Extent = dynamic_extent>
class span {
public:
  using element_type = T;
  using value_type = std::remove_cv_t<T>;
  using size_type = std::size_t;
  using pointer = T *;
  using const_pointer = const T *;
  using reference = T &;
  using iterator = pointer;

  constexpr span() noexcept : data_(nullptr), size_(0) {}
  constexpr span(pointer ptr, size_type count) : data_(ptr), size_(count) {}
  template <std::size_t N>
  constexpr span(T (&arr)[N]) noexcept : data_(arr), size_(N) {}

  constexpr pointer data() const noexcept { return data_; }
  constexpr size_type size() const noexcept { return size_; }
  constexpr bool empty() const noexcept { return size_ == 0; }

  constexpr reference operator[](size_type idx) const { return data_[idx]; }
  constexpr reference front() const { return data_[0]; }
  constexpr reference back() const { return data_[size_ - 1]; }

  constexpr iterator begin() const noexcept { return data_; }
  constexpr iterator end() const noexcept { return data_ + size_; }

private:
  pointer data_;
  size_type size_;
};
} // namespace blackhole
#endif

// ============================================================================
// Concepts (C++20) or SFINAE fallbacks
// ============================================================================

#if BLACKHOLE_HAS_CONCEPTS
#include <concepts>

namespace blackhole {

template <typename T>
concept Numeric = std::is_arithmetic_v<T>;

template <typename T>
concept FloatingPoint = std::floating_point<T>;

template <typename T>
concept Integral = std::integral<T>;

// Physics-specific concepts
template <typename T>
concept PhysicalQuantity = requires(T a, T b) {
  { a + b } -> std::same_as<T>;
  { a - b } -> std::same_as<T>;
  { a *double{} } -> std::same_as<T>;
  { a / double{} } -> std::same_as<T>;
};

} // namespace blackhole

#define BLACKHOLE_REQUIRES(concept) requires concept
#define BLACKHOLE_CONCEPT(name, ...) template <typename T> concept name = __VA_ARGS__

#else
// SFINAE fallbacks for C++17

namespace blackhole {

template <typename T, typename = void>
struct is_numeric : std::false_type {};

template <typename T>
struct is_numeric<T, std::enable_if_t<std::is_arithmetic_v<T>>> : std::true_type {};

template <typename T>
inline constexpr bool is_numeric_v = is_numeric<T>::value;

} // namespace blackhole

#define BLACKHOLE_REQUIRES(concept)
#define BLACKHOLE_CONCEPT(name, ...)

#endif

// ============================================================================
// Constexpr Math (C++23 brings more constexpr math)
// ============================================================================

namespace blackhole {
namespace math {

// constexpr sqrt for compile-time calculations (C++23 has std::sqrt constexpr)
#if defined(BLACKHOLE_CXX23) && defined(__cpp_lib_constexpr_cmath)
using std::sqrt;
using std::abs;
using std::sin;
using std::cos;
#else
// Newton-Raphson sqrt for constexpr contexts
BLACKHOLE_CONSTEXPR23 double sqrt(double x) {
  if (x < 0)
    return std::numeric_limits<double>::quiet_NaN();
  if (x == 0)
    return 0;

  double guess = x;
  double prev = 0;
  while (guess != prev) {
    prev = guess;
    guess = 0.5 * (guess + x / guess);
  }
  return guess;
}

BLACKHOLE_CONSTEXPR23 double abs(double x) { return x < 0 ? -x : x; }

// For runtime, delegate to std::
inline double sin(double x) { return std::sin(x); }
inline double cos(double x) { return std::cos(x); }
#endif

// Physical constants as constexpr
inline constexpr double PI = 3.14159265358979323846;
inline constexpr double TWO_PI = 2.0 * PI;
inline constexpr double HALF_PI = PI / 2.0;
inline constexpr double DEG_TO_RAD = PI / 180.0;
inline constexpr double RAD_TO_DEG = 180.0 / PI;

} // namespace math
} // namespace blackhole

// ============================================================================
// Attribute Macros
// ============================================================================

// [[nodiscard]] with message (C++20)
#if defined(BLACKHOLE_CXX20)
#define BLACKHOLE_NODISCARD(msg) [[nodiscard(msg)]]
#else
#define BLACKHOLE_NODISCARD(msg) [[nodiscard]]
#endif

// [[likely]] and [[unlikely]] (C++20)
#if defined(BLACKHOLE_CXX20)
#define BLACKHOLE_LIKELY [[likely]]
#define BLACKHOLE_UNLIKELY [[unlikely]]
#else
#define BLACKHOLE_LIKELY
#define BLACKHOLE_UNLIKELY
#endif

// [[assume]] (C++23) or compiler-specific
#if defined(BLACKHOLE_CXX23) && defined(__cpp_lib_assume)
#define BLACKHOLE_ASSUME(expr) [[assume(expr)]]
#elif defined(__GNUC__)
#define BLACKHOLE_ASSUME(expr) __builtin_assume(expr)
#elif defined(_MSC_VER)
#define BLACKHOLE_ASSUME(expr) __assume(expr)
#else
#define BLACKHOLE_ASSUME(expr) ((void)0)
#endif

// ============================================================================
// Structured Bindings Enhancement
// ============================================================================

// Helper for returning multiple values with named fields
namespace blackhole {

template <typename T1, typename T2>
struct Pair {
  T1 first;
  T2 second;

  // Structured binding support
  template <std::size_t I>
  auto &get() & {
    if constexpr (I == 0)
      return first;
    else
      return second;
  }

  template <std::size_t I>
  const auto &get() const & {
    if constexpr (I == 0)
      return first;
    else
      return second;
  }
};

template <typename T1, typename T2, typename T3>
struct Triple {
  T1 first;
  T2 second;
  T3 third;

  template <std::size_t I>
  auto &get() & {
    if constexpr (I == 0)
      return first;
    else if constexpr (I == 1)
      return second;
    else
      return third;
  }

  template <std::size_t I>
  const auto &get() const & {
    if constexpr (I == 0)
      return first;
    else if constexpr (I == 1)
      return second;
    else
      return third;
  }
};

} // namespace blackhole

// Structured binding support
namespace std {
template <typename T1, typename T2>
struct tuple_size<blackhole::Pair<T1, T2>> : std::integral_constant<std::size_t, 2> {};

template <std::size_t I, typename T1, typename T2>
struct tuple_element<I, blackhole::Pair<T1, T2>> {
  using type = std::conditional_t<I == 0, T1, T2>;
};

template <typename T1, typename T2, typename T3>
struct tuple_size<blackhole::Triple<T1, T2, T3>> : std::integral_constant<std::size_t, 3> {};

template <std::size_t I, typename T1, typename T2, typename T3>
struct tuple_element<I, blackhole::Triple<T1, T2, T3>> {
  using type = std::conditional_t<I == 0, T1, std::conditional_t<I == 1, T2, T3>>;
};
} // namespace std

#endif // BLACKHOLE_COMPAT_H
