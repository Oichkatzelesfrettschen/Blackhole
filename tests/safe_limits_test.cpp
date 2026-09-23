/**
 * @file safe_limits_test.cpp
 * @brief Validation tests for fast-math-safe numeric limit helpers.
 *
 * This target intentionally builds WITHOUT the -fno-fast-math override
 * that other physics tests carry: safe_limits.h exists precisely to
 * behave correctly under -ffast-math / -ffinite-math-only, so the test
 * must exercise it under those flags. A regression here means the
 * infinity()=0 bug class silently returns.
 *
 * Tests verify:
 * - safeInfinity() produces a true IEEE infinity via compiler builtins
 *   even when -ffinite-math-only is active
 * - safeIsfinite/safeIsnan/safeIsinf classify builtin-produced values
 * - safeMax/safeLowest/divergentResult stay finite and ordered
 * - isEffectivelyInfinite matches the divergentResult contract
 */

#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <limits>

#include "physics/safe_limits.h"

namespace {

int failures = 0;

void expect(bool condition, const char *label) {
  if (condition) {
    std::cout << "  PASS: " << label << "\n";
  } else {
    std::cout << "  FAIL: " << label << "\n";
    ++failures;
  }
}

// Materialize a value from raw bits, the way non-finite data actually
// enters a fast-math build: from storage (files, GPU readbacks, IEEE-
// compiled modules), never from local arithmetic. Producing inf/NaN
// with fast-math arithmetic (e.g. inf - inf) is poison at birth and
// deliberately not tested.
//
// The value is written into a caller-owned object by reference and must
// stay in memory: under -ffinite-math-only, clang annotates by-value
// float/double parameters AND returns with nofpclass(inf nan), so a
// non-finite crossing any by-value boundary is poison. An earlier
// version of this helper returned T by value; under clang 22 thinLTO
// the poison propagated back into main() and collapsed it to a jump to
// address zero before the first statement executed.
template <typename T, typename Bits> void fromBits(Bits bits, T &out) {
  static_assert(sizeof(T) == sizeof(Bits));
  std::memcpy(&out, &bits, sizeof(out));
}

template <typename T> struct Pattern;
template <> struct Pattern<float> {
  static constexpr std::uint32_t INF = 0x7f800000U;
  static constexpr std::uint32_t NAN = 0x7fc00000U;
};
template <> struct Pattern<double> {
  static constexpr std::uint64_t INF = 0x7ff0000000000000ULL;
  static constexpr std::uint64_t NAN = 0x7ff8000000000000ULL;
};

template <typename T> void testType(const char *name) {
  std::cout << "Testing " << name << "...\n";

  T inf;
  fromBits(Pattern<T>::INF, inf);
  expect(physics::safeIsinf(inf), "bit-pattern inf is classified infinite");
  expect(!physics::safeIsfinite(inf), "bit-pattern inf is not finite");
  expect(!physics::safeIsnan(inf), "bit-pattern inf is not NaN");

  T nan;
  fromBits(Pattern<T>::NAN, nan);
  expect(physics::safeIsnan(nan), "bit-pattern NaN is classified NaN");
  expect(!physics::safeIsfinite(nan), "NaN is not finite");
  expect(!physics::safeIsinf(nan), "NaN is not infinite");

  // sign bit set on the inf pattern = negative infinity
  const auto signBit = decltype(Pattern<T>::INF){1} << (sizeof(T) * 8 - 1);
  T negInf;
  fromBits(static_cast<decltype(Pattern<T>::INF)>(Pattern<T>::INF | signBit), negInf);
  expect(physics::safeIsinf(negInf), "negative inf is classified infinite");

  expect(physics::safeIsfinite(T(0)), "zero is finite");
  expect(physics::safeIsfinite(std::numeric_limits<T>::max()), "max is finite");
  expect(!physics::safeIsnan(T(1)), "one is not NaN");

  expect(physics::safeMax<T>() == std::numeric_limits<T>::max(), "safeMax equals numeric max");
  expect(physics::safeLowest<T>() == std::numeric_limits<T>::lowest(),
         "safeLowest equals numeric lowest");
  expect(physics::safeLowest<T>() < physics::safeMax<T>(), "lowest < max ordering");

  const T divergent = physics::divergentResult<T>();
  expect(physics::safeIsfinite(divergent), "divergentResult is finite");
  expect(!physics::isEffectivelyInfinite(divergent),
         "divergentResult below the effective-infinity threshold");
  expect(physics::isEffectivelyInfinite(std::numeric_limits<T>::max()),
         "max is effectively infinite");
  expect(!physics::isEffectivelyInfinite(T(1)), "ordinary value is not effectively infinite");
}

} // namespace

int main() {
#if defined(__FAST_MATH__)
  std::cout << "Built with -ffast-math (the intended condition).\n";
#else
  std::cout << "NOTE: built without -ffast-math; the guarantees still "
               "hold but the regression condition is not exercised.\n";
#endif

  testType<float>("float");
  testType<double>("double");

  if (failures != 0) {
    std::cout << failures << " failure(s)\n";
    return EXIT_FAILURE;
  }
  std::cout << "All safe_limits tests passed\n";
  return EXIT_SUCCESS;
}
