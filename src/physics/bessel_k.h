/**
 * @file bessel_k.h
 * @brief Scaled modified Bessel K values from a fixed trapezoid kernel.
 *
 * DLMF 10.32.9 gives e^x K_nu(x) as the integral of
 * exp(-x (cosh(t) - 1)) cosh(nu t) over t in [0, infinity). The scaled tail
 * e^x integral_x^infinity K_nu(s) ds uses the same integrand divided by
 * cosh(t). The kernel uses cosh(t) - 1 = 2 sinh(t/2)^2 and 128 trapezoid
 * intervals. Its endpoint starts at acosh(1 + 40/x) and receives four fixed
 * updates with the largest evaluated order. tests/bessel_k_test.cpp compares
 * both integrals with mpmath reference values.
 */

#ifndef PHYSICS_BESSEL_K_H
#define PHYSICS_BESSEL_K_H

#include <cmath>

namespace physics {

template <typename T> struct BesselK012Values {
  T scaledK0;
  T scaledK1;
  T scaledK2;
};

template <typename T> struct BesselKAndTailValues {
  T scaledK;
  T scaledTail;
};

template <typename T> struct SynchrotronBesselValues {
  T scaledKTwoThirds;
  T scaledTailFiveThirds;
};

namespace detail {

template <typename T> struct BesselKSum {
  T value = T(0);
  T correction = T(0);

  void add(T term) {
    const T adjusted = term - correction;
    const T next = value + adjusted;
    correction = (next - value) - adjusted;
    value = next;
  }
};

// acosh(1 + y) without forming 1 + y, which rounds to 1 once y falls below
// the spacing at 1 (x above about 3.6e17 in binary64).
template <typename T> [[nodiscard]] inline T acoshOnePlus(T y) {
  return std::log1p(y + std::sqrt(y * (T(2) + y)));
}

template <typename T> [[nodiscard]] inline T besselKUpperLimit(T x, T nuMax) {
  const T inverseX = T(1) / x;
  T upper = acoshOnePlus(T(40) * inverseX);
  upper = acoshOnePlus((T(40) + (nuMax * upper)) * inverseX);
  upper = acoshOnePlus((T(40) + (nuMax * upper)) * inverseX);
  upper = acoshOnePlus((T(40) + (nuMax * upper)) * inverseX);
  upper = acoshOnePlus((T(40) + (nuMax * upper)) * inverseX);
  return upper;
}

template <typename T> [[nodiscard]] inline T besselKExponential(T x, T t) {
  const T halfSinh = std::sinh(T(0.5) * t);
  return std::exp(-(T(2) * x * halfSinh * halfSinh));
}

template <typename T>
[[nodiscard]] inline BesselKAndTailValues<T> besselKAndTailOrder(T nu, T x, T nuMax) {
  constexpr int intervalCount = 128;
  const T upper = besselKUpperLimit(x, nuMax);
  const T step = upper / T(intervalCount);
  BesselKSum<T> scaledKSum;
  BesselKSum<T> scaledTailSum;
  const T firstK = T(1);
  scaledKSum.add(T(0.5) * firstK);
  scaledTailSum.add(T(0.5) * firstK);
  for (int interval = 1; interval < intervalCount; ++interval) {
    const T t = T(interval) * step;
    const T scaledKIntegrand = besselKExponential(x, t) * std::cosh(nu * t);
    scaledKSum.add(scaledKIntegrand);
    scaledTailSum.add(scaledKIntegrand / std::cosh(t));
  }
  const T lastK = besselKExponential(x, upper) * std::cosh(nu * upper);
  scaledKSum.add(T(0.5) * lastK);
  scaledTailSum.add(T(0.5) * (lastK / std::cosh(upper)));
  return {
      .scaledK = scaledKSum.value * step,
      .scaledTail = scaledTailSum.value * step,
  };
}

} // namespace detail

template <typename T> [[nodiscard]] inline T scaledBesselK(T nu, T x) {
  return detail::besselKAndTailOrder(nu, x, nu).scaledK;
}

template <typename T> [[nodiscard]] inline T scaledBesselKTail(T nu, T x) {
  return detail::besselKAndTailOrder(nu, x, nu).scaledTail;
}

template <typename T> [[nodiscard]] inline BesselKAndTailValues<T> scaledBesselKAndTail(T nu, T x) {
  return detail::besselKAndTailOrder(nu, x, nu);
}

template <typename T> [[nodiscard]] inline BesselK012Values<T> scaledBesselK012(T x) {
  constexpr int intervalCount = 128;
  const T upper = detail::besselKUpperLimit(x, T(2));
  const T step = upper / T(intervalCount);
  detail::BesselKSum<T> scaledK0Sum;
  detail::BesselKSum<T> scaledK1Sum;
  detail::BesselKSum<T> scaledK2Sum;
  scaledK0Sum.add(T(0.5));
  scaledK1Sum.add(T(0.5));
  scaledK2Sum.add(T(0.5));
  for (int interval = 1; interval < intervalCount; ++interval) {
    const T t = T(interval) * step;
    const T exponential = detail::besselKExponential(x, t);
    scaledK0Sum.add(exponential);
    scaledK1Sum.add(exponential * std::cosh(t));
    scaledK2Sum.add(exponential * std::cosh(T(2) * t));
  }
  const T lastExponential = detail::besselKExponential(x, upper);
  scaledK0Sum.add(T(0.5) * lastExponential);
  scaledK1Sum.add(T(0.5) * lastExponential * std::cosh(upper));
  scaledK2Sum.add(T(0.5) * lastExponential * std::cosh(T(2) * upper));
  return {
      .scaledK0 = scaledK0Sum.value * step,
      .scaledK1 = scaledK1Sum.value * step,
      .scaledK2 = scaledK2Sum.value * step,
  };
}

template <typename T> [[nodiscard]] inline SynchrotronBesselValues<T> scaledSynchrotronBessel(T x) {
  constexpr int intervalCount = 128;
  const T orderTwoThirds = T(2) / T(3);
  const T orderFiveThirds = T(5) / T(3);
  const T upper = detail::besselKUpperLimit(x, orderFiveThirds);
  const T step = upper / T(intervalCount);
  detail::BesselKSum<T> scaledKSum;
  detail::BesselKSum<T> scaledTailSum;
  scaledKSum.add(T(0.5));
  scaledTailSum.add(T(0.5));
  for (int interval = 1; interval < intervalCount; ++interval) {
    const T t = T(interval) * step;
    const T exponential = detail::besselKExponential(x, t);
    const T scaledKIntegrand = exponential * std::cosh(orderTwoThirds * t);
    const T scaledTailIntegrand = exponential * std::cosh(orderFiveThirds * t) / std::cosh(t);
    scaledKSum.add(scaledKIntegrand);
    scaledTailSum.add(scaledTailIntegrand);
  }
  const T lastExponential = detail::besselKExponential(x, upper);
  scaledKSum.add(T(0.5) * lastExponential * std::cosh(orderTwoThirds * upper));
  scaledTailSum.add(T(0.5) * lastExponential * std::cosh(orderFiveThirds * upper) / std::cosh(upper));
  return {
      .scaledKTwoThirds = scaledKSum.value * step,
      .scaledTailFiveThirds = scaledTailSum.value * step,
  };
}

} // namespace physics

#endif // PHYSICS_BESSEL_K_H
