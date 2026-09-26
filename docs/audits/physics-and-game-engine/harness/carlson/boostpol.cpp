// Boost.Math default policy promotes double -> long double (x87 80-bit on x86-64).
// Measure cost/accuracy of the calls analytic_kerr_geodesic.h makes, with and without promotion.
#include <chrono>
#include <cmath>
#include <cstdio>
#include <vector>
#include <algorithm>
#include <boost/math/special_functions/ellint_1.hpp>
#include <boost/math/special_functions/jacobi_elliptic.hpp>
#include <boost/math/special_functions/ellint_rf.hpp>
using namespace boost::math::policies;
using NoPromote = policy<promote_double<false>>;
template <class F> double ns(F f, int n) {
  double best = 1e30;
  for (int r = 0; r < 5; ++r) {
    volatile double sink = 0; auto t0 = std::chrono::steady_clock::now();
    for (int i = 0; i < n; ++i) sink = sink + f(i);
    auto t1 = std::chrono::steady_clock::now();
    best = std::min(best, std::chrono::duration<double, std::nano>(t1 - t0).count() / n);
  }
  return best;
}
int main() {
  const int n = 200000;
  std::vector<double> k(n), u(n);
  for (int i = 0; i < n; ++i) { k[i] = 0.999 * (i % 997) / 997.0; u[i] = 0.01 + 5.0 * (i % 1009) / 1009.0; }
  double maxRel = 0, maxAbs = 0;
  for (int i = 0; i < n; i += 7) {
    const double a = boost::math::ellint_1(k[i]), b = boost::math::ellint_1(k[i], NoPromote());
    maxRel = std::max(maxRel, std::abs(a - b) / a);
    const double s1 = boost::math::jacobi_sn(k[i], u[i]), s2 = boost::math::jacobi_sn(k[i], u[i], NoPromote());
    maxAbs = std::max(maxAbs, std::abs(s1 - s2));
  }
  std::printf("ellint_1: promoted %.1f ns | promote_double<false> %.1f ns | max rel diff %.2e\n",
              ns([&](int i) { return boost::math::ellint_1(k[i]); }, n),
              ns([&](int i) { return boost::math::ellint_1(k[i], NoPromote()); }, n), maxRel);
  std::printf("jacobi_sn: promoted %.1f ns | promote_double<false> %.1f ns | max abs diff %.2e\n",
              ns([&](int i) { return boost::math::jacobi_sn(k[i], u[i]); }, n),
              ns([&](int i) { return boost::math::jacobi_sn(k[i], u[i], NoPromote()); }, n), maxAbs);
  std::printf("ellint_rf(0,1-k^2,1): promoted %.1f ns | promote_double<false> %.1f ns\n",
              ns([&](int i) { return boost::math::ellint_rf(0.0, 1 - k[i] * k[i], 1.0); }, n),
              ns([&](int i) { return boost::math::ellint_rf(0.0, 1 - k[i] * k[i], 1.0, NoPromote()); }, n));
}
