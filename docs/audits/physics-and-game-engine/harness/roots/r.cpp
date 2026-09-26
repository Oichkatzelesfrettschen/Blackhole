#include <cstdio>
#include "physics/analytic_kerr_geodesic.h"
int main() {
  const double M = 1.0, a = 0.9;
  for (double rr : {1.8, 2.5, 3.0, 3.5}) {
    const double D = rr * rr - 2 * rr + a * a;
    const double xi = -(rr * rr * rr - 3 * M * rr * rr + a * a * rr + a * a * M) / (a * (rr - M));
    const double eta = rr * rr * rr * (4 * M * D - rr * (rr - M) * (rr - M)) / (a * a * (rr - M) * (rr - M));
    auto c = physics::radialQuarticCoeffs(a, xi, eta);
    auto R = physics::findRadialRoots(c);
    std::printf("r_ph=%.2f nReal=%d roots:", rr, R.nReal);
    for (auto z : R.roots) std::printf(" (%.9f,%.2e)", z.real(), z.imag());
    std::puts("");
  }
}
