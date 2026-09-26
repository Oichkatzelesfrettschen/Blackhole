#include <cmath>
#include <cstdio>
#include "physics/verified/energy_conserving_geodesic.hpp"
int main() {
  // Schwarzschild r=10, equatorial radial-plus-azimuthal null ray with a 1e-6 relative norm drift.
  const double r = 10.0, f = 1.0 - 2.0 / r;
  verified::MetricComponents g(-f, 1.0 / f, r * r, r * r, 0.0);
  const double vt = 1.0 / f, vph = 0.03;
  const double vr = std::sqrt((f * vt * vt - r * r * vph * vph) / (1.0 / f)) * (1.0 + 1e-6);
  verified::StateVector s{0, r, M_PI / 2, 0, vt, vr, 0.0, vph};
  auto c = verified::applyConstraintCorrection(g, s, 0.0);
  std::printf("before: v_r=%.6e norm=%.3e | after: v_r=%.6e norm=%.3e\n", s.v1, verified::computeMetricNorm(g, s), c.v1,
              verified::computeMetricNorm(g, c));
}
