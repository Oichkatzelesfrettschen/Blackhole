/**
 * @file photon_ring_test.cpp
 * @brief Kerr photon-orbit Lyapunov exponent against its defining integral.
 *
 * Gates:
 *   1. gamma = pi at a = 0 on r = 3 and the sentinel off it, and within a^2
 *      of pi at a = 1e-3 mid-shell (the closed form never divides by a^2, so
 *      the limit is continuous).
 *   2. gamma within 1e-14 relative of an mpmath evaluation of
 *      sqrt(R''(r)/2) * integral dtheta / sqrt(Theta) at a = 1e-3, 0.5, 0.9,
 *      0.99 across the shell (tests/photon_ring_reference.inc from
 *      scripts/gen_photon_ring_reference.py).
 *   3. gamma finite at both shell endpoints photonShell(a) for a from 1e-3 to
 *      0.9999999, and within 16 ulp times its r-conditioning of the referee's
 *      eta = 0 limit, which is pi at every equatorial photon orbit.
 *   4. gamma(a) = gamma(-a).
 *   5. Shell bounds r_+- = 3 at a = 0 and 1, 4 at a = 1; radii outside the
 *      shell return the divergentResult sentinel.
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <exception>
#include <iterator>
#include <limits>
#include <numbers>
#include <numeric>

#include "photon_ring.h"
#include "safe_limits.h"

using namespace physics;

namespace {

struct LyapunovRow {
  double a = 0.0;
  double r = 0.0;
  double gamma = 0.0;
};

struct LyapunovEndpointRow {
  double a = 0.0;
  double prograde = 0.0;
  double retrograde = 0.0;
};

#include "photon_ring_reference.inc"

int gPass = 0;
int gFail = 0;

void check(bool cond, const char *msg) {
  if (cond) {
    std::printf("  [PASS] %s\n", msg);
    ++gPass;
  } else {
    std::printf("  [FAIL] %s\n", msg);
    ++gFail;
  }
}

void testSchwarzschildLimit() {
  check(photonRingLyapunovExponent(0.0, 3.0) == std::numbers::pi &&
            photonRingLyapunovExponent(0.0, photonShell(0.0).prograde) == std::numbers::pi &&
            photonRingLyapunovExponent(0.0, photonShell(0.0).retrograde) == std::numbers::pi,
        "gamma = pi at a = 0 on the r = 3 shell");
  check(photonRingLyapunovExponent(0.0, 3.1) == divergentResult<double>() &&
            photonRingLyapunovExponent(0.0, 2.9) == divergentResult<double>(),
        "a = 0 radii off r = 3 return the divergent sentinel");
  const double a = 1.0e-3;
  const PhotonShell shell = photonShell(a);
  const double mid = 0.5 * (shell.prograde + shell.retrograde);
  const double dev = std::abs(photonRingLyapunovExponent(a, mid) - std::numbers::pi);
  std::printf("  a = 1e-3 mid-shell |gamma - pi| = %.3e (a^2 = %.1e)\n", dev, a * a);
  check(dev <= a * a, "gamma -> pi continuously: |gamma - pi| <= a^2 at a = 1e-3");
}

void testReferee() {
  double worst = 0.0;
  for (const LyapunovRow &row : LYAPUNOV_ROWS) {
    const double got = photonRingLyapunovExponent(row.a, row.r);
    const double rel = std::abs(got - row.gamma) / row.gamma;
    std::printf("  a = %-6.4g r = %.6f gamma = %.15f rel err %.2e\n", row.a, row.r, got, rel);
    worst = std::max(worst, rel);
  }
  check(worst <= 1.0e-14, "gamma within 1e-14 of the defining integral");
}

void testShellEndpoints() {
  // photonShell rounds r_+- to double, which can leave eta a few roundings
  // below zero; the endpoint must still evaluate as the equatorial orbit.
  // The referee sits at the exact endpoint of each double spin, photonShell's
  // radius within about an ulp of it; gamma's slope in r carries that ulp
  // (dgamma/dr reaches 1.5e4 at the a = 0.9999999 prograde edge), so the gate
  // is 16 u (1 + r |dgamma/dr| / gamma), the slope taken by a one-sided
  // difference into the shell.
  const double u = 0.5 * std::numeric_limits<double>::epsilon();
  double worstRatio = 0.0;
  double worstRel = 0.0;
  bool finite = true;
  for (const LyapunovEndpointRow &row : LYAPUNOV_ENDPOINT_ROWS) {
    const PhotonShell shell = photonShell(row.a);
    const std::array<double, 2> radii = {shell.prograde, shell.retrograde};
    const std::array<double, 2> refs = {row.prograde, row.retrograde};
    for (std::size_t i = 0; i < radii.size(); ++i) {
      const double r = radii.at(i);
      const double got = photonRingLyapunovExponent(row.a, r);
      finite = finite && got != divergentResult<double>();
      const double step = (i == 0 ? 1.0e-7 : -1.0e-7) * r;
      const double slope = (photonRingLyapunovExponent(row.a, r + step) - got) / step;
      const double rel = std::abs(got - refs.at(i)) / refs.at(i);
      worstRel = std::max(worstRel, rel);
      worstRatio = std::max(worstRatio, rel / (16.0 * u * (1.0 + (r * std::abs(slope) / got))));
    }
  }
  std::printf("  shell endpoints, %zu spins: max rel err %.2e, max err / bound %.2f\n",
              std::size(LYAPUNOV_ENDPOINT_ROWS), worstRel, worstRatio);
  check(finite, "gamma finite at both shell endpoints for a = 1e-3 .. 0.9999999");
  check(worstRatio <= 1.0, "endpoint gamma within 16 ulp x its r-conditioning of the eta = 0 limit");
}

void testSpinSymmetry() {
  const double worst =
      std::accumulate(std::begin(LYAPUNOV_ROWS), std::end(LYAPUNOV_ROWS), 0.0,
                      [](double w, const LyapunovRow &row) {
                        return std::max(w, std::abs(photonRingLyapunovExponent(-row.a, row.r) -
                                                    photonRingLyapunovExponent(row.a, row.r)));
                      });
  check(worst <= 1.0e-14, "gamma(-a) = gamma(a)");
}

void testShellBounds() {
  const PhotonShell s0 = photonShell(0.0);
  const PhotonShell s1 = photonShell(1.0);
  check(std::abs(s0.prograde - 3.0) < 1.0e-15 && std::abs(s0.retrograde - 3.0) < 1.0e-15,
        "r_+ = r_- = 3 at a = 0");
  check(std::abs(s1.prograde - 1.0) < 1.0e-12 && std::abs(s1.retrograde - 4.0) < 1.0e-12,
        "r_+ = 1, r_- = 4 at a = 1");
  const PhotonShell s9 = photonShell(0.9);
  check(photonRingLyapunovExponent(0.9, 0.9 * s9.prograde) == divergentResult<double>() &&
            photonRingLyapunovExponent(0.9, 1.1 * s9.retrograde) == divergentResult<double>(),
        "radii outside the shell return the divergent sentinel");
}

} // namespace

int main() try {
  std::printf("Schwarzschild limit:\n");
  testSchwarzschildLimit();
  std::printf("\nmpmath referee:\n");
  testReferee();
  testShellEndpoints();
  testSpinSymmetry();
  std::printf("\nShell bounds:\n");
  testShellBounds();

  std::printf("\n%d/%d tests passed.\n", gPass, gPass + gFail);
  if (gFail > 0) {
    std::printf("[FAILURE] One or more tests failed.\n\n");
    return 1;
  }
  std::printf("[ALL PASS]\n\n");
  return 0;
} catch (const std::exception &error) {
  return std::fprintf(stderr, "[FAIL] Unexpected exception: %s\n", error.what()) < 0 ? 2 : 1;
} catch (...) {
  return std::fprintf(stderr, "[FAIL] Unexpected nonstandard exception\n") < 0 ? 2 : 1;
}
