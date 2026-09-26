/**
 * @file photon_ring_test.cpp
 * @brief Kerr photon-orbit Lyapunov exponent against its defining integral.
 *
 * Gates:
 *   1. gamma = pi at a = 0, and within a^2 of pi at a = 1e-3 mid-shell (the
 *      closed form never divides by a^2, so the limit is continuous).
 *   2. gamma within 1e-14 relative of an mpmath evaluation of
 *      sqrt(R''(r)/2) * integral dtheta / sqrt(Theta) at a = 1e-3, 0.5, 0.9,
 *      0.99 across the shell (tests/photon_ring_reference.inc from
 *      scripts/gen_photon_ring_reference.py).
 *   3. gamma(a) = gamma(-a).
 *   4. Shell bounds r_+- = 3 at a = 0 and 1, 4 at a = 1; radii outside the
 *      shell return the divergentResult sentinel.
 */

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <exception>
#include <iterator>
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

constexpr LyapunovRow LYAPUNOV_ROWS[] = {
#include "photon_ring_reference.inc"
};

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
  check(photonRingLyapunovExponent(0.0, 3.0) == std::numbers::pi, "gamma = pi at a = 0");
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
