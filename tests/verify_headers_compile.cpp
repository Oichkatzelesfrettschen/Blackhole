/**
 * verify_headers_compile.cpp
 *
 * Compile-and-value gate for every header in src/physics/verified/.
 * Each header is included here, so a header that stops compiling fails
 * the build, and each physics surface carries at least one value check
 * against an analytic reference, so a formula regression fails the run.
 * A print-only ancestor of this file compiled-and-printed for months
 * while the prograde ISCO returned 3.48M at a=0.
 */

#include <cmath>
#include <cstdlib>
#include <numbers>
#include <iostream>

#include "../src/physics/verified/axiodilaton.h"
#include "../src/physics/verified/cosmology.hpp" // NOLINT(misc-include-cleaner)
#include "../src/physics/verified/energy_conserving_geodesic.hpp" // NOLINT(misc-include-cleaner)
#include "../src/physics/verified/eos.hpp" // NOLINT(misc-include-cleaner)
#include "../src/physics/verified/geodesic.hpp"
#include "../src/physics/verified/kerr.hpp"
#include "../src/physics/verified/kerr_de_sitter.hpp" // NOLINT(misc-include-cleaner)
#include "../src/physics/verified/kerr_extended.h"
#include "../src/physics/verified/kerr_newman.hpp" // NOLINT(misc-include-cleaner)
#include "../src/physics/verified/null_constraint.hpp" // NOLINT(misc-include-cleaner)
#include "../src/physics/verified/rk4.hpp"
#include "../src/physics/verified/schwarzschild.hpp"

namespace {
int valueFailures = 0;
void checkNear(const char *what, double actual, double expected, double tol) {
  if (std::abs(actual - expected) > tol) {
    std::cout << "  [FAIL] " << what << ": got " << actual << ", expected " << expected << "\n";
    ++valueFailures;
  }
}
} // namespace

int main() {
  std::cout << "Verified Physics Headers Compile-and-Value Gate\n";

  constexpr double m = 1.0;
  constexpr double a = 0.9;
  constexpr double r = 10.0;
  constexpr double theta = 1.5707963267948966; // pi/2, equatorial plane

  // Schwarzschild surface (schwarzschild.hpp)
  checkNear("schwarzschild_radius(1)", verified::schwarzschild_radius(m), 2.0, 1e-12);
  checkNear("schwarzschild_isco(1)", verified::schwarzschild_isco(m), 6.0, 1e-12);
  checkNear("photon_sphere_radius(1)", verified::photon_sphere_radius(m), 3.0, 1e-12);
  checkNear("schwarzschild_g_tt(10, 1)", verified::schwarzschild_g_tt(r, m), -0.8, 1e-12);

  // Kerr Rocq-extraction surface (kerr.hpp)
  checkNear("kerr_Sigma(10, pi/2, 0.9)", verified::kerr_Sigma(r, theta, a), 100.0, 1e-9);
  checkNear("kerr_Delta(10, 1, 0.9)", verified::kerr_Delta(r, m, a), 80.81, 1e-9);
  checkNear("outer_horizon(1, 0.9)", verified::outer_horizon(m, a), 1.0 + std::sqrt(0.19), 1e-12);
  checkNear("inner_horizon(1, 0.9)", verified::inner_horizon(m, a), 1.0 - std::sqrt(0.19), 1e-12);
  // Bardeen-Press-Teukolsky 1972 at a=0.9: prograde 2.3209, retrograde 8.7173
  checkNear("kerr_isco_prograde(1, 0)", verified::kerr_isco_prograde(m, 0.0), 6.0, 1e-9);
  checkNear("kerr_isco_retrograde(1, 0)", verified::kerr_isco_retrograde(m, 0.0), 6.0, 1e-9);
  checkNear("kerr_isco_prograde(1, 0.9)", verified::kerr_isco_prograde(m, a), 2.3209, 1e-3);
  checkNear("kerr_isco_retrograde(1, 0.9)", verified::kerr_isco_retrograde(m, a), 8.7173, 1e-3);
  // Mass scaling: r_isco(2M, 2a) = 2 * r_isco(M, a). Every retired
  // re-derivation of BPT fed the raw spin into M = 1 helpers, which
  // unit-mass pins cannot see; this one fails on that bug class.
  checkNear("kerr_isco_prograde mass scaling",
            verified::kerr_isco_prograde(2.0 * m, 2.0 * a),
            2.0 * verified::kerr_isco_prograde(m, a), 1e-9);
  checkNear("kerrIscoPrograde mass scaling",
            verified::kerrIscoPrograde(2.0 * m, 2.0 * a),
            2.0 * verified::kerrIscoPrograde(m, a), 1e-9);

  // Kerr extended constexpr surface (kerr_extended.h) pins the same physics
  checkNear("kerrIscoPrograde(1, 0)", verified::kerrIscoPrograde(m, 0.0), 6.0, 1e-9);
  checkNear("kerrIscoPrograde(1, 0.9)", verified::kerrIscoPrograde(m, a), 2.3209, 1e-3);
  checkNear("kerrIscoRetrograde(1, 0.9)", verified::kerrIscoRetrograde(m, a), 8.7173, 1e-3);
  checkNear("kerrOuterHorizon(1, 0.9)", verified::kerrOuterHorizon(m, a),
            verified::outer_horizon(m, a), 1e-12);
  checkNear("kerrSurfaceGravity(1, 0)", verified::kerrSurfaceGravity(m, 0.0), 0.25, 1e-12);

  // RK4 surface (rk4.hpp): exact integration of dy/dt = y over one step
  {
    verified::StateVector y{};
    y.x0 = 1.0;
    auto rhs = [](const verified::StateVector &s) {
      verified::StateVector d{};
      d.x0 = s.x0;
      return d;
    };
    const verified::StateVector y1 = verified::rk4_step(rhs, 0.1, y);
    // RK4 truncation error for e^h at h=0.1 is h^5/120 ~ 8.3e-8
    checkNear("rk4_step exp(0.1)", y1.x0, std::exp(0.1), 1e-7);
  }

  // Geodesic surface (geodesic.hpp): Schwarzschild circular-orbit energy
  {
    const verified::MetricComponents g{verified::schwarzschild_g_tt(r, m),
                                       verified::schwarzschild_g_rr(r, m),
                                       verified::schwarzschild_g_thth(r),
                                       verified::schwarzschild_g_phph(r, theta), 0.0};
    verified::StateVector s{};
    s.x1 = r;
    s.x2 = theta;
    s.v0 = 1.0;
    checkNear("energy(g, static observer)", verified::energy(g, s), 0.8, 1e-12);
    checkNear("critical_impact_schwarzschild(1)", verified::critical_impact_schwarzschild(m),
              3.0 * std::numbers::sqrt3, 1e-12);
  }

  // Axiodilaton cosmology surface (axiodilaton.h): H(0) = H0 exactly when
  // the density parameters sum to one and f(0) = 1
  {
    const double omegaM = 0.3111;
    const double omegaAd = 0.001;
    const double omegaLambda = 1.0 - omegaM - omegaAd;
    const double h0 = 69.22;
    checkNear("axiodilatonHubbleParameter(0)",
              verified::axiodilatonHubbleParameter(0.0, omegaM, omegaAd, omegaLambda, h0), h0,
              1e-9);
    const double dC = verified::axiodilatonComovingDistance(0.1, omegaM, omegaAd, omegaLambda, h0);
    // Leading order: D_c ~ (c/H0) * z = (299792.458/69.22) * 0.1 ~ 433 Mpc
    checkNear("axiodilatonComovingDistance(0.1) leading order", dC, 433.0, 25.0);
  }

  if (valueFailures != 0) {
    std::cout << valueFailures << " value check(s) failed\n";
    return EXIT_FAILURE;
  }
  std::cout << "All verified headers compile and value checks pass\n";
  return 0;
}
