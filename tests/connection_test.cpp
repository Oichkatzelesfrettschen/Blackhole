/**
 * @file connection_test.cpp
 * @brief Validation tests for connection coefficients (Christoffel symbols).
 *
 * Tests verify:
 * - Metric tensor symmetry: g_μν = g_νμ
 * - Contravariant/covariant inverse: g^μα g_αν = δ^μ_ν
 * - Connection symmetry: Γ^α_μν = Γ^α_νμ
 * - Schwarzschild limit: Kerr with a=0 matches Schwarzschild
 * - Known analytic values at special points
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <random>

#include "physics/connection.h"
#include "physics/constants.h"
#include "physics/safe_limits.h"

namespace {

constexpr double TOLERANCE = 1e-10;

bool approxEq(double a, double b, double tol = TOLERANCE) {
  if (physics::safeIsnan(a) && physics::safeIsnan(b)) {
    return true;
  }
  if (physics::safeIsinf(a) && physics::safeIsinf(b) && (std::signbit(a) == std::signbit(b))) {
    return true;
  }
  double const scale = std::max({1.0, std::abs(a), std::abs(b)});
  return std::abs(a - b) <= tol * scale;
}

// Test metric tensor symmetry: g_μν = g_νμ
int testMetricSymmetry() {
  std::cout << "Testing metric tensor symmetry...\n";

  std::mt19937 rng(42); // NOLINT(cert-msc32-c,cert-msc51-cpp,bugprone-random-generator-seed) -- deterministic seed for reproducible test
  std::uniform_real_distribution<double> distR(2.5, 100.0);
  std::uniform_real_distribution<double> distTheta(0.1, physics::PI - 0.1);
  std::uniform_real_distribution<double> distA(0.0, 0.99);

  for (size_t i = 0; i < 50; ++i) {
    double const r = distR(rng);
    double const theta = distTheta(rng);
    double const a = distA(rng);
    double const rS = 2.0;

    auto gcov = physics::kerrGcov(r, theta, a, rS);
    auto gcon = physics::kerrGcon(r, theta, a, rS);

    // Check symmetry
    for (size_t mu = 0; mu < 4; ++mu) {
      for (size_t nu = mu + 1; nu < 4; ++nu) {
        if (!approxEq(gcov.at(mu).at(nu), gcov.at(nu).at(mu))) {
          std::cerr << "  FAIL: gcov[" << mu << "][" << nu << "] != gcov["
                    << nu << "][" << mu << "]\n";
          return 1;
        }
        if (!approxEq(gcon.at(mu).at(nu), gcon.at(nu).at(mu))) {
          std::cerr << "  FAIL: gcon[" << mu << "][" << nu << "] != gcon["
                    << nu << "][" << mu << "]\n";
          return 1;
        }
      }
    }
  }

  std::cout << "  PASS: Metric symmetry\n";
  return 0;
}

// Test g^μα g_αν = δ^μ_ν (inverse property)
int testMetricInverse() {
  std::cout << "Testing metric inverse property...\n";

  std::mt19937 rng(123); // NOLINT(cert-msc32-c,cert-msc51-cpp,bugprone-random-generator-seed) -- deterministic seed for reproducible test
  std::uniform_real_distribution<double> distR(3.0, 50.0);
  std::uniform_real_distribution<double> distTheta(0.2, physics::PI - 0.2);
  std::uniform_real_distribution<double> distA(0.0, 0.95);

  for (size_t i = 0; i < 50; ++i) {
    double const r = distR(rng);
    double const theta = distTheta(rng);
    double const a = distA(rng);
    double const rS = 2.0;

    auto gcov = physics::kerrGcov(r, theta, a, rS);
    auto gcon = physics::kerrGcon(r, theta, a, rS);

    // Compute g^μα g_αν
    for (size_t mu = 0; mu < 4; ++mu) {
      for (size_t nu = 0; nu < 4; ++nu) {
        double sum = 0.0;
        for (size_t alpha = 0; alpha < 4; ++alpha) {
          sum += gcon.at(mu).at(alpha) * gcov.at(alpha).at(nu);
        }

        double const expected = (mu == nu) ? 1.0 : 0.0;
        if (!approxEq(sum, expected, 1e-8)) {
          std::cerr << "  FAIL: g^" << mu << "α g_α" << nu << " = " << sum
                    << " expected " << expected << " at r=" << r
                    << " theta=" << theta << " a=" << a << "\n";
          return 1;
        }
      }
    }
  }

  std::cout << "  PASS: Metric inverse\n";
  return 0;
}

// Test connection symmetry in lower indices: Γ^α_μν = Γ^α_νμ
int testConnectionSymmetry() {
  std::cout << "Testing connection symmetry...\n";

  std::mt19937 rng(456); // NOLINT(cert-msc32-c,cert-msc51-cpp,bugprone-random-generator-seed) -- deterministic seed for reproducible test
  std::uniform_real_distribution<double> distR(2.5, 30.0);
  std::uniform_real_distribution<double> distTheta(0.3, physics::PI - 0.3);
  std::uniform_real_distribution<double> distA(0.0, 0.9);

  for (size_t i = 0; i < 50; ++i) {
    double const r = distR(rng);
    double const theta = distTheta(rng);
    double const a = distA(rng);
    double const rS = 2.0;

    auto conn = physics::kerrConnection(r, theta, a, rS);

    // Check symmetry in lower indices
    for (size_t alpha = 0; alpha < 4; ++alpha) {
      for (size_t mu = 0; mu < 4; ++mu) {
        for (size_t nu = mu + 1; nu < 4; ++nu) {
          if (!approxEq(conn.at(alpha).at(mu).at(nu), conn.at(alpha).at(nu).at(mu), 1e-9)) {
            std::cerr << "  FAIL: Γ^" << alpha << "_" << mu << nu
                      << " != Γ^" << alpha << "_" << nu << mu << "\n";
            std::cerr << "    " << conn.at(alpha).at(mu).at(nu) << " vs "
                      << conn.at(alpha).at(nu).at(mu) << "\n";
            return 1;
          }
        }
      }
    }
  }

  std::cout << "  PASS: Connection symmetry\n";
  return 0;
}

// Test Schwarzschild limit: Kerr with a=0 should match Schwarzschild formulas
int testSchwarzschildLimit() {
  std::cout << "Testing Schwarzschild limit (a=0)...\n";

  std::mt19937 rng(789); // NOLINT(cert-msc32-c,cert-msc51-cpp,bugprone-random-generator-seed) -- deterministic seed for reproducible test
  std::uniform_real_distribution<double> distR(3.0, 50.0);
  std::uniform_real_distribution<double> distTheta(0.3, physics::PI - 0.3);

  for (size_t i = 0; i < 30; ++i) {
    double const r = distR(rng);
    double const theta = distTheta(rng);
    double const rS = 2.0;

    auto connKerr = physics::kerrConnection(r, theta, 0.0, rS);
    auto connSchw = physics::schwarzschildConnection(r, theta, rS);

    // All components should match
    for (size_t alpha = 0; alpha < 4; ++alpha) {
      for (size_t mu = 0; mu < 4; ++mu) {
        for (size_t nu = 0; nu < 4; ++nu) {
          if (!approxEq(connKerr.at(alpha).at(mu).at(nu), connSchw.at(alpha).at(mu).at(nu), 1e-9)) {
            std::cerr << "  FAIL: Kerr(a=0) != Schwarzschild at Γ^" << alpha
                      << "_" << mu << nu << "\n";
            return 1;
          }
        }
      }
    }
  }

  std::cout << "  PASS: Schwarzschild limit\n";
  return 0;
}

// Test non-zero components exist for Schwarzschild
int testSchwarzschildNonzero() {
  std::cout << "Testing Schwarzschild non-zero components...\n";

  double const rS = 2.0;
  double const r = 10.0;
  double const theta = physics::PI / 2.0; // Equatorial plane

  auto conn = physics::schwarzschildConnection(r, theta, rS);

  // Key Schwarzschild Christoffel symbols should be non-zero
  // Γ^t_tr, Γ^r_tt, Γ^r_rr, Γ^r_θθ, Γ^r_φφ, Γ^θ_rθ, Γ^θ_φφ, Γ^φ_rφ, Γ^φ_θφ

  // Γ^t_tr should be positive (inward attraction)
  if (conn.at(0).at(0).at(1) <= 0.0) {
    std::cerr << "  FAIL: Γ^t_tr should be positive\n";
    return 1;
  }

  // Γ^r_tt should be positive (gravitational attraction)
  if (conn.at(1).at(0).at(0) <= 0.0) {
    std::cerr << "  FAIL: Γ^r_tt should be positive\n";
    return 1;
  }

  // Γ^r_rr should be negative
  if (conn.at(1).at(1).at(1) >= 0.0) {
    std::cerr << "  FAIL: Γ^r_rr should be negative\n";
    return 1;
  }

  // Γ^r_θθ should be negative (centripetal)
  if (conn.at(1).at(2).at(2) >= 0.0) {
    std::cerr << "  FAIL: Γ^r_θθ should be negative\n";
    return 1;
  }

  // Γ^θ_rθ should be positive
  if (conn.at(2).at(1).at(2) <= 0.0) {
    std::cerr << "  FAIL: Γ^θ_rθ should be positive\n";
    return 1;
  }

  // Γ^φ_rφ should be positive
  if (conn.at(3).at(1).at(3) <= 0.0) {
    std::cerr << "  FAIL: Γ^φ_rφ should be positive\n";
    return 1;
  }

  std::cout << "  PASS: Schwarzschild non-zero components\n";
  return 0;
}

// Test index raising/lowering roundtrip
int testIndexOperations() {
  std::cout << "Testing index raising/lowering...\n";

  double const r = 10.0;
  double const theta = physics::PI / 3.0;
  double const a = 0.5;
  double const rS = 2.0;

  auto gcov = physics::kerrGcov(r, theta, a, rS);
  auto gcon = physics::kerrGcon(r, theta, a, rS);

  std::array<double, 4> ucon = {1.0, 0.1, 0.05, 0.2};
  auto ucov = physics::lowerIndex(ucon, gcov);
  auto uconBack = physics::raiseIndex(ucov, gcon);

  for (size_t i = 0; i < 4; ++i) {
    if (!approxEq(ucon.at(i), uconBack.at(i), 1e-9)) {
      std::cerr << "  FAIL: raise/lower roundtrip failed for component " << i
                << "\n";
      return 1;
    }
  }

  std::cout << "  PASS: Index operations\n";
  return 0;
}

// Test geodesic acceleration has correct sign for radial motion
int testGeodesicAcceleration() {
  std::cout << "Testing geodesic acceleration...\n";

  // For a particle at rest at large r in Schwarzschild, the radial
  // acceleration should point inward (negative)
  double const r = 100.0;
  double const theta = physics::PI / 2.0;
  double const rS = 2.0;

  auto conn = physics::schwarzschildConnection(r, theta, rS);

  // Static observer: u^t = 1/sqrt(-g_tt), u^r = u^θ = u^φ = 0
  auto gcov = physics::schwarzschildGcov(r, theta, rS);
  double const uT = 1.0 / std::sqrt(-gcov.at(0).at(0));

  std::array<double, 4> const ucon = {uT, 0.0, 0.0, 0.0};
  auto acc = physics::geodesicAcceleration(ucon, conn);

  // Radial acceleration should be negative (inward)
  // a^r = -Γ^r_tt (u^t)² < 0
  if (acc.at(1) >= 0.0) {
    std::cerr << "  FAIL: Radial acceleration should be negative (inward)\n";
    std::cerr << "    a^r = " << acc.at(1) << "\n";
    return 1;
  }

  // Other accelerations should be zero for static observer at equator
  if (!approxEq(acc.at(0), 0.0, 1e-8) || !approxEq(acc.at(2), 0.0, 1e-8) ||
      !approxEq(acc.at(3), 0.0, 1e-8)) {
    std::cerr << "  FAIL: Non-radial acceleration should be zero\n";
    return 1;
  }

  std::cout << "  PASS: Geodesic acceleration\n";
  return 0;
}

} // namespace

int main() {
  std::cout << "=== Connection Coefficient Tests ===\n\n";

  int result = 0;

  result |= testMetricSymmetry();
  result |= testMetricInverse();
  result |= testConnectionSymmetry();
  result |= testSchwarzschildLimit();
  result |= testSchwarzschildNonzero();
  result |= testIndexOperations();
  result |= testGeodesicAcceleration();

  std::cout << "\n";
  if (result == 0) {
    std::cout << "All connection tests PASSED\n";
  } else {
    std::cout << "Some connection tests FAILED\n";
  }

  return result;
}
