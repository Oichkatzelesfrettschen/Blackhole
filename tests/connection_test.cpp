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

#include "physics/connection.h"
#include "physics/schwarzschild.h"
#include "physics/safe_limits.h"

#include <cmath>
#include <cstdlib>
#include <iostream>
#include <random>

static constexpr double TOLERANCE = 1e-10;

static bool approx_eq(double a, double b, double tol = TOLERANCE) {
  if (physics::safe_isnan(a) && physics::safe_isnan(b))
    return true;
  if (physics::safe_isinf(a) && physics::safe_isinf(b) && (std::signbit(a) == std::signbit(b)))
    return true;
  double scale = std::max(1.0, std::max(std::abs(a), std::abs(b)));
  return std::abs(a - b) <= tol * scale;
}

// Test metric tensor symmetry: g_μν = g_νμ
static int test_metric_symmetry() {
  std::cout << "Testing metric tensor symmetry...\n";

  std::mt19937 rng(42);
  std::uniform_real_distribution<double> dist_r(2.5, 100.0);
  std::uniform_real_distribution<double> dist_theta(0.1, physics::PI - 0.1);
  std::uniform_real_distribution<double> dist_a(0.0, 0.99);

  for (size_t i = 0; i < 50; ++i) {
    double r = dist_r(rng);
    double theta = dist_theta(rng);
    double a = dist_a(rng);
    double r_s = 2.0;

    auto gcov = physics::kerr_gcov(r, theta, a, r_s);
    auto gcon = physics::kerr_gcon(r, theta, a, r_s);

    // Check symmetry
    for (size_t mu = 0; mu < 4; ++mu) {
      for (size_t nu = mu + 1; nu < 4; ++nu) {
        if (!approx_eq(gcov[mu][nu], gcov[nu][mu])) {
          std::cerr << "  FAIL: gcov[" << mu << "][" << nu << "] != gcov["
                    << nu << "][" << mu << "]\n";
          return 1;
        }
        if (!approx_eq(gcon[mu][nu], gcon[nu][mu])) {
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
static int test_metric_inverse() {
  std::cout << "Testing metric inverse property...\n";

  std::mt19937 rng(123);
  std::uniform_real_distribution<double> dist_r(3.0, 50.0);
  std::uniform_real_distribution<double> dist_theta(0.2, physics::PI - 0.2);
  std::uniform_real_distribution<double> dist_a(0.0, 0.95);

  for (size_t i = 0; i < 50; ++i) {
    double r = dist_r(rng);
    double theta = dist_theta(rng);
    double a = dist_a(rng);
    double r_s = 2.0;

    auto gcov = physics::kerr_gcov(r, theta, a, r_s);
    auto gcon = physics::kerr_gcon(r, theta, a, r_s);

    // Compute g^μα g_αν
    for (size_t mu = 0; mu < 4; ++mu) {
      for (size_t nu = 0; nu < 4; ++nu) {
        double sum = 0.0;
        for (size_t alpha = 0; alpha < 4; ++alpha) {
          sum += gcon[mu][alpha] * gcov[alpha][nu];
        }

        double expected = (mu == nu) ? 1.0 : 0.0;
        if (!approx_eq(sum, expected, 1e-8)) {
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
static int test_connection_symmetry() {
  std::cout << "Testing connection symmetry...\n";

  std::mt19937 rng(456);
  std::uniform_real_distribution<double> dist_r(2.5, 30.0);
  std::uniform_real_distribution<double> dist_theta(0.3, physics::PI - 0.3);
  std::uniform_real_distribution<double> dist_a(0.0, 0.9);

  for (size_t i = 0; i < 50; ++i) {
    double r = dist_r(rng);
    double theta = dist_theta(rng);
    double a = dist_a(rng);
    double r_s = 2.0;

    auto conn = physics::kerr_connection(r, theta, a, r_s);

    // Check symmetry in lower indices
    for (size_t alpha = 0; alpha < 4; ++alpha) {
      for (size_t mu = 0; mu < 4; ++mu) {
        for (size_t nu = mu + 1; nu < 4; ++nu) {
          if (!approx_eq(conn[alpha][mu][nu], conn[alpha][nu][mu], 1e-9)) {
            std::cerr << "  FAIL: Γ^" << alpha << "_" << mu << nu
                      << " != Γ^" << alpha << "_" << nu << mu << "\n";
            std::cerr << "    " << conn[alpha][mu][nu] << " vs "
                      << conn[alpha][nu][mu] << "\n";
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
static int test_schwarzschild_limit() {
  std::cout << "Testing Schwarzschild limit (a=0)...\n";

  std::mt19937 rng(789);
  std::uniform_real_distribution<double> dist_r(3.0, 50.0);
  std::uniform_real_distribution<double> dist_theta(0.3, physics::PI - 0.3);

  for (size_t i = 0; i < 30; ++i) {
    double r = dist_r(rng);
    double theta = dist_theta(rng);
    double r_s = 2.0;

    auto conn_kerr = physics::kerr_connection(r, theta, 0.0, r_s);
    auto conn_schw = physics::schwarzschild_connection(r, theta, r_s);

    // All components should match
    for (size_t alpha = 0; alpha < 4; ++alpha) {
      for (size_t mu = 0; mu < 4; ++mu) {
        for (size_t nu = 0; nu < 4; ++nu) {
          if (!approx_eq(conn_kerr[alpha][mu][nu], conn_schw[alpha][mu][nu],
                         1e-9)) {
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
static int test_schwarzschild_nonzero() {
  std::cout << "Testing Schwarzschild non-zero components...\n";

  double r_s = 2.0;
  double r = 10.0;
  double theta = physics::PI / 2.0; // Equatorial plane

  auto conn = physics::schwarzschild_connection(r, theta, r_s);

  // Key Schwarzschild Christoffel symbols should be non-zero
  // Γ^t_tr, Γ^r_tt, Γ^r_rr, Γ^r_θθ, Γ^r_φφ, Γ^θ_rθ, Γ^θ_φφ, Γ^φ_rφ, Γ^φ_θφ

  // Γ^t_tr should be positive (inward attraction)
  if (conn[0][0][1] <= 0.0) {
    std::cerr << "  FAIL: Γ^t_tr should be positive\n";
    return 1;
  }

  // Γ^r_tt should be positive (gravitational attraction)
  if (conn[1][0][0] <= 0.0) {
    std::cerr << "  FAIL: Γ^r_tt should be positive\n";
    return 1;
  }

  // Γ^r_rr should be negative
  if (conn[1][1][1] >= 0.0) {
    std::cerr << "  FAIL: Γ^r_rr should be negative\n";
    return 1;
  }

  // Γ^r_θθ should be negative (centripetal)
  if (conn[1][2][2] >= 0.0) {
    std::cerr << "  FAIL: Γ^r_θθ should be negative\n";
    return 1;
  }

  // Γ^θ_rθ should be positive
  if (conn[2][1][2] <= 0.0) {
    std::cerr << "  FAIL: Γ^θ_rθ should be positive\n";
    return 1;
  }

  // Γ^φ_rφ should be positive
  if (conn[3][1][3] <= 0.0) {
    std::cerr << "  FAIL: Γ^φ_rφ should be positive\n";
    return 1;
  }

  std::cout << "  PASS: Schwarzschild non-zero components\n";
  return 0;
}

// Test index raising/lowering roundtrip
static int test_index_operations() {
  std::cout << "Testing index raising/lowering...\n";

  double r = 10.0, theta = physics::PI / 3.0, a = 0.5, r_s = 2.0;

  auto gcov = physics::kerr_gcov(r, theta, a, r_s);
  auto gcon = physics::kerr_gcon(r, theta, a, r_s);

  std::array<double, 4> ucon = {1.0, 0.1, 0.05, 0.2};
  auto ucov = physics::lower_index(ucon, gcov);
  auto ucon_back = physics::raise_index(ucov, gcon);

  for (size_t i = 0; i < 4; ++i) {
    if (!approx_eq(ucon[i], ucon_back[i], 1e-9)) {
      std::cerr << "  FAIL: raise/lower roundtrip failed for component " << i
                << "\n";
      return 1;
    }
  }

  std::cout << "  PASS: Index operations\n";
  return 0;
}

// Test geodesic acceleration has correct sign for radial motion
static int test_geodesic_acceleration() {
  std::cout << "Testing geodesic acceleration...\n";

  // For a particle at rest at large r in Schwarzschild, the radial
  // acceleration should point inward (negative)
  double r = 100.0, theta = physics::PI / 2.0, r_s = 2.0;

  auto conn = physics::schwarzschild_connection(r, theta, r_s);

  // Static observer: u^t = 1/sqrt(-g_tt), u^r = u^θ = u^φ = 0
  auto gcov = physics::schwarzschild_gcov(r, theta, r_s);
  double u_t = 1.0 / std::sqrt(-gcov[0][0]);

  std::array<double, 4> ucon = {u_t, 0.0, 0.0, 0.0};
  auto acc = physics::geodesic_acceleration(ucon, conn);

  // Radial acceleration should be negative (inward)
  // a^r = -Γ^r_tt (u^t)² < 0
  if (acc[1] >= 0.0) {
    std::cerr << "  FAIL: Radial acceleration should be negative (inward)\n";
    std::cerr << "    a^r = " << acc[1] << "\n";
    return 1;
  }

  // Other accelerations should be zero for static observer at equator
  if (!approx_eq(acc[0], 0.0, 1e-8) || !approx_eq(acc[2], 0.0, 1e-8) ||
      !approx_eq(acc[3], 0.0, 1e-8)) {
    std::cerr << "  FAIL: Non-radial acceleration should be zero\n";
    return 1;
  }

  std::cout << "  PASS: Geodesic acceleration\n";
  return 0;
}

int main() {
  std::cout << "=== Connection Coefficient Tests ===\n\n";

  int result = 0;

  result |= test_metric_symmetry();
  result |= test_metric_inverse();
  result |= test_connection_symmetry();
  result |= test_schwarzschild_limit();
  result |= test_schwarzschild_nonzero();
  result |= test_index_operations();
  result |= test_geodesic_acceleration();

  std::cout << "\n";
  if (result == 0) {
    std::cout << "All connection tests PASSED\n";
  } else {
    std::cout << "Some connection tests FAILED\n";
  }

  return result;
}
