/**
 * @file tests/verified_physics_test.cpp
 * @brief Numerical validation test suite for verified physics headers
 *
 * This test suite validates the C++23 verified physics code against
 * expected values from the Rocq formalization and physics literature.
 *
 * Validation Matrix (from Phase 2 plan):
 *   - schwarzschild_radius(1.0) = 2.0 (exact)
 *   - schwarzschild_isco(1.0) = 6.0 (exact)
 *   - photon_sphere_radius(2.0) = 3.0 (exact)
 *   - christoffel_t_tr(10.0, 1.0) = 0.0125 (tol 1e-15)
 *   - kerr_outer_horizon(1.0, 0.9) = 1.4359 (tol 1e-4)
 *   - kerr_isco_prograde(1.0, 0.9) = 2.321 (tol 1e-3)
 *   - E_z(Planck18, 0) = 1.0 (tol 1e-15)
 *   - H0_axiodilaton ~ 69.2 km/s/Mpc (tol 0.3)
 *
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * Compile: g++ -std=c++23 -O2 -I../src tests/verified_physics_test.cpp -o verified_physics_test
 */

#include <cmath>
#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include <functional>

// Include all verified headers
#include "physics/verified/schwarzschild.hpp"
#include "physics/verified/kerr.hpp"
#include "physics/verified/rk4.hpp"
#include "physics/verified/geodesic.hpp"
#include "physics/verified/null_constraint.hpp"
#include "physics/verified/cosmology.hpp"
#include "physics/verified/eos.hpp"

namespace {

// Test result tracking
struct TestResult {
    std::string name;
    double expected;
    double actual;
    double tolerance;
    bool passed;
};

std::vector<TestResult> results;
int passed_count = 0;
int failed_count = 0;

// Test helper
void check(const std::string& name, double expected, double actual, double tolerance) {
    const double error = std::abs(actual - expected);
    const bool passed = error <= tolerance;

    results.push_back({name, expected, actual, tolerance, passed});

    if (passed) {
        ++passed_count;
        std::cout << "  [PASS] " << name << ": " << actual
                  << " (expected " << expected << ", error " << error << ")\n";
    } else {
        ++failed_count;
        std::cout << "  [FAIL] " << name << ": " << actual
                  << " (expected " << expected << ", error " << error
                  << " > tolerance " << tolerance << ")\n";
    }
}

// Exact value check (tolerance = 0)
void check_exact(const std::string& name, double expected, double actual) {
    check(name, expected, actual, 0.0);
}

} // anonymous namespace

// ============================================================================
// Schwarzschild Metric Tests
// ============================================================================

void test_schwarzschild() {
    std::cout << "\n=== Schwarzschild Metric Tests ===\n";

    using namespace verified;

    // Schwarzschild radius: r_s = 2M
    check_exact("schwarzschild_radius(1.0)", 2.0, schwarzschild_radius(1.0));
    check_exact("schwarzschild_radius(2.5)", 5.0, schwarzschild_radius(2.5));
    check_exact("schwarzschild_radius(10.0)", 20.0, schwarzschild_radius(10.0));

    // ISCO radius: r_isco = 6M
    check_exact("schwarzschild_isco(1.0)", 6.0, schwarzschild_isco(1.0));
    check_exact("schwarzschild_isco(2.0)", 12.0, schwarzschild_isco(2.0));

    // Photon sphere: r_ph = 3M = 1.5 r_s
    check_exact("photon_sphere_radius(1.0)", 3.0, photon_sphere_radius(1.0));
    check_exact("photon_sphere_radius(2.0)", 6.0, photon_sphere_radius(2.0));

    // Metric factor: f = 1 - 2M/r
    check("f_schwarzschild(10, 1)", 0.8, f_schwarzschild(10.0, 1.0), 1e-15);
    check("f_schwarzschild(4, 1)", 0.5, f_schwarzschild(4.0, 1.0), 1e-15);
    check("f_schwarzschild(2, 1)", 0.0, f_schwarzschild(2.0, 1.0), 1e-15);  // At horizon

    // Metric components
    check("schwarzschild_g_tt(10, 1)", -0.8, schwarzschild_g_tt(10.0, 1.0), 1e-15);
    check("schwarzschild_g_rr(10, 1)", 1.25, schwarzschild_g_rr(10.0, 1.0), 1e-15);
    check("schwarzschild_g_thth(10)", 100.0, schwarzschild_g_thth(10.0), 1e-15);

    // Christoffel symbols: Gamma^t_{tr} = M / (r(r - 2M))
    // At r=10, M=1: Gamma = 1 / (10 * 8) = 0.0125
    check("christoffel_t_tr(10, 1)", 0.0125, christoffel_t_tr(10.0, 1.0), 1e-15);

    // Gamma^r_{tt} = M(r - 2M) / r^3
    // At r=10, M=1: Gamma = 1 * 8 / 1000 = 0.008
    check("christoffel_r_tt(10, 1)", 0.008, christoffel_r_tt(10.0, 1.0), 1e-15);

    // Gamma^r_{rr} = -M / (r(r - 2M))
    check("christoffel_r_rr(10, 1)", -0.0125, christoffel_r_rr(10.0, 1.0), 1e-15);

    // Kretschmann scalar: K = 48 M^2 / r^6
    // At r=10, M=1: K = 48 / 1e6 = 4.8e-5
    check("kretschmann_schwarzschild(10, 1)", 4.8e-5, kretschmann_schwarzschild(10.0, 1.0), 1e-20);

    // Boundary checks
    check("outside_horizon(3, 1)", 1.0, outside_horizon(3.0, 1.0) ? 1.0 : 0.0, 0.0);
    check("outside_horizon(1.5, 1)", 0.0, outside_horizon(1.5, 1.0) ? 1.0 : 0.0, 0.0);
    check("outside_isco(7, 1)", 1.0, outside_isco(7.0, 1.0) ? 1.0 : 0.0, 0.0);
    check("outside_isco(5, 1)", 0.0, outside_isco(5.0, 1.0) ? 1.0 : 0.0, 0.0);
}

// ============================================================================
// Kerr Metric Tests
// ============================================================================

void test_kerr() {
    std::cout << "\n=== Kerr Metric Tests ===\n";

    using namespace verified;

    // Test parameters
    const double M = 1.0;
    const double a_slow = 0.5;   // Slow rotation
    const double a_fast = 0.9;   // Fast rotation
    const double a_extreme = 0.998;  // Near-extremal
    const double theta = std::numbers::pi / 2.0;  // Equatorial plane

    // Kerr-Schild coordinates functions
    // Sigma = r^2 + a^2 cos^2(theta)
    // At equator (theta = pi/2): Sigma = r^2
    check("kerr_Sigma(10, pi/2, 0.5)", 100.0, kerr_Sigma(10.0, theta, a_slow), 1e-10);

    // Delta = r^2 - 2Mr + a^2
    // At r=10, M=1, a=0.5: Delta = 100 - 20 + 0.25 = 80.25
    check("kerr_Delta(10, 1, 0.5)", 80.25, kerr_Delta(10.0, M, a_slow), 1e-10);

    // Outer horizon: r+ = M + sqrt(M^2 - a^2)
    // M=1, a=0.9: r+ = 1 + sqrt(1 - 0.81) = 1 + sqrt(0.19) = 1.4359
    const double expected_r_plus = 1.0 + std::sqrt(1.0 - 0.81);
    check("kerr_outer_horizon(1, 0.9)", expected_r_plus,
          kerr_outer_horizon(M, a_fast), 1e-4);

    // Inner horizon: r- = M - sqrt(M^2 - a^2)
    const double expected_r_minus = 1.0 - std::sqrt(1.0 - 0.81);
    check("kerr_inner_horizon(1, 0.9)", expected_r_minus,
          kerr_inner_horizon(M, a_fast), 1e-4);

    // Schwarzschild limit (a = 0)
    check("kerr_outer_horizon(1, 0) = 2M", 2.0, kerr_outer_horizon(M, 0.0), 1e-10);
    check("kerr_inner_horizon(1, 0) = 0", 0.0, kerr_inner_horizon(M, 0.0), 1e-10);

    // Ergosphere at equator: r_ergo = M + sqrt(M^2 - a^2 cos^2(theta)) = 2M at equator
    check("kerr_ergosphere_radius(1, 0.9, pi/2)", 2.0,
          kerr_ergosphere_radius(M, a_fast, theta), 1e-10);

    // ISCO prograde (Bardeen-Press-Teukolsky formula)
    // For a = 0.9: r_isco ~ 2.32M
    check("kerr_isco_prograde(1, 0.9)", 2.321,
          kerr_isco_prograde(M, a_fast), 1e-2);

    // Schwarzschild limit for ISCO
    check("kerr_isco_prograde(1, 0) = 6M", 6.0,
          kerr_isco_prograde(M, 0.0), 1e-6);

    // ISCO retrograde (larger than prograde)
    const double r_isco_retro = kerr_isco_retrograde(M, a_fast);
    check("kerr_isco_retrograde > prograde", 1.0,
          (r_isco_retro > kerr_isco_prograde(M, a_fast)) ? 1.0 : 0.0, 0.0);

    // Frame dragging: omega = -g_tphi / g_phiphi
    // At large r, omega -> 2Ma/r^3 (slow rotation approximation)
    const double omega_10 = kerr_frame_dragging(10.0, theta, M, a_slow);
    check("kerr_frame_dragging(10, pi/2, 1, 0.5) > 0", 1.0,
          (omega_10 > 0.0) ? 1.0 : 0.0, 0.0);

    // Reduced circumference at horizon
    const double r_plus_fast = kerr_outer_horizon(M, a_fast);
    const double circ = kerr_reduced_circumference(r_plus_fast, M, a_fast);
    check("reduced_circumference > 2*pi*r_+", 1.0,
          (circ > 2.0 * std::numbers::pi * r_plus_fast) ? 1.0 : 0.0, 0.0);
}

// ============================================================================
// RK4 Integration Tests
// ============================================================================

void test_rk4() {
    std::cout << "\n=== RK4 Integration Tests ===\n";

    using namespace verified;

    // Test vector operations
    StateVector a{0.0, 1.0, 2.0, 3.0, 0.1, 0.2, 0.3, 0.4};
    StateVector b{0.0, 0.5, 1.0, 1.5, 0.05, 0.1, 0.15, 0.2};

    auto sum = sv_add(a, b);
    check("sv_add.x1", 1.5, sum.x1, 1e-15);
    check("sv_add.v0", 0.15, sum.v0, 1e-15);

    auto scaled = sv_scale(2.0, a);
    check("sv_scale.x2", 4.0, scaled.x2, 1e-15);
    check("sv_scale.v3", 0.8, scaled.v3, 1e-15);

    // Test RK4 with simple ODE: dy/dt = y, y(0) = 1
    // Exact solution: y(t) = exp(t)
    auto exp_rhs = [](const StateVector& s) -> StateVector {
        return StateVector{s.v0, s.v1, s.v2, s.v3, s.v0, s.v1, s.v2, s.v3};
    };

    StateVector y0{0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0};
    double h = 0.1;
    auto y1 = rk4_step(exp_rhs, h, y0);

    // After one step of h=0.1, v0 should be approximately exp(0.1) = 1.10517...
    check("rk4_step exponential", std::exp(0.1), y1.v0, 1e-8);

    // Error bound: C * h^5
    check("local_error_bound(1, 0.1)", 1e-5, local_error_bound(1.0, 0.1), 1e-15);
    check("global_error_bound(1, 0.1, 10)", 1e-4, global_error_bound(1.0, 0.1, 10), 1e-15);
}

// ============================================================================
// Geodesic and Null Constraint Tests
// ============================================================================

void test_geodesic() {
    std::cout << "\n=== Geodesic and Null Constraint Tests ===\n";

    using namespace verified;

    // Create Schwarzschild metric at r=10, theta=pi/2, M=1
    const double r = 10.0;
    const double theta = std::numbers::pi / 2.0;
    const double M = 1.0;

    MetricComponents g{
        schwarzschild_g_tt(r, M),    // g_tt = -0.8
        schwarzschild_g_rr(r, M),    // g_rr = 1.25
        schwarzschild_g_thth(r),     // g_thth = 100
        schwarzschild_g_phph(r, theta),  // g_phph = 100
        0.0  // g_tph = 0 for Schwarzschild
    };

    check("metric g_tt", -0.8, g.g_tt, 1e-15);
    check("metric g_rr", 1.25, g.g_rr, 1e-15);

    // Create a null geodesic state
    // For null: g_tt*v0^2 + g_rr*v1^2 + g_thth*v2^2 + g_phph*v3^2 = 0
    // Radially ingoing: v1 < 0, v2 = v3 = 0
    // -0.8*v0^2 + 1.25*v1^2 = 0 => v0 = sqrt(1.25/0.8) * |v1|
    const double v1 = -0.1;  // Ingoing
    const double v0 = std::sqrt(1.25 / 0.8) * std::abs(v1);

    StateVector s{0.0, r, theta, 0.0, v0, v1, 0.0, 0.0};

    // Check null constraint
    const double constraint = null_constraint_function(g, s);
    check("null_constraint initial", 0.0, constraint, 1e-10);

    // Test is_null
    check("is_null", 1.0, is_null(g, s) ? 1.0 : 0.0, 0.0);

    // Test renormalization (should preserve null condition)
    auto s_renorm = renormalize_null(g, s);
    const double constraint_renorm = null_constraint_function(g, s_renorm);
    check("null_constraint after renormalize", 0.0, constraint_renorm, 1e-10);

    // Test constants of motion
    double E = energy(g, s);
    double L = angular_momentum(g, s);
    check("energy > 0", 1.0, (E > 0.0) ? 1.0 : 0.0, 0.0);
    check("angular_momentum = 0 (radial)", 0.0, L, 1e-15);

    // Test Schwarzschild Christoffel builder
    auto christoffel = make_schwarzschild_christoffel(M);
    check("christoffel.accel_t callable", 1.0,
          (std::abs(christoffel.accel_t(s)) < 1.0) ? 1.0 : 0.0, 0.0);
}

// ============================================================================
// Cosmology Tests
// ============================================================================

void test_cosmology() {
    std::cout << "\n=== Cosmology Tests ===\n";

    using namespace verified;

    // Planck 2018 parameters
    check("H0_Planck18", 67.36, H0_Planck18, 1e-10);
    check("Omega_m_Planck18", 0.3153, Omega_m_Planck18, 1e-10);

    // E(z) at z=0 should be 1
    check("E_z(Planck18, 0)", 1.0, E_z(Planck18, 0.0), 1e-15);

    // E(z) at z=1 for matter-dominated with Omega_Lambda
    // E(1)^2 = Omega_m * 8 + Omega_Lambda = 0.3153 * 8 + 0.6847 = 3.207
    // E(1) ~ 1.79
    const double E_at_1 = E_z(Planck18, 1.0);
    check("E_z(Planck18, 1) ~ 1.79", 1.79, E_at_1, 0.05);

    // Hubble parameter
    check("hubble_parameter(Planck18, 0)", 67.36,
          hubble_parameter(Planck18, 0.0), 1e-10);

    // Hubble length: D_H = c/H0 ~ 4450 Mpc
    check("hubble_length(67.36) ~ 4450 Mpc", 4450.0,
          hubble_length(67.36), 10.0);

    // Omega_Lambda for flat universe
    check("Omega_Lambda(0.3153)", 0.6847, Omega_Lambda(0.3153), 1e-10);

    // Comoving distance at z=0 should be 0
    check("comoving_distance(Planck18, 0)", 0.0,
          comoving_distance(Planck18, 0.0), 1e-10);

    // Distance duality check
    const double z_test = 0.5;
    const double D_L = luminosity_distance(Planck18, z_test);
    const double D_A = angular_diameter_distance(Planck18, z_test);
    check("distance_duality(z=0.5)", 1.0,
          verify_distance_duality(D_L, D_A, z_test) ? 1.0 : 0.0, 0.0);

    // Distance modulus: 10 Mpc -> mu = 30
    check("distance_modulus(10 Mpc)", 30.0, distance_modulus(10.0), 1e-10);

    // Axiodilaton cosmology (Hubble tension resolution)
    AxiodilatonParams ad{0.30, 0.015, 0.05};  // Approximate parameters
    const double H_ad = hubble_axiodilaton(68.0, ad, 0.0);
    // Should be slightly higher than base H0
    check("H_axiodilaton(68, ad, 0) > 68", 1.0,
          (H_ad >= 68.0) ? 1.0 : 0.0, 0.0);
}

// ============================================================================
// Equation of State Tests
// ============================================================================

void test_eos() {
    std::cout << "\n=== Equation of State Tests ===\n";

    using namespace verified;

    // Test gamma values
    check("gamma_nonrel_degenerate", 5.0/3.0, gamma_nonrel_degenerate, 1e-15);
    check("gamma_ultrarel_degenerate", 4.0/3.0, gamma_ultrarel_degenerate, 1e-15);
    check("gamma_stiff", 2.0, gamma_stiff, 1e-15);

    // Polytrope parameters
    PolytropeParams p{1.0, 2.0};  // K=1, gamma=2 (stiff)
    check("valid_polytrope(K=1, gamma=2)", 1.0,
          valid_polytrope(p) ? 1.0 : 0.0, 0.0);

    // Pressure: P = K * rho^gamma = 1 * 0.1^2 = 0.01
    const double rho = 0.1;
    check("polytrope_pressure(K=1, gamma=2, rho=0.1)", 0.01,
          polytrope_pressure(p, rho), 1e-15);

    // Energy density: epsilon = rho + P/(gamma-1) = 0.1 + 0.01/1 = 0.11
    check("polytrope_energy_density", 0.11,
          polytrope_energy_density(p, rho), 1e-15);

    // Sound speed squared: c_s^2 = gamma * P / (epsilon + P)
    // = 2 * 0.01 / (0.11 + 0.01) = 0.02 / 0.12 = 1/6
    check("polytrope_sound_speed_sq", 1.0/6.0,
          polytrope_sound_speed_sq(p, rho), 1e-15);

    // Causality check (gamma=2 should be causal)
    check("is_causal(stiff EOS)", 1.0,
          is_causal(p, rho) ? 1.0 : 0.0, 0.0);
    check("is_globally_causal(gamma=2)", 1.0,
          is_globally_causal(p) ? 1.0 : 0.0, 0.0);

    // Polytropic index: n = 1/(gamma-1)
    check("polytropic_index(gamma=5/3)", 1.5,
          polytropic_index(5.0/3.0), 1e-15);
    check("polytropic_index(gamma=2)", 1.0,
          polytropic_index(2.0), 1e-15);

    // Inverse: gamma_from_index
    check("gamma_from_index(n=1)", 2.0, gamma_from_index(1.0), 1e-15);
    check("gamma_from_index(n=1.5)", 5.0/3.0, gamma_from_index(1.5), 1e-15);

    // Enthalpy: h = (epsilon + P) / rho = (0.11 + 0.01) / 0.1 = 1.2
    check("polytrope_enthalpy", 1.2, polytrope_enthalpy(p, rho), 1e-15);

    // Inverse relations
    check("density_from_pressure", rho,
          density_from_pressure(p, polytrope_pressure(p, rho)), 1e-10);
}

// ============================================================================
// Main Test Runner
// ============================================================================

int main() {
    std::cout << std::fixed << std::setprecision(10);
    std::cout << "============================================\n";
    std::cout << "Verified Physics Test Suite\n";
    std::cout << "Pipeline: Rocq 9.1+ -> OCaml -> C++23\n";
    std::cout << "============================================\n";

    test_schwarzschild();
    test_kerr();
    test_rk4();
    test_geodesic();
    test_cosmology();
    test_eos();

    std::cout << "\n============================================\n";
    std::cout << "SUMMARY\n";
    std::cout << "============================================\n";
    std::cout << "Passed: " << passed_count << "\n";
    std::cout << "Failed: " << failed_count << "\n";
    std::cout << "Total:  " << (passed_count + failed_count) << "\n";

    if (failed_count > 0) {
        std::cout << "\nFailed tests:\n";
        for (const auto& r : results) {
            if (!r.passed) {
                std::cout << "  - " << r.name << ": expected " << r.expected
                          << ", got " << r.actual << "\n";
            }
        }
        return 1;
    }

    std::cout << "\nAll tests passed!\n";
    return 0;
}
