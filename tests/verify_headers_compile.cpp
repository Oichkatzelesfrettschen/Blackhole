#include <iostream>
#include <iomanip>

// Test compilation of all verified headers
#include "../src/physics/verified/schwarzschild.h"
#include "../src/physics/verified/kerr.h"
#include "../src/physics/verified/rk4.h"
#include "../src/physics/verified/geodesic.h"
#include "../src/physics/verified/axiodilaton.h"

int main() {
    std::cout << "Verified Physics Headers Compilation Test\n";
    std::cout << "==========================================\n\n";

    // Test 1: Schwarzschild functions compile and execute
    std::cout << "Test 1: Schwarzschild Functions\n";
    constexpr double M = 1.0;
    constexpr double r_s = verified::schwarzschild_radius(M);
    constexpr double r_isco = verified::schwarzschild_isco(M);
    constexpr double r_photon = verified::photon_sphere_radius(M);

    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  schwarzschild_radius(1.0) = " << r_s << " (expected 2.0)\n";
    std::cout << "  schwarzschild_isco(1.0) = " << r_isco << " (expected 6.0)\n";
    std::cout << "  photon_sphere_radius(1.0) = " << r_photon << " (expected 3.0)\n";

    // Test 2: Schwarzschild metric components
    std::cout << "\nTest 2: Schwarzschild Metric Components\n";
    double r = 10.0;
    double g_tt = verified::schwarzschild_g_tt(r, M);
    std::cout << "  g_tt(r=10.0, M=1.0) = " << g_tt << " (expected -0.800000)\n";

    // Test 3: Kerr functions (runtime)
    std::cout << "\nTest 3: Kerr Metric Functions\n";
    double a = 0.9;
    double theta = 1.5707963267948966;  // pi/2 (equatorial plane)
    double kerr_sigma = verified::kerr_Sigma(r, theta, a);
    double kerr_delta = verified::kerr_Delta(r, M, a);
    std::cout << "  kerr_Sigma(r=10.0, theta=pi/2, a=0.9) = " << kerr_sigma << "\n";
    std::cout << "  kerr_Delta(r=10.0, M=1.0, a=0.9) = " << kerr_delta << "\n";

    // Test 4: Kerr horizons
    std::cout << "\nTest 4: Kerr Black Hole Horizons\n";
    double r_outer = verified::outer_horizon(M, a);
    double r_inner = verified::inner_horizon(M, a);
    std::cout << "  outer_horizon(M=1.0, a=0.9) = " << r_outer << " (expected ~1.436)\n";
    std::cout << "  inner_horizon(M=1.0, a=0.9) = " << r_inner << " (expected ~0.564)\n";

    // Test 5: ISCO computation
    std::cout << "\nTest 5: Bardeen-Press-Teukolsky ISCO\n";
    double isco_pro = verified::isco_radius_prograde(M, a);
    double isco_ret = verified::isco_radius_retrograde(M, a);
    std::cout << "  isco_prograde(M=1.0, a=0.9) = " << isco_pro << " (expected ~2.321)\n";
    std::cout << "  isco_retrograde(M=1.0, a=0.9) = " << isco_ret << " (expected ~8.77)\n";

    // Test 6: RK4 StateVector operations
    std::cout << "\nTest 6: RK4 State Vector Operations\n";
    verified::StateVector<double> state1 = {0.0, 10.0, 1.57, 0.0, 1.0, 0.01, 0.0, 0.1};
    verified::StateVector<double> state2 = {0.0, 0.1, 0.0, 0.0, 0.01, 0.001, 0.0, 0.001};
    auto state_sum = state1 + state2;
    auto state_scaled = state1 * 0.5;
    std::cout << "  StateVector addition: OK\n";
    std::cout << "  StateVector scaling: OK\n";
    std::cout << "  StateVector norm: " << state1.norm() << "\n";

    // Test 7: Geodesic functions
    std::cout << "\nTest 7: Geodesic Equations\n";
    auto geodesic_rhs = verified::schwarzschild_geodesic_rhs(state1, 0.0, M, 0.0);
    double E = verified::energy(state1, M, a);
    double L = verified::angular_momentum(state1, M, a);
    std::cout << "  schwarzschild_geodesic_rhs: computed\n";
    std::cout << "  energy(state) = " << E << "\n";
    std::cout << "  angular_momentum(state) = " << L << "\n";

    // Test 8: Cosmology functions
    std::cout << "\nTest 8: Axiodilaton Cosmology\n";
    double Omega_m = 0.3111;
    double Omega_ad = 0.001;
    double Omega_Lambda = 0.6878;
    double H0 = 69.22;
    double z = 0.1;

    double H_z = verified::axiodilaton_hubble_parameter(z, Omega_m, Omega_ad, Omega_Lambda, H0);
    double D_c = verified::axiodilaton_comoving_distance(z, Omega_m, Omega_ad, Omega_Lambda, H0);
    std::cout << "  H(z=0.1) = " << H_z << "\n";
    std::cout << "  D_c(z=0.1) = " << D_c << " Mpc\n";
    std::cout << "  H0_prediction = " << verified::axiodilaton_H0_prediction<double>() << " km/s/Mpc\n";

    // Test 9: Planck 2018 parameters
    std::cout << "\nTest 9: Planck 2018 + Axiodilaton Parameters\n";
    std::cout << "  Omega_m = " << verified::planck2018::Omega_m_planck<double>() << "\n";
    std::cout << "  Omega_ad = " << verified::planck2018::Omega_ad<double>() << "\n";
    std::cout << "  Omega_Lambda = " << verified::planck2018::Omega_Lambda_planck<double>() << "\n";

    // Test 10: Null geodesic initialization
    std::cout << "\nTest 10: Null Geodesic Initialization\n";
    double r_observer = 100.0;
    double b = 10.0;  // Impact parameter
    auto photon_state = verified::init_null_geodesic(r_observer, b, M);
    std::cout << "  init_null_geodesic(r=" << r_observer << ", b=" << b << ", M=" << M << ") OK\n";
    std::cout << "  Initial photon position: r=" << photon_state.x1 << ", theta=" << photon_state.x2 << "\n";

    std::cout << "\n==========================================\n";
    std::cout << "All verified header compilations successful!\n";

    return 0;
}
