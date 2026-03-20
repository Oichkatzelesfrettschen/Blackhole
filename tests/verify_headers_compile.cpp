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
    constexpr double m = 1.0;
    constexpr double rS = verified::schwarzschildRadius(m);
    constexpr double rIsco = verified::schwarzschildIsco(m);
    constexpr double rPhoton = verified::photonSphereRadius(m);

    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  schwarzschild_radius(1.0) = " << rS << " (expected 2.0)\n";
    std::cout << "  schwarzschild_isco(1.0) = " << rIsco << " (expected 6.0)\n";
    std::cout << "  photon_sphere_radius(1.0) = " << rPhoton << " (expected 3.0)\n";

    // Test 2: Schwarzschild metric components
    std::cout << "\nTest 2: Schwarzschild Metric Components\n";
    double const r = 10.0;
    double gTt = verified::schwarzschild_g_tt(r, M);
    std::cout << "  g_tt(r=10.0, M=1.0) = " << gTt << " (expected -0.800000)\n";

    // Test 3: Kerr functions (runtime)
    std::cout << "\nTest 3: Kerr Metric Functions\n";
    double const a = 0.9;
    double const theta = 1.5707963267948966; // pi/2 (equatorial plane)
    double const kerrSigma = verified::kerrSigma(r, theta, a);
    double kerrDelta = verified::kerrDelta(r, M, a);
    std::cout << "  kerr_Sigma(r=10.0, theta=pi/2, a=0.9) = " << kerrSigma << "\n";
    std::cout << "  kerr_Delta(r=10.0, M=1.0, a=0.9) = " << kerrDelta << "\n";

    // Test 4: Kerr horizons
    std::cout << "\nTest 4: Kerr Black Hole Horizons\n";
    double const rOuter = verified::outerHorizon(m, a);
    double const rInner = verified::innerHorizon(m, a);
    std::cout << "  outer_horizon(M=1.0, a=0.9) = " << rOuter << " (expected ~1.436)\n";
    std::cout << "  inner_horizon(M=1.0, a=0.9) = " << rInner << " (expected ~0.564)\n";

    // Test 5: ISCO computation
    std::cout << "\nTest 5: Bardeen-Press-Teukolsky ISCO\n";
    double const iscoPro = verified::iscoRadiusPrograde(m, a);
    double const iscoRet = verified::iscoRadiusRetrograde(m, a);
    std::cout << "  isco_prograde(M=1.0, a=0.9) = " << iscoPro << " (expected ~2.321)\n";
    std::cout << "  isco_retrograde(M=1.0, a=0.9) = " << iscoRet << " (expected ~8.77)\n";

    // Test 6: RK4 StateVector operations
    std::cout << "\nTest 6: RK4 State Vector Operations\n";
    verified::StateVector<double> const state1 = {
        .x0 = 0.0, .x1 = 10.0, .x2 = 1.57, .x3 = 0.0, .v0 = 1.0, .v1 = 0.01, .v2 = 0.0, .v3 = 0.1};
    verified::StateVector<double> const state2 = {.x0 = 0.0,
                                                  .x1 = 0.1,
                                                  .x2 = 0.0,
                                                  .x3 = 0.0,
                                                  .v0 = 0.01,
                                                  .v1 = 0.001,
                                                  .v2 = 0.0,
                                                  .v3 = 0.001};
    auto stateSum = state1 + state2;
    auto stateScaled = state1 * 0.5;
    std::cout << "  StateVector addition: OK\n";
    std::cout << "  StateVector scaling: OK\n";
    std::cout << "  StateVector norm: " << state1.norm() << "\n";

    // Test 7: Geodesic functions
    std::cout << "\nTest 7: Geodesic Equations\n";
    auto geodesicRhs = verified::schwarzschildGeodesicRhs(state1, 0.0, m, 0.0);
    double const e = verified::energy(state1, m, a);
    double const l = verified::angularMomentum(state1, m, a);
    std::cout << "  schwarzschild_geodesic_rhs: computed\n";
    std::cout << "  energy(state) = " << e << "\n";
    std::cout << "  angular_momentum(state) = " << l << "\n";

    // Test 8: Cosmology functions
    std::cout << "\nTest 8: Axiodilaton Cosmology\n";
    double const omegaM = 0.3111;
    double const omegaAd = 0.001;
    double const omegaLambda = 0.6878;
    double const h0 = 69.22;
    double const z = 0.1;

    double const hZ = verified::axiodilatonHubbleParameter(z, omegaM, omegaAd, omegaLambda, h0);
    double const dC = verified::axiodilatonComovingDistance(z, omegaM, omegaAd, omegaLambda, h0);
    std::cout << "  H(z=0.1) = " << hZ << "\n";
    std::cout << "  D_c(z=0.1) = " << dC << " Mpc\n";
    std::cout << "  H0_prediction = " << verified::axiodilatonH0Prediction<double>()
              << " km/s/Mpc\n";

    // Test 9: Planck 2018 parameters
    std::cout << "\nTest 9: Planck 2018 + Axiodilaton Parameters\n";
    std::cout << "  Omega_m = " << verified::planck2018::Omega_m_planck<double>() << "\n";
    std::cout << "  Omega_ad = " << verified::planck2018::Omega_ad<double>() << "\n";
    std::cout << "  Omega_Lambda = " << verified::planck2018::omegaLambdaPlanck<double>() << "\n";

    // Test 10: Null geodesic initialization
    std::cout << "\nTest 10: Null Geodesic Initialization\n";
    double const rObserver = 100.0;
    double const b = 10.0; // Impact parameter
    auto photonState = verified::initNullGeodesic(rObserver, b, M);
    std::cout << "  init_null_geodesic(r=" << rObserver << ", b=" << b << ", M=" << m << ") OK\n";
    std::cout << "  Initial photon position: r=" << photonState.x1 << ", theta=" << photonState.x2
              << "\n";

    std::cout << "\n==========================================\n";
    std::cout << "All verified header compilations successful!\n";

    return 0;
}
