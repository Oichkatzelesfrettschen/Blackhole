/**
 * @file wiregrid_overlay_test.cpp
 * @brief Headless validation of the Boyer-Lindquist coordinate wiregrid overlay math.
 *
 * WHY: The per-pixel wiregrid overlay (shader/include/wiregrid.glsl and
 *      src/cuda/device_physics.cuh d_wiregrid_overlay) evaluates Kerr ergosphere
 *      and event-horizon formulas per pixel.  These are pure analytic functions
 *      with known closed-form results and can be validated without a GL or CUDA
 *      context by porting the identical math to C++.
 *
 * WHAT: Each test verifies one invariant of the Kerr overlay geometry:
 *   1. Event horizon r_+ = M + sqrt(M^2 - a^2) at known spin values.
 *   2. Ergosphere equatorial radius r_ergo(theta=pi/2) = M + sqrt(M^2) = 2M
 *      for all spins (cos(pi/2) = 0, so a^2 cos^2 drops out).
 *   3. Ergosphere polar radius r_ergo(theta=0) = M + sqrt(M^2 - a^2) = r_+
 *      (ergosphere touches horizon at poles).
 *   4. isInsideErgosphere() for points just inside and just outside boundaries.
 *   5. Lapse function alpha = sqrt(1 - 2/r) = 0 at and inside horizon.
 *   6. Grid line intensity > 0 at phi = k * pi/6, theta = k * pi/6 (line locations).
 *   7. Grid line intensity = 0 midway between lines (phi = pi/12).
 *   8. Ergosphere boundary highlight visible at r = r_ergo(a=0.9, theta=pi/2).
 *   9. Curvature boost: grid intensity stronger near horizon than at r=100M.
 *  10. Overlay opacity in [0, 1] for all tested (r, theta, phi, a) combinations.
 *
 * HOW: C++ port of the GLSL/CUDA math using std::math.  All functions live in an
 *      anonymous namespace so static analysis tools see internal linkage.
 *
 * References:
 *   Bardeen, Press, Teukolsky (1972) ApJ 178, 347 (ergosphere definition)
 */

#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>

namespace {

constexpr double PI = std::numbers::pi;

// ---------------------------------------------------------------------------
// C++ port of wiregrid.glsl / d_wiregrid_overlay helper math (M = 1)
// ---------------------------------------------------------------------------

/** @brief Event horizon r_+ = 1 + sqrt(1 - a^2), M=1. */
double wg_event_horizon(double a) {
    a = std::clamp(a, -0.9999, 0.9999);
    return 1.0 + std::sqrt(std::max(1.0 - a * a, 0.0));
}

/** @brief Ergosphere outer radius r_ergo = 1 + sqrt(1 - a^2 cos^2(theta)), M=1. */
double wg_ergosphere(double a, double theta) {
    a = std::clamp(a, -0.9999, 0.9999);
    double const cos_t = std::cos(theta);
    return 1.0 + std::sqrt(std::max(1.0 - a * a * cos_t * cos_t, 0.0));
}

/** @brief True if r_+ < r < r_ergo (inside ergosphere but outside horizon). */
bool wg_inside_ergosphere(double r, double theta, double a) {
    return (r > wg_event_horizon(a)) && (r < wg_ergosphere(a, theta));
}

/** @brief Lapse function alpha = sqrt(1 - 2/r), 0 inside horizon. */
double wg_lapse(double r, double a) {
    if (r <= wg_event_horizon(a)) return 0.0;
    return std::sqrt(std::max(1.0 - 2.0 / r, 0.0));
}

/** @brief smoothstep(edge, 0, dist): 1 at dist=0, 0 at dist>=edge. */
double wg_smoothstep(double edge, double dist) {
    if (edge < 1e-10) return 0.0;
    double t = std::clamp(dist / edge, 0.0, 1.0);
    return 1.0 - t * t * (3.0 - 2.0 * t);
}

/** @brief Grid line intensity at phi with given spacing and line_width. */
double wg_phi_line(double phi, double spacing, double lw) {
    double phase = std::fmod(phi, spacing);
    if (phase < 0.0) phase += spacing;
    double dist = std::min(phase, spacing - phase);
    return wg_smoothstep(lw, dist);
}

/** @brief Grid line intensity at theta with given spacing and line_width. */
double wg_theta_line(double theta, double spacing, double lw) {
    double const phase = std::fmod(theta, spacing);
    double const dist  = std::min(phase, spacing - phase);
    return wg_smoothstep(lw, dist);
}

/** @brief Combined grid + curvature boost. */
double wg_grid(double r, double theta, double phi, double a,
               double spacing, double lw) {
    double grid  = std::max(wg_phi_line(phi, spacing, lw),
                            wg_theta_line(theta, spacing, lw));
    double boost = 1.0 + (1.0 - wg_lapse(r, a)) * 2.0;
    return grid * boost;
}

/**
 * @brief Full wiregrid overlay RGBA (mirrors wiregridOverlay() in wiregrid.glsl).
 *
 * @param r          BL radial coordinate (geometric units, M=1).
 * @param theta      Polar angle [rad].
 * @param phi        Azimuthal angle [rad].
 * @param a          Dimensionless spin.
 * @param show_ergo  Show ergosphere boundary/glow.
 * @param grid_scale Grid density multiplier.
 * @return {R, G, B, A} in [0, 1].
 */
struct RGBA { double r, g, b, a; };
RGBA wg_overlay(double r, double theta, double phi, double a,
                bool show_ergo, double grid_scale) {
    double const spacing = (PI / 6.0) / grid_scale;
    double const lw      = 0.02 / grid_scale;
    double const grid    = wg_grid(r, theta, phi, a, spacing, lw);
    double const grid_a  = std::clamp(grid * 0.5, 0.0, 0.8);
    double ergo_a = 0.0;
    if (show_ergo) {
        double const r_ergo   = wg_ergosphere(a, theta);
        double const boundary = wg_smoothstep(0.2, std::abs(r - r_ergo));
        double interior = 0.0;
        if (wg_inside_ergosphere(r, theta, a)) {
            double const omega     = 2.0 * a * r / (r*r*r + a*a*r + 2.0*a*a);
            double const r_plus    = wg_event_horizon(a);
            double const omega_max = 2.0 * a * (r_plus + 0.01) /
                                     ((r_plus+0.01)*(r_plus+0.01)*(r_plus+0.01) +
                                      a*a*(r_plus+0.01) + 2.0*a*a);
            interior = (omega / std::max(omega_max, 1e-10)) * 0.3;
        }
        ergo_a = std::max(boundary * 0.9, interior);
    }
    double const total = grid_a + ergo_a;
    double const t     = ergo_a / std::max(total, 0.01);
    return {0.3 + t * 0.7, 0.8 - t * 0.5, 1.0 - t, std::max(grid_a, ergo_a)};
}

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

static bool g_all_pass = true;

void check(bool cond, const char *name, const char *detail = "") {
    if (cond) {
        std::cout << "  [PASS] " << name << "\n";
    } else {
        std::cout << "  [FAIL] " << name;
        if (detail[0] != '\0') { std::cout << " -- " << detail; }
        std::cout << "\n";
        g_all_pass = false;
    }
}

bool near(double a, double b, double tol = 1e-9) {
    return std::abs(a - b) <= tol * std::max(1.0, std::abs(b));
}

// ---------------------------------------------------------------------------
// Test 1: Event horizon at known spin values
// ---------------------------------------------------------------------------

/**
 * @brief Verify r_+ = 1 + sqrt(1 - a^2) at a* in {0, 0.5, 0.9, 0.998}.
 *
 * References: Kerr (1963) PRL 11, 237; exact formula for M=1.
 */
void testEventHorizon() {
    std::cout << "Test 1: event horizon r_+ at known spin values\n";
    struct Case { double a; double expected; };
    const Case cases[] = {
        {0.0,   2.0},                           // Schwarzschild limit
        {0.5,   1.0 + std::sqrt(0.75)},
        {0.9,   1.0 + std::sqrt(1.0 - 0.81)},
        {0.998, 1.0 + std::sqrt(1.0 - 0.998*0.998)},
    };
    for (const auto &c : cases) {
        char buf[64];
        (void)std::snprintf(buf, sizeof(buf), "a*=%.3f: expected %.6f got %.6f",
                            c.a, c.expected, wg_event_horizon(c.a));
        check(near(wg_event_horizon(c.a), c.expected, 1e-12), "r_+ formula", buf);
    }
}

// ---------------------------------------------------------------------------
// Test 2: Ergosphere equatorial radius = 2M for all spins
// ---------------------------------------------------------------------------

/**
 * @brief At theta=pi/2, r_ergo = 1 + sqrt(1 - a^2*0) = 1+1 = 2 for all a.
 *
 * WHY: cos(pi/2) = 0, so the a^2 cos^2(theta) term vanishes.  This means
 *      the ergosphere radius at the equator is always 2M regardless of spin,
 *      making it an ideal test point with a known exact value.
 */
void testErgosphereEquatorial() {
    std::cout << "Test 2: ergosphere equatorial radius = 2M for all spins\n";
    const double theta = PI / 2.0;
    for (double a : {0.0, 0.3, 0.6, 0.9, 0.998}) {
        char buf[64];
        (void)std::snprintf(buf, sizeof(buf), "a*=%.3f", a);
        check(near(wg_ergosphere(a, theta), 2.0, 1e-10), "r_ergo(pi/2) == 2M", buf);
    }
}

// ---------------------------------------------------------------------------
// Test 3: Ergosphere at poles touches the horizon
// ---------------------------------------------------------------------------

/**
 * @brief At theta=0 (north pole), r_ergo = r_+ because cos(0) = 1
 *        so r_ergo = 1 + sqrt(1 - a^2) = r_+.
 */
void testErgosphereAtPoles() {
    std::cout << "Test 3: ergosphere polar radius == event horizon radius\n";
    for (double a : {0.0, 0.5, 0.9, 0.998}) {
        double const r_plus = wg_event_horizon(a);
        double const r_ergo = wg_ergosphere(a, 0.0);
        char buf[64];
        (void)std::snprintf(buf, sizeof(buf), "a*=%.3f: r_+=%.6f r_ergo(0)=%.6f", a, r_plus, r_ergo);
        check(near(r_ergo, r_plus, 1e-9), "r_ergo(theta=0) == r_+", buf);
    }
}

// ---------------------------------------------------------------------------
// Test 4: isInsideErgosphere() boundary conditions
// ---------------------------------------------------------------------------

/**
 * @brief Points just inside/outside the ergosphere at equator (theta=pi/2, a=0.9).
 *
 * At theta=pi/2: r_+ = 1+sqrt(0.19) ~ 1.436, r_ergo = 2.0.
 * Inside:  r_+ < r < r_ergo -> true.
 * Outside: r > r_ergo        -> false.
 * At r_+:  r == r_plus        -> false (not strictly greater).
 */
void testInsideErgosphere() {
    std::cout << "Test 4: isInsideErgosphere() boundary conditions\n";
    const double a     = 0.9;
    const double theta = PI / 2.0;
    const double r_plus = wg_event_horizon(a);   // ~1.436
    const double r_ergo = wg_ergosphere(a, theta); // == 2.0

    check( wg_inside_ergosphere(r_plus + 0.01, theta, a), "inside (r = r_plus + epsilon)");
    check( wg_inside_ergosphere((r_plus + r_ergo) / 2.0, theta, a), "inside (r = midpoint)");
    check(!wg_inside_ergosphere(r_ergo + 0.01,  theta, a), "outside (r = r_ergo + epsilon)");
    check(!wg_inside_ergosphere(r_plus,          theta, a), "outside (r = r_plus, not strictly inside)");
    check(!wg_inside_ergosphere(r_ergo,          theta, a), "outside (r = r_ergo, not strictly inside)");
}

// ---------------------------------------------------------------------------
// Test 5: Lapse function = 0 at/inside horizon
// ---------------------------------------------------------------------------

/**
 * @brief alpha = sqrt(1 - 2/r): exactly 0 at Schwarzschild r=2M and inside.
 */
void testLapseFunction() {
    std::cout << "Test 5: lapse function = 0 inside horizon, > 0 outside\n";
    check(near(wg_lapse(2.0, 0.0), 0.0, 1e-12), "alpha(r=2M, Schwarzschild) == 0");
    check(near(wg_lapse(1.5, 0.0), 0.0, 1e-12), "alpha(r=1.5M, inside) == 0");
    check(wg_lapse(3.0, 0.0) > 0.0,              "alpha(r=3M) > 0");
    check(wg_lapse(100.0, 0.0) > 0.9,            "alpha(r=100M) close to 1");
    // Kerr a*=0.9: r_+ ~ 1.436, alpha at r=1.436+0.01 should be 0 (still inside or at horizon)
    check(near(wg_lapse(wg_event_horizon(0.9), 0.9), 0.0, 1e-10), "alpha at Kerr horizon == 0");
}

// ---------------------------------------------------------------------------
// Test 6: Grid line intensity > 0 at gridline locations
// ---------------------------------------------------------------------------

/**
 * @brief At phi = k * pi/6 (k = 0, 1, ..., 5), the phi gridline should be visible.
 *
 * WHY: pi/6 is the default spacing; at phi = k * pi/6, the modular distance to the
 *      nearest line is 0, so smoothstep returns 1.
 */
void testGridLineAtLocations() {
    std::cout << "Test 6: grid intensity > 0 at phi = k*pi/6 gridline locations\n";
    const double spacing = PI / 6.0;
    const double lw = 0.02;
    for (int k = 0; k <= 5; ++k) {
        double const phi = k * spacing;
        double const intensity = wg_phi_line(phi, spacing, lw);
        char buf[32];
        (void)std::snprintf(buf, sizeof(buf), "phi=k=%d*pi/6", k);
        check(intensity > 0.5, "gridline intensity > 0.5 at exact gridline", buf);
    }
}

// ---------------------------------------------------------------------------
// Test 7: Grid line intensity ~ 0 midway between gridlines
// ---------------------------------------------------------------------------

/**
 * @brief At phi = pi/12 (midway between 0 and pi/6), the line intensity should be 0.
 *
 * WHY: At the midpoint phi = spacing/2 = pi/12, the distance to the nearest line
 *      equals lw * (spacing/2 / lw) >> lw so smoothstep returns 0.
 */
void testGridLineZeroMidway() {
    std::cout << "Test 7: grid intensity = 0 midway between gridlines\n";
    const double spacing = PI / 6.0;
    const double lw = 0.02;
    const double phi_mid = spacing / 2.0; // pi/12 = midway
    const double intensity = wg_phi_line(phi_mid, spacing, lw);
    char buf[64];
    (void)std::snprintf(buf, sizeof(buf), "phi=pi/12: intensity=%.6f (expected 0)", intensity);
    check(near(intensity, 0.0, 1e-10), "midway intensity == 0", buf);
}

// ---------------------------------------------------------------------------
// Test 8: Ergosphere boundary highlight visible at r = r_ergo
// ---------------------------------------------------------------------------

/**
 * @brief At r exactly on the ergosphere boundary, ergosphereBoundary() should be ~ 0.9.
 *
 * The boundary function: smoothstep(0.2, 0, |r - r_ergo|) = 1.0 at exact boundary,
 * so the overlay includes 0.9 * 1.0 = 0.9 of ergosphere alpha.
 */
void testErgoBoundaryHighlight() {
    std::cout << "Test 8: ergosphere boundary highlight at r = r_ergo\n";
    const double a      = 0.9;
    const double theta  = PI / 2.0;
    const double r_ergo = wg_ergosphere(a, theta); // == 2.0
    RGBA const ov = wg_overlay(r_ergo, theta, 0.0, a, true, 1.0);
    char buf[64];
    (void)std::snprintf(buf, sizeof(buf), "opacity=%.4f at r_ergo", ov.a);
    check(ov.a > 0.4, "ergosphere boundary alpha > 0.4 at r_ergo", buf);
}

// ---------------------------------------------------------------------------
// Test 9: Curvature boost: stronger grid near horizon than far away
// ---------------------------------------------------------------------------

/**
 * @brief Grid intensity (without ergosphere) should be stronger at r=3M than r=100M.
 *
 * WHY: The lapse function alpha -> 0 near the horizon, so boost = 1 + (1-alpha)*2
 *      approaches 3x at the horizon and 1x at infinity.  A gridline at the same
 *      angular position should be brighter near the BH.
 */
void testCurvatureBoost() {
    std::cout << "Test 9: grid intensity stronger near horizon than at r=100M\n";
    const double a       = 0.9;
    const double theta   = PI / 2.0;
    const double phi_on  = 0.0;            // at a gridline (phi=0 = k*pi/6 for k=0)
    const double spacing = PI / 6.0;
    const double lw      = 0.02;
    double const grid_near = wg_grid(3.0,   theta, phi_on, a, spacing, lw);
    double const grid_far  = wg_grid(100.0, theta, phi_on, a, spacing, lw);
    char buf[64];
    (void)std::snprintf(buf, sizeof(buf), "near=%.4f far=%.4f", grid_near, grid_far);
    check(grid_near > grid_far, "grid stronger near horizon", buf);
}

// ---------------------------------------------------------------------------
// Test 10: Overlay opacity in [0, 1] for diverse (r, theta, phi, a) samples
// ---------------------------------------------------------------------------

/**
 * @brief Verify wiregridOverlay RGBA.a is in [0, 1] for all input combinations.
 *
 * WHY: The alpha channel is used for over-compositing; values outside [0,1]
 *      would produce visible artifacts (white overdrive or negative subtraction).
 */
void testOpacityBounds() {
    std::cout << "Test 10: overlay opacity in [0, 1] for diverse inputs\n";
    const double r_vals[]     = {1.5, 2.0, 3.0, 5.0, 20.0, 100.0};
    const double theta_vals[] = {0.01, PI/6, PI/3, PI/2, PI - 0.01};
    const double phi_vals[]   = {0.0, PI/12, PI/6, PI/2, PI, 2*PI - 0.01};
    const double a_vals[]     = {0.0, 0.5, 0.9, 0.998};

    int fail_count = 0;
    for (double r : r_vals)
      for (double theta : theta_vals)
        for (double phi : phi_vals)
          for (double a : a_vals) {
              RGBA const ov = wg_overlay(r, theta, phi, a, true, 1.0);
              if (ov.a < 0.0 || ov.a > 1.0001) {
                  char buf[128];
                  (void)std::snprintf(buf, sizeof(buf),
                    "r=%.1f theta=%.3f phi=%.3f a=%.3f -> alpha=%.6f", r, theta, phi, a, ov.a);
                  std::cout << "  [FAIL] alpha out of [0,1]: " << buf << "\n";
                  ++fail_count;
                  g_all_pass = false;
              }
          }
    if (fail_count == 0) {
        std::cout << "  [PASS] all " << (6*5*6*4) << " samples have alpha in [0,1]\n";
    }
}

} // namespace

int main() {
    std::cout << "\n================================================\n"
              << "WIREGRID BL-COORDINATE OVERLAY VALIDATION\n"
              << "Tests: Kerr geometry, grid lines, ergosphere\n"
              << "================================================\n\n";

    testEventHorizon();       std::cout << "\n";
    testErgosphereEquatorial(); std::cout << "\n";
    testErgosphereAtPoles();  std::cout << "\n";
    testInsideErgosphere();   std::cout << "\n";
    testLapseFunction();      std::cout << "\n";
    testGridLineAtLocations(); std::cout << "\n";
    testGridLineZeroMidway(); std::cout << "\n";
    testErgoBoundaryHighlight(); std::cout << "\n";
    testCurvatureBoost();     std::cout << "\n";
    testOpacityBounds();      std::cout << "\n";

    std::cout << "================================================\n"
              << "RESULT: " << (g_all_pass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
              << "================================================\n\n";

    return g_all_pass ? 0 : 1;
}
