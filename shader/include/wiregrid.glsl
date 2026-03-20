/**
 * @file include/wiregrid.glsl
 * @brief Boyer-Lindquist coordinate overlay: spherical grid + ergosphere visualization.
 *
 * WHY: Visualize Kerr spacetime geometry directly on the ray-traced image using the BL
 *      coordinates already computed by the geodesic integrator.  The old approach rendered
 *      a separate Euclidean Flamm-paraboloid mesh with a perspective camera, which was
 *      geometrically inconsistent with the geodesic view and has been removed.
 *
 * WHAT: Per-pixel overlay evaluated at the ray endpoint BL position (r, theta, phi).
 *   - Spherical coordinate grid: constant-phi radial lines + constant-theta angular lines.
 *   - Ergosphere boundary: orange-red highlight at r_ergo(theta) = M + sqrt(M^2 - a^2 cos^2 theta).
 *   - Curvature modulation: grid intensity boosted near the horizon via the lapse function.
 *
 * HOW (call from fragment/compute shader after tracing):
 *   #include "include/wiregrid.glsl"
 *   vec4 wg = wiregridOverlay(r, theta, phi, a_star, show_ergosphere, grid_scale);
 *   color = mix(color, wg.rgb, wg.a);
 *
 * Coordinates: all in geometric units M = 1 (schwarzschildRadius = 2M).
 *   r     -- BL radial coordinate, r = sqrt(x^2 + y^2 + z^2) (spherical approx)
 *   theta -- polar angle, theta = acos(z / r)
 *   phi   -- azimuthal angle, phi = atan(y, x)
 *   a_star -- dimensionless spin parameter in [0, 1)
 *
 * References:
 *   Bardeen, Press, Teukolsky (1972) ApJ 178, 347 (ergosphere)
 */

#ifndef WIREGRID_GLSL_OVERLAY
#define WIREGRID_GLSL_OVERLAY

// ---------------------------------------------------------------------------
// Kerr geometry helpers (standalone; no dependency on other includes)
// ---------------------------------------------------------------------------

float wg_eventHorizon(float a_star) {
    float a = clamp(a_star, -0.9999, 0.9999);
    return 1.0 + sqrt(max(1.0 - a * a, 0.0));
}

// r_ergo = M + sqrt(M^2 - a^2 cos^2(theta)), M=1
float wg_ergosphere(float a_star, float theta) {
    float a = clamp(a_star, -0.9999, 0.9999);
    float cos_t = cos(theta);
    return 1.0 + sqrt(max(1.0 - a * a * cos_t * cos_t, 0.0));
}

bool wg_insideErgosphere(float r, float theta, float a_star) {
    return (r > wg_eventHorizon(a_star)) && (r < wg_ergosphere(a_star, theta));
}

// Lapse function alpha = sqrt(1 - 2/r) (Schwarzschild approx, valid far from equatorial Kerr)
float wg_lapse(float r, float a_star) {
    if (r <= wg_eventHorizon(a_star)) return 0.0;
    return sqrt(max(1.0 - 2.0 / r, 0.0));
}

// Omega_ZAMO = 2Mar / (r^3 + a^2 r + 2 a^2), M=1
float wg_frameDragging(float r, float a_star) {
    float a = clamp(a_star, -0.9999, 0.9999);
    float denom = r * r * r + a * a * r + 2.0 * a * a;
    return (denom < 1e-10) ? 0.0 : (2.0 * a * r) / denom;
}

// ---------------------------------------------------------------------------
// Grid line generators
// ---------------------------------------------------------------------------

float wg_phiLine(float phi, float spacing, float width) {
    // Wrap phi to [0, spacing) and measure distance to nearest gridline
    float phase = mod(phi, spacing);
    float dist  = min(phase, spacing - phase);
    return smoothstep(width, 0.0, dist);
}

float wg_thetaLine(float theta, float spacing, float width) {
    float phase = mod(theta, spacing);
    float dist  = min(phase, spacing - phase);
    return smoothstep(width, 0.0, dist);
}

float wg_sphericalGrid(float r, float theta, float phi, float a_star,
                       float phi_spacing, float theta_spacing, float line_width) {
    float phi_line   = wg_phiLine(phi, phi_spacing, line_width);
    float theta_line = wg_thetaLine(theta, theta_spacing, line_width);
    float grid = max(phi_line, theta_line);
    // Boost near horizon (alpha -> 0 -> boost -> 3x)
    float boost = 1.0 + (1.0 - wg_lapse(r, a_star)) * 2.0;
    return grid * boost;
}

// ---------------------------------------------------------------------------
// Ergosphere visualization
// ---------------------------------------------------------------------------

float wg_ergoBoundary(float r, float theta, float a_star, float thickness) {
    float r_ergo = wg_ergosphere(a_star, theta);
    return smoothstep(thickness, 0.0, abs(r - r_ergo));
}

float wg_ergoInterior(float r, float theta, float a_star) {
    if (!wg_insideErgosphere(r, theta, a_star)) return 0.0;
    float omega     = wg_frameDragging(r, a_star);
    float omega_max = wg_frameDragging(wg_eventHorizon(a_star) + 0.01, a_star);
    float intensity = omega / max(omega_max, 1e-10);
    return intensity * 0.3;
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/**
 * @brief Per-pixel BL-coordinate wiregrid overlay.
 *
 * @param r            BL radial coordinate in units of M
 * @param theta        Polar angle [rad]
 * @param phi          Azimuthal angle [rad]
 * @param a_star       Dimensionless Kerr spin in [0, 1)
 * @param show_ergo    Show ergosphere boundary + interior glow
 * @param grid_scale   Grid density multiplier (1.0 = pi/6 rad spacing)
 * @return RGBA: RGB = overlay color, A = opacity to blend with scene
 */
vec4 wiregridOverlay(float r, float theta, float phi, float a_star,
                     bool show_ergo, float grid_scale) {
    float spacing   = 0.523598776 / grid_scale; // pi/6 rad = 30 deg
    float lw        = 0.02 / max(grid_scale, 0.01);

    float grid       = wg_sphericalGrid(r, theta, phi, a_star, spacing, spacing, lw);
    vec3  grid_rgb   = vec3(0.3, 0.8, 1.0);   // Cyan-white
    float grid_alpha = clamp(grid * 0.5, 0.0, 0.8);

    vec3  ergo_rgb   = vec3(1.0, 0.3, 0.0);   // Orange-red (frame dragging)
    float ergo_alpha = 0.0;
    if (show_ergo) {
        float boundary = wg_ergoBoundary(r, theta, a_star, 0.2);
        float interior = wg_ergoInterior(r, theta, a_star);
        ergo_alpha = max(boundary * 0.9, interior);
    }

    float total = grid_alpha + ergo_alpha;
    vec3  final_rgb   = mix(grid_rgb, ergo_rgb, ergo_alpha / max(total, 0.01));
    float final_alpha = max(grid_alpha, ergo_alpha);
    return vec4(final_rgb, final_alpha);
}

// Convenience overload with default grid_scale = 1.0
vec4 wiregridOverlay(float r, float theta, float phi, float a_star, bool show_ergo) {
    return wiregridOverlay(r, theta, phi, a_star, show_ergo, 1.0);
}

#endif // WIREGRID_GLSL_OVERLAY
