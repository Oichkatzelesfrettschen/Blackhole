/**
 * @file wiregrid.glsl
 * @brief Wireframe grid overlay with ergosphere visualization
 *
 * WHY: Visualize spacetime curvature and frame dragging effects
 * WHAT: Spherical coordinate grid + ergosphere boundary overlay
 * HOW: Grid lines at constant r, θ with intensity based on gravitational potential
 *
 * Features:
 * - Radial grid lines (constant θ, varying r)
 * - Angular grid lines (constant r, varying θ)
 * - Ergosphere boundary highlight (frame dragging region)
 * - Color-coded curvature intensity
 * - Runtime scale control
 *
 * Usage:
 *   #include "wiregrid.glsl"
 *   vec4 grid = wiregridOverlay(r, theta, phi, a_star, show_ergosphere);
 *   color = mix(color, grid.rgb, grid.a);
 *
 * References:
 *   - Bardeen, Press, Teukolsky (1972) ApJ 178, 347 (ergosphere)
 *   - Thorne (1974) "Black Holes and Time Warps" (frame dragging)
 */

#version 460 core

/**
 * @brief Compute event horizon radius for Kerr black hole
 *
 * r_+ = M + √(M² - a²)
 *
 * @param a_star Dimensionless spin parameter
 * @return Event horizon radius in units of M
 */
float eventHorizon(float a_star) {
    a_star = clamp(a_star, -0.9999, 0.9999);
    float a_sqr = a_star * a_star;
    return 1.0 + sqrt(1.0 - a_sqr);
}

/**
 * @brief Compute ergosphere outer boundary radius
 *
 * r_ergo = M + √(M² - a² cos²θ)
 *
 * Frame dragging region between r_+ and r_ergo where g_tt > 0.
 * All observers are forced to co-rotate with the black hole.
 *
 * @param a_star Dimensionless spin parameter
 * @param theta Polar angle [rad] (0 = north pole, π/2 = equator)
 * @return Ergosphere radius in units of M
 */
float ergosphere(float a_star, float theta) {
    a_star = clamp(a_star, -0.9999, 0.9999);
    float cos_theta = cos(theta);
    float a_sqr_cos_sqr = a_star * a_star * cos_theta * cos_theta;
    return 1.0 + sqrt(1.0 - a_sqr_cos_sqr);
}

/**
 * @brief Check if point is inside ergosphere
 *
 * @param r Radius in units of M
 * @param theta Polar angle [rad]
 * @param a_star Dimensionless spin parameter
 * @return true if inside ergosphere (r_+ < r < r_ergo)
 */
bool isInsideErgosphere(float r, float theta, float a_star) {
    float r_plus = eventHorizon(a_star);
    float r_ergo = ergosphere(a_star, theta);

    return (r > r_plus && r < r_ergo);
}

/**
 * @brief Compute frame dragging angular velocity (Ω_ZAMO)
 *
 * Ω = 2Mar / (r³ + a²r + 2Ma²)
 *
 * This is the angular velocity of Zero Angular Momentum Observers (ZAMOs).
 * All matter inside the ergosphere must rotate faster than this.
 *
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @return Frame dragging frequency [rad/s in geometric units]
 */
float frameDraggingOmega(float r, float a_star) {
    a_star = clamp(a_star, -0.9999, 0.9999);
    float a_sqr = a_star * a_star;

    float numerator = 2.0 * a_star * r;
    float denominator = r * r * r + a_sqr * r + 2.0 * a_sqr;

    if (denominator < 1e-10) {
        return 0.0;
    }

    return numerator / denominator;
}

/**
 * @brief Compute gravitational potential for grid intensity
 *
 * Uses lapse function α = √(-g_tt) as proxy for curvature.
 * α → 0 near horizon (strong curvature), α → 1 at infinity (flat).
 *
 * @param r Radius in units of M
 * @param theta Polar angle [rad]
 * @param a_star Dimensionless spin parameter
 * @return Lapse function α ∈ [0, 1]
 */
float lapseFunction(float r, float theta, float a_star) {
    // Simplified Kerr lapse (approximate)
    // α ≈ √(1 - 2M/r) for Schwarzschild limit

    float r_plus = eventHorizon(a_star);

    if (r <= r_plus) {
        return 0.0;  // Inside horizon
    }

    // Approximate lapse
    float alpha_sqr = 1.0 - 2.0 / r;
    return sqrt(max(alpha_sqr, 0.0));
}

/**
 * @brief Generate radial grid lines (constant θ)
 *
 * @param phi Azimuthal angle [rad]
 * @param grid_spacing Angular spacing between lines [rad]
 * @param line_width Line width in angular units [rad]
 * @return Line intensity [0, 1]
 */
float radialGridLine(float phi, float grid_spacing, float line_width) {
    float phase = mod(phi, grid_spacing);
    float dist = min(phase, grid_spacing - phase);

    return smoothstep(line_width, 0.0, dist);
}

/**
 * @brief Generate angular grid lines (constant r)
 *
 * @param theta Polar angle [rad]
 * @param grid_spacing Angular spacing between lines [rad]
 * @param line_width Line width in angular units [rad]
 * @return Line intensity [0, 1]
 */
float angularGridLine(float theta, float grid_spacing, float line_width) {
    float phase = mod(theta, grid_spacing);
    float dist = min(phase, grid_spacing - phase);

    return smoothstep(line_width, 0.0, dist);
}

/**
 * @brief Generate spherical coordinate grid
 *
 * Combines radial and angular grid lines with curvature-based intensity.
 *
 * @param r Radius in units of M
 * @param theta Polar angle [rad]
 * @param phi Azimuthal angle [rad]
 * @param a_star Dimensionless spin parameter
 * @param radial_spacing Spacing for radial lines [rad]
 * @param angular_spacing Spacing for angular lines [rad]
 * @param line_width Line width [rad]
 * @return Grid intensity [0, 1]
 */
float sphericalGrid(float r, float theta, float phi, float a_star,
                     float radial_spacing, float angular_spacing, float line_width) {
    float radial = radialGridLine(phi, radial_spacing, line_width);
    float angular = angularGridLine(theta, angular_spacing, line_width);

    float grid = max(radial, angular);

    // Modulate by curvature (stronger near horizon)
    float alpha = lapseFunction(r, theta, a_star);
    float curvature_boost = 1.0 + (1.0 - alpha) * 2.0;  // 1x at infinity, 3x near horizon

    return grid * curvature_boost;
}

/**
 * @brief Generate ergosphere boundary visualization
 *
 * Highlights the ergosphere outer boundary where frame dragging begins.
 *
 * @param r Radius in units of M
 * @param theta Polar angle [rad]
 * @param a_star Dimensionless spin parameter
 * @param thickness Boundary thickness in M
 * @return Boundary intensity [0, 1]
 */
float ergosphereBoundary(float r, float theta, float a_star, float thickness) {
    float r_ergo = ergosphere(a_star, theta);

    // Distance from ergosphere boundary
    float dist = abs(r - r_ergo);

    // Smooth falloff
    return smoothstep(thickness, 0.0, dist);
}

/**
 * @brief Compute ergosphere interior glow
 *
 * Fills the ergosphere region with a glow indicating frame dragging intensity.
 *
 * @param r Radius in units of M
 * @param theta Polar angle [rad]
 * @param a_star Dimensionless spin parameter
 * @return Interior intensity [0, 1]
 */
float ergosphereInterior(float r, float theta, float a_star) {
    if (!isInsideErgosphere(r, theta, a_star)) {
        return 0.0;
    }

    // Frame dragging intensity (stronger near horizon)
    float omega = frameDraggingOmega(r, a_star);
    float omega_max = frameDraggingOmega(eventHorizon(a_star) + 0.01, a_star);

    float intensity = omega / max(omega_max, 1e-10);

    return intensity * 0.3;  // 30% opacity maximum
}

/**
 * @brief Generate complete wiregrid overlay with ergosphere
 *
 * Combines spherical grid + ergosphere boundary + interior glow.
 *
 * @param r Radius in units of M
 * @param theta Polar angle [rad]
 * @param phi Azimuthal angle [rad]
 * @param a_star Dimensionless spin parameter
 * @param show_ergosphere Enable ergosphere visualization
 * @param grid_scale Grid density multiplier (1.0 = default)
 * @return RGBA color (RGB = color, A = opacity)
 */
vec4 wiregridOverlay(float r, float theta, float phi, float a_star,
                      bool show_ergosphere, float grid_scale) {
    // Grid parameters
    float radial_spacing = 0.523598776 / grid_scale;   // π/6 rad (30 deg)
    float angular_spacing = 0.523598776 / grid_scale;  // π/6 rad (30 deg)
    float line_width = 0.02 / grid_scale;              // Adaptive width

    // Generate grid
    float grid = sphericalGrid(r, theta, phi, a_star,
                                radial_spacing, angular_spacing, line_width);

    // Grid color (cyan-white, intensity based on curvature)
    vec3 grid_color = vec3(0.3, 0.8, 1.0);
    float grid_alpha = clamp(grid * 0.5, 0.0, 0.8);

    // Ergosphere visualization
    vec3 ergo_color = vec3(1.0, 0.3, 0.0);  // Orange-red (frame dragging)
    float ergo_alpha = 0.0;

    if (show_ergosphere) {
        // Boundary highlight
        float boundary = ergosphereBoundary(r, theta, a_star, 0.2);

        // Interior glow
        float interior = ergosphereInterior(r, theta, a_star);

        ergo_alpha = max(boundary * 0.9, interior);
    }

    // Composite
    vec3 final_color = mix(grid_color, ergo_color, ergo_alpha / max(grid_alpha + ergo_alpha, 0.01));
    float final_alpha = max(grid_alpha, ergo_alpha);

    return vec4(final_color, final_alpha);
}

/**
 * @brief Simplified wiregrid overlay (default parameters)
 *
 * Convenience wrapper with standard settings.
 *
 * @param r Radius in units of M
 * @param theta Polar angle [rad]
 * @param phi Azimuthal angle [rad]
 * @param a_star Dimensionless spin parameter
 * @param show_ergosphere Enable ergosphere visualization
 * @return RGBA color
 */
vec4 wiregridOverlay(float r, float theta, float phi, float a_star, bool show_ergosphere) {
    return wiregridOverlay(r, theta, phi, a_star, show_ergosphere, 1.0);
}
