/**
 * kerr.glsl
 * Kerr spacetime metric for rotating black holes.
 *
 * Key formulas from Bardeen-Press-Teukolsky (1972).
 * Reduces to Schwarzschild when spin a = 0.
 */

#ifndef KERR_GLSL
#define KERR_GLSL

// ============================================================================
// Kerr Metric Functions
// ============================================================================

/**
 * Σ = r² + a² cos²θ
 */
float kerrSigma(float r, float a, float cosTheta) {
    return r * r + a * a * cosTheta * cosTheta;
}

/**
 * Δ = r² - r_s r + a²
 * Horizons exist where Δ = 0.
 */
float kerrDelta(float r, float a, float r_s) {
    return r * r - r_s * r + a * a;
}

/**
 * Outer (event) horizon: r_+ = M + √(M² - a²)
 * where M = r_s/2 in geometric units
 */
float kerrOuterHorizon(float r_s, float a) {
    float M = r_s * 0.5;
    float discriminant = M * M - a * a;
    if (discriminant < 0.0) {
        return -1.0; // Naked singularity
    }
    return M + sqrt(discriminant);
}

/**
 * Inner (Cauchy) horizon: r_- = M - √(M² - a²)
 */
float kerrInnerHorizon(float r_s, float a) {
    float M = r_s * 0.5;
    float discriminant = M * M - a * a;
    if (discriminant < 0.0) {
        return -1.0;
    }
    return M - sqrt(discriminant);
}

/**
 * Ergosphere outer boundary: r_ergo(θ) = M + √(M² - a² cos²θ)
 * Inside: no static observers possible (frame dragging mandatory)
 */
float ergosphereRadius(float r_s, float a, float cosTheta) {
    float M = r_s * 0.5;
    float discriminant = M * M - a * a * cosTheta * cosTheta;
    if (discriminant < 0.0) {
        return M; // At poles, equals outer horizon
    }
    return M + sqrt(discriminant);
}

// ============================================================================
// ISCO - Bardeen-Press-Teukolsky (1972) Formula
// ============================================================================

/**
 * Compute ISCO radius for equatorial orbits.
 *
 * r_ISCO/M = 3 + Z2 ∓ √((3 - Z1)(3 + Z1 + 2Z2))
 *
 * @param r_s Schwarzschild radius
 * @param a Spin parameter (|a| ≤ M = r_s/2)
 * @param prograde true for prograde (minus), false for retrograde (plus)
 */
float kerrISCO(float r_s, float a, bool prograde) {
    float M = r_s * 0.5;
    float a_star = clamp(a / M, -1.0, 1.0);

    // For retrograde, use negative spin
    float a_eff = prograde ? a_star : -a_star;

    // BPT formula
    float one_minus_a2 = 1.0 - a_eff * a_eff;
    float cbrt_factor = pow(max(one_minus_a2, 0.0), 1.0/3.0);
    float cbrt_plus = pow(1.0 + a_eff, 1.0/3.0);
    float cbrt_minus = pow(max(1.0 - a_eff, 0.0), 1.0/3.0);

    float Z1 = 1.0 + cbrt_factor * (cbrt_plus + cbrt_minus);
    float Z2 = sqrt(3.0 * a_eff * a_eff + Z1 * Z1);

    float sqrt_term = sqrt(max(0.0, (3.0 - Z1) * (3.0 + Z1 + 2.0 * Z2)));

    // Prograde: minus; Retrograde: plus
    float r_isco_over_M = 3.0 + Z2 - sqrt_term;

    return r_isco_over_M * M;
}

/**
 * Prograde photon orbit radius.
 * r_ph = 2M(1 + cos(2/3 * arccos(-a*)))
 */
float kerrPhotonOrbitPrograde(float r_s, float a) {
    float M = r_s * 0.5;
    float a_star = clamp(a / M, -1.0, 1.0);

    float angle = (2.0 / 3.0) * acos(clamp(-a_star, -1.0, 1.0));
    return 2.0 * M * (1.0 + cos(angle));
}

/**
 * Retrograde photon orbit radius.
 * r_ph = 2M(1 + cos(2/3 * arccos(a*)))
 */
float kerrPhotonOrbitRetrograde(float r_s, float a) {
    float M = r_s * 0.5;
    float a_star = clamp(a / M, -1.0, 1.0);

    float angle = (2.0 / 3.0) * acos(clamp(a_star, -1.0, 1.0));
    return 2.0 * M * (1.0 + cos(angle));
}

// ============================================================================
// Frame Dragging
// ============================================================================

/**
 * Frame-dragging angular velocity (Lense-Thirring).
 *
 * ω = (2Ma r) / (Σ(r² + a²) + 2Ma²r sin²θ)
 *
 * Local inertial frames are dragged at this rate.
 */
float frameDraggingOmega(float r, float theta, float r_s, float a) {
    float M = r_s * 0.5;
    float cosTheta = cos(theta);
    float sinTheta = sin(theta);
    float sin2Theta = sinTheta * sinTheta;

    float sigma = kerrSigma(r, a, cosTheta);
    float r2_plus_a2 = r * r + a * a;

    float numerator = 2.0 * M * a * r;
    float denominator = sigma * r2_plus_a2 + 2.0 * M * a * a * r * sin2Theta;

    if (denominator < 1e-10) {
        return 0.0;
    }

    return numerator / denominator;
}

/**
 * Orbital angular velocity for circular equatorial orbit.
 *
 * Ω = ±M^(1/2) / (r^(3/2) ± a M^(1/2))
 *
 * + for prograde, - for retrograde
 */
float kerrOrbitalOmega(float r, float r_s, float a, bool prograde) {
    float M = r_s * 0.5;
    float sqrt_M = sqrt(M);
    float r_32 = r * sqrt(r);

    if (prograde) {
        return sqrt_M / (r_32 + a * sqrt_M);
    } else {
        return -sqrt_M / (r_32 - a * sqrt_M);
    }
}

// ============================================================================
// Kerr Redshift
// ============================================================================

/**
 * Gravitational redshift for static observer in Kerr.
 *
 * 1 + z = 1/√(1 - r_s r/Σ)
 */
float kerrRedshift(float r, float theta, float r_s, float a) {
    float cosTheta = cos(theta);
    float sigma = kerrSigma(r, a, cosTheta);

    float factor = 1.0 - r_s * r / sigma;
    if (factor <= 0.0) {
        return 1e10; // Very large redshift near horizon
    }

    return 1.0 / sqrt(factor) - 1.0;
}

/**
 * Combined redshift for orbiting emitter in Kerr.
 *
 * Includes gravitational + Doppler from orbital motion.
 * g = (1 + z)^(-1) = proper_time / coordinate_time
 */
float kerrOrbitalRedshiftFactor(float r, float r_s, float a, float viewAngle, bool prograde) {
    // Gravitational component
    float M = r_s * 0.5;
    float sigma = r * r; // Equatorial plane: a²cos²θ = 0
    float delta = kerrDelta(r, a, r_s);

    float g_tt = -(1.0 - r_s * r / sigma);
    float grav_factor = sqrt(max(0.001, -g_tt));

    // Orbital velocity at radius r
    float omega = kerrOrbitalOmega(r, r_s, a, prograde);
    float v = omega * r; // Linear velocity

    // Doppler factor
    float v_los = v * sin(viewAngle);
    float v_clamped = clamp(v_los, -0.99, 0.99);
    float doppler = sqrt((1.0 - v_clamped) / (1.0 + v_clamped));

    return grav_factor * doppler;
}

// ============================================================================
// Geodesic Modification for Kerr
// ============================================================================

/**
 * Compute geodesic acceleration in Kerr spacetime.
 *
 * The full Kerr geodesic equation is complex; this is a simplified
 * version for visualization that captures the main effects:
 * - Stronger bending near horizon (modified effective potential)
 * - Frame-dragging contribution
 *
 * For exact geodesics, need full Christoffel symbol integration.
 */
vec3 kerrGeodesicAccel(vec3 pos, vec3 vel, float r_s, float a) {
    float r = length(pos);
    float r2 = r * r;

    // Compute theta from position
    float cosTheta = pos.z / max(r, 0.001);
    float sigma = kerrSigma(r, a, cosTheta);
    float delta = kerrDelta(r, a, r_s);

    // Angular momentum components
    vec3 h = cross(pos, vel);
    float h2 = dot(h, h);

    // Base Schwarzschild-like acceleration (modified by Kerr)
    float r5 = r2 * r2 * r;
    vec3 radial_accel = -1.5 * r_s * h2 * pos / r5;

    // Frame-dragging contribution (in phi direction)
    float omega_fd = frameDraggingOmega(r, acos(cosTheta), r_s, a);
    vec3 phi_dir = normalize(vec3(-pos.y, pos.x, 0.0) + vec3(0.001)); // Azimuthal direction

    // Add frame-dragging effect
    float fd_strength = omega_fd * r_s / max(r, r_s);
    vec3 frame_drag_accel = fd_strength * phi_dir;

    // Kerr correction factor (weaker at poles, stronger at equator)
    float sin2Theta = 1.0 - cosTheta * cosTheta;
    float kerr_factor = 1.0 + 0.5 * a * a * sin2Theta / sigma;

    return radial_accel * kerr_factor + frame_drag_accel;
}

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Check if point is outside outer horizon.
 */
bool kerrIsExterior(float r, float r_s, float a) {
    return r > kerrOuterHorizon(r_s, a);
}

/**
 * Check if point is in ergosphere.
 */
bool kerrInErgosphere(float r, float theta, float r_s, float a) {
    float r_plus = kerrOuterHorizon(r_s, a);
    float r_ergo = ergosphereRadius(r_s, a, cos(theta));
    return r < r_ergo && r > r_plus;
}

/**
 * Get effective shadow size for Kerr black hole.
 * The shadow is asymmetric for a ≠ 0.
 *
 * Returns approximate shadow radius (varies with viewing angle).
 */
float kerrShadowRadius(float r_s, float a, float viewAngle) {
    float M = r_s * 0.5;
    float a_star = clamp(a / M, -1.0, 1.0);

    // Approximate shadow size (exact requires ray tracing)
    // For edge-on view: shadow is asymmetric
    // For pole-on view: shadow is circular

    float r_ph_pro = kerrPhotonOrbitPrograde(r_s, a);
    float r_ph_ret = kerrPhotonOrbitRetrograde(r_s, a);

    // Critical impact parameters
    float b_pro = r_ph_pro * sqrt(r_ph_pro / (r_ph_pro - r_s));
    float b_ret = r_ph_ret * sqrt(r_ph_ret / (r_ph_ret - r_s));

    // Average for approximate circular shadow
    float sin_view = abs(sin(viewAngle));
    return mix((b_pro + b_ret) * 0.5, b_ret, sin_view * abs(a_star));
}

#endif // KERR_GLSL
