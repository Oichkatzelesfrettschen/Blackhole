/**
 * @file doppler_beaming.glsl
 * @brief Relativistic Doppler beaming for accretion disk rendering
 *
 * WHY: Rotating disks show 10-1000x flux asymmetry due to relativistic beaming
 * WHAT: GPU implementation of disk Doppler boost calculations
 * HOW: Keplerian velocity + viewing angle geometry + δ^(3+α) boost
 *
 * Usage in blackhole_main.frag:
 *   #include "doppler_beaming.glsl"
 *   float boost = diskDopplerBoost(r, a_star, phi, inclination, alpha);
 *   vec3 disk_color *= boost;
 *
 * References:
 *   - Cunningham (1975) ApJ 202, 788 (Kerr disk imaging)
 *   - Begelman, Blandford, Rees (1984) Rev. Mod. Phys. 56, 255
 */

#ifndef DOPPLER_BEAMING_GLSL
#define DOPPLER_BEAMING_GLSL

/**
 * @brief Compute Lorentz factor γ from velocity β
 *
 * γ = 1 / √(1 - β²)
 *
 * @param beta Velocity as fraction of c (v/c)
 * @return Lorentz factor γ ≥ 1
 */
float lorentzFactor(float beta) {
    beta = abs(beta);
    if (beta >= 1.0) {
        return 1e10;  // Effectively infinity
    }
    return 1.0 / sqrt(1.0 - beta * beta);
}

/**
 * @brief Compute relativistic Doppler factor
 *
 * δ = 1 / (γ(1 - β cos θ))
 *
 * where θ is angle between velocity and line of sight.
 *
 * @param beta Velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @return Doppler factor δ
 */
float dopplerFactor(float beta, float theta) {
    float gamma = lorentzFactor(beta);
    float cos_theta = cos(theta);
    float denominator = gamma * (1.0 - beta * cos_theta);

    if (abs(denominator) < 1e-30) {
        return 1e10;
    }

    return 1.0 / denominator;
}

/**
 * @brief Compute Doppler boost for orbiting disk material
 *
 * For a circular orbit at radius r around a Kerr black hole:
 *   v_φ/c = √(M/(r - 2M ± a√M/r))
 *
 * The Doppler boost factor for flux is:
 *   F_obs = δ^(3+α) F_emit
 *
 * where δ = 1/(γ(1 - β cos θ)) and α is the spectral index.
 *
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter (-1 < a* < 1)
 * @param phi Azimuthal angle [rad] (0 = approaching, π = receding)
 * @param inclination Disk inclination [rad] (0 = face-on, π/2 = edge-on)
 * @param alpha Spectral index (F_ν ∝ ν^α), use 0 for blackbody
 * @return Doppler boost factor (1 = no boost)
 */
float diskDopplerBoost(float r, float a_star, float phi, float inclination, float alpha) {
    // Clamp inputs
    a_star = clamp(a_star, -0.9999, 0.9999);
    r = max(r, 1.1);  // Minimum radius to avoid singularities

    // Keplerian velocity for circular orbit
    // v_φ/c = √(M/(r - 2M ± a√M/r))
    float discriminant = r - 2.0 + a_star * sqrt(1.0 / r);
    if (discriminant <= 0.0) {
        // Inside ISCO or unphysical orbit
        return 1.0;
    }

    float v_orbital = sqrt(1.0 / discriminant);
    float beta = min(v_orbital, 0.99);  // Cap at 0.99c

    // Line-of-sight velocity component
    // For disk in x-y plane, observer at inclination i:
    // cos θ = sin(i) * cos(φ)
    float cos_theta = sin(inclination) * cos(phi);

    // Doppler factor
    float delta = dopplerFactor(beta, acos(clamp(cos_theta, -1.0, 1.0)));

    // Beaming boost for flux
    float boost_exponent = 3.0 + alpha;  // δ^(3+α) for optically thin
    float boost = pow(delta, boost_exponent);

    // Clamp to reasonable range
    return clamp(boost, 0.01, 1000.0);
}

/**
 * @brief Compute Doppler boost with default blackbody spectrum (α=0)
 *
 * Convenience wrapper for blackbody disks.
 *
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @param phi Azimuthal angle [rad]
 * @param inclination Disk inclination [rad]
 * @return Doppler boost factor
 */
float diskDopplerBoost(float r, float a_star, float phi, float inclination) {
    return diskDopplerBoost(r, a_star, phi, inclination, 0.0);
}

/**
 * @brief Compute Doppler boost color shift
 *
 * Maps Doppler factor to RGB color (blue = approaching, red = receding).
 * Useful for visualization of disk rotation.
 *
 * @param delta Doppler factor δ
 * @return RGB color (0 = red, 1 = white, 2+ = blue)
 */
vec3 dopplerColorShift(float delta) {
    // δ < 1: redshift (receding), δ > 1: blueshift (approaching)

    if (delta < 1.0) {
        // Redshift: interpolate from deep red (δ=0.1) to white (δ=1.0)
        float t = (delta - 0.1) / 0.9;
        t = clamp(t, 0.0, 1.0);
        return mix(vec3(0.5, 0.0, 0.0), vec3(1.0), t);
    } else {
        // Blueshift: interpolate from white (δ=1.0) to blue (δ=10)
        float t = (delta - 1.0) / 9.0;
        t = clamp(t, 0.0, 1.0);
        return mix(vec3(1.0), vec3(0.0, 0.5, 1.0), t);
    }
}

/**
 * @brief Compute disk color with Doppler beaming
 *
 * Combines base disk color with Doppler boost factor.
 *
 * @param base_color Base disk color (without Doppler)
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @param phi Azimuthal angle [rad]
 * @param inclination Disk inclination [rad]
 * @param alpha Spectral index
 * @param show_color_shift If true, multiply by color shift for visualization
 * @return Doppler-boosted RGB color
 */
vec3 diskColorWithDoppler(vec3 base_color, float r, float a_star, float phi,
                           float inclination, float alpha, bool show_color_shift) {
    float boost = diskDopplerBoost(r, a_star, phi, inclination, alpha);

    vec3 color = base_color * boost;

    if (show_color_shift) {
        float delta = pow(boost, 1.0 / (3.0 + alpha));  // Recover δ from boost
        vec3 shift = dopplerColorShift(delta);
        color *= shift;
    }

    return color;
}

/**
 * @brief Compute disk asymmetry ratio (approaching/receding)
 *
 * Returns the ratio of flux on approaching side to receding side.
 * Useful for validation and debugging.
 *
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @param inclination Disk inclination [rad]
 * @param alpha Spectral index
 * @return Asymmetry ratio (typically 10-1000 for edge-on disks)
 */
float diskAsymmetryRatio(float r, float a_star, float inclination, float alpha) {
    float boost_approaching = diskDopplerBoost(r, a_star, 0.0, inclination, alpha);
    float boost_receding = diskDopplerBoost(r, a_star, 3.14159265, inclination, alpha);

    return boost_approaching / max(boost_receding, 0.001);
}

#endif // DOPPLER_BEAMING_GLSL
