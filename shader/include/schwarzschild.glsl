/**
 * schwarzschild.glsl
 * Schwarzschild spacetime metric functions for GPU ray tracing.
 *
 * All functions use normalized units where r_s = 1.0
 * Pass actual r_s as uniform and multiply/divide as needed.
 */

#ifndef SCHWARZSCHILD_GLSL
#define SCHWARZSCHILD_GLSL

// ============================================================================
// Core Metric Functions
// ============================================================================

/**
 * Metric factor f(r) = 1 - r_s/r
 *
 * @param r Radial coordinate
 * @param r_s Schwarzschild radius
 * @return f(r) metric factor
 */
float metricFactor(float r, float r_s) {
    return 1.0 - r_s / r;
}

/**
 * Photon sphere radius: r_ph = 1.5 r_s
 * Named with sch_ prefix to avoid collision with uniform variables
 */
float sch_photonSphereRadius(float r_s) {
    return 1.5 * r_s;
}

/**
 * ISCO radius: r_ISCO = 3 r_s
 * Named with sch_ prefix to avoid collision with uniform variables
 */
float sch_iscoRadius(float r_s) {
    return 3.0 * r_s;
}

/**
 * Critical impact parameter: b_crit = (3√3/2) r_s
 * Photons with b < b_crit are captured
 */
float criticalImpactParameter(float r_s) {
    return 2.598076211353316 * r_s;
}

// ============================================================================
// Gravitational Effects
// ============================================================================

/**
 * Gravitational redshift factor: z = 1/√(1 - r_s/r) - 1
 *
 * @param r Radial coordinate
 * @param r_s Schwarzschild radius
 * @return Redshift z (infinity at horizon)
 */
float gravitationalRedshift(float r, float r_s) {
    if (r <= r_s) {
        return 1e10; // Large value for horizon
    }
    float f = 1.0 - r_s / r;
    return 1.0 / sqrt(f) - 1.0;
}

/**
 * Time dilation factor: dτ/dt = √(1 - r_s/r)
 *
 * @param r Radial coordinate
 * @param r_s Schwarzschild radius
 * @return Time dilation factor (0 at horizon, 1 at infinity)
 */
float timeDilationFactor(float r, float r_s) {
    if (r <= r_s) {
        return 0.0;
    }
    return sqrt(1.0 - r_s / r);
}

/**
 * Escape velocity ratio: v_esc/c = √(r_s/r)
 *
 * @param r Radial coordinate
 * @param r_s Schwarzschild radius
 * @return v_esc/c (1 at horizon)
 */
float escapeVelocityRatio(float r, float r_s) {
    if (r <= r_s) {
        return 1.0;
    }
    return sqrt(r_s / r);
}

// ============================================================================
// Light Deflection
// ============================================================================

/**
 * Gravitational deflection angle (weak field approximation)
 * δφ = 4GM/(bc²) = 2r_s/b
 *
 * @param b Impact parameter
 * @param r_s Schwarzschild radius
 * @return Deflection angle in radians
 */
float gravitationalDeflection(float b, float r_s) {
    return 2.0 * r_s / b;
}

/**
 * Check if photon will be captured (b < b_crit)
 */
bool isPhotonCaptured(float b, float r_s) {
    return b < criticalImpactParameter(r_s);
}

// ============================================================================
// Ray Tracing Helpers
// ============================================================================

/**
 * Effective potential for null geodesics
 * V_eff(r) = (1 - r_s/r) / r²
 */
float nullEffectivePotential(float r, float r_s) {
    return (1.0 - r_s / r) / (r * r);
}

/**
 * Squared radial derivative for null geodesics
 * (dr/dφ)² = r⁴/b² - r²(1 - r_s/r)
 */
float nullRadialDerivSq(float r, float r_s, float b) {
    float r2 = r * r;
    float r4 = r2 * r2;
    float b2 = b * b;
    return r4 / b2 - r2 * (1.0 - r_s / r);
}

/**
 * Bending function for ray direction update
 * Returns the angle change per step based on local curvature
 */
float bendingAngle(float r, float r_s, float stepSize) {
    // First-order approximation of geodesic bending
    float r2 = r * r;
    return 1.5 * r_s * stepSize / r2;
}

// ============================================================================
// Accretion Disk Helpers
// ============================================================================

/**
 * Keplerian angular velocity: Ω = √(GM/r³) = √(r_s/(2r³)) (in c=G=1 units)
 */
float keplerianAngularVelocity(float r, float r_s) {
    if (r <= sch_iscoRadius(r_s)) {
        return 0.0; // Inside ISCO, no stable orbit
    }
    return sqrt(r_s / (2.0 * r * r * r));
}

/**
 * Orbital velocity: v/c = √(r_s/(2r))
 */
float orbitalVelocityRatio(float r, float r_s) {
    if (r <= r_s) {
        return 1.0;
    }
    return sqrt(r_s / (2.0 * r));
}

/**
 * Doppler factor for orbiting matter
 * Combines gravitational redshift and Doppler from orbital motion
 */
float totalDopplerFactor(float r, float r_s, float viewAngle) {
    float grav_factor = timeDilationFactor(r, r_s);
    float v = orbitalVelocityRatio(r, r_s);
    float doppler = sqrt((1.0 - v * cos(viewAngle)) / (1.0 + v * cos(viewAngle)));
    return grav_factor * doppler;
}

#endif // SCHWARZSCHILD_GLSL
