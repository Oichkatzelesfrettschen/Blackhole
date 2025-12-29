/**
 * thin_disk.glsl
 * Novikov-Thorne thin accretion disk model for GPU.
 *
 * Implements radiative flux, temperature, and color calculations
 * for geometrically thin, optically thick disks.
 *
 * Based on Page & Thorne (1974) ApJ 191, 499.
 */

#ifndef THIN_DISK_GLSL
#define THIN_DISK_GLSL

// ============================================================================
// Physical Constants
// ============================================================================

const float STEFAN_BOLTZMANN = 5.670374419e-5; // erg/(cm² s K⁴)

// ============================================================================
// Disk Parameters (set via uniforms)
// ============================================================================

// Default values - override via uniforms
#ifndef DISK_M_DOT
#define DISK_M_DOT 1.0e18  // g/s (approximately Eddington for 10 M_sun)
#endif

// ============================================================================
// Novikov-Thorne Flux Profile
// ============================================================================

/**
 * Compute Novikov-Thorne correction factor for Schwarzschild.
 *
 * f(r) = 1 - √(r_in/r) + relativistic corrections
 */
float novikovThorneFactor(float r, float r_in, float r_s) {
    if (r <= r_in) return 0.0;

    float r_g = r_s * 0.5;
    float x = sqrt(r / r_g);
    float x_in = sqrt(r_in / r_g);

    // Leading term
    float term1 = 1.0 - sqrt(r_in / r);

    // Relativistic corrections (simplified Page & Thorne)
    float term2 = (3.0 / (2.0 * x * x)) * log(x / x_in);
    float term3 = -(3.0 * (x - x_in)) / (x * x * x_in);

    return max(0.0, term1 - term2 + term3);
}

/**
 * Compute disk surface flux.
 *
 * F(r) = (3 G M Ṁ)/(8π r³) * f(r)
 *
 * @param r Radius
 * @param r_in Inner edge (ISCO)
 * @param r_s Schwarzschild radius
 * @param M_dot Accretion rate
 * @return Flux (arbitrary units, normalized)
 */
float diskFlux(float r, float r_in, float r_s, float M_dot) {
    if (r < r_in) return 0.0;

    // Prefactor: 3GM/(8π r³) in geometric units
    float r3 = r * r * r;
    float prefactor = 3.0 * r_s / (16.0 * PI * r3);

    // Relativistic correction
    float f_r = novikovThorneFactor(r, r_in, r_s);

    return prefactor * M_dot * f_r;
}

/**
 * Compute disk temperature from flux.
 *
 * T = (F/σ)^(1/4)
 *
 * Returns normalized temperature (0-1 range for visualization).
 */
float diskTemperature(float flux, float T_max) {
    if (flux <= 0.0) return 0.0;
    float T = pow(flux, 0.25);
    return clamp(T / T_max, 0.0, 1.0);
}

// ============================================================================
// Relativistic Effects
// ============================================================================

/**
 * Gravitational redshift factor for disk emission.
 *
 * g = √(1 - 3M/r) = √(1 - 1.5 r_s/r)
 */
float diskGravitationalRedshift(float r, float r_s) {
    float x = 1.5 * r_s / r;
    if (x >= 1.0) return 0.0;
    return sqrt(1.0 - x);
}

/**
 * Doppler factor for orbiting disk element.
 *
 * v_orb = √(GM/r) = c√(r_s/(2r))
 * β = v/c
 * δ = 1/(γ(1 - β cos φ sin i))
 */
float diskDopplerFactor(float r, float phi, float inclination, float r_s) {
    // Orbital velocity in units of c
    float beta = sqrt(0.5 * r_s / r);

    // Line-of-sight component
    float sin_i = sin(inclination);
    float beta_los = beta * sin(phi) * sin_i;

    // Lorentz factor
    float gamma = 1.0 / sqrt(1.0 - beta * beta);

    // Doppler factor
    return 1.0 / (gamma * (1.0 - beta_los));
}

/**
 * Combined relativistic intensity factor.
 *
 * I_obs/I_emit = (g δ)^4 for bolometric
 *              = (g δ)^3 for monochromatic (specific intensity I_ν)
 */
float diskIntensityFactor(float r, float phi, float inclination, float r_s,
                          bool bolometric) {
    float g = diskGravitationalRedshift(r, r_s);
    float delta = diskDopplerFactor(r, phi, inclination, r_s);

    float factor = g * delta;
    if (bolometric) {
        return factor * factor * factor * factor;
    } else {
        return factor * factor * factor;
    }
}

// ============================================================================
// Temperature to Color Mapping
// ============================================================================

/**
 * Convert temperature to RGB color (blackbody approximation).
 *
 * Uses Planckian locus approximation for 1000K - 40000K.
 */
vec3 temperatureToRGB(float T) {
    // Clamp to valid range
    T = clamp(T, 1000.0, 40000.0);
    float t = T / 100.0;

    vec3 color;

    // Red
    if (T <= 6600.0) {
        color.r = 1.0;
    } else {
        color.r = 329.698727446 * pow(t - 60.0, -0.1332047592);
        color.r = clamp(color.r / 255.0, 0.0, 1.0);
    }

    // Green
    if (T <= 6600.0) {
        color.g = 99.4708025861 * log(t) - 161.1195681661;
    } else {
        color.g = 288.1221695283 * pow(t - 60.0, -0.0755148492);
    }
    color.g = clamp(color.g / 255.0, 0.0, 1.0);

    // Blue
    if (T >= 6600.0) {
        color.b = 1.0;
    } else if (T <= 1900.0) {
        color.b = 0.0;
    } else {
        color.b = 138.5177312231 * log(t - 10.0) - 305.0447927307;
        color.b = clamp(color.b / 255.0, 0.0, 1.0);
    }

    return color;
}

/**
 * Convert normalized temperature (0-1) to disk color.
 *
 * Maps temperature range appropriate for AGN/X-ray binary disks.
 */
vec3 diskTemperatureColor(float T_normalized, float T_min, float T_max) {
    float T = mix(T_min, T_max, T_normalized);
    return temperatureToRGB(T);
}

// ============================================================================
// Complete Disk Rendering
// ============================================================================

/**
 * Parameters for disk rendering.
 */
struct DiskRenderParams {
    float r_in;         // Inner edge (ISCO)
    float r_out;        // Outer edge
    float r_s;          // Schwarzschild radius
    float M_dot;        // Accretion rate (normalized)
    float inclination;  // Viewing angle
    float T_max;        // Peak temperature (K)
    float T_min;        // Outer edge temperature (K)
};

/**
 * Compute observed disk color at given position.
 *
 * @param r Radius in disk plane
 * @param phi Azimuthal angle (0 = toward observer)
 * @param params Disk parameters
 * @return RGB color with intensity
 */
vec4 diskColor(float r, float phi, DiskRenderParams params) {
    if (r < params.r_in || r > params.r_out) {
        return vec4(0.0);
    }

    // Compute local flux
    float flux = diskFlux(r, params.r_in, params.r_s, params.M_dot);

    // Temperature (normalized)
    float T_norm = diskTemperature(flux, params.T_max);

    // Base color from temperature
    vec3 color = diskTemperatureColor(T_norm, params.T_min, params.T_max);

    // Relativistic intensity modification
    float intensity = diskIntensityFactor(r, phi, params.inclination,
                                          params.r_s, false);

    // Apply intensity
    color *= intensity;

    // Alpha based on emission strength
    float alpha = clamp(flux * 1000.0, 0.0, 1.0);

    return vec4(color, alpha);
}

/**
 * Sample disk along a ray.
 *
 * For ray that intersects disk plane at (r, phi), returns color.
 */
vec4 sampleDisk(vec3 hitPoint, vec3 diskNormal, float r_s) {
    // Project to disk plane
    float r = length(hitPoint.xy);
    float phi = atan(hitPoint.y, hitPoint.x);

    // Default disk parameters
    DiskRenderParams params;
    params.r_in = 3.0 * r_s;     // ISCO for Schwarzschild
    params.r_out = 100.0 * r_s;
    params.r_s = r_s;
    params.M_dot = 1.0;          // Normalized
    params.inclination = acos(abs(dot(normalize(hitPoint), diskNormal)));
    params.T_max = 1.0;
    params.T_min = 0.1;

    return diskColor(r, phi, params);
}

// ============================================================================
// Disk Intersection
// ============================================================================

/**
 * Intersect ray with thin disk (z = 0 plane).
 *
 * @param rayOrigin Ray start position
 * @param rayDir Ray direction (normalized)
 * @param t_hit Output: parameter at intersection
 * @return true if ray hits disk plane
 */
bool intersectDiskPlane(vec3 rayOrigin, vec3 rayDir, out float t_hit) {
    // Disk in z = 0 plane
    if (abs(rayDir.z) < 1e-10) {
        return false; // Ray parallel to disk
    }

    t_hit = -rayOrigin.z / rayDir.z;
    return t_hit > 0.0;
}

/**
 * Check if point is within disk bounds.
 */
bool isInDisk(vec3 point, float r_in, float r_out) {
    float r = length(point.xy);
    return r >= r_in && r <= r_out;
}

// ============================================================================
// Kerr Disk Modifications
// ============================================================================

/**
 * ISCO radius for Kerr black hole (simplified).
 */
float kerrISCORadius(float r_s, float a, bool prograde) {
    float M = r_s * 0.5;
    float a_star = clamp(a / M, -1.0, 1.0);

    // Approximate formula
    if (prograde) {
        // r_ISCO goes from 6M (a=0) to M (a=M)
        return M * (3.0 + pow(1.0 - a_star, 0.5) * 3.0);
    } else {
        // Retrograde: larger ISCO
        return M * (3.0 + pow(1.0 + abs(a_star), 0.5) * 3.0);
    }
}

/**
 * Frame-dragging modification to disk emission.
 *
 * Disk corotates with frame-dragging, modifying observed Doppler.
 */
float kerrDiskDopplerFactor(float r, float phi, float inclination,
                            float r_s, float a) {
    float M = r_s * 0.5;

    // Frame-dragging angular velocity
    float omega_fd = (2.0 * M * a * r) / (r * r * (r * r + a * a) + 2.0 * M * a * a * r);

    // Keplerian orbital velocity + frame dragging
    float omega_K = sqrt(M) / (pow(r, 1.5) + a * sqrt(M));
    float v = r * omega_K; // Effective velocity

    float beta = v / (C_LIGHT);
    beta = clamp(beta, -0.99, 0.99);

    float sin_i = sin(inclination);
    float beta_los = beta * sin(phi) * sin_i;

    float gamma = 1.0 / sqrt(1.0 - beta * beta);

    return 1.0 / (gamma * (1.0 - beta_los));
}

#endif // THIN_DISK_GLSL
