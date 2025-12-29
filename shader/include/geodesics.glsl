/**
 * geodesics.glsl
 * Null geodesic integration for photon ray tracing around black holes.
 *
 * Implements GPU-efficient ray marching along curved spacetime paths.
 */

#ifndef GEODESICS_GLSL
#define GEODESICS_GLSL

// ============================================================================
// Ray State Structure
// ============================================================================

struct GeodesicRay {
    vec3 position;    // Current position (Cartesian)
    vec3 direction;   // Current direction (unit vector)
    float r;          // Current radius
    float phi;        // Accumulated azimuthal angle
    float affine;     // Affine parameter (arc length)
    bool terminated;  // Ray ended (hit horizon or escaped)
    int termination;  // 0=running, 1=horizon, 2=escaped, 3=max_steps
};

// ============================================================================
// Geodesic Integration
// ============================================================================

/**
 * Initialize a geodesic ray from camera position and direction.
 */
GeodesicRay initGeodesicRay(vec3 origin, vec3 dir) {
    GeodesicRay ray;
    ray.position = origin;
    ray.direction = normalize(dir);
    ray.r = length(origin);
    ray.phi = atan(origin.y, origin.x);
    ray.affine = 0.0;
    ray.terminated = false;
    ray.termination = 0;
    return ray;
}

/**
 * Compute impact parameter for a ray.
 * b = |r × v| for a ray at position r with velocity v
 */
float computeImpactParameter(vec3 position, vec3 direction) {
    vec3 cross_prod = cross(position, direction);
    return length(cross_prod);
}

/**
 * Step the geodesic ray using curved spacetime integration.
 *
 * Uses a modified Euler method that accounts for spacetime curvature.
 * The ray direction is bent toward the black hole based on local geometry.
 *
 * @param ray The ray state to update
 * @param r_s Schwarzschild radius
 * @param dt Step size
 */
void stepGeodesic(inout GeodesicRay ray, float r_s, float dt) {
    if (ray.terminated) {
        return;
    }

    float r = ray.r;

    // Check for horizon crossing
    if (r <= r_s * 1.001) {
        ray.terminated = true;
        ray.termination = 1; // Horizon
        return;
    }

    // Compute gravitational acceleration toward center
    // In Schwarzschild geometry, the effective force is stronger near horizon
    vec3 radial_dir = -normalize(ray.position);
    float r2 = r * r;
    float r3 = r2 * r;

    // Geodesic deviation: d²x/dλ² includes Christoffel symbol terms
    // Simplified: acceleration ~ 1.5 * r_s / r² for null geodesics
    float accel_magnitude = 1.5 * r_s / r2;

    // Additional bending from angular momentum (photon sphere effect)
    // Near r = 1.5 r_s, orbits become unstable
    float angular_factor = 1.0 + 0.5 * r_s / r;

    // Compute perpendicular component of position relative to ray
    vec3 perp = ray.position - dot(ray.position, ray.direction) * ray.direction;
    float perp_dist = length(perp);

    // Bending direction
    vec3 bend_dir;
    if (perp_dist > 0.001) {
        bend_dir = normalize(perp);
    } else {
        bend_dir = radial_dir;
    }

    // Apply geodesic bending to direction
    float bend_amount = accel_magnitude * angular_factor * dt;
    ray.direction = normalize(ray.direction - bend_dir * bend_amount);

    // Advance position
    ray.position += ray.direction * dt;
    ray.r = length(ray.position);
    ray.affine += dt;

    // Check for escape
    if (ray.r > 100.0 * r_s) {
        ray.terminated = true;
        ray.termination = 2; // Escaped
    }
}

/**
 * Higher-order geodesic integration using RK2 (Midpoint method).
 *
 * More accurate than simple Euler, important for close approaches.
 * Error: O(dt³) per step, O(dt²) global
 */
void stepGeodesicRK2(inout GeodesicRay ray, float r_s, float dt) {
    if (ray.terminated) {
        return;
    }

    // Store initial state
    vec3 pos0 = ray.position;
    vec3 dir0 = ray.direction;

    // Half step
    stepGeodesic(ray, r_s, dt * 0.5);

    // Get midpoint state
    vec3 pos_mid = ray.position;
    vec3 dir_mid = ray.direction;

    // Reset and use midpoint derivative for full step
    ray.position = pos0;
    ray.direction = dir_mid; // Use midpoint direction

    // Full step
    stepGeodesic(ray, r_s, dt);
}

/**
 * Compute geodesic acceleration for RK4 stages.
 *
 * Returns the acceleration vector for a photon at position pos
 * with angular momentum squared h2.
 */
vec3 geodesicAcceleration(vec3 pos, float h2, float r_s) {
    float r2 = dot(pos, pos);
    float r = sqrt(r2);
    float r5 = r2 * r2 * r;

    // Prevent division by zero near singularity
    if (r < r_s * 0.1) {
        return vec3(0.0);
    }

    // Geodesic equation: a = -1.5 * r_s * h² / r⁵ * r̂
    return -1.5 * r_s * h2 * pos / r5;
}

/**
 * Fourth-order Runge-Kutta geodesic integrator.
 *
 * Integrates the geodesic equation:
 *   dx/dλ = v
 *   dv/dλ = a(x, h²)
 *
 * where h² = |x × v|² is the conserved angular momentum squared.
 *
 * Error: O(dt⁵) per step, O(dt⁴) global
 * Recommended for high-accuracy ray tracing near the photon sphere.
 */
void stepGeodesicRK4(inout GeodesicRay ray, float r_s, float dt) {
    if (ray.terminated) {
        return;
    }

    vec3 x0 = ray.position;
    vec3 v0 = ray.direction;

    // Compute conserved angular momentum squared
    vec3 h = cross(x0, v0);
    float h2 = dot(h, h);

    // k1: derivatives at initial point
    vec3 k1_x = v0;
    vec3 k1_v = geodesicAcceleration(x0, h2, r_s);

    // k2: derivatives at midpoint using k1
    vec3 x1 = x0 + 0.5 * dt * k1_x;
    vec3 v1 = v0 + 0.5 * dt * k1_v;
    vec3 k2_x = v1;
    vec3 k2_v = geodesicAcceleration(x1, h2, r_s);

    // k3: derivatives at midpoint using k2
    vec3 x2 = x0 + 0.5 * dt * k2_x;
    vec3 v2 = v0 + 0.5 * dt * k2_v;
    vec3 k3_x = v2;
    vec3 k3_v = geodesicAcceleration(x2, h2, r_s);

    // k4: derivatives at endpoint using k3
    vec3 x3 = x0 + dt * k3_x;
    vec3 v3 = v0 + dt * k3_v;
    vec3 k4_x = v3;
    vec3 k4_v = geodesicAcceleration(x3, h2, r_s);

    // RK4 weighted average
    ray.position = x0 + (dt / 6.0) * (k1_x + 2.0 * k2_x + 2.0 * k3_x + k4_x);
    ray.direction = normalize(v0 + (dt / 6.0) * (k1_v + 2.0 * k2_v + 2.0 * k3_v + k4_v));
    ray.r = length(ray.position);
    ray.affine += dt;

    // Check termination conditions
    if (ray.r <= r_s * 1.001) {
        ray.terminated = true;
        ray.termination = 1; // Horizon
    } else if (ray.r > 100.0 * r_s) {
        ray.terminated = true;
        ray.termination = 2; // Escaped
    }
}

// ============================================================================
// Full Ray Trace
// ============================================================================

/**
 * Trace a complete geodesic from origin to termination.
 *
 * @param origin Starting position
 * @param direction Initial ray direction
 * @param r_s Schwarzschild radius
 * @param max_steps Maximum integration steps
 * @param dt Step size
 * @return Final ray state
 */
GeodesicRay traceGeodesic(vec3 origin, vec3 direction, float r_s,
                          int max_steps, float dt) {
    GeodesicRay ray = initGeodesicRay(origin, direction);

    for (int i = 0; i < max_steps; i++) {
        if (ray.terminated) {
            break;
        }
        stepGeodesic(ray, r_s, dt);
    }

    if (!ray.terminated) {
        ray.termination = 3; // Max steps reached
    }

    return ray;
}

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Compute the viewing angle between ray direction and radial direction.
 * Used for Doppler calculations.
 */
float viewingAngle(vec3 position, vec3 direction) {
    vec3 radial = normalize(position);
    return acos(clamp(dot(direction, radial), -1.0, 1.0));
}

/**
 * Project a direction onto the equatorial plane.
 * Useful for accretion disk intersection tests.
 */
vec3 projectToEquatorial(vec3 dir) {
    return normalize(vec3(dir.x, dir.y, 0.0));
}

/**
 * Find intersection of ray with accretion disk (z=0 plane).
 * Returns t such that origin + t*direction intersects z=0.
 */
float intersectEquatorialPlane(vec3 origin, vec3 direction) {
    if (abs(direction.z) < 0.0001) {
        return -1.0; // Parallel to plane
    }
    return -origin.z / direction.z;
}

#endif // GEODESICS_GLSL
