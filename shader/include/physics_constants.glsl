/**
 * physics_constants.glsl
 * Physical constants for black hole rendering.
 *
 * Note: For GPU rendering, we use normalized units where:
 *   - Schwarzschild radius r_s = 1.0 (set by uniform)
 *   - Speed of light c = 1.0
 *   - Gravitational constant G = 1.0
 *
 * This avoids floating-point precision issues with CGS values.
 */

#ifndef PHYSICS_CONSTANTS_GLSL
#define PHYSICS_CONSTANTS_GLSL

// ============================================================================
// Mathematical Constants
// ============================================================================

const float PI = 3.14159265358979323846;
const float TWO_PI = 6.28318530717958647692;
const float HALF_PI = 1.57079632679489661923;
const float INV_PI = 0.31830988618379067154;

// ============================================================================
// Physical Ratios (dimensionless, exact)
// ============================================================================

/// Photon sphere radius in Schwarzschild radii: r_ph = 1.5 r_s
const float PHOTON_SPHERE_RATIO = 1.5;

/// ISCO radius in Schwarzschild radii: r_ISCO = 3 r_s
const float ISCO_RATIO = 3.0;

/// Critical impact parameter: b_crit = (3√3/2) r_s ≈ 2.598 r_s
const float CRITICAL_IMPACT_RATIO = 2.598076211353316;

// ============================================================================
// Rendering Tolerances
// ============================================================================

/// Minimum radius for ray termination (avoid singularity)
const float MIN_RADIUS_FACTOR = 1.001;

/// Maximum ray length in Schwarzschild radii
const float MAX_RAY_LENGTH = 100.0;

/// Step size factor for ray marching
const float RAY_STEP_FACTOR = 0.1;

/// Convergence tolerance for iterative calculations
const float CONVERGENCE_TOL = 1e-6;

#endif // PHYSICS_CONSTANTS_GLSL
