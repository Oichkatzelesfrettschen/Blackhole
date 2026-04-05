#ifndef KERR_SCHILD_GLSL
#define KERR_SCHILD_GLSL

/**
 * @file kerr_schild.glsl
 * @brief Outgoing Kerr-Schild coordinate utilities for GPU ray tracing.
 *
 * WHY: Boyer-Lindquist (BL) coordinates have a coordinate singularity at
 *      Delta = r^2 - r_s*r + a^2 = 0 (the outer horizon).  kerr.glsl
 *      kerrStep() uses the outgoing KS phi/t update (A + dr_dlam)/Delta
 *      whose numerator cancels the Delta pole for ingoing photons at r_+.
 *      This file provides the full coordinate utility library for callers
 *      that need explicit KS metric components or velocity transforms.
 *
 * WHAT: GLSL port of src/physics/coordinates.h KS functions, restricted to
 *       the outgoing (not ingoing) null foliation required for backward
 *       ray tracing (camera -> scene).  Reference: arXiv:2310.02321.
 *
 *   Convention: r_s = 2M (Schwarzschild radius), a = spin parameter.
 *   C++ reference uses mGeom = M = r_s/2; wherever C++ writes 2*mGeom
 *   this file writes r_s directly.
 *
 *   Provided functions:
 *     ksF()                  -- scalar f = 2Mr/Sigma = r_s*r/Sigma
 *     ksOutgoingNullVec()    -- outgoing principal null vector l^mu = (1,1,0,0)
 *     ksIngoingNullT()       -- ingoing null t-component (n^r = -1)
 *     blToKsDtDr()           -- dt_KS/dr correction = 2Mr/Delta = r_s*r/Delta
 *     blToKsDphiDr()         -- dphi_KS/dr correction = a/Delta
 *     blToKsVelocity()       -- BL 4-velocity -> outgoing KS 4-velocity
 *     ksToBlVelocity()       -- outgoing KS 4-velocity -> BL 4-velocity
 *     ksToBlPhi()            -- KS phi -> BL phi (instantaneous correction)
 *     ksRadialMetric()       -- key KS metric components (g_tt, g_tr, g_rr, g_phph)
 *
 * HOW (integration with existing shaders):
 *   #include "include/kerr.glsl"          // must precede this file
 *   #include "include/kerr_schild.glsl"
 *
 * References:
 *   - arXiv:2310.02321  (outgoing null vector for backward ray tracing)
 *   - Kerr (1963), Visser (2007) "The Kerr spacetime" Ch. 1
 *   - MTW Ch. 33
 *   - src/physics/coordinates.h (authoritative C++ reference implementation)
 */

// ============================================================================
// KS scalar function f = 2Mr / Sigma
// ============================================================================

/**
 * @brief Kerr-Schild scalar function f = 2Mr/Sigma = r_s*r/Sigma.
 *
 * The KS metric decomposes as g_mu_nu = eta_mu_nu + f * l_mu * l_nu.
 *
 * @param r       Radial coordinate [geometric units]
 * @param theta   Polar angle [rad]
 * @param r_s     Schwarzschild radius = 2M [geometric units]
 * @param a       Spin parameter [geometric units]
 * @return f (dimensionless)
 */
float ksF(float r, float theta, float r_s, float a) {
    float cosT  = cos(theta);
    float sigma = r * r + a * a * cosT * cosT;
    if (sigma < 1e-30) { return 0.0; }
    return (r_s * r) / sigma;     // 2Mr/Sigma where r_s = 2M
}

// ============================================================================
// Principal null vectors
// ============================================================================

/**
 * @brief Outgoing principal null vector l^mu in outgoing KS coordinates.
 *
 * In outgoing Kerr-Schild coordinates the outgoing null generator takes the
 * simple form l^mu = (1, 1, 0, 0).  This is the correct null vector for
 * BACKWARD ray tracing (camera -> scene) per arXiv:2310.02321.
 *
 * WHY outgoing (not ingoing): backward rays travel from observer toward the
 * black hole; they follow the outgoing null cone.  Using the ingoing null
 * vector gives incorrect caustic structure for observer-to-source tracing.
 *
 * @return vec4(l^t, l^r, l^theta, l^phi) = (1, 1, 0, 0)
 */
vec4 ksOutgoingNullVec() {
    return vec4(1.0, 1.0, 0.0, 0.0);
}

/**
 * @brief t-component of the ingoing null vector n^mu in outgoing KS coords.
 *
 * Solves g_mu_nu n^mu n^nu = 0 with n^r = -1, n^theta = 0, n^phi = 0.
 * The quadratic g_tt*(n^t)^2 + 2*g_tr*n^t*(n^r) + g_rr*(n^r)^2 = 0 gives:
 *   n^t = (g_tr + sqrt(g_tr^2 - g_tt * g_rr)) / g_tt
 *
 * @param r     Radial coordinate [geometric units]
 * @param theta Polar angle [rad]
 * @param r_s   Schwarzschild radius [geometric units]
 * @param a     Spin parameter [geometric units]
 * @return n^t  (n^r = -1, n^theta = n^phi = 0)
 */
float ksIngoingNullT(float r, float theta, float r_s, float a) {
    float cosT   = cos(theta);
    float sinT   = sin(theta);
    float sin2   = sinT * sinT;
    float sigma  = r * r + a * a * cosT * cosT;
    float delta  = r * r - r_s * r + a * a;
    float f      = (r_s * r) / max(sigma, 1e-30);

    // BL metric components
    float blTt   = -(1.0 - f);
    float blTph  = -f * a * sin2;
    float blRr   = sigma / max(abs(delta), 1e-30);
    float blPhph = (r*r + a*a + f * a * a * sin2) * sin2;

    // KS transformation coefficients
    // alpha = 2Mr/Delta = r_s*r/Delta (C++ uses rS = 2*mGeom = r_s)
    // beta  = a/Delta
    float invD   = 1.0 / max(abs(delta), 1e-30);
    float alpha  = r_s * r * invD;
    float beta   = a * invD;

    float gTt  = blTt;
    float gTr  = blTt * alpha + blTph * beta;
    float gRr  = blTt * alpha * alpha + 2.0 * blTph * alpha * beta
               + blRr + blPhph * beta * beta;

    if (abs(gTt) < 1e-30) { return 1.0; }

    float disc     = gTr * gTr - gTt * gRr;
    float sqrtDisc = sqrt(max(disc, 0.0));
    return (gTr + sqrtDisc) / gTt;
}

// ============================================================================
// BL <-> KS differential transformations
// ============================================================================

/**
 * @brief dt correction for BL -> outgoing KS time transformation.
 *
 * The outgoing KS coordinate transformation is:
 *   dt_KS = dt_BL + (2Mr / Delta) * dr
 *
 * Returns dt_KS/dr = 2Mr/Delta = r_s*r/Delta.
 *
 * @param r    Radial coordinate [geometric units]
 * @param r_s  Schwarzschild radius = 2M [geometric units]
 * @param a    Spin parameter [geometric units]
 * @return 2Mr/Delta  (0.0 at the horizon to avoid division by zero)
 */
float blToKsDtDr(float r, float r_s, float a) {
    float delta = r * r - r_s * r + a * a;
    if (abs(delta) < 1e-30) { return 0.0; }
    return (r_s * r) / delta;     // 2Mr/Delta where r_s = 2M
}

/**
 * @brief dphi correction for BL -> outgoing KS azimuthal transformation.
 *
 * The outgoing KS coordinate transformation is:
 *   dphi_KS = dphi_BL + (a / Delta) * dr
 *
 * @param r    Radial coordinate [geometric units]
 * @param r_s  Schwarzschild radius = 2M [geometric units]
 * @param a    Spin parameter [geometric units]
 * @return a/Delta  (0.0 at the horizon to avoid division by zero)
 */
float blToKsDphiDr(float r, float r_s, float a) {
    float delta = r * r - r_s * r + a * a;
    if (abs(delta) < 1e-30) { return 0.0; }
    return a / delta;
}

// ============================================================================
// 4-velocity transforms
// ============================================================================

/**
 * @brief Convert a BL 4-velocity to outgoing KS 4-velocity.
 *
 * Transformation from Boyer-Lindquist to outgoing Kerr-Schild:
 *   u^t_KS   = u^t_BL   + (2Mr/Delta) * u^r_BL
 *   u^r_KS   = u^r_BL
 *   u^th_KS  = u^th_BL
 *   u^phi_KS = u^phi_BL + (a/Delta)   * u^r_BL
 *
 * @param uBl  BL 4-velocity components (t, r, theta, phi)
 * @param r    Radial coordinate [geometric units]
 * @param r_s  Schwarzschild radius = 2M [geometric units]
 * @param a    Spin parameter [geometric units]
 * @return Outgoing KS 4-velocity (t, r, theta, phi)
 */
vec4 blToKsVelocity(vec4 uBl, float r, float r_s, float a) {
    float delta    = r * r - r_s * r + a * a;
    float invDelta = (abs(delta) > 1e-30) ? 1.0 / delta : 0.0;
    float dtCorr   = r_s * r * invDelta;   // 2Mr/Delta = r_s*r/Delta
    float dphCorr  = a * invDelta;         // a/Delta

    return vec4(uBl.x + dtCorr  * uBl.y,
                uBl.y,
                uBl.z,
                uBl.w + dphCorr * uBl.y);
}

/**
 * @brief Convert an outgoing KS 4-velocity back to BL 4-velocity.
 *
 * Inverse of blToKsVelocity:
 *   u^t_BL   = u^t_KS   - (2Mr/Delta) * u^r_KS
 *   u^r_BL   = u^r_KS
 *   u^th_BL  = u^th_KS
 *   u^phi_BL = u^phi_KS - (a/Delta)   * u^r_KS
 *
 * @param uKs  Outgoing KS 4-velocity components (t, r, theta, phi)
 * @param r    Radial coordinate [geometric units]
 * @param r_s  Schwarzschild radius = 2M [geometric units]
 * @param a    Spin parameter [geometric units]
 * @return BL 4-velocity (t, r, theta, phi)
 */
vec4 ksToBlVelocity(vec4 uKs, float r, float r_s, float a) {
    float delta    = r * r - r_s * r + a * a;
    float invDelta = (abs(delta) > 1e-30) ? 1.0 / delta : 0.0;
    float dtCorr   = r_s * r * invDelta;
    float dphCorr  = a * invDelta;

    return vec4(uKs.x - dtCorr  * uKs.y,
                uKs.y,
                uKs.z,
                uKs.w - dphCorr * uKs.y);
}

// ============================================================================
// phi coordinate transform (instantaneous, not path-integrated)
// ============================================================================

/**
 * @brief Convert a KS phi coordinate to BL phi at a given radius.
 *
 * The exact transform requires integrating a/Delta along the entire geodesic.
 * This function computes the instantaneous (single-snapshot) correction:
 *
 *   phi_BL = phi_KS - (a / (r_+ - r_-)) * ln|(r - r_+) / (r - r_-)|
 *
 * Returns phi_KS unchanged in the Schwarzschild limit (a = 0) or near
 * the horizons where the log argument approaches zero.
 *
 * @param r      Radial coordinate [geometric units]
 * @param phiKs  KS azimuthal coordinate [rad]
 * @param r_s    Schwarzschild radius = 2M [geometric units]
 * @param a      Spin parameter [geometric units]
 * @return BL phi [rad]
 */
float ksToBlPhi(float r, float phiKs, float r_s, float a) {
    if (abs(a) < 1e-15) { return phiKs; }    // Schwarzschild: no correction

    float M        = 0.5 * r_s;
    float disc     = M * M - a * a;
    if (disc <= 0.0) { return phiKs; }        // Extremal / super-extremal

    float sqrtDisc = sqrt(disc);
    float rPlus    = M + sqrtDisc;
    float rMinus   = M - sqrtDisc;
    float dHoriz   = rPlus - rMinus;
    if (abs(dHoriz) < 1e-15) { return phiKs; }

    float argPlus  = abs(r - rPlus);
    float argMinus = abs(r - rMinus);
    if (argPlus < 1e-15 || argMinus < 1e-15) { return phiKs; }

    return phiKs - (a / dHoriz) * log(argPlus / argMinus);
}

// ============================================================================
// Key KS metric components for null-condition checks
// ============================================================================

/**
 * @brief Outgoing KS metric components needed for radial null conditions.
 *
 * Returns the four components used to evaluate g_mu_nu n^mu n^nu = 0 for a
 * purely radial direction (n^theta = n^phi = 0):
 *   g_tt * (n^t)^2 + 2 * g_tr * n^t * n^r + g_rr * (n^r)^2 = 0
 *
 * Derived from the BL metric via outgoing KS transformation:
 *   gTt   = g_BL_tt   (unchanged)
 *   gTr   = g_BL_tt * alpha + g_BL_tph * beta
 *   gRr   = g_BL_tt * alpha^2 + 2 * g_BL_tph * alpha * beta
 *         + g_BL_rr + g_BL_phph * beta^2
 *   gPhph = g_BL_phph  (unchanged)
 * where alpha = 2Mr/Delta = r_s*r/Delta, beta = a/Delta.
 *
 * @param r     Radial coordinate [geometric units]
 * @param theta Polar angle [rad]
 * @param r_s   Schwarzschild radius = 2M [geometric units]
 * @param a     Spin parameter [geometric units]
 * @return vec4(g_tt, g_tr, g_rr, g_phph)
 */
vec4 ksRadialMetric(float r, float theta, float r_s, float a) {
    float cosT   = cos(theta);
    float sinT   = sin(theta);
    float sin2   = sinT * sinT;
    float sigma  = r * r + a * a * cosT * cosT;
    float delta  = r * r - r_s * r + a * a;
    float f      = (r_s * r) / max(sigma, 1e-30);

    // BL metric components
    float blTt   = -(1.0 - f);
    float blTph  = -f * a * sin2;
    float blRr   = sigma / max(abs(delta), 1e-30);
    float blPhph = (r*r + a*a + f * a * a * sin2) * sin2;

    // Transformation coefficients: alpha = r_s*r/Delta, beta = a/Delta
    float invD   = 1.0 / max(abs(delta), 1e-30);
    float alpha  = r_s * r * invD;
    float beta   = a * invD;

    float gTt  = blTt;
    float gTr  = blTt * alpha + blTph * beta;
    float gRr  = blTt * alpha * alpha + 2.0 * blTph * alpha * beta
               + blRr + blPhph * beta * beta;
    float gPhph = blPhph;

    return vec4(gTt, gTr, gRr, gPhph);
}

#endif // KERR_SCHILD_GLSL
