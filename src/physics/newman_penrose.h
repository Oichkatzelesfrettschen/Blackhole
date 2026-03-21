/**
 * @file newman_penrose.h
 * @brief Newman-Penrose null tetrad formalism and Weyl scalars for Kerr spacetime.
 *
 * WHY: The Newman-Penrose (NP) formalism expresses GR in a complex null tetrad
 * basis (l^mu, n^mu, m^mu, mbar^mu) and spin-weighted Weyl scalars Psi_0..Psi_4.
 * For exact Kerr (Petrov Type D algebraically special):
 *   - Psi_2 is the ONLY nonzero Weyl scalar (all others vanish identically).
 *   - Psi_4 ~ r^{-1} at scri+ encodes outgoing GWs for PERTURBED Kerr.
 *   - The Kretschmann invariant K = R_abcd R^abcd = 48 |Psi_2|^2 gives the
 *     local curvature strength; used for AMR step-size control (section 3.5 of
 *     the lacunae: strong curvature -> smaller RK4 steps near r = 0 and r = r_+).
 *
 * WHAT: Exact closed-form expressions using the Kinnersley (1969) principal null
 * tetrad in Boyer-Lindquist (BL) coordinates (t, r, theta, phi):
 *
 *   l^mu  = (1/Delta) * [(r^2 + a^2),  Delta, 0,  a]   outgoing null direction
 *   n^mu  = (1/(2 Sigma)) * [(r^2 + a^2), -Delta, 0,  a]  ingoing null direction
 *   m^mu  = (1/(sqrt(2)*conj(rho))) * [i a sin(theta), 0, 1, i/sin(theta)]
 *   mbar^mu = complex conjugate of m^mu
 *
 * where rho = -1/(r - i a cos theta), Sigma = r^2 + a^2 cos^2 theta,
 *       Delta = r^2 - r_s r + a^2.
 *
 * Weyl scalar (Petrov Type D, Kinnersley tetrad):
 *   Psi_2 = M_geo * rho^3 = -M_geo / (r - i a cos theta)^3
 *
 * Writing z = r - i a cos(theta), Sigma = |z|^2 = r^2 + a^2 cos^2(theta):
 *   Re(Psi_2) = -M_geo * r * (r^2 - 3 a^2 cos^2 theta) / Sigma^3
 *   Im(Psi_2) = -M_geo * a * cos(theta) * (3 r^2 - a^2 cos^2 theta) / Sigma^3
 *
 * Kretschmann invariant (exact, Type D identity K = 48 |Psi_2|^2):
 *   K = 48 M_geo^2 / Sigma^3   [units: 1/cm^4 in CGS-geometric]
 *
 * Limit checks:
 *   Schwarzschild (a=0): Re(Psi_2) = -M_geo/r^3, Im(Psi_2) = 0, K = 48 M_geo^2/r^6
 *   Equatorial (cos theta = 0): Im(Psi_2) = 0, K = 48 M_geo^2/r^6
 *   Ring singularity (r=0, cos theta=0, a!=0): Sigma=0 -> K -> inf
 *   Outer horizon r_+: Sigma = r_+^2 + a^2 cos^2 theta > 0, so K is finite
 *   Large r: K ~ 48 M_geo^2/r^6 (same fall-off as Schwarzschild)
 *
 * HOW: All functions take M_geo = G M / c^2 [cm] and spin parameter a [cm]
 *      (a = a_star * M_geo where a_star is the dimensionless spin in [0,1)).
 *      Sigma is returned separately so callers can detect the ring singularity
 *      (Sigma = 0) before passing it into division-heavy expressions.
 *
 * References:
 *   - Kinnersley (1969), J. Math. Phys. 10, 1195
 *   - Chandrasekhar (1983), Mathematical Theory of Black Holes, Ch. 9
 *   - Newman & Penrose (1962), J. Math. Phys. 3, 566
 *   - Teukolsky (1972), PRL 29, 1114 (uses NP formalism for Kerr perturbations)
 */

#ifndef PHYSICS_NEWMAN_PENROSE_H
#define PHYSICS_NEWMAN_PENROSE_H

#include <cmath>
#include <numbers>

#include "constants.h"
#include "safe_limits.h"

namespace physics {

// ============================================================================
// Core Kerr NP Quantities
// ============================================================================

/**
 * @brief Complex Weyl scalar Psi_2 decomposed into real and imaginary parts.
 *
 * In the Kinnersley tetrad, Psi_2 is the only nonzero Weyl scalar for exact
 * Kerr (Petrov Type D).  The pair (re, im) satisfies:
 *   |Psi_2|^2 = re^2 + im^2 = M_geo^2 / Sigma^3
 */
struct NPWeylPsi2 {
    double re = 0.0; /**< Re(Psi_2) = -M_geo r (r^2 - 3 a^2 c^2) / Sigma^3 */
    double im = 0.0; /**< Im(Psi_2) = -M_geo a c (3 r^2 - a^2 c^2) / Sigma^3 */
};

/**
 * @brief Kerr-BL Sigma function.
 *
 * Sigma = r^2 + a^2 cos^2(theta) = |r - i a cos(theta)|^2
 *
 * WHY: Sigma is the denominator of most Kerr metric components.  Returning it
 * separately allows callers to guard against the ring singularity (Sigma = 0
 * at r = 0, theta = pi/2 when a != 0) before computing derived quantities.
 *
 * @param r         Boyer-Lindquist radial coordinate [cm]
 * @param cosTheta  cos(theta); equatorial plane: 0, north pole: +1
 * @param a         Spin parameter [cm] (a = a_star * M_geo)
 * @return Sigma = r^2 + a^2 cos^2 theta [cm^2]; always >= 0
 */
[[nodiscard]] inline double kerrSigma(double r, double cosTheta, double a) noexcept {
    const double c = cosTheta;
    return (r * r) + (a * a * c * c);
}

/**
 * @brief Kerr-BL Delta function.
 *
 * Delta = r^2 - r_s r + a^2 = r^2 - 2 M_geo r + a^2
 *
 * Delta = 0 at the inner (r_-) and outer (r_+) horizons.
 *
 * @param r     Boyer-Lindquist radial coordinate [cm]
 * @param mGeo  Geometric mass G M / c^2 [cm]
 * @param a     Spin parameter [cm]
 * @return Delta [cm^2]; zero at both horizons
 */
[[nodiscard]] inline double kerrDelta(double r, double mGeo, double a) noexcept {
    return (r * r) - (2.0 * mGeo * r) + (a * a);
}

/**
 * @brief Weyl scalar Psi_2 for exact Kerr in the Kinnersley null tetrad.
 *
 * WHY: Psi_2 is the mass/spin monopole Weyl curvature of the Kerr spacetime.
 * For Petrov Type D solutions, all other Weyl scalars vanish exactly; Psi_2
 * encodes the full curvature structure.  In perturbation theory, a nonzero
 * Psi_4 signals outgoing gravitational radiation on the Kerr background.
 *
 * WHAT: With rho = -1/(r - i a cos theta),
 *   Psi_2 = M_geo * rho^3 = -M_geo / (r - i a cos theta)^3
 *
 * Expanding via conj(z)^3 / |z|^6 with z = r - iac:
 *   Re(Psi_2) = -M_geo * r * (r^2 - 3 a^2 c^2) / Sigma^3
 *   Im(Psi_2) = -M_geo * a * c * (3 r^2 - a^2 c^2) / Sigma^3
 *
 * The identity r^2(r^2-3y)^2 + y(3r^2-y)^2 = (r^2+y)^3  (with y=a^2c^2)
 * ensures |Psi_2|^2 = M_geo^2 / Sigma^3 exactly.
 *
 * @param r         Boyer-Lindquist radial coordinate [cm]
 * @param cosTheta  cos(theta); equatorial: 0, pole: +/-1
 * @param mGeo      Geometric mass G M / c^2 [cm]
 * @param a         Spin parameter [cm] (a = a_star * M_geo, a=0 for Schwarzschild)
 * @return NPWeylPsi2 with (re, im); both zero if mGeo <= 0 or Sigma <= 0
 */
[[nodiscard]] inline NPWeylPsi2 kerrWeylPsi2(double r, double cosTheta,
                                              double mGeo, double a) noexcept {
    if (mGeo <= 0.0) { return {}; }

    const double c     = cosTheta;
    const double sigma = kerrSigma(r, c, a);
    if (sigma <= 0.0) { return {}; } /* ring singularity guard */

    const double sigma3 = sigma * sigma * sigma;
    const double r2     = r * r;
    const double a2c2   = a * a * c * c;

    /* Re(Psi_2) = -M_geo * r * (r^2 - 3 a^2 c^2) / Sigma^3 */
    const double re = -mGeo * r * (r2 - (3.0 * a2c2)) / sigma3;
    /* Im(Psi_2) = -M_geo * a * c * (3 r^2 - a^2 c^2) / Sigma^3 */
    const double im = -mGeo * a * c * ((3.0 * r2) - a2c2) / sigma3;

    return {.re = re, .im = im};
}

/**
 * @brief Kretschmann curvature invariant for exact Kerr.
 *
 * WHY: K = R_abcd R^abcd quantifies the local spacetime curvature strength.
 * At the ring singularity (Sigma=0), K diverges physically.  Away from it,
 * K is smooth and large near the horizon, enabling AMR-style step refinement:
 * a geodesic integrator can halve the step size whenever K exceeds a threshold,
 * concentrating integration effort where curvature is strongest.
 *
 * WHAT: For Petrov Type D spacetimes the Kretschmann scalar equals
 *   K = 48 |Psi_2|^2 = 48 M_geo^2 / Sigma^3
 *
 * This result follows from the Type D identity and is exact for Kerr.
 * Schwarzschild limit (a=0): K = 48 M_geo^2 / r^6
 * Equatorial plane (cos theta=0): K = 48 M_geo^2 / r^6 (spin independent)
 * Outer horizon (r=r_+, Sigma>0): K = 48 M_geo^2 / (r_+^2 + a^2 cos^2 theta)^3
 *
 * @param r         Boyer-Lindquist radial coordinate [cm]
 * @param cosTheta  cos(theta)
 * @param mGeo      Geometric mass G M / c^2 [cm]
 * @param a         Spin parameter [cm]
 * @return K = 48 M_geo^2 / Sigma^3 [cm^{-4}]; 0 if mGeo <= 0 or Sigma <= 0
 */
[[nodiscard]] inline double kerrKretschmann(double r, double cosTheta,
                                             double mGeo, double a) noexcept {
    if (mGeo <= 0.0) { return 0.0; }

    const double sigma = kerrSigma(r, cosTheta, a);
    if (sigma <= 0.0) { return safeInfinity<double>(); }

    const double sigma3 = sigma * sigma * sigma;
    return 48.0 * mGeo * mGeo / sigma3;
}

// ============================================================================
// Kinnersley Null Tetrad Components (Boyer-Lindquist coordinates)
// ============================================================================

/**
 * @brief Contravariant components of the Kinnersley outgoing null vector l^mu.
 *
 * In Boyer-Lindquist (t, r, theta, phi) index order:
 *   l^t   = (r^2 + a^2) / Delta
 *   l^r   = 1
 *   l^theta = 0
 *   l^phi = a / Delta
 *
 * l^mu is a principal null direction of the Weyl tensor, tangent to outgoing
 * null geodesics that generate the outer horizon.  It satisfies:
 *   g_mu_nu l^mu l^nu = 0  (null)
 *
 * WHY: The outgoing principal null direction is the natural frame for backward
 * ray-tracing from the camera toward the black hole; photons propagating along
 * l^mu encounter no NP spin-coefficient complications at the outer horizon.
 *
 * @param r     Boyer-Lindquist radial coordinate [cm]
 * @param mGeo  Geometric mass G M / c^2 [cm]
 * @param a     Spin parameter [cm]
 * @param lT    Output: l^t component (affine-parameterized, Delta factored out)
 * @param lR    Output: l^r component (= 1)
 * @param lPhi  Output: l^phi component
 */
inline void kinnersleyL(double r, double mGeo, double a,
                         double& lT, double& lR, double& lPhi) noexcept {
    const double delta = kerrDelta(r, mGeo, a);
    if (std::abs(delta) < 1.0e-30) {
        /* At the horizon Delta=0; l^t, l^phi diverge (coordinate singularity). */
        lT   = safeInfinity<double>();
        lR   = 1.0;
        lPhi = safeInfinity<double>();
        return;
    }
    lT   = ((r * r) + (a * a)) / delta;
    lR   = 1.0;
    lPhi = a / delta;
}

/**
 * @brief Contravariant components of the Kinnersley ingoing null vector n^mu.
 *
 * In Boyer-Lindquist (t, r, theta, phi) index order:
 *   n^t   = (r^2 + a^2) / (2 Sigma)
 *   n^r   = -Delta / (2 Sigma)
 *   n^theta = 0
 *   n^phi = a / (2 Sigma)
 *
 * n^mu is the ingoing principal null direction, regular at both horizons.
 * It satisfies g_mu_nu n^mu l^nu = -1 (cross-normalization with l^mu).
 *
 * @param r         Boyer-Lindquist radial coordinate [cm]
 * @param cosTheta  cos(theta)
 * @param mGeo      Geometric mass G M / c^2 [cm]
 * @param a         Spin parameter [cm]
 * @param nT        Output: n^t component
 * @param nR        Output: n^r component
 * @param nPhi      Output: n^phi component
 */
inline void kinnersleyN(double r, double cosTheta, double mGeo, double a,
                         double& nT, double& nR, double& nPhi) noexcept {
    const double sigma = kerrSigma(r, cosTheta, a);
    if (sigma <= 0.0) {
        nT = nR = nPhi = 0.0;
        return;
    }
    const double delta    = kerrDelta(r, mGeo, a);
    const double twoSigma = 2.0 * sigma;
    nT   = ((r * r) + (a * a)) / twoSigma;
    nR   = -delta / twoSigma;
    nPhi = a / twoSigma;
}

// ============================================================================
// Derived Quantities
// ============================================================================

/**
 * @brief Verify the Petrov Type D identity K = 48 |Psi_2|^2 numerically.
 *
 * WHY: Provides a self-consistency check that the Kretschmann and Psi_2
 * implementations are mutually consistent.  For exact Kerr both paths reduce
 * to 48 M_geo^2 / Sigma^3, so the relative error should be < 1e-13 (double
 * precision round-off).  A large relative error signals a bug or an attempt
 * to apply these formulas outside the Kerr family.
 *
 * @param r         Boyer-Lindquist radial coordinate [cm]
 * @param cosTheta  cos(theta)
 * @param mGeo      Geometric mass G M / c^2 [cm]
 * @param a         Spin parameter [cm]
 * @return Relative error |K - 48|Psi_2|^2| / K; 0 if K = 0
 */
[[nodiscard]] inline double petrovTypeDCheck(double r, double cosTheta,
                                              double mGeo, double a) noexcept {
    const double kScalar  = kerrKretschmann(r, cosTheta, mGeo, a);
    const NPWeylPsi2 psi2 = kerrWeylPsi2(r, cosTheta, mGeo, a);
    const double psi2mod2 = (psi2.re * psi2.re) + (psi2.im * psi2.im);
    const double expected = 48.0 * psi2mod2;

    if (kScalar <= 0.0) { return 0.0; }
    return std::abs(kScalar - expected) / kScalar;
}

/**
 * @brief Squared magnitude |Psi_2|^2 = M_geo^2 / Sigma^3.
 *
 * Convenience wrapper; avoids squaring re/im separately when only the
 * magnitude is needed (e.g., for Kretschmann-based AMR thresholds).
 *
 * @param r         Boyer-Lindquist radial coordinate [cm]
 * @param cosTheta  cos(theta)
 * @param mGeo      Geometric mass G M / c^2 [cm]
 * @param a         Spin parameter [cm]
 * @return |Psi_2|^2 = M_geo^2 / Sigma^3 [cm^{-4}]; 0 if Sigma = 0 or mGeo = 0
 */
[[nodiscard]] inline double kerrWeylPsi2ModSq(double r, double cosTheta,
                                               double mGeo, double a) noexcept {
    if (mGeo <= 0.0) { return 0.0; }
    const double sigma = kerrSigma(r, cosTheta, a);
    if (sigma <= 0.0) { return safeInfinity<double>(); }
    const double sigma3 = sigma * sigma * sigma;
    return (mGeo * mGeo) / sigma3;
}

} // namespace physics

#endif // PHYSICS_NEWMAN_PENROSE_H
