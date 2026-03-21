/**
 * @file lqg_kerr.h
 * @brief Loop Quantum Gravity (LQG) corrected Kerr metric (Bambi-Modesto class).
 *
 * WHY: Loop quantum gravity predicts a minimum area gap, which regularises the
 * classical Kerr singularity.  EHT 2024-2025 shadow observations constrain the
 * LQG polymer length to l < ~0.3 M at M87* mass scales (arXiv:2511.17975).
 * This header implements the Hayward-type effective-mass regularisation, the
 * simplest class of LQG-corrected rotating metrics compatible with those bounds.
 *
 * WHAT: The mass function becomes radially dependent (Bambi & Modesto 2011,
 * arXiv:1107.4501; Hayward 2006 for the non-rotating seed):
 *
 *   M_eff(r) = M * r^3 / (r^3 + 2 l^2 M)
 *
 * where l [length] is the LQG polymer parameter (related to the area gap
 * Delta_0 = 4 sqrt(3) pi l_Planck^2 by l ~ l_Planck for the minimal model).
 *
 * The metric in Boyer-Lindquist coordinates is then the standard Kerr form
 * with Kerr Delta replaced by:
 *
 *   Delta_LQG(r) = r^2 - 2 M_eff(r) r + a^2
 *
 * All other Kerr formulas (Sigma, A, g_tph) are unchanged.
 *
 * Key limits:
 *   - l = 0   -> exact Kerr (classical limit)
 *   - r -> 0  -> M_eff -> 0, metric regular at the origin (singularity removed)
 *   - r -> inf -> M_eff -> M, asymptotically flat and reduces to Kerr
 *
 * EHT observational bound: l / M < 0.3 at 1-sigma for M87* (arXiv:2511.17975).
 *
 * HOW: Call lqgEffectiveMass() to obtain M_eff(r), then lqgDelta() for the
 * modified radial discriminant.  The remaining five metric components follow
 * from the standard Kerr formulas with Delta_LQG substituted for Delta_Kerr.
 * All functions are inline, stateless, and work in geometric units (G = c = 1).
 *
 * References:
 *   - Hayward, S. A. (2006). Phys. Rev. Lett. 96, 031103 -- regular black hole seed
 *   - Bambi, C. & Modesto, L. (2011). arXiv:1107.4501 -- Kerr extension
 *   - Islam, S. U. et al. (2020). JCAP 09, 030 -- shadow and geodesics
 *   - EHT Collaboration + Vagnozzi et al. (2022). arXiv:2205.07787 -- EHT constraints
 *   - LQG shadow paper (2025). arXiv:2511.17975 -- latest EHT LQG bounds
 */

#ifndef PHYSICS_LQG_KERR_H
#define PHYSICS_LQG_KERR_H

#include <cmath>
#include <limits>

namespace physics {

// ============================================================================
// Effective mass function
// ============================================================================

/**
 * @brief LQG radially dependent effective mass: M_eff(r) = M r^3 / (r^3 + 2 l^2 M).
 *
 * At r = 0 this vanishes (singularity removed); at r -> inf it approaches M.
 * The crossover radius where the LQG correction is O(1) is r ~ (2 l^2 M)^{1/3}.
 *
 * @param r Boyer-Lindquist radial coordinate [geometric units].
 * @param M Geometric mass [geometric units].
 * @param l LQG polymer length [geometric units]; l = 0 recovers Kerr.
 * @return M_eff(r) [geometric units].
 */
[[nodiscard]] constexpr double lqgEffectiveMass(double r, double M, double l) noexcept {
    const double r3    = r * r * r;
    const double denom = r3 + 2.0 * l * l * M;
    return M * r3 / denom;
}

/**
 * @brief Fractional LQG correction: (M - M_eff(r)) / M = 2 l^2 M / (r^3 + 2 l^2 M).
 *
 * Provides a direct measure of how much the metric deviates from Kerr at
 * radius r.  Peaks at r = 0 (correction = 1) and falls off as (l/r)^2.
 *
 * @param r Boyer-Lindquist r [geometric units].
 * @param M Geometric mass [geometric units].
 * @param l LQG polymer length [geometric units].
 * @return Fractional correction epsilon in [0, 1].
 */
[[nodiscard]] constexpr double lqgCorrection(double r, double M, double l) noexcept {
    const double r3    = r * r * r;
    const double denom = r3 + 2.0 * l * l * M;
    return 2.0 * l * l * M / denom;
}

// ============================================================================
// LQG-modified Delta
// ============================================================================

/**
 * @brief LQG-modified radial discriminant: Delta_LQG = r^2 - 2 M_eff(r) r + a^2.
 *
 * WHY Delta matters: it encodes the horizon structure.  In the LQG metric
 * Delta_LQG may have 0, 1, or 2 positive roots depending on (M, a, l), just
 * as in Kerr.  For small l the outer horizon shifts inward; for large l
 * (super-extremal regime) there may be no horizon (regular particle).
 *
 * @param r Boyer-Lindquist r [geometric units].
 * @param M Geometric mass [geometric units].
 * @param a Spin parameter J/M [geometric units].
 * @param l LQG polymer length [geometric units].
 * @return Delta_LQG [length^2].
 */
[[nodiscard]] inline double lqgDelta(double r, double M, double a, double l) noexcept {
    const double mEff = lqgEffectiveMass(r, M, l);
    return r * r - 2.0 * mEff * r + a * a;
}

// ============================================================================
// Metric components (BL coordinates)
// ============================================================================

/**
 * @brief Kerr-LQG Sigma: r^2 + a^2 cos^2(theta).
 *
 * Sigma is not affected by the LQG regularisation -- the correction enters
 * only through M_eff(r) inside Delta.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param theta Polar angle [rad].
 * @return Sigma [length^2].
 */
[[nodiscard]] inline double lqgSigma(double r, double a, double theta) noexcept {
    const double c = std::cos(theta);
    return r * r + a * a * c * c;
}

/**
 * @brief A function: (r^2 + a^2)^2 - a^2 Delta_LQG sin^2(theta).
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param l     LQG polymer length [geometric units].
 * @return A [length^4].
 */
[[nodiscard]] inline double lqgA(double r, double theta,
                                 double M, double a, double l) noexcept {
    const double r2a2  = r * r + a * a;
    const double s     = std::sin(theta);
    const double Delta = lqgDelta(r, M, a, l);
    return r2a2 * r2a2 - a * a * Delta * s * s;
}

/**
 * @brief g_tt = -(Delta_LQG - a^2 sin^2 theta) / Sigma.
 *
 * The ergosphere is where g_tt = 0, which occurs at Delta_LQG = a^2 sin^2(theta).
 * For l > 0 the ergosphere shifts relative to Kerr.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param l     LQG polymer length [geometric units].
 * @return g_tt.
 */
[[nodiscard]] inline double lqgGtt(double r, double theta,
                                   double M, double a, double l) noexcept {
    const double Sigma = lqgSigma(r, a, theta);
    const double Delta = lqgDelta(r, M, a, l);
    const double s     = std::sin(theta);
    return -(Delta - a * a * s * s) / Sigma;
}

/**
 * @brief g_rr = Sigma / Delta_LQG.
 *
 * Returns +inf at the horizons (coordinate singularity in BL).
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param l     LQG polymer length [geometric units].
 * @return g_rr.
 */
[[nodiscard]] inline double lqgGrr(double r, double theta,
                                   double M, double a, double l) noexcept {
    const double Delta = lqgDelta(r, M, a, l);
    if (std::abs(Delta) < 1.0e-30) return std::numeric_limits<double>::infinity();
    return lqgSigma(r, a, theta) / Delta;
}

/**
 * @brief g_theta_theta = Sigma (unchanged from Kerr).
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param theta Polar angle [rad].
 * @return g_thth [length^2].
 */
[[nodiscard]] inline double lqgGthth(double r, double a, double theta) noexcept {
    return lqgSigma(r, a, theta);
}

/**
 * @brief g_phi_phi = A sin^2(theta) / Sigma.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param l     LQG polymer length [geometric units].
 * @return g_phph [length^2].
 */
[[nodiscard]] inline double lqgGphph(double r, double theta,
                                     double M, double a, double l) noexcept {
    const double Sigma = lqgSigma(r, a, theta);
    const double A     = lqgA(r, theta, M, a, l);
    const double s     = std::sin(theta);
    return A * s * s / Sigma;
}

/**
 * @brief g_t_phi = -2 M_eff(r) r a sin^2(theta) / Sigma.
 *
 * WHY M_eff here: the frame-dragging cross term in the Kerr family is
 * -2 M r a sin^2 / Sigma.  In the LQG extension the classical mass M is
 * replaced by M_eff(r) consistently, preserving the structure.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param l     LQG polymer length [geometric units].
 * @return g_tph [length^2].
 */
[[nodiscard]] inline double lqgGtph(double r, double theta,
                                    double M, double a, double l) noexcept {
    const double Sigma = lqgSigma(r, a, theta);
    const double mEff  = lqgEffectiveMass(r, M, l);
    const double s     = std::sin(theta);
    return -2.0 * mEff * r * a * s * s / Sigma;
}

// ============================================================================
// Horizon radius (bisection helper)
// ============================================================================

/**
 * @brief Approximate outer horizon radius by bisection on Delta_LQG(r) = 0.
 *
 * WHY bisection: Delta_LQG(r) = r^2 - 2 M_eff(r) r + a^2 has no closed form
 * for l != 0.  The bracket [a, 2M + 1] always contains the outer horizon for
 * sub-extremal parameters (verified by Delta(a) = a^2 > 0 and Delta(2M) < 0
 * for small l and a < M).
 *
 * Returns NaN when no horizon is found (e.g. super-extremal l).
 *
 * @param M         Geometric mass [geometric units].
 * @param a         Spin parameter [geometric units].
 * @param l         LQG polymer length [geometric units].
 * @param tolerance Bisection convergence tolerance [geometric units].
 * @return Outer horizon radius, or NaN if not found.
 */
[[nodiscard]] inline double lqgOuterHorizon(double M, double a, double l,
                                            double tolerance = 1.0e-12) noexcept {
    // For l = 0 use the exact Kerr formula.
    if (l == 0.0) {
        const double disc = M * M - a * a;
        if (disc < 0.0) return std::numeric_limits<double>::quiet_NaN();
        return M + std::sqrt(disc);
    }

    // Bracket the outer horizon r_+.
    //
    // Delta_LQG(r) = (r - r_+)(r - r_-) for sub-extremal BH.
    //   r < r_-  : Delta > 0
    //   r_- < r < r_+  : Delta < 0  (between horizons)
    //   r > r_+  : Delta > 0
    //
    // Bisection for the outer horizon: find root where Delta crosses from
    // negative to positive.  Use r_lo = M (always between horizons for
    // sub-extremal parameters) and r_hi = 3*M + a + 1 (always outside).
    const double r_lo = M;
    const double r_hi = 3.0 * M + a + 1.0;

    if (lqgDelta(r_lo, M, a, l) >= 0.0 || lqgDelta(r_hi, M, a, l) <= 0.0) {
        return std::numeric_limits<double>::quiet_NaN();
    }

    double lo = r_lo, hi = r_hi;
    for (int i = 0; i < 128 && (hi - lo) > tolerance; ++i) {
        const double mid = 0.5 * (lo + hi);
        if (lqgDelta(mid, M, a, l) < 0.0)  // still between horizons
            lo = mid;
        else                                // at or outside outer horizon
            hi = mid;
    }
    return 0.5 * (lo + hi);
}

// ============================================================================
// EHT shadow and photon orbit helpers
// ============================================================================

/**
 * @brief Approximate photon sphere radius for LQG-Kerr (equatorial).
 *
 * The equatorial photon sphere is where d^2 r / d lambda^2 = 0 for null
 * geodesics.  For small LQG corrections, the leading shift relative to Kerr is
 * negative (orbit moves inward) proportional to (l/M)^2.  This uses a
 * first-order Newton step from the Kerr value r_ph = 2M(1 + cos(2/3 arccos(-a*)))
 * to obtain a quick estimate; exact solutions require root finding.
 *
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param l     LQG polymer length [geometric units].
 * @return Approximate prograde photon sphere radius [geometric units].
 */
[[nodiscard]] inline double lqgPhotonSphereApprox(double M, double a,
                                                  double l) noexcept {
    // Kerr prograde photon sphere as starting point.
    const double aStar = (M > 0.0) ? a / M : 0.0;
    const double r_ph_kerr = 2.0 * M * (1.0 + std::cos((2.0 / 3.0) * std::acos(-aStar)));

    // First-order LQG correction: d(M_eff)/dl evaluated at r_ph_kerr.
    // DeltaM = M - M_eff(r_ph) = 2 l^2 M / (r^3 + 2 l^2 M)
    const double r3   = r_ph_kerr * r_ph_kerr * r_ph_kerr;
    const double corr = 2.0 * l * l * M / (r3 + 2.0 * l * l * M);
    // Shadow shifts inward by ~ corr * M (rough linear estimate).
    return r_ph_kerr * (1.0 - 0.5 * corr);
}

} // namespace physics

#endif // PHYSICS_LQG_KERR_H
