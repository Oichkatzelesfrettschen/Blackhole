/**
 * @file rte_integrator.h
 * @brief Volumetric radiative transfer equation (RTE) CPU integrator.
 *
 * WHY: Blackhole's ray-traced images currently accumulate emission only at the
 * accretion disk surface.  Volumetric RTE -- integrating the transfer equation
 * dI_nu/ds = j_nu - alpha_nu * I_nu along each geodesic through the magnetised
 * plasma -- is required for:
 *   - Synchrotron self-absorption in compact radio sources
 *   - Optically thick disk emission at sub-mm wavelengths
 *   - GRMHD post-processing (grmonty-style Monte Carlo or ray-marching)
 *   - EHT image simulation with correct specific-intensity units
 *
 * WHAT: This header provides:
 *   1. RteState  -- specific intensity + optical depth + path-length accumulators.
 *   2. RteSample -- per-step emission/absorption/path-length sample.
 *   3. rteStep() -- exact formal solution for a single uniform segment.
 *   4. integrateRtePath() -- full geodesic path integration.
 *   5. Physical coefficient functions:
 *        planckFunction()             -- B_nu(T), blackbody source function
 *        synchrotronThermalEmissivity()  -- Mahadevan (1996) thermal synchrotron j_nu
 *        synchrotronThermalAbsorption()  -- Kirchhoff: alpha_nu = j_nu / B_nu
 *        bremsstrahlungEmissivity()      -- free-free j_nu (Rybicki-Lightman Eq. 5.14)
 *        bremsstrahlungAbsorption()      -- free-free alpha_nu via Kirchhoff
 *   6. GR helpers:
 *        grTransformIntensity() -- I_obs = g^3 * I_emit (Liouville invariant)
 *        grTransformFrequency() -- nu_obs = g * nu_emit
 *
 * SCOPE: CPU reference path only (C++23, float64, Boost Bessel when available).
 * The CUDA path (D3) will port rteStep() to device_physics.cuh.
 *
 * CONVENTIONS:
 *   - CGS units throughout: erg, cm, s, Hz, sr.
 *   - Specific intensity I_nu [erg / (cm^2 s Hz sr)].
 *   - Emission coefficient j_nu [erg / (cm^3 s Hz sr)] (isotropic).
 *   - Absorption coefficient alpha_nu [cm^-1].
 *   - Source function S_nu = j_nu / alpha_nu [same units as I_nu].
 *   - Optical depth tau = integral alpha_nu ds (dimensionless).
 *   - Dimensionless electron temperature Theta_e = k_B T_e / (m_e c^2).
 *
 * FORMAL SOLUTION (exact for uniform j_nu and alpha_nu over step ds):
 *
 *   I_nu(s+ds) = I_nu(s) * exp(-tau) + S_nu * (1 - exp(-tau))
 *
 * where tau = alpha_nu * ds. For tau -> 0 (optically thin):
 *
 *   I_nu(s+ds) = I_nu(s) + j_nu * ds   (first-order Taylor)
 *
 * The implementation switches between these regimes at tau = 1e-4 to avoid
 * catastrophic cancellation in (1 - exp(-tau)) for small tau.
 *
 * References:
 *   - Rybicki & Lightman (1979), Radiative Processes in Astrophysics, Wiley.
 *     Ch. 1 (transfer equation), Ch. 5 (bremsstrahlung), Ch. 6 (synchrotron).
 *   - Mahadevan (1996), ApJ 457, 805. Thermal synchrotron approximation.
 *   - Leung, Gammie & Noble (2011), ApJ 737, 21. grmonty thermal synchrotron.
 *   - Mihalas & Mihalas (1984), Foundations of Radiation Hydrodynamics. GR Liouville.
 *   - Moscibrodzka & Falcke (2013), A&A 559, L3. EHT absorption/emission.
 */

#ifndef PHYSICS_RTE_INTEGRATOR_H
#define PHYSICS_RTE_INTEGRATOR_H

#include "constants.h"
#include "synchrotron.h"

#include <cmath>
#include <cstddef>
#include <numbers>
#include <vector>

#ifdef __has_include
#  if __has_include(<boost/math/special_functions/bessel.hpp>)
#    include <boost/math/special_functions/bessel.hpp>
// NOLINTBEGIN(cppcoreguidelines-macro-usage)
#    define PHYSICS_RTE_HAS_BOOST_BESSEL 1
// NOLINTEND(cppcoreguidelines-macro-usage)
#  endif
#endif

namespace physics {

// ============================================================================
// Core RTE types
// ============================================================================

/**
 * @brief Specific intensity and accumulated transport quantities for one ray.
 *
 * Accumulates along the geodesic as rteStep() is called for each segment.
 * Initialise with iNu = background intensity (e.g., CMB or zero), tau = 0.
 */
struct RteState {
    double iNu = 0.0;   ///< Specific intensity [erg / (cm^2 s Hz sr)]
    double tau  = 0.0;  ///< Accumulated optical depth (dimensionless)
    double sCm  = 0.0;  ///< Accumulated proper path length [cm]
};

/**
 * @brief Emission/absorption sample for a single path segment.
 *
 * Each sample represents a uniform segment of length dsCm over which
 * jNu and alphaNu are assumed constant (piecewise-constant approximation).
 * Finer step sizes converge to the exact integral.
 */
struct RteSample {
    double jNu    = 0.0;  ///< Emission coefficient [erg / (cm^3 s Hz sr)]
    double alphaNu = 0.0; ///< Absorption coefficient [cm^-1]
    double dsCm   = 0.0;  ///< Segment proper path length [cm]
};

// ============================================================================
// Core integrator: formal solution
// ============================================================================

/**
 * @brief Advance RTE state by one uniform segment (exact formal solution).
 *
 * WHY: The formal solution
 *
 *   I(s+ds) = I(s) * exp(-tau) + S_nu * (1 - exp(-tau))
 *
 * is exact when j_nu and alpha_nu are constant over ds.  It is unconditionally
 * stable for any tau >= 0 and automatically handles both the optically thin
 * (tau << 1) and thick (tau >> 1) limits.
 *
 * NUMERICS: For tau < 1e-4 we use the Taylor expansion
 *   (1 - exp(-tau)) = tau - tau^2/2 + ...  ~ tau * (1 - tau/2)
 * to avoid catastrophic cancellation in float64.  The switch-over threshold
 * 1e-4 gives < 1e-8 relative error compared to the exact form.
 *
 * @param state   Current RTE state (modified in place via return value)
 * @param jNu     Emission coefficient [erg / (cm^3 s Hz sr)]
 * @param alphaNu Absorption coefficient [cm^-1]
 * @param dsCm    Segment proper path length [cm]
 * @return Updated RteState with advanced I_nu, tau, sCm.
 */
[[nodiscard]] inline RteState rteStep(RteState state,
                                       double jNu,
                                       double alphaNu,
                                       double dsCm) noexcept {
    if (dsCm <= 0.0) { return state; }

    const double tau = (alphaNu > 0.0) ? alphaNu * dsCm : 0.0;

    // Source function S_nu = j_nu / alpha_nu; for pure emission (alpha=0): S=j*ds directly
    double deltaI = 0.0;
    if (tau < 1.0e-4) {
        // Optically thin: (1 - exp(-tau)) ~ tau - tau^2/2 -> exact at second order
        const double oneMexpTau = tau * (1.0 - 0.5 * tau);
        if (alphaNu > 0.0) {
            deltaI = (jNu / alphaNu) * oneMexpTau - state.iNu * tau;
        } else {
            deltaI = jNu * dsCm;  // pure emission, no absorption
        }
    } else {
        const double expNegTau = std::exp(-tau);
        if (alphaNu > 0.0) {
            deltaI = (jNu / alphaNu) * (1.0 - expNegTau) - state.iNu * (1.0 - expNegTau);
            // Equivalently: I_new = I_old * expNegTau + S_nu * (1 - expNegTau)
            // Rewritten as delta to avoid precision loss on the I_old term for large tau:
            state.iNu = state.iNu * expNegTau + (jNu / alphaNu) * (1.0 - expNegTau);
            state.tau  += tau;
            state.sCm  += dsCm;
            return state;
        }
        // alpha=0, pure emission (tau=0 above but tau calculated as alphaNu*dsCm=0)
        deltaI = jNu * dsCm;
    }

    state.iNu  += deltaI;
    state.tau  += tau;
    state.sCm  += dsCm;
    return state;
}

/**
 * @brief Integrate the RTE along a full path (sequence of uniform segments).
 *
 * Applies rteStep() sequentially for each sample in the path.  The samples
 * should be ordered from the far end of the path toward the observer (the
 * standard ray-marching convention where intensity accumulates "backward"
 * along the photon geodesic).
 *
 * @param path    Vector of RteSample segments, ordered far-to-near.
 * @param initial Initial RteState (background intensity); default is zero.
 * @return RteState at the end of the path (closest to observer).
 */
[[nodiscard]] inline RteState integrateRtePath(const std::vector<RteSample>& path,
                                                RteState initial = {}) noexcept {
    RteState state = initial;
    for (const auto& sample : path) {
        state = rteStep(state, sample.jNu, sample.alphaNu, sample.dsCm);
    }
    return state;
}

// ============================================================================
// Blackbody / Planck source function
// ============================================================================

/**
 * @brief Planck (blackbody) function B_nu(T).
 *
 * B_nu(T) = (2 h nu^3 / c^2) / (exp(h nu / kT) - 1)
 *
 * WHY: B_nu is the source function for matter in local thermodynamic
 * equilibrium (LTE).  It also appears in Kirchhoff's law for thermal
 * emission/absorption: alpha_nu = j_nu / B_nu.
 *
 * LIMITS:
 *   - Rayleigh-Jeans (h nu << k T): B_nu ~ 2 nu^2 k T / c^2
 *   - Wien (h nu >> k T):            B_nu ~ (2 h nu^3 / c^2) * exp(-h nu / kT)
 *
 * Returns 0.0 for non-positive inputs.
 *
 * @param nu    Frequency [Hz]
 * @param tempK Blackbody temperature [K]
 * @return B_nu [erg / (cm^2 s Hz sr)]
 */
[[nodiscard]] inline double planckFunction(double nu, double tempK) noexcept {
    if (nu <= 0.0 || tempK <= 0.0) { return 0.0; }
    constexpr double kTwoPiHbar = 2.0 * std::numbers::pi * HBAR;  // h = 2*pi*hbar
    const double h   = kTwoPiHbar;
    const double x   = (h * nu) / (K_B * tempK);
    // Avoid overflow: exp(x) - 1 -> exp(x) for x >> 1
    const double denom = (x > 500.0) ? std::exp(x) : std::expm1(x);
    if (denom <= 0.0) { return 0.0; }
    return (2.0 * h * nu * nu * nu / (C * C)) / denom;
}

/**
 * @brief Rayleigh-Jeans approximation to B_nu.
 *
 * B_nu^{RJ} = 2 nu^2 k_B T / c^2
 *
 * Valid when h nu << k T (radio/sub-mm for cold sources or low frequencies).
 *
 * @param nu    Frequency [Hz]
 * @param tempK Temperature [K]
 * @return B_nu^{RJ} [erg / (cm^2 s Hz sr)]
 */
[[nodiscard]] inline double rayleighJeans(double nu, double tempK) noexcept {
    if (nu <= 0.0 || tempK <= 0.0) { return 0.0; }
    return 2.0 * nu * nu * K_B * tempK / (C * C);
}

// ============================================================================
// Thermal synchrotron (Mahadevan 1996 / Leung 2011)
// ============================================================================

/**
 * @brief Thermal synchrotron emissivity (Mahadevan 1996 Eq. A2).
 *
 * WHY: In hot accretion flows (ADAF/RIAF) around black holes the electron
 * distribution is well approximated by a relativistic Maxwell-Juttner
 * distribution at temperature T_e.  The EHT imaging codes (grmonty, IPOLE,
 * BHOSS) use the Mahadevan (1996) / Leung (2011) thermal synchrotron formula
 * as the primary source of mm-wave emission.
 *
 * WHAT: The emission coefficient (isotropically pitch-angle averaged) is:
 *
 *   j_nu = [sqrt(3) * e^3 * n_e * nu_B / (m_e * c^2 * K_2(1/Theta_e))]
 *          * Theta_e^2 * I_M(x_M)
 *
 * where:
 *   - nu_B = e*B / (2*pi*m_e*c) = cyclotron frequency
 *   - Theta_e = k_B T_e / (m_e c^2) = dimensionless electron temperature
 *   - nu_s = (3/2) nu_B Theta_e^2 = characteristic synchrotron frequency
 *   - x_M = nu / nu_s = dimensionless frequency
 *   - I_M(x) = 4.0505/x^{1/6} * (1 + 0.40/x^{1/4} + 0.5316/x^{1/2})
 *              * exp(-1.8899 * x^{1/3})     [Mahadevan 1996, Eq. A2]
 *   - K_2(z) = modified Bessel function of second kind, order 2
 *
 * WHY the K_2 factor: it arises from the partition function of the
 * Maxwell-Juttner distribution.  For Theta_e >> 1: K_2(1/Theta_e) ~ 2 Theta_e^2.
 *
 * FALLBACK: When Boost is unavailable, uses the large-Theta_e approximation
 * K_2(1/Theta_e) ~ 2*Theta_e^2, valid to < 1% for Theta_e > 3.
 *
 * References:
 *   - Mahadevan (1996), ApJ 457, 805, Eqs. 20-25 and A2.
 *   - Leung, Gammie & Noble (2011), ApJ 737, 21, Appendix B.
 *
 * @param nu      Frequency [Hz]
 * @param bField  Magnetic field strength [Gauss]
 * @param nE      Electron number density [cm^-3]
 * @param thetaE  Dimensionless electron temperature k_B T_e / (m_e c^2) > 0
 * @return j_nu [erg / (cm^3 s Hz sr)]
 */
[[nodiscard]] inline double synchrotronThermalEmissivity(double nu,
                                                          double bField,
                                                          double nE,
                                                          double thetaE) noexcept {
    if (nu <= 0.0 || bField <= 0.0 || nE <= 0.0 || thetaE <= 0.0) { return 0.0; }

    const double nuB  = gyrofrequency(bField);         // e*B / (2*pi*m_e*c) [Hz]
    const double nuS  = 1.5 * nuB * thetaE * thetaE;  // characteristic frequency [Hz]
    if (nuS <= 0.0) { return 0.0; }

    const double xM   = nu / nuS;
    if (xM <= 0.0) { return 0.0; }

    // Mahadevan (1996) Eq. A2 spectral function I_M(x)
    const double xm16  = std::pow(xM, -1.0 / 6.0);  // x^{-1/6}
    const double xm14  = std::pow(xM, -1.0 / 4.0);  // x^{-1/4}
    const double xm12  = std::pow(xM, -1.0 / 2.0);  // x^{-1/2}
    const double im    = 4.0505 * xm16 * (1.0 + 0.40 * xm14 + 0.5316 * xm12)
                         * std::exp(-1.8899 * std::pow(xM, 1.0 / 3.0));

    // Modified Bessel K_2(1/Theta_e): partition function of Maxwell-Juttner distribution
    double k2 = 0.0;
#ifdef PHYSICS_RTE_HAS_BOOST_BESSEL
    k2 = boost::math::cyl_bessel_k(2.0, 1.0 / thetaE);
#else
    // Large-Theta_e asymptote: K_2(1/Theta_e) ~ 2 Theta_e^2 + ...  (valid to ~1% for Theta_e > 3)
    k2 = 2.0 * thetaE * thetaE;
#endif
    if (k2 <= 0.0) { return 0.0; }

    // Prefactor: sqrt(3) * e^3 * n_e * nu_B / (m_e * c^2)
    // Using CGS constants from synchrotron.h (E_CHARGE, M_ELECTRON, C, PI):
    const double prefactor = std::sqrt(3.0) * E_CHARGE * E_CHARGE * E_CHARGE
                             * nE * nuB
                             / (M_ELECTRON * C * C);

    return (prefactor / k2) * thetaE * thetaE * im;
}

/**
 * @brief Thermal synchrotron absorption coefficient via Kirchhoff's law.
 *
 * For a plasma in local thermodynamic equilibrium at electron temperature T_e,
 * the absorption coefficient satisfies Kirchhoff's law exactly:
 *
 *   alpha_nu = j_nu / B_nu(T_e)
 *
 * WHY: In detailed balance, stimulated emission exactly equals absorption,
 * making j/alpha = B_nu(T_e) for a thermal distribution.  This relation holds
 * for the Maxwell-Juttner distribution used in the Mahadevan emissivity formula.
 *
 * @param nu      Frequency [Hz]
 * @param bField  Magnetic field strength [Gauss]
 * @param nE      Electron density [cm^-3]
 * @param thetaE  Dimensionless electron temperature k_B T_e / (m_e c^2)
 * @return alpha_nu [cm^-1]
 */
[[nodiscard]] inline double synchrotronThermalAbsorption(double nu,
                                                          double bField,
                                                          double nE,
                                                          double thetaE) noexcept {
    if (thetaE <= 0.0 || nu <= 0.0) { return 0.0; }
    const double tempK = thetaE * M_ELECTRON * C * C / K_B;
    const double bNu   = planckFunction(nu, tempK);
    if (bNu <= 0.0) { return 0.0; }
    return synchrotronThermalEmissivity(nu, bField, nE, thetaE) / bNu;
}

// ============================================================================
// Free-free (bremsstrahlung) emission and absorption
// ============================================================================

/**
 * @brief Free-free (bremsstrahlung) emission coefficient.
 *
 * WHY: Thermal bremsstrahlung is the dominant emission mechanism in hot
 * optically thin plasmas (T ~ 10^8 - 10^11 K) and provides the continuum
 * background under synchrotron in hard X-ray coronae.
 *
 * WHAT: R&L (1979) Eq. 5.14, CGS Gaussian units:
 *
 *   j_nu^{ff} = (Z^2 n_e n_i) / T^{1/2} * 6.8e-38 * g_ff * exp(-h nu / kT)
 *
 * where g_ff is the frequency-averaged Gaunt factor.  For mm/radio waves
 * (h nu << kT) the exponential is ~ 1.  We use the classical approximation
 * g_ff ~ sqrt(3)/pi * ln(4.7e10 * kT / nu) for h nu << kT, clipped to [1, 10].
 *
 * @param nu      Frequency [Hz]
 * @param nE      Electron number density [cm^-3]
 * @param nI      Ion number density [cm^-3]
 * @param tempK   Plasma temperature [K]
 * @param z       Mean ion charge (default 1 for hydrogen)
 * @return j_nu^ff [erg / (cm^3 s Hz sr)]
 */
[[nodiscard]] inline double bremsstrahlungEmissivity(double nu,
                                                      double nE,
                                                      double nI,
                                                      double tempK,
                                                      double z = 1.0) noexcept {
    if (nu <= 0.0 || nE <= 0.0 || nI <= 0.0 || tempK <= 0.0) { return 0.0; }

    // Gaunt factor (classical approximation, valid for h*nu << kT)
    constexpr double kGauntPrefactor = 4.7e10;  // [K/Hz], empirical constant
    const double kToverH = K_B * tempK / (2.0 * std::numbers::pi * HBAR);  // kT/h [Hz]
    const double logArg  = kToverH / nu;
    double gff = 1.0;
    if (logArg > 1.0) {
        gff = std::clamp(std::sqrt(3.0) / std::numbers::pi * std::log(kGauntPrefactor * kToverH / nu),
                         1.0, 10.0);
    }

    const double expFactor = std::exp(-2.0 * std::numbers::pi * HBAR * nu / (K_B * tempK));
    // R&L (1979) Eq. 5.14 prefactor in CGS [erg cm^3 s^{-1} Hz^{-1} K^{1/2}]
    constexpr double kRLPrefactor = 6.8e-38;

    return (kRLPrefactor * z * z * nE * nI * gff * expFactor) / std::sqrt(tempK);
}

/**
 * @brief Free-free (bremsstrahlung) absorption coefficient.
 *
 * Via Kirchhoff's law: alpha_nu^{ff} = j_nu^{ff} / B_nu(T).
 * In the Rayleigh-Jeans limit (h nu << kT): alpha_nu^{ff} ~ nu^{-2} T^{-3/2}.
 *
 * @param nu      Frequency [Hz]
 * @param nE      Electron density [cm^-3]
 * @param nI      Ion density [cm^-3]
 * @param tempK   Temperature [K]
 * @param z       Mean ion charge
 * @return alpha_nu^ff [cm^-1]
 */
[[nodiscard]] inline double bremsstrahlungAbsorption(double nu,
                                                      double nE,
                                                      double nI,
                                                      double tempK,
                                                      double z = 1.0) noexcept {
    const double bNu = planckFunction(nu, tempK);
    if (bNu <= 0.0) { return 0.0; }
    return bremsstrahlungEmissivity(nu, nE, nI, tempK, z) / bNu;
}

// ============================================================================
// GR radiative transfer helpers
// ============================================================================

/**
 * @brief Transform specific intensity from plasma rest frame to observer frame.
 *
 * WHY: Liouville's theorem in curved spacetime states that the phase-space
 * distribution function f is a Lorentz scalar along geodesics.  The specific
 * intensity in frequency satisfies:
 *
 *   I_nu / nu^3 = const  along each ray
 *
 * Therefore an intensity I_emit at emitted frequency nu_emit transforms to
 * the observed intensity at nu_obs as:
 *
 *   I_obs = (nu_obs / nu_emit)^3 * I_emit = g^3 * I_emit
 *
 * where g = nu_obs / nu_emit is the photon redshift factor (gravitational +
 * Doppler, < 1 for redshift, > 1 for blueshift).
 *
 * WHY applies to ray marching: when accumulating j_nu and alpha_nu computed
 * in the plasma rest frame, the final intensity must be multiplied by g^3
 * to convert to the observer's measurement.  Alternatively, j_nu can be
 * transformed to the observer frame first: j_nu^obs = g^2 * j_nu^emit,
 * alpha_nu^obs = g^{-1} * alpha_nu^emit, and I_obs results directly.
 *
 * Reference: Mihalas & Mihalas (1984) Sec. 4-3; Younsi et al. (2012), A&A 545, A13.
 *
 * @param iEmit  Specific intensity in plasma rest frame [erg/(cm^2 s Hz sr)]
 * @param g      Redshift factor nu_obs / nu_emit (> 0)
 * @return Observed specific intensity [erg/(cm^2 s Hz sr)]
 */
[[nodiscard]] inline double grTransformIntensity(double iEmit, double g) noexcept {
    if (g <= 0.0) { return 0.0; }
    return iEmit * g * g * g;
}

/**
 * @brief Transform emission coefficient from plasma rest frame to observer frame.
 *
 * Under the Liouville invariant I_nu/nu^3 = const:
 *   j_nu^obs = g^2 * j_nu^emit
 *
 * (one power of g from nu^3 -> g * nu^3, two powers from the 1/nu^3 factor;
 * net result for emission = g^2).
 *
 * @param jEmit  Emission coefficient in plasma frame [erg/(cm^3 s Hz sr)]
 * @param g      Redshift factor nu_obs / nu_emit
 * @return j_nu in observer frame [erg/(cm^3 s Hz sr)]
 */
[[nodiscard]] inline double grTransformEmission(double jEmit, double g) noexcept {
    if (g <= 0.0) { return 0.0; }
    return jEmit * g * g;
}

/**
 * @brief Transform absorption coefficient from plasma rest frame to observer frame.
 *
 * Under Liouville:
 *   alpha_nu^obs = alpha_nu^emit / g
 *
 * @param alphaEmit  Absorption in plasma frame [cm^-1]
 * @param g          Redshift factor nu_obs / nu_emit
 * @return alpha_nu in observer frame [cm^-1]
 */
[[nodiscard]] inline double grTransformAbsorption(double alphaEmit, double g) noexcept {
    if (g <= 0.0) { return 0.0; }
    return alphaEmit / g;
}

/**
 * @brief Observed frequency given emitted frequency and redshift factor.
 *
 * nu_obs = g * nu_emit where g = sqrt(-g_tt - 2 g_tphi Omega - g_phiphi Omega^2)
 * is the lapse/redshift function including gravitational and Doppler terms.
 *
 * @param nuEmit  Emitted frequency in plasma rest frame [Hz]
 * @param g       Redshift factor nu_obs / nu_emit
 * @return Observed frequency [Hz]
 */
[[nodiscard]] inline double grTransformFrequency(double nuEmit, double g) noexcept {
    return nuEmit * g;
}

// ============================================================================
// Convenience: RTE with inline GR transforms
// ============================================================================

/**
 * @brief Advance RTE state with GR-transformed coefficients.
 *
 * Applies the full Liouville transform of emission and absorption from the
 * plasma rest frame to the observer frame before calling rteStep().
 * This is the correct form for integrating along a geodesic where j and alpha
 * are computed in the comoving plasma frame.
 *
 * @param state     Current RTE state in observer frame
 * @param jEmit     Emission in plasma rest frame [erg/(cm^3 s Hz sr)]
 * @param alphaEmit Absorption in plasma rest frame [cm^-1]
 * @param dsCm      Coordinate proper path length [cm]
 * @param g         Redshift factor nu_obs / nu_emit
 * @return Updated RteState
 */
[[nodiscard]] inline RteState rteStepGR(RteState state,
                                         double jEmit,
                                         double alphaEmit,
                                         double dsCm,
                                         double g) noexcept {
    return rteStep(state,
                   grTransformEmission(jEmit, g),
                   grTransformAbsorption(alphaEmit, g),
                   dsCm);
}

} // namespace physics

#endif // PHYSICS_RTE_INTEGRATOR_H
