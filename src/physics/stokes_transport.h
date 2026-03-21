/**
 * @file stokes_transport.h
 * @brief Polarized radiative transfer: Stokes I,Q,U,V transport with Mueller
 *        matrix propagation (Faraday rotation + absorption).
 *
 * WHY: Scalar intensity transport (rte_integrator.h, D1) cannot model the
 * polarization that EHT directly measures.  The 2021 M87* polarized image
 * (EHT Paper VII, 2021) and the Sgr A* polarization (Paper VIII, 2022) are
 * the primary validation targets for GR ray tracing codes.  Polarization
 * constrains the magnetic field geometry, electron temperature, and accretion
 * flow structure in ways that total intensity cannot.
 *
 * WHAT: This header provides:
 *   1. StokesVector: (I, Q, U, V) with polarimetry helper methods.
 *   2. StokesEmission: (j_I, j_Q, j_U, j_V) emission vector.
 *   3. FaradayPropagation: propagation coefficients (alpha_I, rho_V, rho_Q,
 *      alpha_Q, alpha_V) entering the Mueller K matrix.
 *   4. stokesStep(): EXACT formal solution for the simplified K matrix
 *      (total absorption alpha_I + Faraday rotation rho_V).
 *   5. stokesStepFull(): 4th-order Runge-Kutta step for the complete K matrix
 *      including dichroism and Faraday conversion (general magnetized plasma).
 *   6. integrateStokesPath(): full path integration over FaradayPropagation samples.
 *   7. Physical coefficient functions:
 *        synchrotronPolarizedEmission()   -- j_Q, j_U from B-field geometry
 *        synchrotronLinearPolarFrac()     -- (p+1)/(p+7/3) for power-law e-
 *        thermalSynchLinearPolarFrac()    -- fit for Maxwell-Juttner electrons
 *        faradayRotationCoeff()           -- rho_V [rad/cm] for thermal plasma
 *        faradayConversionCoeff()         -- rho_Q [rad/cm] for thermal plasma
 *   8. Utility: faradayRotateStokes(), stokesPolarizationBound().
 *
 * POLARIZED RTE: dS/ds = J - K * S
 *
 * S = (I, Q, U, V)^T (Stokes vector, I is total intensity).
 * J = (j_I, j_Q, j_U, j_V)^T (emission vector).
 * K is the 4x4 Mueller propagation matrix (Hamaker & Bregman 1996):
 *
 *   K = | alpha_I  alpha_Q  alpha_U  alpha_V  |
 *       | alpha_Q  alpha_I   rho_V   -rho_U   |
 *       | alpha_U  -rho_V   alpha_I   rho_Q   |
 *       | alpha_V   rho_U   -rho_Q   alpha_I  |
 *
 * Physical meaning of each coefficient (all in [rad/cm] or [cm^-1]):
 *   alpha_I:  total absorption coefficient (isotropic; same as rte_integrator.h)
 *   alpha_Q:  linear dichroism (differential absorption of 0 deg vs 90 deg linear)
 *   alpha_U:  linear dichroism (45 deg vs 135 deg)
 *   alpha_V:  circular dichroism (differential absorption of L vs R circular)
 *   rho_V:    Faraday rotation coefficient (rotates Q into U and vice versa)
 *   rho_Q:    Faraday conversion (converts linear Q into circular V)
 *   rho_U:    Faraday conversion (converts linear U into circular V); zero in
 *             aligned coordinate where U direction aligns with B_perp projection
 *
 * SIMPLIFIED K (this header's primary exact solution):
 *   alpha_Q = alpha_U = alpha_V = rho_Q = rho_U = 0, only alpha_I and rho_V.
 *   This decouples (I,V) from (Q,U) and allows an analytic step.
 *   Validity: good approximation when Faraday rotation >> dichroism, which is
 *   typical for EHT frequencies (230 GHz) and Theta_e >> 1.
 *
 * EXACT SOLUTION for simplified K (derivation):
 *   The (I,V) system evolves independently as scalar RTE (see rte_integrator.h).
 *   The (Q,U) system satisfies:
 *     d[Q;U]/ds = [j_Q;j_U] - [alpha_I, rho_V; -rho_V, alpha_I] * [Q;U]
 *   whose propagator is exp(-A*ds) * R(R*ds), an exponential decay times a
 *   rotation by angle phi = rho_V * ds in the Q-U plane.  The particular
 *   solution (emission integral) is computed exactly using:
 *     Ic = integral_0^ds exp(-A*t)*cos(R*t) dt
 *        = [A*(1-E*C) + R*E*S] / (A^2+R^2)      [E=exp(-A*ds), C=cos(R*ds), S=sin(R*ds)]
 *     Is = integral_0^ds exp(-A*t)*sin(R*t) dt
 *        = [R*(1-E*C) - A*E*S] / (A^2+R^2)
 *   giving:
 *     Q_emit = j_Q * Ic - j_U * Is
 *     U_emit = j_Q * Is + j_U * Ic
 *
 * CONVENTIONS:
 *   - EVPA chi = 0.5 * atan2(U,Q): angle of polarization E-vector on sky.
 *   - Circular polarization: V > 0 for right-circular (IAU convention).
 *   - Faraday rotation: Delta_chi = rho_V * ds (positive rho_V rotates
 *     EVPA counter-clockwise as viewed toward observer).
 *   - All frequencies in Hz, path lengths in cm.
 *
 * References:
 *   - Hamaker & Bregman (1996), A&AS 117, 137. Mueller matrix formalism.
 *   - Huang et al. (2009), ApJ 706, 960. GRPOL polarized GRRT.
 *   - Shcherbakov & Huang (2011), MNRAS 410, 1052. Faraday coefficients.
 *   - Moscibrodzka et al. (2017), A&A 559, L3. EHT polarization imaging.
 *   - Dexter (2016), MNRAS 462, 115. grtrans polarized GRRT.
 *   - EHT Collaboration Paper VII (2021), ApJL 910, L13. M87* polarization.
 *   - Landi Degl'Innocenti & Landolfi (2004), Polarization in Spectral Lines.
 */

#ifndef PHYSICS_STOKES_TRANSPORT_H
#define PHYSICS_STOKES_TRANSPORT_H

#include "constants.h"
#include "rte_integrator.h"
#include "synchrotron.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <numbers>
#include <vector>

#ifdef __has_include
#  if __has_include(<boost/math/special_functions/bessel.hpp>)
#    include <boost/math/special_functions/bessel.hpp>
// NOLINTBEGIN(cppcoreguidelines-macro-usage)
#    define PHYSICS_STOKES_HAS_BOOST_BESSEL 1
// NOLINTEND(cppcoreguidelines-macro-usage)
#  endif
#endif

namespace physics {

// ============================================================================
// Stokes vector
// ============================================================================

/**
 * @brief Stokes polarization vector S = (I, Q, U, V).
 *
 * I >= 0 is the total intensity.  Q, U describe linear polarization in
 * two orthogonal orientations; V describes circular polarization.
 * The physical constraint is I^2 >= Q^2 + U^2 + V^2 (not enforced here
 * as intermediate steps may temporarily violate it in noisy Monte Carlo).
 *
 * The EVPA chi = 0.5 * atan2(U, Q) gives the electric vector position
 * angle of the linear polarization.
 */
struct StokesVector {
    double i = 0.0;  ///< Total intensity I
    double q = 0.0;  ///< Linear polarization: 0/90 deg axis
    double u = 0.0;  ///< Linear polarization: 45/135 deg axis
    double v = 0.0;  ///< Circular polarization (V > 0: right-circular)

    /// Linear polarized intensity sqrt(Q^2 + U^2).
    [[nodiscard]] double linPolInt() const noexcept { return std::hypot(q, u); }

    /// Fractional linear polarization sqrt(Q^2+U^2)/I (0 if I=0).
    [[nodiscard]] double linPolFrac() const noexcept {
        return (i > 0.0) ? linPolInt() / i : 0.0;
    }

    /// Fractional circular polarization V/I (0 if I=0).
    [[nodiscard]] double circPolFrac() const noexcept {
        return (i > 0.0) ? v / i : 0.0;
    }

    /// Total fractional polarization sqrt(Q^2+U^2+V^2)/I (0 if I=0).
    [[nodiscard]] double totalPolFrac() const noexcept {
        if (i <= 0.0) { return 0.0; }
        return std::sqrt(q * q + u * u + v * v) / i;
    }

    /// Electric vector position angle [rad] in (-pi/2, pi/2]; 0 if unpolarized.
    [[nodiscard]] double evpa() const noexcept {
        return 0.5 * std::atan2(u, q);
    }

    /// Rotate EVPA by delta_chi [rad] (Faraday rotation rotates Q and U).
    [[nodiscard]] StokesVector rotateEvpa(double deltaChi) const noexcept {
        const double cos2 = std::cos(2.0 * deltaChi);
        const double sin2 = std::sin(2.0 * deltaChi);
        return {i, q * cos2 - u * sin2, q * sin2 + u * cos2, v};
    }

    /// Component-wise addition.
    [[nodiscard]] StokesVector operator+(const StokesVector& o) const noexcept {
        return {i + o.i, q + o.q, u + o.u, v + o.v};
    }

    /// Scale all components by a scalar.
    [[nodiscard]] StokesVector operator*(double s) const noexcept {
        return {i * s, q * s, u * s, v * s};
    }
};

// ============================================================================
// Emission vector
// ============================================================================

/**
 * @brief Polarized emission vector (j_I, j_Q, j_U, j_V).
 *
 * j_I [erg/(cm^3 s Hz sr)] is the total emissivity (as in rte_integrator.h).
 * j_Q, j_U give the linear polarization of emitted photons.
 * For synchrotron: j_Q and j_U are perpendicular to the projected B field,
 * and |sqrt(j_Q^2 + j_U^2)| / j_I = Pi_max (intrinsic polarization fraction).
 */
struct StokesEmission {
    double jI = 0.0;  ///< Total intensity emission [erg/(cm^3 s Hz sr)]
    double jQ = 0.0;  ///< Q emission
    double jU = 0.0;  ///< U emission
    double jV = 0.0;  ///< V emission (small for thermal synchrotron)

    /// Fractional linear polarization of emission sqrt(jQ^2+jU^2)/jI.
    [[nodiscard]] double linPolFrac() const noexcept {
        return (jI > 0.0) ? std::hypot(jQ, jU) / jI : 0.0;
    }
};

// ============================================================================
// Propagation coefficients (Mueller K matrix entries)
// ============================================================================

/**
 * @brief Mueller K matrix coefficients for the polarized RTE propagation.
 *
 * These are the six independent entries of the symmetric-about-diagonal
 * propagation matrix K (Hamaker & Bregman 1996):
 *
 *   alpha_I:  total absorption [cm^-1]
 *   alpha_Q:  linear dichroism [cm^-1] (differential absorption)
 *   alpha_V:  circular dichroism [cm^-1]
 *   rho_V:    Faraday rotation [rad/cm]
 *   rho_Q:    Faraday conversion [rad/cm]
 *
 * rho_U is zero when the coordinate frame is aligned with the projected
 * magnetic field direction (the standard choice in GRRT codes).
 * alpha_U = 0 in the same aligned frame.
 */
struct FaradayPropagation {
    double alphaI = 0.0;  ///< Total absorption [cm^-1]
    double alphaQ = 0.0;  ///< Linear dichroism [cm^-1]
    double alphaV = 0.0;  ///< Circular dichroism [cm^-1]
    double rhoV   = 0.0;  ///< Faraday rotation coefficient [rad/cm]
    double rhoQ   = 0.0;  ///< Faraday conversion coefficient [rad/cm]
    double dsCm   = 0.0;  ///< Segment path length [cm]
};

// ============================================================================
// Exact formal solution: simplified K (alpha_I + rho_V only)
// ============================================================================

/**
 * @brief Exact formal solution of the polarized RTE for one segment.
 *
 * Solves dS/ds = J - K_simp * S exactly over a segment of length dsCm,
 * where K_simp has only alpha_I (total absorption) and rho_V (Faraday rotation):
 *
 *   K_simp = diag(alpha_I) + | 0   0    0    0  |
 *                             | 0   0   rho_V 0  |
 *                             | 0 -rho_V 0   0  |
 *                             | 0   0    0    0  |
 *
 * This decouples (I,V) as independent scalar channels and couples (Q,U)
 * via Faraday rotation while they are absorbed.  The exact analytic step
 * for (Q,U) uses the integrals derived in the file header.
 *
 * For the full K matrix (with dichroism and Faraday conversion), use
 * stokesStepFull() which applies 4th-order Runge-Kutta.
 *
 * @param s     Current Stokes state
 * @param em    Emission coefficients (jI, jQ, jU, jV)
 * @param alphaI Total absorption [cm^-1]
 * @param rhoV   Faraday rotation [rad/cm]
 * @param dsCm   Segment path length [cm]
 * @return Updated Stokes state
 */
[[nodiscard]] inline StokesVector stokesStep(const StokesVector& s,
                                              const StokesEmission& em,
                                              double alphaI,
                                              double rhoV,
                                              double dsCm) noexcept {
    if (dsCm <= 0.0) { return s; }

    const double A = (alphaI > 0.0) ? alphaI : 0.0;
    const double R = rhoV;  // Faraday rotation rate [rad/cm]
    const double L = dsCm;

    const double tauL = A * L;
    const double E    = (tauL < 700.0) ? std::exp(-tauL) : 0.0;  // exp(-alpha*ds)
    const double phi  = R * L;                                      // Faraday rotation angle [rad]
    const double Cphi = std::cos(phi);
    const double Sphi = std::sin(phi);

    // ---------------------------------------------------------------------------
    // I channel: standard scalar RTE (rte_integrator.h rteStep equivalent)
    // ---------------------------------------------------------------------------
    double iNew = 0.0;
    if (tauL < 1.0e-4) {
        iNew = s.i + em.jI * L;  // optically thin Taylor
    } else {
        iNew = s.i * E + (em.jI / A) * (1.0 - E);
    }

    // ---------------------------------------------------------------------------
    // V channel: scalar RTE (decoupled from Q,U in simplified K)
    // ---------------------------------------------------------------------------
    double vNew = 0.0;
    if (tauL < 1.0e-4) {
        vNew = s.v + em.jV * L;
    } else {
        vNew = s.v * E + (em.jV / A) * (1.0 - E);
    }

    // ---------------------------------------------------------------------------
    // (Q,U) channel: absorption + Faraday rotation
    // d[Q;U]/ds = [jQ;jU] - [A, R; -R, A] * [Q;U]
    //
    // Homogeneous solution (initial conditions):
    //   Q_hom = E * (Q_0 * cos(phi) - U_0 * sin(phi))
    //   U_hom = E * (Q_0 * sin(phi) + U_0 * cos(phi))
    //
    // Particular solution (emission integral Ic, Is defined in file header):
    //   Ic = [A*(1-E*C) + R*E*S] / D
    //   Is = [R*(1-E*C) - A*E*S] / D
    //   where D = A^2 + R^2, C=cos(phi), S=sin(phi)
    //
    //   Q_emit = jQ * Ic - jU * Is
    //   U_emit = jQ * Is + jU * Ic
    // ---------------------------------------------------------------------------
    const double qHom = E * (s.q * Cphi - s.u * Sphi);
    const double uHom = E * (s.q * Sphi + s.u * Cphi);

    double qNew = 0.0;
    double uNew = 0.0;

    const double D = A * A + R * R;
    if (D < 1.0e-60) {
        // Neither absorption nor rotation: pure emission
        qNew = s.q + em.jQ * L;
        uNew = s.u + em.jU * L;
    } else if (A < 1.0e-15 * std::abs(R)) {
        // Rotation-dominated (A ~ 0): Ic = sin(phi)/R, Is = (1-cos(phi))/R
        const double ic = Sphi / R;
        const double is_ = (1.0 - Cphi) / R;
        qNew = qHom + em.jQ * ic - em.jU * is_;
        uNew = uHom + em.jQ * is_ + em.jU * ic;
    } else if (std::abs(R) < 1.0e-15 * A) {
        // Absorption-dominated (R ~ 0): Ic = (1-exp(-A*L))/A, Is = 0
        const double oneME = (tauL < 1.0e-4) ? L - 0.5 * tauL * L : (1.0 - E) / A;
        qNew = qHom + em.jQ * oneME;
        uNew = uHom + em.jU * oneME;
    } else {
        const double ec = E * Cphi;
        const double es = E * Sphi;
        const double ic  = (A * (1.0 - ec) + R * es) / D;
        const double is_ = (R * (1.0 - ec) - A * es) / D;
        qNew = qHom + em.jQ * ic - em.jU * is_;
        uNew = uHom + em.jQ * is_ + em.jU * ic;
    }

    return {iNew, qNew, uNew, vNew};
}

// ============================================================================
// RK4 step for full Mueller K matrix
// ============================================================================

/**
 * @brief RK4 step for the full polarized RTE with all K matrix terms.
 *
 * Solves dS/ds = J - K * S using 4th-order Runge-Kutta.  Use this when
 * dichroism (alpha_Q, alpha_V) or Faraday conversion (rho_Q) are significant.
 *
 * For the simplified case (only alpha_I + rho_V), prefer stokesStep() which
 * is exact for a uniform segment.
 *
 * The K matrix applied to a Stokes vector x = (I,Q,U,V):
 *   (K*x)[0] = alphaI*I + alphaQ*Q + alphaV*V   (+ alphaU*U, assumed 0)
 *   (K*x)[1] = alphaQ*I + alphaI*Q + rhoV*U  (+ -rhoU*V = 0)
 *   (K*x)[2] = alphaI*U - rhoV*Q + rhoQ*V  (+ alphaU*I = 0)
 *   (K*x)[3] = alphaV*I + alphaI*V - rhoQ*U  (+ rhoU*Q = 0)
 *
 * @param s     Current Stokes state
 * @param em    Emission coefficients
 * @param k     Propagation matrix coefficients
 * @return Updated Stokes state after one RK4 step
 */
[[nodiscard]] inline StokesVector stokesStepFull(const StokesVector& s,
                                                  const StokesEmission& em,
                                                  const FaradayPropagation& k) noexcept {
    if (k.dsCm <= 0.0) { return s; }

    const double ds = k.dsCm;

    // dS/ds = J - K*S
    auto deriv = [&](const StokesVector& x) -> StokesVector {
        const double dI = em.jI - (k.alphaI * x.i + k.alphaQ * x.q + k.alphaV * x.v);
        const double dQ = em.jQ - (k.alphaQ * x.i + k.alphaI * x.q + k.rhoV  * x.u);
        const double dU = em.jU - (k.alphaI * x.u - k.rhoV  * x.q + k.rhoQ  * x.v);
        const double dV = em.jV - (k.alphaV * x.i + k.alphaI * x.v - k.rhoQ * x.u);
        return {dI, dQ, dU, dV};
    };

    // RK4 coefficients
    const StokesVector k1 = deriv(s);
    const StokesVector k2 = deriv(s + k1 * (0.5 * ds));
    const StokesVector k3 = deriv(s + k2 * (0.5 * ds));
    const StokesVector k4 = deriv(s + k3 * ds);

    const double sixth = 1.0 / 6.0;
    return {
        s.i + ds * sixth * (k1.i + 2.0 * k2.i + 2.0 * k3.i + k4.i),
        s.q + ds * sixth * (k1.q + 2.0 * k2.q + 2.0 * k3.q + k4.q),
        s.u + ds * sixth * (k1.u + 2.0 * k2.u + 2.0 * k3.u + k4.u),
        s.v + ds * sixth * (k1.v + 2.0 * k2.v + 2.0 * k3.v + k4.v),
    };
}

// ============================================================================
// Path integration
// ============================================================================

/**
 * @brief Integrate polarized RTE along a full path.
 *
 * Applies stokesStep() (simplified K: alpha_I + rho_V only) sequentially
 * for each sample in the path, ordered from the far end toward the observer.
 *
 * @param emissions  Per-segment emission vectors (jI, jQ, jU, jV)
 * @param props      Per-segment propagation coefficients (alphaI, rhoV, dsCm)
 * @param initial    Initial Stokes state (background; default zero)
 * @return Stokes vector at end of path (closest to observer)
 */
[[nodiscard]] inline StokesVector integrateStokesPath(
    const std::vector<StokesEmission>&    emissions,
    const std::vector<FaradayPropagation>& props,
    StokesVector initial = {}) noexcept {

    const std::size_t N = std::min(emissions.size(), props.size());
    StokesVector state = initial;
    for (std::size_t k = 0; k < N; ++k) {
        state = stokesStep(state, emissions[k], props[k].alphaI, props[k].rhoV, props[k].dsCm);
    }
    return state;
}

// ============================================================================
// Polarization invariant check
// ============================================================================

/**
 * @brief Verify the polarization invariant I >= sqrt(Q^2 + U^2 + V^2).
 *
 * @param s StokesVector to check
 * @return true if the polarization bound is satisfied (within tol)
 */
[[nodiscard]] inline bool stokesPolarizationBound(const StokesVector& s,
                                                   double tol = 1.0e-10) noexcept {
    const double pol2 = s.q * s.q + s.u * s.u + s.v * s.v;
    return (s.i * s.i + tol) >= pol2;
}

// ============================================================================
// Physical emission coefficients
// ============================================================================

/**
 * @brief Intrinsic linear polarization fraction for power-law electrons.
 *
 * For N(gamma) ~ gamma^(-p) the optically thin synchrotron polarization
 * fraction is (Rybicki & Lightman 1979, Eq. 6.75):
 *
 *   Pi_lin = (p + 1) / (p + 7/3)
 *
 * which gives Pi_lin = 0.69 for p=2, 0.72 for p=3.
 *
 * @param p Electron power-law index (2 <= p <= 4 typical)
 * @return Fractional linear polarization in [0, 1)
 */
[[nodiscard]] inline double synchrotronLinearPolarFrac(double p) noexcept {
    if (p <= 0.0) { return 0.0; }
    return (p + 1.0) / (p + 7.0 / 3.0);
}

/**
 * @brief Intrinsic linear polarization fraction for thermal electrons.
 *
 * For a Maxwell-Juttner electron distribution the intrinsic polarization
 * fraction varies with frequency as Pi(x_M) = Pi_max * h(x_M) where
 * x_M = nu / nu_s.  At peak (x_M ~ 1): Pi ~ 0.69-0.75.
 *
 * WHY simplified: The exact formula requires integrating G(x)/F(x) over
 * the thermal distribution.  For practical ray marching we use the
 * asymptotic form Pi_max = (p_eff + 1) / (p_eff + 7/3) where p_eff = 3
 * is the effective spectral index for thermal synchrotron near the peak.
 * This gives Pi_max = 4/3 / (3 + 7/3) ~ 0.75 which matches full
 * calculations (Mahadevan 1996, Bromley et al. 2001) to < 10%.
 *
 * @param thetaE Dimensionless electron temperature k_B T_e / (m_e c^2)
 * @return Fractional linear polarization ~ 0.75 for Theta_e >> 1
 */
[[nodiscard]] inline double thermalSynchLinearPolarFrac(double thetaE) noexcept {
    if (thetaE <= 0.0) { return 0.0; }
    // p_eff ~ 3 for thermal synchrotron (near peak), slightly increasing for
    // large Theta_e as the emission shifts to higher x_M
    const double pEff = 3.0 + 0.5 * std::log(1.0 + thetaE);  // soft correction
    return (pEff + 1.0) / (pEff + 7.0 / 3.0);
}

/**
 * @brief Polarized synchrotron emission vector given total emissivity and field geometry.
 *
 * Given j_I (from synchrotronThermalEmissivity or power-law), the polarization
 * fraction Pi, and the projected magnetic field angle chi on the sky plane,
 * computes the full emission vector.
 *
 * WHY: Synchrotron photons are emitted with E-vector perpendicular to the
 * projected B field (in flat space).  For a uniform field at EVPA chi_B,
 * the polarization E-vector is at chi_B + pi/2.  This convention follows
 * the IAU definition where chi = 0 points North and increases toward East.
 *
 * FORMULA:
 *   j_Q = -j_I * Pi * cos(2 * chi_B)    [chi_B = EVPA of projected B field]
 *   j_U = -j_I * Pi * sin(2 * chi_B)
 *   j_V = 0    [thermal synchrotron has negligible intrinsic circular polarization]
 *
 * The minus sign arises because the E-vector is perpendicular to B:
 *   chi_E = chi_B + pi/2  ->  cos(2*chi_E) = -cos(2*chi_B), sin(2*chi_E) = -sin(2*chi_B).
 *
 * @param jI      Total intensity emissivity [erg/(cm^3 s Hz sr)]
 * @param piLin   Fractional linear polarization (from synchrotronLinearPolarFrac)
 * @param chiBRad EVPA of projected B field on sky [rad]
 * @return Polarized emission vector (jV = 0)
 */
[[nodiscard]] inline StokesEmission synchrotronPolarizedEmission(double jI,
                                                                   double piLin,
                                                                   double chiBRad) noexcept {
    const double cos2chi = std::cos(2.0 * chiBRad);
    const double sin2chi = std::sin(2.0 * chiBRad);
    return {jI, -jI * piLin * cos2chi, -jI * piLin * sin2chi, 0.0};
}

// ============================================================================
// Faraday rotation and conversion coefficients
// ============================================================================

/**
 * @brief Faraday rotation coefficient rho_V for a cold (non-relativistic) plasma.
 *
 * The cold-plasma Faraday rotation coefficient (R&L 1979, Eq. 2.114; Shcherbakov 2008):
 *
 *   rho_V = (e^3 / (2*pi * m_e^2 * c^4)) * n_e * B_parallel / nu^2
 *         = 1.049e-8 * n_e [cm^-3] * B_par [G] / nu^2 [Hz]   [rad/cm]
 *
 * B_parallel = B * cos(theta_B) is the magnetic field component along the
 * photon propagation direction (line of sight).
 *
 * WHY cold plasma formula: Valid for h nu << m_e c^2 (radio through mm waves).
 * At EHT 230 GHz: h*nu ~ 1e-3 m_e*c^2 -> < 0.1% relativistic correction
 * for non-relativistic electrons.  For relativistic electrons (Theta_e > 1)
 * the coefficient is suppressed; use faradayRotationCoeffRelativistic() for Theta_e >> 1.
 *
 * Reference: Shcherbakov & Huang (2011), MNRAS 410, 1052, Eq. (B11).
 *
 * @param nu          Frequency [Hz]
 * @param nE          Electron number density [cm^-3]
 * @param bParallel   B-field component along LOS (B * cos theta_B) [Gauss]
 * @return rho_V [rad/cm]
 */
[[nodiscard]] inline double faradayRotationCoeff(double nu,
                                                  double nE,
                                                  double bParallel) noexcept {
    if (nu <= 0.0 || nE <= 0.0) { return 0.0; }
    // Prefactor: e^3 / (2*pi * m_e^2 * c^4) [rad / (cm^-3 * G * Hz^2 * cm)]
    // = e^3 / (2*pi * m_e^2 * c^4) in CGS
    const double e3 = E_CHARGE * E_CHARGE * E_CHARGE;
    const double me2c4 = M_ELECTRON * M_ELECTRON * C * C * C * C;
    const double prefac = e3 / (2.0 * std::numbers::pi * me2c4);
    return prefac * nE * bParallel / (nu * nu);
}

/**
 * @brief Relativistic Faraday rotation coefficient for hot plasma (Theta_e >> 1).
 *
 * For a Maxwell-Juttner electron distribution at dimensionless temperature
 * Theta_e, the Faraday rotation is suppressed relative to the cold-plasma
 * formula by the factor f_rm(Theta_e) (Shcherbakov 2008, Eq. B12):
 *
 *   rho_V^{rel} = rho_V^{cold} * f_rm(Theta_e)
 *
 * where:
 *   f_rm(Theta_e) = (K_0(1/Theta_e) + K_1(1/Theta_e)) / (2 * Theta_e^2 * K_2(1/Theta_e))
 *
 * For Theta_e -> 0: f_rm -> 1 (cold limit).
 * For Theta_e >> 1: K_0 ~ K_1 ~ K_2 -> 2*Theta_e^2, so f_rm -> 1/Theta_e^2 (highly suppressed).
 *
 * Fallback when boost is unavailable: f_rm ~ 1/(1 + Theta_e^2) (approximation).
 *
 * @param nu          Frequency [Hz]
 * @param nE          Electron density [cm^-3]
 * @param bParallel   B_parallel [Gauss]
 * @param thetaE      Dimensionless electron temperature
 * @return rho_V [rad/cm], suppressed for hot plasma
 */
[[nodiscard]] inline double faradayRotationCoeffRelativistic(double nu,
                                                              double nE,
                                                              double bParallel,
                                                              double thetaE) noexcept {
    if (thetaE <= 0.0) { return faradayRotationCoeff(nu, nE, bParallel); }

    double frm = 0.0;
#ifdef PHYSICS_STOKES_HAS_BOOST_BESSEL
    const double z   = 1.0 / thetaE;
    const double k0  = boost::math::cyl_bessel_k(0.0, z);
    const double k1  = boost::math::cyl_bessel_k(1.0, z);
    const double k2  = boost::math::cyl_bessel_k(2.0, z);
    const double denom = 2.0 * thetaE * thetaE * k2;
    frm = (denom > 0.0) ? (k0 + k1) / denom : 0.0;
#else
    // Approximation: f_rm ~ 1 / (1 + Theta_e^2) -- correct limits but not exact
    frm = 1.0 / (1.0 + thetaE * thetaE);
#endif
    return faradayRotationCoeff(nu, nE, bParallel) * frm;
}

/**
 * @brief Faraday conversion coefficient rho_Q for hot plasma (Theta_e >> 1).
 *
 * Faraday conversion transfers linear polarization to circular (and back).
 * For a thermal plasma (Shcherbakov & Huang 2011, Eq. B13):
 *
 *   rho_Q = (e^3 * n_e * B_perp) / (pi * m_e^2 * c^4) * f_conv(Theta_e) / nu^2
 *
 * where B_perp = B * sin(theta_B) and f_conv is a function of Theta_e.
 *
 * This implementation uses the leading-order Shcherbakov (2008) approximation:
 *   f_conv(Theta_e) ~ K_1(1/Theta_e) / (Theta_e * K_2(1/Theta_e)) - 1/(2*Theta_e^2)
 *
 * @param nu          Frequency [Hz]
 * @param nE          Electron density [cm^-3]
 * @param bPerp       B_perp = B * sin(theta_B) [Gauss]
 * @param thetaE      Dimensionless electron temperature
 * @return rho_Q [rad/cm]
 */
[[nodiscard]] inline double faradayConversionCoeff(double nu,
                                                    double nE,
                                                    double bPerp,
                                                    double thetaE) noexcept {
    if (nu <= 0.0 || nE <= 0.0 || thetaE <= 0.0) { return 0.0; }

    double fconv = 0.0;
#ifdef PHYSICS_STOKES_HAS_BOOST_BESSEL
    const double z  = 1.0 / thetaE;
    const double k1 = boost::math::cyl_bessel_k(1.0, z);
    const double k2 = boost::math::cyl_bessel_k(2.0, z);
    if (k2 > 0.0) {
        // K_1/(Theta_e*K_2) - 1/(2*Theta_e^2) can go slightly negative at moderate
        // Theta_e (~1-3) due to approximation error.  Physical conversion vanishes
        // rather than flipping sign -- clamp to zero.
        fconv = std::max(0.0, k1 / (thetaE * k2) - 1.0 / (2.0 * thetaE * thetaE));
    }
#else
    // Approximation for Theta_e >> 1: f_conv ~ 1/(2*Theta_e^2)
    fconv = (thetaE > 0.5) ? 0.5 / (thetaE * thetaE) : 1.0;
#endif

    const double e3    = E_CHARGE * E_CHARGE * E_CHARGE;
    const double me2c4 = M_ELECTRON * M_ELECTRON * C * C * C * C;
    const double prefac = e3 / (std::numbers::pi * me2c4);
    return prefac * nE * bPerp * fconv / (nu * nu);
}

// ============================================================================
// Rotation Measure (RM) integration
// ============================================================================

/**
 * @brief Compute accumulated Rotation Measure (RM) along a path.
 *
 * RM = integral rho_V ds  [rad/m^2 when ds is in meters; rad/cm^2 in CGS]
 *
 * In VLBI, RM is measured in rad/m^2 and the EVPA rotates as:
 *   Delta_chi = RM * lambda^2
 *
 * @param rhoVPerStep  Faraday rotation coefficient [rad/cm] at each step
 * @param dsPerStep    Path element [cm] at each step
 * @return RM [rad/cm] (multiply by (lambda[cm])^2 for rotation in rad)
 */
[[nodiscard]] inline double accumulatedRM(const std::vector<double>& rhoVPerStep,
                                           const std::vector<double>& dsPerStep) noexcept {
    const std::size_t N = std::min(rhoVPerStep.size(), dsPerStep.size());
    double rm = 0.0;
    for (std::size_t k = 0; k < N; ++k) {
        rm += rhoVPerStep[k] * dsPerStep[k];
    }
    return rm;
}

/**
 * @brief Apply accumulated Faraday rotation to a Stokes vector.
 *
 * Rotates EVPA by angle phi = RM * lambda^2:
 *   Q' = Q * cos(2*phi) - U * sin(2*phi)
 *   U' = Q * sin(2*phi) + U * cos(2*phi)
 * I and V are unchanged.
 *
 * @param s       Input Stokes vector
 * @param rmRad   Accumulated rotation angle Delta_chi = RM * lambda^2 [rad]
 * @return Faraday-rotated Stokes vector
 */
[[nodiscard]] inline StokesVector faradayRotateStokes(const StokesVector& s,
                                                       double rmRad) noexcept {
    return s.rotateEvpa(rmRad);
}

// ============================================================================
// GR polarization transport
// ============================================================================

/**
 * @brief Apply GR redshift to a Stokes vector (Liouville invariant I/nu^3).
 *
 * Under the Liouville invariant I_nu/nu^3 = const, all four Stokes
 * parameters transform with the same g^3 factor:
 *
 *   S_obs = g^3 * S_emit
 *
 * WHY: Stokes parameters are all derived from the same intensity tensor,
 * so all four transform as g^3 (Broderick & Blandford 2004, ApJ 974, 415).
 *
 * @param s  Stokes vector in plasma rest frame
 * @param g  Redshift factor nu_obs / nu_emit
 * @return Stokes vector in observer frame
 */
[[nodiscard]] inline StokesVector grTransformStokes(const StokesVector& s,
                                                     double g) noexcept {
    if (g <= 0.0) { return {}; }
    const double g3 = g * g * g;
    return {s.i * g3, s.q * g3, s.u * g3, s.v * g3};
}

/**
 * @brief Rotate Stokes polarization angle for GR parallel transport.
 *
 * As the photon travels along a curved geodesic, the polarization direction
 * (the polarization 4-vector f^mu) must be parallel transported.  In the
 * geometrical optics limit this results in a rotation of the EVPA by an
 * angle psi_PT that accumulates along the geodesic.
 *
 * This function applies a given parallel transport rotation psi_PT to the
 * Stokes vector -- it is the responsibility of the geodesic integrator to
 * compute psi_PT (e.g., using the Connors-Piran-Stark formula for Kerr).
 *
 * @param s       Stokes vector
 * @param psiRad  Parallel transport rotation angle [rad]
 * @return Rotated Stokes vector
 */
[[nodiscard]] inline StokesVector grParallelTransportRotate(const StokesVector& s,
                                                             double psiRad) noexcept {
    return s.rotateEvpa(psiRad);
}

} // namespace physics

#endif // PHYSICS_STOKES_TRANSPORT_H
