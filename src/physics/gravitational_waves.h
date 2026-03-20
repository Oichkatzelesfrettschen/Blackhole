/**
 * @file gravitational_waves.h
 * @brief Gravitational wave physics for compact binary systems.
 *
 * Implements the quadrupole formula and post-Newtonian corrections
 * for gravitational wave strain from inspiraling binaries.
 *
 * Key formulas:
 *
 * Strain amplitude (leading order):
 *   h = (4/D) * (G M_c/c^2)^(5/3) * (pi f/c)^(2/3)
 *
 * Chirp mass:
 *   M_c = (m1 m2)^(3/5) / (m1 + m2)^(1/5)
 *
 * Frequency evolution (Peters 1964):
 *   df/dt = (96/5) pi^(8/3) (G M_c/c^3)^(5/3) f^(11/3)
 *
 * Time to coalescence:
 *   tau = (5/256) (G M_c/c^3)^(-5/3) (pi f)^(-8/3)
 *
 * References:
 * - Peters & Mathews (1963), Phys. Rev. 131, 435
 * - Blanchet (2014), Living Reviews in Relativity
 * - LIGO Scientific Collaboration, Phys. Rev. Lett. 116, 061102 (2016)
 *
 * Cleanroom implementation based on standard GR formulas.
 */

#ifndef PHYSICS_GRAVITATIONAL_WAVES_H
#define PHYSICS_GRAVITATIONAL_WAVES_H

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <numbers>
#include <vector>

#include "constants.h"
#include "safe_limits.h"

namespace physics {

// ============================================================================
// Binary System Parameters
// ============================================================================

/**
 * @brief Parameters for a compact binary system.
 */
struct BinarySystem {
  double m1;          ///< Primary mass [g]
  double m2;          ///< Secondary mass [g]
  double a1;          ///< Primary spin parameter [cm]
  double a2;          ///< Secondary spin parameter [cm]
  double distance;    ///< Luminosity distance [cm]
  double inclination; ///< Orbital inclination [rad]

  // Derived quantities
  [[nodiscard]] double mTotal() const { return m1 + m2; }
  [[nodiscard]] double mu() const { return (m1 * m2) / mTotal(); } // Reduced mass
  [[nodiscard]] double eta() const { return mu() / mTotal(); }     // Symmetric mass ratio
  [[nodiscard]] double q() const { return m2 / m1; }               // Mass ratio (q <= 1)
};

/**
 * @brief Compute chirp mass.
 *
 * M_c = (m1 m2)^(3/5) / (m1 + m2)^(1/5)
 *     = M_total * eta^(3/5)
 *
 * The chirp mass is the primary parameter measured from GW signal.
 *
 * @param m1 Primary mass [g]
 * @param m2 Secondary mass [g]
 * @return Chirp mass [g]
 */
[[nodiscard]] inline double chirpMass(double m1, double m2) {
  const double mTot = m1 + m2;
  const double etaVal = (m1 * m2) / (mTot * mTot);
  return mTot * std::pow(etaVal, 0.6);
}

/**
 * @brief Compute chirp mass in geometric units.
 *
 * M_c^(geo) = G M_c / c^3 [seconds]
 *
 * @param mc Chirp mass [g]
 * @return Chirp mass in seconds
 */
[[nodiscard]] inline double chirpMassGeometric(double mc) {
  return (G * mc) / (C * C * C);
}

// ============================================================================
// Gravitational Wave Strain - Newtonian Order
// ============================================================================

/**
 * @brief Compute GW strain amplitude at Newtonian order.
 *
 * h0 = (4/D) * (G M_c/c^2)^(5/3) * (pi f/c)^(2/3)
 *
 * This is the leading-order strain for circular orbits.
 *
 * @param mc Chirp mass [g]
 * @param f Gravitational wave frequency [Hz]
 * @param d Luminosity distance [cm]
 * @return Dimensionless strain amplitude
 */
[[nodiscard]] inline double gwStrainAmplitude(double mc, double f, double d) {
  if ((d <= 0) || (f <= 0)) { return 0.0; }

  const double gmcOverC2 = (G * mc) / C2;
  const double factor1 = std::pow(gmcOverC2, 5.0 / 3.0);
  const double factor2 = std::pow((physics::PI * f) / C, 2.0 / 3.0);

  return (4.0 / d) * factor1 * factor2;
}

/**
 * @brief Compute plus and cross polarization strains.
 *
 * hPlus = h0 * (1 + cos^2(iota))/2 * cos(2*phase)
 * hCross = h0 * cos(iota) * sin(2*phase)
 *
 * @param h0 Strain amplitude
 * @param inclination Orbital inclination [rad]
 * @param phase Orbital phase [rad]
 * @param hPlus Output: plus polarization
 * @param hCross Output: cross polarization
 */
inline void gwPolarizations(double h0, double inclination, double phase,
                            double &hPlus, double &hCross) {
  const double cosI = std::cos(inclination);
  const double cosI2 = cosI * cosI;

  hPlus  = h0 * ((1.0 + cosI2) / 2.0) * std::cos(2.0 * phase);
  hCross = h0 * cosI * std::sin(2.0 * phase);
}

// ============================================================================
// Frequency Evolution
// ============================================================================

/**
 * @brief Compute GW frequency derivative (chirp rate).
 *
 * df/dt = (96/5) pi^(8/3) (G M_c/c^3)^(5/3) f^(11/3)
 *
 * @param mc Chirp mass [g]
 * @param f Current frequency [Hz]
 * @return Frequency derivative [Hz/s]
 */
[[nodiscard]] inline double frequencyDerivative(double mc, double f) {
  const double mcGeo  = chirpMassGeometric(mc);
  const double factor1 = std::pow(mcGeo, 5.0 / 3.0);
  const double factor2 = std::pow(physics::PI, 8.0 / 3.0);
  const double factor3 = std::pow(f, 11.0 / 3.0);

  return (96.0 / 5.0) * factor2 * factor1 * factor3;
}

/**
 * @brief Compute time to coalescence.
 *
 * tau = (5/256) (G M_c/c^3)^(-5/3) (pi f)^(-8/3)
 *
 * @param mc Chirp mass [g]
 * @param f Current frequency [Hz]
 * @return Time to merger [s]
 */
[[nodiscard]] inline double timeToCoalescence(double mc, double f) {
  if (f <= 0) { return safeInfinity<double>(); }

  const double mcGeo   = chirpMassGeometric(mc);
  const double factor1 = std::pow(mcGeo, -5.0 / 3.0);
  const double factor2 = std::pow(physics::PI * f, -8.0 / 3.0);

  return (5.0 / 256.0) * factor1 * factor2;
}

/**
 * @brief Compute orbital separation from GW frequency.
 *
 * From Kepler's law: a^3 = G M_total / (4 pi^2 f_orb^2)
 * where f_GW = 2 f_orb for quadrupole radiation.
 *
 * @param mTotal Total mass [g]
 * @param f GW frequency [Hz]
 * @return Orbital separation [cm]
 */
[[nodiscard]] inline double orbitalSeparation(double mTotal, double f) {
  if (f <= 0) { return safeInfinity<double>(); }

  const double fOrb    = f / 2.0;
  const double aCubed  = (G * mTotal) / (4.0 * physics::PI * physics::PI * fOrb * fOrb);

  return std::cbrt(aCubed);
}

/**
 * @brief Compute GW frequency at ISCO.
 *
 * f_ISCO = c^3 / (pi G M_total) * (r_ISCO/M)^(-3/2)
 *
 * For Schwarzschild: r_ISCO = 6M, so f_ISCO = c^3/(6^(3/2) pi G M)
 *
 * @param mTotal Total mass [g]
 * @param rIscoOverM ISCO radius in units of M (6 for Schwarzschild)
 * @return ISCO frequency [Hz]
 */
[[nodiscard]] inline double gwFrequencyIsco(double mTotal, double rIscoOverM = 6.0) {
  const double mGeo = (G * mTotal) / (C * C * C);

  return 1.0 / (physics::PI * mGeo * std::pow(rIscoOverM, 1.5));
}

// ============================================================================
// Post-Newtonian Corrections
// ============================================================================

/**
 * @brief Compute strain with 1PN correction.
 *
 * Includes the first post-Newtonian correction to the amplitude:
 * h = h0 * [1 + (55/48 - 55/16 eta) x + O(x^2)]
 *
 * where x = (pi G M f/c^3)^(2/3) is the PN expansion parameter.
 *
 * @param mc Chirp mass [g]
 * @param etaVal Symmetric mass ratio
 * @param f GW frequency [Hz]
 * @param d Distance [cm]
 * @return 1PN-corrected strain amplitude
 */
[[nodiscard]] inline double gwStrain1pn(double mc, double etaVal, double f, double d) {
  const double h0     = gwStrainAmplitude(mc, f, d);
  const double mTot   = mc / std::pow(etaVal, 0.6);
  const double mGeo   = (G * mTot) / (C * C * C);
  const double x      = std::pow(physics::PI * mGeo * f, 2.0 / 3.0);
  const double pnCorr = 1.0 + (((55.0 / 48.0) - (55.0 * etaVal / 16.0)) * x);

  return h0 * pnCorr;
}

/**
 * @brief Compute GW phase with full 3.5PN corrections including spin couplings.
 *
 * Phi(f) = 2*pi*f*t_c - phi_c - pi/4 + (3/128 eta)*(pi*M*f)^(-5/3)
 *           * [1 + PN_corrections + spin_corrections]
 *
 * Non-spin terms through 3.5PN from Blanchet (2014) Living Rev. Rel.
 *
 * Spin corrections:
 *   1.5PN SO  -- Kidder (1995) Phys. Rev. D 52, 821
 *   2PN  SS   -- Poisson (1998) Phys. Rev. D 57, 5287
 *   2.5PN SO  -- Blanchet, Buonanno, Faye (2006) Phys. Rev. D 74, 104034
 *   3PN  SO   -- Blanchet, Buonanno, Faye (2011) arXiv:1104.5659 Eq. 7.10
 *   3PN  SS   -- Mikoczi, Vasuth, Gergely (2005) Phys. Rev. D 71, 124043
 *   3.5PN SO  -- Blanchet, Buonanno, Faye (2011) arXiv:1104.5659 Eq. 7.11
 *
 * Uses symmetric/antisymmetric spin combinations:
 *   chiS = (chi1 + chi2) / 2
 *   chiA = (chi1 - chi2) / 2
 *   delta = (m1 - m2) / (m1 + m2) = sqrt(1 - 4*eta)
 *
 * @param mc      Chirp mass [g]
 * @param etaVal  Symmetric mass ratio
 * @param f       GW frequency [Hz]
 * @param tC      Time of coalescence [s]
 * @param phiC    Phase at coalescence [rad]
 * @param chiEff  Effective aligned spin (default 0 = no spin)
 * @param chi1    Dimensionless spin of primary (default 0)
 * @param chi2    Dimensionless spin of secondary (default 0)
 * @return GW phase [rad]
 */
[[nodiscard]] inline double gwPhase3p5pn(double mc, double etaVal, double f,
                                         double tC = 0.0, double phiC = 0.0,
                                         double chiEff = 0.0,
                                         double chi1 = 0.0, double chi2 = 0.0) {
  const double mTot  = mc / std::pow(etaVal, 0.6);
  const double mGeo  = (G * mTot) / (C * C * C);

  const double v    = std::cbrt(physics::PI * mGeo * f);
  const double v2   = v * v;
  const double v3   = v2 * v;
  const double v4   = v3 * v;
  const double v5   = v4 * v;
  const double v6   = v5 * v;
  const double v7   = v6 * v;
  const double logV = std::log(v);

  const double eta2 = etaVal * etaVal;
  const double eta3 = eta2 * etaVal;

  const double chiS  = 0.5 * (chi1 + chi2);
  const double chiA  = 0.5 * (chi1 - chi2);
  const double delta = std::sqrt(std::max(1.0 - (4.0 * etaVal), 0.0));

  // Non-spin PN coefficients (Blanchet 2014 LRR, Eqs. 234-241)
  const double psiN = 1.0;
  const double psi1PN = ((3715.0 / 756.0) + (55.0 * etaVal / 9.0)) * v2;
  const double psi15PNpm = -16.0 * physics::PI * v3;
  const double psi2PNpm = ((15293365.0 / 508032.0) + (27145.0 * etaVal / 504.0) +
                           (3085.0 * eta2 / 72.0)) * v4;
  const double psi25PNpm = physics::PI * ((38645.0 / 756.0) - (65.0 * etaVal / 9.0)) *
                           (1.0 + (3.0 * logV)) * v5;

  // 3PN (Blanchet 2014 Eq. 238, Euler-Mascheroni constant)
  const double psi3PNpm = ((11583231236531.0 / 4694215680.0)
                           - (640.0 * physics::PI * physics::PI / 3.0)
                           - (6848.0 * std::numbers::egamma / 21.0)
                           + (etaVal * ((-15737765635.0 / 3048192.0)
                                        + (2255.0 * physics::PI * physics::PI / 12.0)))
                           + (76055.0 * eta2 / 1728.0)
                           - (127825.0 * eta3 / 1296.0)
                           - (6848.0 * std::log(4.0 * v) / 21.0)) * v6;

  const double psi35PNpm = physics::PI * ((77096675.0 / 254016.0)
                                   + (378515.0 * etaVal / 1512.0)
                                   - (74045.0 * eta2 / 756.0)) * v7;

  // Spin-orbit corrections
  const double psi15PNSO = ((113.0 / 12.0) + (25.0 * etaVal / 4.0)) * chiEff * v3;
  const double psi2PNSS  = -(25.0 / 2.0) * etaVal *
                            ((chi1 * chi1) + (chi2 * chi2) + (2.0 * chi1 * chi2)) * v4;
  const double psi25PNSO = physics::PI * (
    (((- 4159.0 / 672.0) - (189.0 * etaVal / 8.0)) * chiS)
    + (delta * (((-4159.0 / 672.0) + (189.0 * etaVal / 8.0)) * chiA))
  ) * v5;
  const double psi3PNSO  = (
    (((14585.0 / 8.0) - (215.0 * etaVal / 2.0) - (15.0 * eta2 / 2.0)) * chiS)
    + (delta * (((14585.0 / 8.0) - (475.0 * etaVal / 6.0)) * chiA))
  ) * v6;

  const double chiS2 = chiS * chiS;
  const double chiA2 = chiA * chiA;
  const double psi3PNSS = (
    (((5.0 / 2.0) + (40.0 * etaVal / 3.0)) * chiS2)
    + (5.0 * delta * chiS * chiA)
    + (((5.0 / 2.0) - (10.0 * etaVal)) * chiA2)
  ) * v6;

  const double psi35PNSO = physics::PI * (
    (((732985.0 / 2268.0) - (140.0 * etaVal / 9.0)) * chiS)
    + (delta * (((732985.0 / 2268.0) - (24260.0 * etaVal / 81.0)) * chiA))
  ) * v7;

  const double pnSum = psiN
                     + psi1PN
                     + psi15PNpm + psi15PNSO
                     + psi2PNpm  + psi2PNSS
                     + psi25PNpm + psi25PNSO
                     + psi3PNpm  + psi3PNSO + psi3PNSS
                     + psi35PNpm + psi35PNSO;

  const double psiLeading = 3.0 / (128.0 * etaVal * v5);

  return (2.0 * physics::PI * f * tC) - phiC - (physics::PI / 4.0) + (psiLeading * pnSum);
}

/**
 * @brief Compute GW phase with full 4.5PN corrections including spin couplings.
 *
 * Extends gwPhase3p5pn() with 4PN and 4.5PN point-mass contributions.
 *
 * 4PN non-log:  [3058673/7056 + 5429*eta/7 + 617*eta^2/72] * v^8
 * 4PN log:      -6848/21 * (gamma_E + log(4*v)) * v^8
 *               (tail-of-tail logarithmic contribution)
 * 4.5PN:        pi * (38645/756 - 65*eta/9) * [1 + 3*log(v/v_lso)] * v^9
 *               where v_lso = 1/sqrt(6)
 *
 * Spin corrections are identical to gwPhase3p5pn() (through 3.5PN SO/SS).
 *
 * References:
 * - Blanchet+ (2023) arXiv:2304.11185 (4PN point-mass)
 * - Blanchet (2014) Living Rev. Rel. (lower-order terms)
 * - Spin references same as gwPhase3p5pn()
 *
 * @param f       GW frequency [Hz]
 * @param mChirp  Chirp mass [g]
 * @param etaVal  Symmetric mass ratio
 * @param chiEff  Effective aligned spin (default 0)
 * @param chi1    Dimensionless spin of primary (default 0)
 * @param chi2    Dimensionless spin of secondary (default 0)
 * @param tC      Time of coalescence [s] (default 0)
 * @param phiC    Phase at coalescence [rad] (default 0)
 * @return GW phase [rad]
 */
[[nodiscard]] inline double gwPhase4p5pn(double f, double mChirp, double etaVal,
                                         double chiEff = 0.0,
                                         double chi1 = 0.0, double chi2 = 0.0,
                                         double tC = 0.0, double phiC = 0.0) {
  const double mTot = mChirp / std::pow(etaVal, 0.6);
  const double mGeo = (G * mTot) / (C * C * C);

  const double v    = std::cbrt(physics::PI * mGeo * f);
  const double v2   = v * v;
  const double v3   = v2 * v;
  const double v4   = v3 * v;
  const double v5   = v4 * v;
  const double v6   = v5 * v;
  const double v7   = v6 * v;
  const double v8   = v7 * v;
  const double v9   = v8 * v;
  const double logV = std::log(v);

  const double eta2 = etaVal * etaVal;
  const double eta3 = eta2 * etaVal;

  const double chiS  = 0.5 * (chi1 + chi2);
  const double chiA  = 0.5 * (chi1 - chi2);
  const double delta = std::sqrt(std::max(1.0 - (4.0 * etaVal), 0.0));

  // Non-spin PN coefficients (Blanchet 2014 LRR, Eqs. 234-241)
  const double psiN = 1.0;
  const double psi1PN = ((3715.0 / 756.0) + (55.0 * etaVal / 9.0)) * v2;
  const double psi15PNpm = -16.0 * physics::PI * v3;
  const double psi2PNpm = ((15293365.0 / 508032.0) + (27145.0 * etaVal / 504.0) +
                           (3085.0 * eta2 / 72.0)) * v4;
  const double psi25PNpm = physics::PI * ((38645.0 / 756.0) - (65.0 * etaVal / 9.0)) *
                           (1.0 + (3.0 * logV)) * v5;

  // 3PN (Euler-Mascheroni constant)
  const double psi3PNpm = ((11583231236531.0 / 4694215680.0)
                           - (640.0 * physics::PI * physics::PI / 3.0)
                           - (6848.0 * std::numbers::egamma / 21.0)
                           + (etaVal * ((-15737765635.0 / 3048192.0)
                                        + (2255.0 * physics::PI * physics::PI / 12.0)))
                           + (76055.0 * eta2 / 1728.0)
                           - (127825.0 * eta3 / 1296.0)
                           - (6848.0 * std::log(4.0 * v) / 21.0)) * v6;

  const double psi35PNpm = physics::PI * ((77096675.0 / 254016.0)
                                   + (378515.0 * etaVal / 1512.0)
                                   - (74045.0 * eta2 / 756.0)) * v7;

  // 4PN point-mass (Blanchet+ 2023 arXiv:2304.11185)
  const double psi4PNnonlog = ((3058673.0 / 7056.0)
                               + (5429.0 * etaVal / 7.0)
                               + (617.0 * eta2 / 72.0)) * v8;
  const double psi4PNlog = (-6848.0 / 21.0) * (std::numbers::egamma + std::log(4.0 * v)) * v8;
  const double psi4PNpm  = psi4PNnonlog + psi4PNlog;

  // 4.5PN point-mass -- vLso = 1/sqrt(6) for Schwarzschild ISCO
  constexpr double vLso = 1.0 / 2.44948974278317809819; // 1/sqrt(6)
  const double psi45PNpm = physics::PI * ((38645.0 / 756.0) - (65.0 * etaVal / 9.0))
                           * (1.0 + (3.0 * std::log(v / vLso))) * v9;

  // Spin-orbit corrections (aligned-spin TaylorF2 phasing)
  const double psi15PNSO = ((113.0 / 12.0) + (25.0 * etaVal / 4.0)) * chiEff * v3;
  const double psi2PNSS  = -(25.0 / 2.0) * etaVal *
                            ((chi1 * chi1) + (chi2 * chi2) + (2.0 * chi1 * chi2)) * v4;
  const double psi25PNSO = physics::PI * (
    (((-4159.0 / 672.0) - (189.0 * etaVal / 8.0)) * chiS)
    + (delta * (((-4159.0 / 672.0) + (189.0 * etaVal / 8.0)) * chiA))
  ) * v5;
  const double psi3PNSO  = (
    (((14585.0 / 8.0) - (215.0 * etaVal / 2.0) - (15.0 * eta2 / 2.0)) * chiS)
    + (delta * (((14585.0 / 8.0) - (475.0 * etaVal / 6.0)) * chiA))
  ) * v6;

  const double chiS2 = chiS * chiS;
  const double chiA2 = chiA * chiA;
  const double psi3PNSS = (
    (((5.0 / 2.0) + (40.0 * etaVal / 3.0)) * chiS2)
    + (5.0 * delta * chiS * chiA)
    + (((5.0 / 2.0) - (10.0 * etaVal)) * chiA2)
  ) * v6;

  const double psi35PNSO = physics::PI * (
    (((732985.0 / 2268.0) - (140.0 * etaVal / 9.0)) * chiS)
    + (delta * (((732985.0 / 2268.0) - (24260.0 * etaVal / 81.0)) * chiA))
  ) * v7;

  const double pnSum = psiN
                     + psi1PN
                     + psi15PNpm + psi15PNSO
                     + psi2PNpm  + psi2PNSS
                     + psi25PNpm + psi25PNSO
                     + psi3PNpm  + psi3PNSO + psi3PNSS
                     + psi35PNpm + psi35PNSO
                     + psi4PNpm
                     + psi45PNpm;

  const double psiLeading = 3.0 / (128.0 * etaVal * v5);

  return (2.0 * physics::PI * f * tC) - phiC - (physics::PI / 4.0) + (psiLeading * pnSum);
}

// ============================================================================
// Waveform Generation
// ============================================================================

/**
 * @brief Point in a GW waveform.
 */
struct WaveformPoint {
  double t;      ///< Time [s]
  double f;      ///< Frequency [Hz]
  double hPlus;  ///< Plus polarization
  double hCross; ///< Cross polarization
  double phase;  ///< Orbital phase [rad]
};

/**
 * @brief Compute effective aligned spin parameter from binary.
 *
 * chiEff = (m1*a1_star + m2*a2_star) / (m1 + m2)
 *
 * WHY: chiEff is the dominant spin parameter in the waveform phase and
 * is directly constrained by LIGO/Virgo parameter estimation.
 *
 * @param binary Binary system parameters (a1, a2 in cm; converted internally)
 * @return Effective aligned spin (-1 <= chiEff <= 1)
 */
[[nodiscard]] inline double chiEffFromBinary(const BinarySystem &binary) {
  const double m1Geo  = (G * binary.m1) / C2;
  const double m2Geo  = (G * binary.m2) / C2;
  const double a1Star = (m1Geo > 0) ? (binary.a1 / m1Geo) : 0.0;
  const double a2Star = (m2Geo > 0) ? (binary.a2 / m2Geo) : 0.0;
  return ((binary.m1 * a1Star) + (binary.m2 * a2Star)) / binary.mTotal();
}

/**
 * @brief Generate inspiral waveform with spin corrections.
 *
 * Integrates the frequency evolution and computes strain at each step.
 * Uses the stationary phase approximation for efficiency.
 * Spin-orbit and spin-spin PN phase corrections are included when
 * binary.a1 or binary.a2 are nonzero.
 *
 * @param binary Binary system parameters
 * @param fLow Starting frequency [Hz]
 * @param fHigh Ending frequency [Hz]
 * @param dt Time step [s]
 * @return Vector of waveform points
 */
[[nodiscard]] inline std::vector<WaveformPoint> generateInspiralWaveform(
    const BinarySystem &binary, double fLow, double fHigh, double dt) {

  std::vector<WaveformPoint> waveform;
  waveform.reserve(static_cast<size_t>((fHigh - fLow) / (fLow * 1e-4)));

  const double mc      = chirpMass(binary.m1, binary.m2);
  const double etaVal  = binary.eta();

  const double m1Geo  = (G * binary.m1) / C2;
  const double m2Geo  = (G * binary.m2) / C2;
  const double a1Star = (m1Geo > 0) ? (binary.a1 / m1Geo) : 0.0;
  const double a2Star = (m2Geo > 0) ? (binary.a2 / m2Geo) : 0.0;
  const double chiEff = chiEffFromBinary(binary);

  double f     = fLow;
  double t     = 0.0;
  double phase = 0.0;

  while ((f < fHigh) && (f > 0)) {
    const double h0 = gwStrain1pn(mc, etaVal, f, binary.distance);

    double hPlus  = 0.0;
    double hCross = 0.0;
    gwPolarizations(h0, binary.inclination, phase, hPlus, hCross);

    WaveformPoint pt{};
    pt.t      = t;
    pt.f      = f;
    pt.hPlus  = hPlus;
    pt.hCross = hCross;
    pt.phase  = phase;
    waveform.push_back(pt);

    const double dfDt = frequencyDerivative(mc, f);
    f += dfDt * dt;

    phase = gwPhase3p5pn(mc, etaVal, f, t, 0.0, chiEff, a1Star, a2Star);
    t += dt;

    if (waveform.size() > 10000000) { break; }
  }

  return waveform;
}

// ============================================================================
// Ringdown (Quasi-Normal Modes)
// ============================================================================

/**
 * @brief Compute dominant QNM frequency for Schwarzschild.
 *
 * omega_22 ~= 0.3737 / M (geometric units)
 *
 * @param mFinal Final black hole mass [g]
 * @return QNM frequency [Hz]
 */
[[nodiscard]] inline double qnmFrequencySchwarzschild(double mFinal) {
  const double mGeo = (G * mFinal) / (C * C * C);
  return 0.3737 / (2.0 * physics::PI * mGeo);
}

/**
 * @brief Compute QNM damping time for Schwarzschild.
 *
 * tau_22 ~= M / 0.0890 (geometric units)
 *
 * @param mFinal Final black hole mass [g]
 * @return Damping time [s]
 */
[[nodiscard]] inline double qnmDampingTimeSchwarzschild(double mFinal) {
  const double mGeo = (G * mFinal) / (C * C * C);
  return mGeo / 0.0890;
}

/**
 * @brief Compute spin-dependent QNM frequency for Kerr (l=2, m=2 mode).
 *
 * Uses polynomial fits from Berti, Cardoso & Starinets (2009) Table VIII
 * for the dominant (2,2) quasi-normal mode:
 *
 *   f_1 = 1.5251 - 1.1568 * (1 - a_star)^0.1292
 *   q   = 0.7000 + 1.4187 * (1 - a_star)^(-0.4990)
 *   omega_R = f_1 / (2 pi M_geo)
 *
 * WHY: QNM frequency depends significantly on spin; at a*=0.9 the
 * frequency is ~30% higher than the Schwarzschild value. The fit
 * reduces to the Schwarzschild limit (omega_R = 0.3737/M) as a* -> 0.
 *
 * Reference: Berti, Cardoso & Starinets (2009), Class. Quant. Grav. 26,
 *            163001, Table VIII (n=0 overtone, l=m=2).
 *
 * @param mFinal Final black hole mass [g]
 * @param aStar  Dimensionless spin parameter (0 <= aStar <= 1)
 * @return QNM frequency [Hz]
 */
[[nodiscard]] inline double qnmFrequencyKerr(double mFinal, double aStar) {
  if (aStar <= 0.0) { return qnmFrequencySchwarzschild(mFinal); }
  const double aStarClamped = std::min(aStar, 0.9999);

  const double mGeo = (G * mFinal) / (C * C * C);
  const double f1   = 1.5251 - (1.1568 * std::pow(1.0 - aStarClamped, 0.1292));

  return f1 / (2.0 * physics::PI * mGeo);
}

/**
 * @brief Compute spin-dependent QNM damping time for Kerr (l=2, m=2 mode).
 *
 * Uses quality factor q from Berti et al. (2009):
 *
 *   q   = 0.7000 + 1.4187 * (1 - a_star)^(-0.4990)
 *   tau = 2 q / omega_R
 *
 * WHY: For rapidly spinning black holes (a* > 0.7) the ringdown rings
 * many more cycles than the Schwarzschild case; the damping time can
 * increase by a factor of ~3. Using the Schwarzschild value for Kerr
 * underestimates the number of visible ringdown cycles.
 *
 * Reference: Berti, Cardoso & Starinets (2009), Class. Quant. Grav. 26,
 *            163001, Table VIII (n=0 overtone, l=m=2).
 *
 * @param mFinal Final black hole mass [g]
 * @param aStar  Dimensionless spin parameter (0 <= aStar <= 1)
 * @return Damping time [s]
 */
[[nodiscard]] inline double qnmDampingTimeKerr(double mFinal, double aStar) {
  if (aStar <= 0.0) { return qnmDampingTimeSchwarzschild(mFinal); }
  const double aStarClamped = std::min(aStar, 0.9999);

  const double mGeo   = (G * mFinal) / (C * C * C);
  const double qFit   = 0.7000 + (1.4187 * std::pow(1.0 - aStarClamped, -0.4990));
  const double f1     = 1.5251 - (1.1568 * std::pow(1.0 - aStarClamped, 0.1292));
  const double omegaR = f1 / mGeo;

  return (2.0 * qFit) / omegaR;
}

/**
 * @brief Compute ringdown strain.
 *
 * h(t) = A * exp(-t/tau) * cos(omega t + phi)
 *
 * @param amp     Initial amplitude
 * @param omegaQnm QNM angular frequency [rad/s]
 * @param tau     Damping time [s]
 * @param t       Time since ringdown start [s]
 * @param phi     Initial phase [rad]
 * @return Strain at time t
 */
[[nodiscard]] inline double ringdownStrain(double amp, double omegaQnm, double tau,
                                           double t, double phi = 0.0) {
  if (t < 0) { return 0.0; }
  return amp * std::exp(-t / tau) * std::cos((omegaQnm * t) + phi);
}

// ============================================================================
// Energy and Angular Momentum
// ============================================================================

/**
 * @brief Compute GW luminosity (energy emission rate).
 *
 * L_GW = (32/5) c^5/G * eta^2 (M omega)^(10/3)
 *
 * @param mTotal Total mass [g]
 * @param etaVal Symmetric mass ratio
 * @param f GW frequency [Hz]
 * @return GW luminosity [erg/s]
 */
[[nodiscard]] inline double gwLuminosity(double mTotal, double etaVal, double f) {
  const double mGeo   = (G * mTotal) / (C * C * C);
  const double omega  = physics::PI * f;
  const double mOmega = mGeo * omega;
  const double factor = std::pow(mOmega, 10.0 / 3.0);

  return (32.0 / 5.0) * ((C * C * C * C * C) / G) * etaVal * etaVal * factor;
}

/**
 * @brief Compute total energy radiated in GWs.
 *
 * E_rad ~= eta M c^2 * (1 - sqrt(8/9))  (for equal mass, non-spinning)
 *
 * More accurate formula uses numerical relativity fits.
 *
 * @param mTotal Total mass [g]
 * @param etaVal Symmetric mass ratio
 * @return Radiated energy [erg]
 */
[[nodiscard]] inline double gwEnergyRadiated(double mTotal, double etaVal) {
  // Phenomenological fit from numerical relativity
  // E_rad/M ~= 0.0559 eta^2 (equal mass limit)
  const double epsilon = 0.0559 * etaVal * etaVal;

  return epsilon * mTotal * C2;
}

// ============================================================================
// Convenience Functions
// ============================================================================

/**
 * @brief Create binary neutron star system.
 *
 * @param m1Solar Primary mass in solar masses
 * @param m2Solar Secondary mass in solar masses
 * @param dMpc Distance in Mpc
 * @return BinarySystem
 */
[[nodiscard]] inline BinarySystem bnsSystem(double m1Solar, double m2Solar, double dMpc) {
  BinarySystem binary{};
  binary.m1 = m1Solar * M_SUN;
  binary.m2 = m2Solar * M_SUN;
  binary.a1 = 0.0;
  binary.a2 = 0.0;
  binary.distance   = dMpc * 1e6 * PARSEC;
  binary.inclination = 0.0;
  return binary;
}

/**
 * @brief Create binary black hole system.
 *
 * @param m1Solar Primary mass in solar masses
 * @param m2Solar Secondary mass in solar masses
 * @param a1Star Dimensionless primary spin (0-1)
 * @param a2Star Dimensionless secondary spin (0-1)
 * @param dMpc Distance in Mpc
 * @return BinarySystem
 */
[[nodiscard]] inline BinarySystem bbhSystem(double m1Solar, double m2Solar,
                                             double a1Star, double a2Star, double dMpc) {
  BinarySystem binary{};
  binary.m1 = m1Solar * M_SUN;
  binary.m2 = m2Solar * M_SUN;

  const double m1Geo = (G * binary.m1) / C2;
  const double m2Geo = (G * binary.m2) / C2;
  binary.a1 = a1Star * m1Geo;
  binary.a2 = a2Star * m2Geo;

  binary.distance    = dMpc * 1e6 * PARSEC;
  binary.inclination = 0.0;
  return binary;
}

/**
 * @brief Compute characteristic strain for detector sensitivity.
 *
 * h_c = 2 f |h_tilde(f)| ~= h * sqrt(N_cycles)
 *
 * @param mc Chirp mass [g]
 * @param f GW frequency [Hz]
 * @param d Distance [cm]
 * @return Characteristic strain
 */
[[nodiscard]] inline double characteristicStrain(double mc, double f, double d) {
  const double h0      = gwStrainAmplitude(mc, f, d);
  const double tau     = timeToCoalescence(mc, f);
  const double nCycles = f * tau;

  return h0 * std::sqrt(nCycles);
}

// ============================================================================
// Higher GW Multipole Modes (l > 2)
// ============================================================================

/**
 * @brief QNM mode identifier (l, m, n) for Kerr quasi-normal modes.
 *
 * Conventions: l = angular multipole number (l >= 2),
 *              m = azimuthal number (0 < m <= l, prograde),
 *              n = overtone index (n = 0 is the fundamental mode).
 *
 * The dominant GW mode is (l=2, m=2, n=0). Subdominant modes carry
 * significant power for unequal-mass mergers:
 *   (3,3): ~10% of flux at mass ratio q=0.5
 *   (4,4): ~3%  of flux at mass ratio q=0.5
 *   (2,1): ~2%  of flux (GW kick channel)
 *
 * Reference: Kamaretsos et al. (2012), Phys. Rev. D 85, 024018.
 */
struct QNMMode {
  int l = 2; /**< Angular multipole number */
  int m = 2; /**< Azimuthal number (prograde: m > 0) */
  int n = 0; /**< Overtone index (0 = fundamental) */

  [[nodiscard]] constexpr bool operator==(const QNMMode &other) const noexcept {
    return l == other.l && m == other.m && n == other.n;
  }
};

/**
 * @brief Berti 2009 polynomial fit coefficients for a Kerr QNM mode.
 *
 * Fit form (Berti, Cardoso & Starinets 2009, Table VIII):
 *   omega_R * M = f1 - f2 * (1 - a*)^f3
 *   Q           = q1 + q2 * (1 - a*)^(-q3)
 *
 * where Q = omega_R * tau / 2 is the quality factor,
 * omega_R is the real QNM angular frequency, and tau the damping time.
 *
 * Reference: Berti, Cardoso & Starinets (2009), Class. Quant. Grav. 26,
 *            163001. arXiv:0905.2975, Table VIII.
 */
struct QNMFitParams {
  double f1 = 0, f2 = 0, f3 = 0; /**< Frequency fit coefficients */
  double q1 = 0, q2 = 0, q3 = 0; /**< Quality-factor fit coefficients */
  bool   valid = false;           /**< True if this mode has a fit entry */
};

/**
 * @brief Look up Berti 2009 polynomial fit coefficients for (l, m, n=0) modes.
 *
 * Schwarzschild (a*=0) exact limits from Leaver (1985):
 *   (2,2): omega_R*M = 0.3737,  Q = 2.100
 *   (3,3): omega_R*M = 0.5994,  Q = 3.234
 *   (4,4): omega_R*M = 0.8092,  Q = 4.298
 *
 * Fit accuracy at a*=0 (typical ~1-2% error from polynomial approximation):
 *   (2,2): 0.3683 vs 0.3737 (1.4%)
 *   (3,3): 0.5913 vs 0.5994 (1.4%)
 *
 * WHY: Subdominant modes must be computed consistently with the dominant
 * (2,2,0) mode to produce physically realistic multi-mode ringdown waveforms.
 * The Berti fits are the community-standard reference for this purpose.
 *
 * @param mode QNM mode (l, m, n)
 * @return Fit parameters, `valid=false` if mode is not in the table
 */
[[nodiscard]] inline QNMFitParams qnmFitParams(QNMMode mode) noexcept {
  if (mode.n != 0 || mode.m <= 0 || mode.m > mode.l) {
    return {}; /* valid=false: only n=0 prograde modes are tabulated */
  }
  if (mode.l == 2 && mode.m == 2) {
    /* (2,2,0): validated against existing qnmFrequencyKerr implementation.
     * Schw. limit: f1-f2 = 0.3683 (exact: 0.3737, ~1.4% fit error). */
    return {.f1=1.5251, .f2=1.1568, .f3=0.1292, .q1=0.7000, .q2=1.4187, .q3=0.4990, .valid=true};
  }
  if (mode.l == 3 && mode.m == 3) {
    /* (3,3,0): Berti 2009 Table VIII.
     * Schw. limit: f1-f2 = 0.5913 (exact: 0.5994, ~1.4% fit error).
     * Q at a*=0: q1+q2 = 3.243 (exact: 3.234, ~0.3% error). */
    return {.f1=1.8956, .f2=1.3043, .f3=0.1818, .q1=0.9000, .q2=2.3430, .q3=0.4810, .valid=true};
  }
  if (mode.l == 4 && mode.m == 4) {
    /* (4,4,0): Berti 2009 Table VIII (f2 adjusted so f1-f2 = 0.8092).
     * Q at a*=0: q1+q2 = 4.300 (exact: 4.298, ~0.05% error). */
    return {.f1=2.3902, .f2=1.5810, .f3=0.2020, .q1=0.9400, .q2=3.3600, .q3=0.5100, .valid=true};
  }
  return {}; /* valid=false: mode not yet tabulated */
}

/**
 * @brief Compute QNM frequency for a specified Kerr mode (l, m, n).
 *
 * Generalizes qnmFrequencyKerr() to any mode in the Berti 2009 table.
 * For the dominant (2,2,0) mode the result is identical to
 * qnmFrequencyKerr(mFinal, aStar).
 *
 * WHY: Unequal-mass mergers excite (3,3), (4,4), and (2,1) subdominant modes
 * at the 2-10% level. Neglecting them underestimates ringdown power and biases
 * source-parameter estimation.
 *
 * @param mFinal Final black hole mass [g]
 * @param aStar  Dimensionless spin (0 <= aStar < 1)
 * @param mode   QNM mode (l, m, n)
 * @return QNM frequency [Hz], or 0 if the mode is not in the fit table
 */
[[nodiscard]] inline double qnmFrequencyKerrMode(double mFinal, double aStar,
                                                  QNMMode mode) noexcept {
  const QNMFitParams p = qnmFitParams(mode);
  if (!p.valid) { return 0.0; }
  /* No early return for a*=0: at a*=0, (1-a*)^f3 = 1, so omega_R*M = f1 - f2,
   * the correct mode-specific Schwarzschild limit (Berti 2009 Table VIII). */
  const double aStarC = std::min(std::max(aStar, 0.0), 0.9999);
  const double mGeo   = (G * mFinal) / (C * C * C);
  const double f1     = p.f1 - (p.f2 * std::pow(1.0 - aStarC, p.f3));

  return f1 / (2.0 * physics::PI * mGeo);
}

/**
 * @brief Compute QNM damping time for a specified Kerr mode (l, m, n).
 *
 * Generalizes qnmDampingTimeKerr() to any mode in the Berti 2009 table.
 *
 * @param mFinal Final black hole mass [g]
 * @param aStar  Dimensionless spin (0 <= aStar < 1)
 * @param mode   QNM mode (l, m, n)
 * @return Damping time [s], or 0 if mode not in table
 */
[[nodiscard]] inline double qnmDampingTimeKerrMode(double mFinal, double aStar,
                                                    QNMMode mode) noexcept {
  const QNMFitParams p = qnmFitParams(mode);
  if (!p.valid) { return 0.0; }
  /* No early return for a*=0: Q = q1 + q2*(1-0)^(-q3) = q1 + q2 at Schwarzschild,
   * which is mode-specific and correct per Berti 2009 Table VIII. */
  const double aStarC = std::min(std::max(aStar, 0.0), 0.9999);
  const double mGeo   = (G * mFinal) / (C * C * C);
  const double f1     = p.f1 - (p.f2 * std::pow(1.0 - aStarC, p.f3));
  const double omegaR = f1 / mGeo; /* omega_R * M / M_geo = dimensionless */
  const double qFit   = p.q1 + (p.q2 * std::pow(1.0 - aStarC, -p.q3));

  return (2.0 * qFit) / omegaR;
}

/**
 * @brief Relative amplitude of a subdominant ringdown mode.
 *
 * Approximates A_{lm} / A_{22} as a function of the mass-ratio asymmetry
 * delta = (m1 - m2) / (m1 + m2).  Equal-mass mergers (delta=0) suppress
 * odd-parity modes, while unequal-mass mergers enhance them.
 *
 * Amplitude model (Kamaretsos et al. 2012, Phys. Rev. D 85, 024018, Table I):
 *   A_33 ~ 0.44 * |delta|        (antisymmetric, zero at equal mass)
 *   A_44 ~ 0.04 + 0.19 * delta^2 (symmetric, nonzero at equal mass)
 *   A_22 = 1.0                   (dominant mode, normalized)
 *
 * WHY: Real GW events have delta != 0. For LIGO O3 events with q in [0.4, 1],
 * the (3,3) contributes up to ~10% of the total ringdown power. Ignoring it
 * over-estimates the final mass and under-estimates the spin from matched
 * filter analysis.
 *
 * @param mode      QNM mode
 * @param m1        Primary mass [any consistent unit]
 * @param m2        Secondary mass [same unit as m1], m1 >= m2
 * @return Amplitude relative to A_22 = 1 (dimensionless ratio)
 */
[[nodiscard]] inline double qnmModeAmplitude(QNMMode mode,
                                              double m1, double m2) noexcept {
  if (mode.l == 2 && mode.m == 2) { return 1.0; }

  const double mTot  = m1 + m2;
  if (mTot <= 0.0) { return 0.0; }
  const double delta = (m1 - m2) / mTot;

  if (mode.l == 3 && mode.m == 3) {
    /* Kamaretsos 2012 Eq. (8): A_33 ~ 0.44 |delta| */
    return 0.44 * std::abs(delta);
  }
  if (mode.l == 4 && mode.m == 4) {
    /* Kamaretsos 2012: A_44 ~ 0.04 + 0.19 * delta^2 */
    return 0.04 + (0.19 * delta * delta);
  }
  return 0.0; /* mode not modelled */
}

/**
 * @brief Compute multi-mode ringdown strain.
 *
 * Superposes the (2,2,0), (3,3,0), and (4,4,0) QNM contributions:
 *
 *   h(t) = sum_{lm} A_{lm}/r * exp(-t/tau_{lm}) * cos(omega_{lm} t + phi_{lm})
 *
 * where A_{lm} = relativeAmplitude(l,m) * amp22. The relative amplitudes
 * use the Kamaretsos 2012 mass-ratio model.
 *
 * WHY: A single (2,2) contribution underestimates the true ringdown signal
 * by up to ~10% for asymmetric mergers, leading to biased final-state
 * parameter estimates when fitting to LIGO data.
 *
 * @param amp22   Initial amplitude of the dominant (2,2) mode
 * @param mFinal  Final black hole mass [g]
 * @param aStar   Final black hole spin (0 <= aStar < 1)
 * @param m1      Primary mass [g] (for subdominant amplitudes)
 * @param m2      Secondary mass [g]
 * @param t       Time since ringdown start [s]
 * @param phi22   Initial phase of the (2,2) mode [rad]
 * @return Total ringdown strain (sum over tabulated modes)
 */
[[nodiscard]] inline double ringdownStrainMultimode(double amp22, double mFinal,
                                                     double aStar,
                                                     double m1, double m2,
                                                     double t,
                                                     double phi22 = 0.0) noexcept {
  if (t < 0.0) { return 0.0; }

  double h = 0.0;

  /* Iterate over the three tabulated prograde modes */
  const QNMMode modes[3] = {{.l=2,.m=2,.n=0}, {.l=3,.m=3,.n=0}, {.l=4,.m=4,.n=0}};
  /* Phase offsets: (2,2) uses phi22; subdominant modes start in-phase */
  const double phases[3] = {phi22, 0.0, 0.0};

  for (int i = 0; i < 3; ++i) {
    const QNMMode &mode = modes[i];
    const double amp    = amp22 * qnmModeAmplitude(mode, m1, m2);
    if (amp == 0.0) { continue; }

    const double freq = qnmFrequencyKerrMode(mFinal, aStar, mode);
    const double tau  = qnmDampingTimeKerrMode(mFinal, aStar, mode);
    if (freq <= 0.0 || tau <= 0.0) { continue; }

    const double omega = 2.0 * physics::PI * freq;
    h += amp * std::exp(-t / tau) * std::cos((omega * t) + phases[i]);
  }
  return h;
}

} // namespace physics

#endif // PHYSICS_GRAVITATIONAL_WAVES_H
