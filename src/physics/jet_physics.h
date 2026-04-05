/**
 * @file jet_physics.h
 * @brief Relativistic jet physics for supermassive black holes.
 *
 * Implements physics of relativistic jets launched from black hole systems:
 * - Blandford-Znajek mechanism (electromagnetic energy extraction)
 * - Jet collimation and opening angles
 * - Lorentz factors and bulk velocities
 * - Jet base positioning (EHT-constrained for M87)
 * - State-dependent jet power (MAD vs SANE)
 *
 * Key observations:
 * - M87 jet base: ~0.09 light-years from horizon (EHT Jan 2026)
 * - Sgr A*: Weak jets, Γ ~ 5-15
 * - M87: Powerful jets, Γ ~ 10-20
 * - Blazars: Highly relativistic, Γ up to 50
 *
 * References:
 * - Blandford & Znajek (1977), MNRAS 179, 433
 * - Tchekhovskoy et al. (2011), MNRAS 418, L79 (MAD jets)
 * - EHT Collaboration (2026), M87 jet base detection
 * - Narayan & McClintock (2012), MNRAS 419, L69 (ADAF jets)
 *
 * Cleanroom implementation based on standard astrophysics formulas.
 */

#ifndef PHYSICS_JET_PHYSICS_H
#define PHYSICS_JET_PHYSICS_H

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <vector>

#include "constants.h"
#include "kerr.h"
#include "mad_disk.h"

namespace physics {

// ============================================================================
// Jet Parameters
// ============================================================================

/**
 * @brief Jet configuration parameters.
 */
struct JetParams {
  double mass;              ///< Black hole mass [g]
  double a;                 ///< Spin parameter [cm]
  double mdot;              ///< Accretion rate [g/s]
  AccretionState state;     ///< Accretion state (affects jet power)
  double magneticFlux;      ///< Dimensionless magnetic flux Φ_BH

  // Jet properties
  double lorentzFactor; ///< Bulk Lorentz factor Γ
  double openingAngle;  ///< Half-opening angle [rad]
  double baseDistance;  ///< Distance of jet base from horizon [cm]
};

/**
 * @brief Create jet parameters for M87.
 *
 * Based on EHT observations (Jan 2026).
 *
 * @param aStar Dimensionless spin (~0.9 from EHT)
 * @param mdotEdd Accretion rate in Eddington units (~0.001)
 * @return JetParams
 */
inline JetParams m87Jet(double aStar = 0.9, double mdotEdd = 0.001) {
  JetParams jet{};

  // M87* mass: ~6.5 billion solar masses
  double const mSolar = 6.5e9;
  jet.mass = mSolar * M_SUN;

  // Spin
  double const mGeo = G * jet.mass / C2;
  jet.a = aStar * mGeo;

  // Low accretion rate
  double const lEdd = 1.26e38 * mSolar;
  jet.mdot = mdotEdd * lEdd / (0.1 * C2);

  // MAD state (favored by EHT observations)
  jet.state = AccretionState::MAD;
  jet.magneticFlux = 50.0;

  // Jet properties
  jet.lorentzFactor = 15.0;               // Γ ~ 10-20 for M87
  jet.openingAngle = 10.0 * (PI / 180.0); // ~10 degrees

  // Jet base: 0.09 light-years = 8.5×10^17 cm
  jet.baseDistance = 0.09 * 9.461e17; // Convert ly to cm

  return jet;
}

/**
 * @brief Create jet parameters for Sgr A*.
 *
 * @param aStar Dimensionless spin (0.94 from EHT-GRMHD)
 * @param mdotEdd Accretion rate (~10^-5 for Sgr A*)
 * @return JetParams
 */
inline JetParams sgrAStarJet(double aStar = 0.94, double mdotEdd = 1e-5) {
  JetParams jet{};

  // Sgr A* mass: 4.3 million solar masses
  double const mSolar = 4.3e6;
  jet.mass = mSolar * M_SUN;

  // High spin (EHT-constrained)
  double const mGeo = G * jet.mass / C2;
  jet.a = aStar * mGeo;

  // Very low accretion rate
  double const lEdd = 1.26e38 * mSolar;
  jet.mdot = mdotEdd * lEdd / (0.1 * C2);

  // MAD state
  jet.state = AccretionState::MAD;
  jet.magneticFlux = 50.0;

  // Weaker jets than M87
  jet.lorentzFactor = 10.0;               // Γ ~ 5-15
  jet.openingAngle = 15.0 * (PI / 180.0); // ~15 degrees

  // Jet base closer to horizon (smaller mass)
  jet.baseDistance = 0.01 * 9.461e17; // ~0.01 ly

  return jet;
}

// ============================================================================
// Blandford-Znajek Mechanism
// ============================================================================

/**
 * @brief Compute horizon angular velocity.
 *
 * Ω_H = a / (2 M r_+)
 *
 * where r_+ is the outer horizon radius.
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Angular velocity [rad/s]
 */
inline double horizonAngularVelocity(double mass, double a) {
  double const rPlus = kerrOuterHorizon(mass, a);
  double const mGeo = G * mass / C2;

  // Ω_H in geometric units
  double const omegaGeom = a / (2.0 * mGeo * rPlus);

  // Convert to physical units [rad/s]
  return omegaGeom * C / mGeo;
}

/**
 * @brief Estimate magnetic field at horizon for BZ mechanism.
 *
 * B_H ~ sqrt(8π ρ v²) where ρ is gas density near horizon.
 *
 * For MAD state, magnetic pressure ~ gas pressure.
 *
 * @param jet Jet parameters
 * @return Magnetic field at horizon [Gauss]
 */
inline double horizonMagneticField(const JetParams &jet) {
  double const rPlus = kerrOuterHorizon(jet.mass, jet.a);

  // Gas density near horizon (rough estimate)
  // ρ ~ Ṁ / (4π r² v) where v ~ c
  double const rho = jet.mdot / (FOUR_PI * rPlus * rPlus * C);

  // For MAD: P_mag ~ P_gas ~ ρ c²
  double const pMag = rho * C2;

  // B = sqrt(8π P_mag)
  double b = std::sqrt(8.0 * PI * pMag);

  // MAD state has stronger fields
  if (jet.state == AccretionState::MAD) {
    b *= 2.0; // Enhancement factor
  }

  return b;
}

/**
 * @brief Compute Blandford-Znajek power.
 *
 * P_BZ ~ (B_H² r_+² c / 4π) Ω_H² f(a*)
 *
 * where f(a*) is a spin-dependent factor.
 *
 * Normalized form:
 * P_BZ / (Ṁ c²) = η_BZ ~ 0.01 to 0.4
 *
 * @param jet Jet parameters
 * @return Jet power [erg/s]
 */
inline double blandfordZnajekPower(const JetParams &jet) {
  double const rPlus = kerrOuterHorizon(jet.mass, jet.a);
  double const mGeo = G * jet.mass / C2;
  double const aStar = jet.a / mGeo;

  // Horizon angular velocity
  double const omegaH = horizonAngularVelocity(jet.mass, jet.a);

  // Magnetic field at horizon
  double const bH = horizonMagneticField(jet);

  // BZ power formula
  // P_BZ ~ (B_H² r_+² c / 4π) Ω_H² for a* ~ 1
  double const powerPrefactor = (bH * bH * rPlus * rPlus * C) / FOUR_PI;
  double const omegaFactor = omegaH * omegaH;

  // Spin-dependent enhancement: f(a*) ~ a*² for near-extremal
  double const spinFactor = aStar * aStar;

  double pBz = powerPrefactor * omegaFactor * spinFactor;

  // For MAD state, efficiency can be higher
  if (jet.state == AccretionState::MAD) {
    pBz *= 2.0; // MAD enhancement
  }

  return pBz;
}

/**
 * @brief Compute jet efficiency η = P_jet / (Ṁ c²).
 *
 * @param jet Jet parameters
 * @return Efficiency (0 to ~0.4)
 */
inline double jetEfficiency(const JetParams &jet) {
  double const pJet = blandfordZnajekPower(jet);
  double const pAccretion = jet.mdot * C2;

  double const eta = pJet / pAccretion;

  // Clamp to physical range
  return std::clamp(eta, 0.0, 0.4);
}

// ============================================================================
// Jet Geometry
// ============================================================================

/**
 * @brief Compute jet opening angle (state-dependent).
 *
 * MAD jets are more collimated due to strong magnetic fields.
 *
 * @param jet Jet parameters
 * @return Half-opening angle [rad]
 */
inline double jetOpeningAngle(const JetParams &jet) {
  // Base opening angle
  double theta = jet.openingAngle;

  // MAD jets are more collimated
  if (jet.state == AccretionState::MAD) {
    theta *= 0.7;  // 30% narrower
  } else if (jet.state == AccretionState::SANE) {
    theta *= 1.3;  // 30% wider
  }

  return theta;
}

/**
 * @brief Check if a point is inside the jet cone.
 *
 * @param r Radius from black hole [cm]
 * @param theta Polar angle from jet axis [rad]
 * @param jet Jet parameters
 * @return true if inside jet
 */
inline bool isInsideJet(double r, double theta, const JetParams &jet) {
  // Jet only exists above base distance
  if (r < jet.baseDistance) {
    return false;
  }

  // Conical jet
  double const halfAngle = jetOpeningAngle(jet);

  return (theta < halfAngle) || (theta > (PI - halfAngle));
}

/**
 * @brief Compute jet velocity at distance r.
 *
 * Jets accelerate from sub-relativistic at base to highly
 * relativistic at large distances.
 *
 * @param r Distance from black hole [cm]
 * @param jet Jet parameters
 * @return Lorentz factor Γ(r)
 */
inline double jetLorentzFactorAtRadius(double r, const JetParams &jet) {
  // Acceleration scale: ~10 times horizon radius
  double const rPlus = kerrOuterHorizon(jet.mass, jet.a);
  double const rAccel = 10.0 * rPlus;

  // At base: Γ ~ 2 (mildly relativistic)
  // At large r: Γ → Γ_∞ (terminal Lorentz factor)
  double const gammaBase = 2.0;
  double const gammaInf = jet.lorentzFactor;

  // Smooth acceleration profile
  double const x = (r - jet.baseDistance) / rAccel;
  double const gamma = gammaBase + ((gammaInf - gammaBase) * std::tanh(x));

  return gamma;
}

/**
 * @brief Compute jet velocity β = v/c.
 *
 * β = sqrt(1 - 1/Γ²)
 *
 * @param gamma Lorentz factor
 * @return Velocity in units of c
 */
inline double lorentzToBeta(double gamma) {
  if (gamma <= 1.0) {
    return 0.0;
  }
  return std::sqrt(1.0 - (1.0 / (gamma * gamma)));
}

/**
 * @brief Compute Doppler beaming factor.
 *
 * δ = 1 / (Γ(1 - β cos θ_obs))
 *
 * @param gamma Lorentz factor
 * @param thetaObs Viewing angle [rad]
 * @return Doppler factor
 */
inline double jetDopplerFactor(double gamma, double thetaObs) {
  double const beta = lorentzToBeta(gamma);
  double const cosTheta = std::cos(thetaObs);

  return 1.0 / (gamma * (1.0 - (beta * cosTheta)));
}

// ============================================================================
// Jet Emission
// ============================================================================

/**
 * @brief Compute synchrotron emissivity in jet.
 *
 * j_ν ∝ n_e B^(p+1)/2 ν^(-(p-1)/2)
 *
 * where n_e is electron density, B is magnetic field, p is power-law index.
 *
 * @param r Radius [cm]
 * @param theta Polar angle [rad]
 * @param nu Frequency [Hz]
 * @param jet Jet parameters
 * @return Emissivity [erg/(s cm³ Hz sr)]
 */
inline double jetSynchrotronEmissivity(double r, double theta, double nu, const JetParams &jet) {
  if (!isInsideJet(r, theta, jet)) {
    return 0.0;
  }

  // Magnetic field in jet (decreases with distance)
  double const rPlus = kerrOuterHorizon(jet.mass, jet.a);
  double const bBase = horizonMagneticField(jet);
  double const b = bBase * (rPlus / r); // B ∝ 1/r

  // Electron density (decreases as jet expands)
  double const nEBase = jet.mdot / (FOUR_PI * rPlus * rPlus * C * 9.109e-28); // Rough estimate
  double const nE = nEBase * (rPlus * rPlus) / (r * r);                       // n ∝ 1/r²

  // Power-law index
  double const p = 2.5; // Typical non-thermal
  double const alpha = (p - 1.0) / 2.0;

  // Synchrotron emissivity (simplified)
  double jNu = nE * std::pow(b, (p + 1.0) / 2.0) * std::pow(nu, -alpha);

  // Normalization constant (order of magnitude)
  jNu *= 1.0e-20;

  return jNu;
}

/**
 * @brief Compute observed flux from jet including Doppler boosting.
 *
 * F_obs = F_emit * δ^(3+α)
 *
 * @param r Radius [cm]
 * @param theta Polar angle [rad]
 * @param thetaObs Viewing angle [rad]
 * @param nu Frequency [Hz]
 * @param jet Jet parameters
 * @return Observed flux
 */
inline double jetObservedFlux(double r, double theta, double thetaObs, double nu,
                              const JetParams &jet) {
  // Intrinsic emissivity
  double const fEmit = jetSynchrotronEmissivity(r, theta, nu, jet);

  // Lorentz factor at this radius
  double const gamma = jetLorentzFactorAtRadius(r, jet);

  // Doppler factor
  double const delta = jetDopplerFactor(gamma, thetaObs);

  // Spectral index
  double const alpha = 0.7;

  // Doppler boosting: F_obs = F_emit * δ^(3+α)
  double const boost = std::pow(delta, 3.0 + alpha);

  return fEmit * boost;
}

// ============================================================================
// Jet Structure Visualization
// ============================================================================

/**
 * @brief Jet structure point for visualization.
 */
struct JetStructurePoint {
  double r;              ///< Distance from BH [cm]
  double theta;          ///< Polar angle [rad]
  double lorentzFactor;  ///< Local Γ
  double beta;           ///< Local β = v/c
  double emissivity;     ///< Synchrotron emissivity
  double bField;         ///< Magnetic field [Gauss]
};

/**
 * @brief Generate jet structure profile along axis.
 *
 * @param jet Jet parameters
 * @param nPoints Number of points
 * @return Vector of structure points
 */
inline std::vector<JetStructurePoint> jetStructureProfile(const JetParams &jet, int nPoints = 100) {
  std::vector<JetStructurePoint> profile;
  profile.reserve(static_cast<std::size_t>(nPoints));

  double const rPlus = kerrOuterHorizon(jet.mass, jet.a);
  double const rMin = jet.baseDistance;
  double const rMax = rMin * 1000.0; // Extend to 1000× base distance

  double const logRMin = std::log(rMin);
  double const logRMax = std::log(rMax);
  double const dLogR = (logRMax - logRMin) / (nPoints - 1);

  for (int i = 0; i < nPoints; ++i) {
    JetStructurePoint pt{};
    pt.r = std::exp(logRMin + (i * dLogR));
    pt.theta = 0.0;  // Along axis

    pt.lorentzFactor = jetLorentzFactorAtRadius(pt.r, jet);
    pt.beta = lorentzToBeta(pt.lorentzFactor);

    // Magnetic field
    double const bBase = horizonMagneticField(jet);
    pt.bField = bBase * (rPlus / pt.r);

    // Emissivity at 230 GHz
    pt.emissivity = jetSynchrotronEmissivity(pt.r, pt.theta, 230.0e9, jet);

    profile.push_back(pt);
  }

  return profile;
}

} // namespace physics

#endif // PHYSICS_JET_PHYSICS_H
