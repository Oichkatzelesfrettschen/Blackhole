/**
 * @file thin_disk.h
 * @brief Novikov-Thorne thin accretion disk model.
 *
 * The Novikov-Thorne (1973) model describes a geometrically thin,
 * optically thick accretion disk in the equatorial plane.
 *
 * Key assumptions:
 * - Disk is geometrically thin: H/r << 1
 * - Gas follows circular Keplerian orbits
 * - Viscous torque transports angular momentum outward
 * - Energy is radiated locally as blackbody
 * - Inner edge at ISCO (zero-torque boundary)
 *
 * Radiative flux (Page & Thorne 1974):
 *   F(r) = (3 G M Ṁ)/(8π r³) * (1 - √(r_ISCO/r)) * f(r)
 *
 * where f(r) contains relativistic corrections.
 *
 * Temperature profile:
 *   T(r) = [F(r) / σ]^(1/4)
 *
 * Radiative efficiency:
 *   η = 1 - E_ISCO/c² ≈ 0.057 (Schwarzschild) to 0.42 (maximal Kerr)
 *
 * References:
 * - Novikov & Thorne (1973), in "Black Holes"
 * - Page & Thorne (1974), ApJ 191, 499
 * - Shakura & Sunyaev (1973), A&A 24, 337
 *
 * Cleanroom implementation based on standard formulas.
 */

#ifndef PHYSICS_THIN_DISK_H
#define PHYSICS_THIN_DISK_H

#include "constants.h"
#include "kerr.h"
#include <algorithm>
#include <cmath>
#include <cstddef>
#include <limits>
#include <numbers>
#include <vector>

namespace physics {

// ============================================================================
// Physical Constants for Disk Physics
// ============================================================================

/// Stefan-Boltzmann constant [erg/(cm² s K⁴)]
constexpr double STEFAN_BOLTZMANN = 5.670374419e-5;

/// Radiation constant a = 4σ/c [erg/(cm³ K⁴)]
constexpr double RADIATION_CONSTANT = 4.0 * STEFAN_BOLTZMANN / C;

// ============================================================================
// Disk Parameters
// ============================================================================

/**
 * @brief Parameters for a thin accretion disk.
 */
struct DiskParams {
  double mass        = 0.0; ///< Black hole mass [g]
  double mDot        = 0.0; ///< Accretion rate [g/s]
  double a           = 0.0; ///< Spin parameter [cm] (0 for Schwarzschild)
  double rIn         = 0.0; ///< Inner radius [cm] (typically ISCO)
  double rOut        = 0.0; ///< Outer radius [cm]
  double inclination = 0.0; ///< Viewing inclination [rad]
};

/**
 * @brief Create disk parameters for Schwarzschild black hole.
 *
 * @param mSolar Black hole mass in solar masses
 * @param mDotEdd Accretion rate in Eddington units
 * @param rOutRg Outer radius in gravitational radii
 * @return DiskParams
 */
[[nodiscard]] inline DiskParams schwarzschildDisk(double mSolar, double mDotEdd = 0.1,
                                                   double rOutRg = 1000.0) {
  DiskParams disk;
  disk.mass = mSolar * M_SUN;
  disk.a    = 0.0;

  // Eddington luminosity: L_Edd = 4pi G M m_p c / sigma_T
  const double lEdd = 1.26e38 * mSolar; // erg/s

  // Eddington accretion rate (assuming eta = 0.1)
  const double mDotEddCgs = lEdd / (0.1 * C2);
  disk.mDot = mDotEdd * mDotEddCgs;

  // Radii in cm
  const double rG = G * disk.mass / C2;
  disk.rIn  = 6.0 * rG; // ISCO for Schwarzschild
  disk.rOut = rOutRg * rG;
  disk.inclination = 0.0;

  return disk;
}

/**
 * @brief Create disk parameters for Kerr black hole.
 *
 * @param mSolar Black hole mass in solar masses
 * @param aStar Dimensionless spin (-1 to 1)
 * @param mDotEdd Accretion rate in Eddington units
 * @param prograde True for prograde disk
 * @return DiskParams
 */
[[nodiscard]] inline DiskParams kerrDisk(double mSolar, double aStar,
                                          double mDotEdd = 0.1, bool prograde = true) {
  DiskParams disk;
  disk.mass = mSolar * M_SUN;

  // Spin parameter
  const double mGeo = G * disk.mass / C2;
  disk.a = aStar * mGeo;

  // Eddington rate
  const double lEdd = 1.26e38 * mSolar;
  double eta = 1.0 - std::sqrt(1.0 - (2.0 / 3.0)); // Approximate
  if (std::abs(aStar) > 0.9) {
    eta = 0.3; // Higher for high spin
  }
  disk.mDot = mDotEdd * lEdd / (eta * C2);

  // ISCO
  disk.rIn  = kerrIscoRadius(disk.mass, disk.a, prograde);
  disk.rOut = 1000.0 * mGeo;
  disk.inclination = 0.0;

  return disk;
}

// ============================================================================
// Novikov-Thorne Functions
// ============================================================================

/**
 * @brief Compute specific energy at radius r (Schwarzschild).
 *
 * E/c^2 = (1 - 2M/r) / sqrt(1 - 3M/r)
 *
 * @param r Radius [cm]
 * @param mass Black hole mass [g]
 * @return Specific energy (dimensionless, per unit rest mass)
 */
[[nodiscard]] inline double specificEnergySchwarzschild(double r, double mass) {
  const double rG = G * mass / C2;
  const double x  = rG / r;

  if (r <= (3.0 * rG)) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  const double numerator   = 1.0 - (2.0 * x);
  const double denominator = std::sqrt(1.0 - (3.0 * x));

  return numerator / denominator;
}

/**
 * @brief Compute specific angular momentum at radius r (Schwarzschild).
 *
 * L/(Mc) = sqrt(Mr) / sqrt(1 - 3M/r)
 *
 * @param r Radius [cm]
 * @param mass Black hole mass [g]
 * @return Specific angular momentum / (Mc)
 */
[[nodiscard]] inline double specificAngularMomentumSchwarzschild(double r, double mass) {
  const double rG = G * mass / C2;
  const double x  = rG / r;

  if (r <= (3.0 * rG)) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  return std::sqrt(rG * r) / std::sqrt(1.0 - (3.0 * x));
}

/**
 * @brief Compute angular velocity at radius r (Schwarzschild).
 *
 * Omega = sqrt(GM/r^3)
 *
 * @param r Radius [cm]
 * @param mass Black hole mass [g]
 * @return Angular velocity [rad/s]
 */
[[nodiscard]] inline double angularVelocitySchwarzschild(double r, double mass) {
  return std::sqrt(G * mass / (r * r * r));
}

/**
 * @brief Compute relativistic correction factor for flux.
 *
 * The Novikov-Thorne flux involves an integral:
 * f(r) = int[rIn to r] (L - L_in) dE/dr dr / (Omega(E - Omega L))
 *
 * For Schwarzschild, this has a closed-form solution.
 *
 * @param r Radius [cm]
 * @param rIn Inner radius [cm]
 * @param mass Black hole mass [g]
 * @return Correction factor (dimensionless)
 */
[[nodiscard]] inline double novikovThorneFactor(double r, double rIn, double mass) {
  const double rG = G * mass / C2;

  // Dimensionless radii
  const double x   = std::sqrt(r / rG);
  const double xIn = std::sqrt(rIn / rG);

  // Page & Thorne (1974) formula
  // Leading term: 1 - sqrt(rIn/r)
  const double term1 = 1.0 - std::sqrt(rIn / r);

  // First relativistic correction
  const double term2 = (3.0 / (2.0 * x * x)) * std::log(x / xIn);

  // Higher-order terms (simplified)
  const double term3 = -(3.0 * (x - xIn)) / (x * x * xIn);

  return (term1 - term2) + term3;
}

/**
 * @brief Compute radiative flux from disk surface.
 *
 * F(r) = (3 G M Mdot)/(8pi r^3) * f(r)
 *
 * where f(r) is the relativistic correction.
 *
 * @param r Radius [cm]
 * @param disk Disk parameters
 * @return Radiative flux [erg/(cm^2 s)]
 */
[[nodiscard]] inline double diskFlux(double r, const DiskParams &disk) {
  if (r < disk.rIn || r > disk.rOut) {
    return 0.0;
  }

  // Leading coefficient
  const double prefactor = (3.0 * G * disk.mass * disk.mDot) / (8.0 * std::numbers::pi * r * r * r);

  // Relativistic correction
  double fR = 0.0;
  if (std::abs(disk.a) < 1e-10) {
    // Schwarzschild
    fR = novikovThorneFactor(r, disk.rIn, disk.mass);
  } else {
    // Kerr - simplified approximation
    const double rG       = G * disk.mass / C2;
    const double basic    = 1.0 - std::sqrt(disk.rIn / r);
    const double aStar    = disk.a / rG;
    const double spinFactor = 1.0 + (0.5 * aStar * std::sqrt(rG / r));
    fR = basic * spinFactor;
  }

  return prefactor * fR;
}

/**
 * @brief Compute disk temperature from flux.
 *
 * T(r) = [F(r) / sigma]^(1/4)
 *
 * @param flux Radiative flux [erg/(cm^2 s)]
 * @return Temperature [K]
 */
[[nodiscard]] inline double diskTemperatureFromFlux(double flux) {
  if (flux <= 0) { return 0.0; }
  return std::pow(flux / STEFAN_BOLTZMANN, 0.25);
}

/**
 * @brief Compute disk temperature at radius r.
 *
 * @param r Radius [cm]
 * @param disk Disk parameters
 * @return Temperature [K]
 */
[[nodiscard]] inline double diskTemperature(double r, const DiskParams &disk) {
  const double flux = diskFlux(r, disk);
  return diskTemperatureFromFlux(flux);
}

/**
 * @brief Compute peak temperature and its radius.
 *
 * For Schwarzschild: T_max at r ~ 49/12 * r_ISCO
 *
 * @param disk Disk parameters
 * @param tMax Output: peak temperature [K]
 * @param rPeak Output: radius of peak [cm]
 */
inline void diskPeakTemperature(const DiskParams &disk,
                                 double &tMax, double &rPeak) {
  // Peak is roughly at (49/12) * rIn for Schwarzschild
  rPeak = (49.0 / 12.0) * disk.rIn;

  // Ensure within disk bounds
  rPeak = std::min(rPeak, disk.rOut);

  tMax = diskTemperature(rPeak, disk);
}

// ============================================================================
// Disk Spectrum
// ============================================================================

/**
 * @brief Compute Planck function at temperature T.
 *
 * B_nu(T) = (2h nu^3/c^2) / (exp(h*nu/kT) - 1)
 *
 * @param nu Frequency [Hz]
 * @param T Temperature [K]
 * @return Specific intensity [erg/(s cm^2 Hz sr)]
 */
[[nodiscard]] inline double planckFunction(double nu, double tempK) {
  if (tempK <= 0 || nu <= 0) { return 0.0; }

  constexpr double h = 6.62607015e-27; // Planck constant [erg s]

  const double x = (h * nu) / (K_B * tempK);

  // Avoid overflow
  if (x > 700) { return 0.0; }

  const double prefactor = (2.0 * h * nu * nu * nu) / (C * C);
  return prefactor / (std::exp(x) - 1.0);
}

/**
 * @brief Compute disk spectrum at frequency nu.
 *
 * Integrates blackbody emission over the disk:
 * L_nu = 4pi cos(i) int B_nu(T(r)) 2pi*r dr
 *
 * @param nu Frequency [Hz]
 * @param disk Disk parameters
 * @param nPoints Number of integration points
 * @return Specific luminosity [erg/(s Hz)]
 */
[[nodiscard]] inline double diskSpectrum(double nu, const DiskParams &disk,
                                          int nPoints = 100) {
  double sum = 0.0;
  const double logRIn  = std::log(disk.rIn);
  const double logROut = std::log(disk.rOut);
  const double dLogR   = (logROut - logRIn) / nPoints;

  for (int i = 0; i < nPoints; ++i) {
    const double logR = logRIn + ((i + 0.5) * dLogR);
    const double r    = std::exp(logR);

    const double diskTemp = diskTemperature(r, disk);
    const double bNu  = planckFunction(nu, diskTemp);

    // Integrate r dr = r^2 d(log r)
    sum += bNu * r * r * dLogR;
  }

  // Factor of 2 for both sides, cos(i) for projection
  return (4.0 * std::numbers::pi * std::cos(disk.inclination)) * (2.0 * std::numbers::pi * sum);
}

/**
 * @brief Compute bolometric disk luminosity.
 *
 * L = eta * Mdot * c^2
 *
 * where eta is the radiative efficiency.
 *
 * @param disk Disk parameters
 * @return Luminosity [erg/s]
 */
[[nodiscard]] inline double diskLuminosity(const DiskParams &disk) {
  const double rIsco = disk.rIn;

  // Efficiency from ISCO binding energy
  // E_ISCO/c^2 for Schwarzschild: 1 - sqrt(8/9) ~ 0.0572
  const double eIsco = specificEnergySchwarzschild(rIsco, disk.mass);
  const double eta   = 1.0 - eIsco;

  return eta * disk.mDot * C2;
}

// ============================================================================
// Relativistic Effects
// ============================================================================

/**
 * @brief Compute gravitational redshift factor for disk emission.
 *
 * g = sqrt(1 - 3M/r)
 *
 * @param r Emission radius [cm]
 * @param mass Black hole mass [g]
 * @return Redshift factor (0-1)
 */
[[nodiscard]] inline double diskRedshiftFactor(double r, double mass) {
  const double rG = G * mass / C2;
  const double x  = (3.0 * rG) / r;

  if (x >= 1.0) { return 0.0; }
  return std::sqrt(1.0 - x);
}

/**
 * @brief Compute Doppler factor for orbiting disk element.
 *
 * delta = 1 / (gamma*(1 - beta*cos(phi)))
 *
 * where gamma = 1/sqrt(1-beta^2), beta = v/c
 *
 * @param r Orbital radius [cm]
 * @param phi Azimuthal angle relative to observer [rad]
 * @param inclination Disk inclination [rad]
 * @param mass Black hole mass [g]
 * @return Doppler factor
 */
[[nodiscard]] inline double diskDopplerFactor(double r, double phi, double inclination,
                                               double mass) {
  // Orbital velocity
  const double v    = std::sqrt(G * mass / r);
  const double beta = v / C;

  // Velocity component toward observer
  const double sinI    = std::sin(inclination);
  const double betaLos = beta * std::sin(phi) * sinI;

  // Lorentz factor
  const double gamma = 1.0 / std::sqrt(1.0 - (beta * beta));

  return 1.0 / (gamma * (1.0 - betaLos));
}

/**
 * @brief Compute observed flux including relativistic effects.
 *
 * F_obs = F_emit * g^4 * delta^4
 *
 * @param r Emission radius [cm]
 * @param phi Azimuthal angle [rad]
 * @param disk Disk parameters
 * @return Observed flux [erg/(cm^2 s)]
 */
[[nodiscard]] inline double diskFluxObserved(double r, double phi, const DiskParams &disk) {
  const double fEmit = diskFlux(r, disk);
  const double g     = diskRedshiftFactor(r, disk.mass);
  const double delta = diskDopplerFactor(r, phi, disk.inclination, disk.mass);

  // Combined factor: I_obs/I_emit = (g*delta)^4 for specific intensity
  const double factor  = g * delta;
  const double factor4 = factor * factor * factor * factor;

  return fEmit * factor4;
}

// ============================================================================
// Disk Structure (for visualization)
// ============================================================================

/**
 * @brief Radial profile point.
 */
struct DiskProfilePoint {
  double r           = 0.0; ///< Radius [cm]
  double rRg         = 0.0; ///< Radius in gravitational radii
  double flux        = 0.0; ///< Surface flux [erg/(cm^2 s)]
  double temperature = 0.0; ///< Temperature [K]
  double vOrb        = 0.0; ///< Orbital velocity [cm/s]
  double omega       = 0.0; ///< Angular velocity [rad/s]
};

/**
 * @brief Generate radial profile of disk.
 *
 * @param disk Disk parameters
 * @param nPoints Number of radial points
 * @return Vector of profile points
 */
[[nodiscard]] inline std::vector<DiskProfilePoint> diskProfile(const DiskParams &disk,
                                                                int nPoints = 100) {
  std::vector<DiskProfilePoint> profile;
  if (nPoints <= 0) {
    return profile;
  }
  profile.reserve(static_cast<std::size_t>(nPoints));

  const double rG     = G * disk.mass / C2;
  const double logRIn  = std::log(disk.rIn);
  const double logROut = std::log(disk.rOut);
  const double dLogR   = (logROut - logRIn) / (nPoints - 1);

  for (int i = 0; i < nPoints; ++i) {
    const double logR = logRIn + (i * dLogR);
    const double r    = std::exp(logR);

    DiskProfilePoint pt;
    pt.r    = r;
    pt.rRg  = r / rG;
    pt.flux = diskFlux(r, disk);
    pt.temperature = diskTemperatureFromFlux(pt.flux);
    pt.vOrb = std::sqrt(G * disk.mass / r);
    pt.omega = angularVelocitySchwarzschild(r, disk.mass);

    profile.push_back(pt);
  }

  return profile;
}

// ============================================================================
// Color Temperature Mapping
// ============================================================================

/**
 * @brief Convert temperature to RGB color (approximate blackbody).
 *
 * Uses Planckian locus approximation for T > 1000 K.
 *
 * @param tempK Temperature [K]
 * @param outR Output: red (0-1)
 * @param outG Output: green (0-1)
 * @param outB Output: blue (0-1)
 */
inline void temperatureToRgb(double tempK, double &outR, double &outG, double &outB) {
  // Clamp temperature range
  const double tClamped = std::clamp(tempK, 1000.0, 40000.0);
  const double t = tClamped / 100.0;

  // Red
  if (tClamped <= 6600) {
    outR = 1.0;
  } else {
    outR = std::clamp(329.698727446 * std::pow(t - 60.0, -0.1332047592) / 255.0, 0.0, 1.0);
  }

  // Green
  if (tClamped <= 6600) {
    outG = (99.4708025861 * std::log(t)) - 161.1195681661;
  } else {
    outG = 288.1221695283 * std::pow(t - 60.0, -0.0755148492);
  }
  outG = std::clamp(outG / 255.0, 0.0, 1.0);

  // Blue
  if (tClamped >= 6600) {
    outB = 1.0;
  } else if (tClamped <= 1900) {
    outB = 0.0;
  } else {
    outB = std::clamp((138.5177312231 * std::log(t - 10.0)) - 305.0447927307, 0.0, 255.0) / 255.0;
  }
}

} // namespace physics

#endif // PHYSICS_THIN_DISK_H
