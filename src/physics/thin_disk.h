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
 *   F(r) = (3 G M Ṁ)/(8π r³) * f(r)
 *
 * where f(r) is the Page-Thorne relativistic factor of page_thorne.h, zero at
 * the ISCO and tending to 1 at large r.
 *
 * Temperature profile:
 *   T(r) = [F(r) / σ]^(1/4)
 *
 * Radiative efficiency:
 *   η = 1 - E_ISCO/c² = 0.0572 (Schwarzschild) to 0.3210 (a* = 0.998)
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

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <limits>
#include <numbers>
#include <vector>

#include "constants.h"
#include "kerr.h"
#include "page_thorne.h"

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
  double mass = 0.0;        ///< Black hole mass [g]
  double mDot = 0.0;        ///< Accretion rate [g/s]
  double a = 0.0;           ///< Spin parameter [cm]; negative for a retrograde disk
  double rIn = 0.0;         ///< Inner radius [cm] (typically ISCO)
  double rOut = 0.0;        ///< Outer radius [cm]
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
  disk.a = 0.0;

  // Eddington luminosity: L_Edd = 4pi G M m_p c / sigma_T
  const double lEdd = 1.26e38 * mSolar; // erg/s

  // Eddington accretion rate (assuming eta = 0.1)
  const double mDotEddCgs = lEdd / (0.1 * C2);
  disk.mDot = mDotEdd * mDotEddCgs;

  // Radii in cm
  const double rG = G * disk.mass / C2;
  disk.rIn = 6.0 * rG; // ISCO for Schwarzschild
  disk.rOut = rOutRg * rG;
  disk.inclination = 0.0;

  return disk;
}

/**
 * @brief Create disk parameters for Kerr black hole.
 *
 * The spin is signed (kerrIscoRadius convention): a* > 0 rotates with a disk
 * orbiting along +z and a* < 0 against it. prograde selects the disk's
 * orbital sense, +z (true) or -z (false); the -z disk around spin a* is the
 * +z disk around -a*.
 *
 * @param mSolar Black hole mass in solar masses
 * @param aStar Dimensionless signed spin (-1 to 1)
 * @param mDotEdd Accretion rate in Eddington units
 * @param prograde True for a disk orbiting along +z
 * @return DiskParams; disk.a is the spin relative to the disk's orbit,
 *         negative when the disk counter-rotates (8.717 M ISCO at a* = -0.9).
 */
[[nodiscard]] inline DiskParams kerrDisk(double mSolar, double aStar, double mDotEdd = 0.1,
                                         bool prograde = true) {
  DiskParams disk;
  disk.mass = mSolar * M_SUN;

  // Spin relative to the disk's orbital sense: disk.a > 0 co-rotates with the
  // disk and disk.a < 0 counter-rotates.
  const double mGeo = G * disk.mass / C2;
  // Clamped like the Page-Thorne flux (pageThorneSpin), so rIn below is the
  // flux's zero-torque edge at every input spin, including |aStar| = 1.
  const double aDisk = pageThorneSpin(prograde ? aStar : -aStar);
  disk.a = aDisk * mGeo;

  // Eddington rate at the Novikov-Thorne efficiency 1 - E_isco
  const double lEdd = 1.26e38 * mSolar;
  const double eta = novikovThorneEfficiency(aDisk);
  disk.mDot = mDotEdd * lEdd / (eta * C2);

  // ISCO of the disk at its relative spin (kerrIscoRadius convention).
  disk.rIn = kerrIscoRadius(disk.mass, disk.a, true);
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
  const double x = rG / r;

  if (r <= (3.0 * rG)) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  const double numerator = 1.0 - (2.0 * x);
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
  const double x = rG / r;

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
 * @brief Compute radiative flux from disk surface.
 *
 * F(r) = (3 G M Mdot)/(8pi r^3) * f(r)
 *
 * where f(r) is pageThorneRelativisticFactor at r/r_g and the signed spin
 * a/r_g, exact for every spin including Schwarzschild.
 *
 * @param r Radius [cm]
 * @param disk Disk parameters
 * @param profile Page-Thorne profile of disk (diskPageThorneProfile)
 * @return Radiative flux [erg/(cm^2 s)]
 */
[[nodiscard]] inline double diskFlux(double r, const DiskParams &disk,
                                     const PageThorneProfile &profile) {
  if (r < disk.rIn || r > disk.rOut) {
    return 0.0;
  }

  // Leading coefficient
  const double prefactor = (3.0 * G * disk.mass * disk.mDot) / (8.0 * std::numbers::pi * r * r * r);

  const double rM = r / (G * disk.mass / C2);
  return prefactor * (rM * rM * rM * profile.shape(rM));
}

/**
 * @brief Page-Thorne profile of a disk: its spin disk.a in units of r_g.
 */
[[nodiscard]] inline PageThorneProfile diskPageThorneProfile(const DiskParams &disk) {
  return PageThorneProfile(disk.a / (G * disk.mass / C2));
}

/**
 * @brief diskFlux with the disk's Page-Thorne profile built for this call.
 */
[[nodiscard]] inline double diskFlux(double r, const DiskParams &disk) {
  return diskFlux(r, disk, diskPageThorneProfile(disk));
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
  if (flux <= 0) {
    return 0.0;
  }
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
 * The peak is the Page-Thorne flux maximum (9.55 r_g at a = 0).
 *
 * @param disk Disk parameters
 * @param tMax Output: peak temperature [K]
 * @param rPeak Output: radius of peak [cm]
 */
inline void diskPeakTemperature(const DiskParams &disk, double &tMax, double &rPeak) {
  const double rG = G * disk.mass / C2;
  rPeak = std::max(pageThorneFluxPeakRadius(disk.a / rG) * rG, disk.rIn);

  // Ensure within disk bounds
  rPeak = std::min(rPeak, disk.rOut);

  tMax = diskTemperature(rPeak, disk);
}

// ============================================================================
// Disk Spectrum
// ============================================================================

// Thin-disk-local blackbody helper; canonical Doxygen entry lives in rte_integrator.h.
[[nodiscard]] inline double planckFunction(double nu, double tempK) {
  if (tempK <= 0 || nu <= 0) {
    return 0.0;
  }

  constexpr double h = 6.62607015e-27; // Planck constant [erg s]

  const double x = (h * nu) / (K_B * tempK);

  // Avoid overflow
  if (x > 700) {
    return 0.0;
  }

  const double prefactor = (2.0 * h * nu * nu * nu) / (C * C);
  return prefactor / std::expm1(x);
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
[[nodiscard]] inline double diskSpectrum(double nu, const DiskParams &disk, int nPoints = 100) {
  double sum = 0.0;
  const double logRIn = std::log(disk.rIn);
  const double logROut = std::log(disk.rOut);
  const double dLogR = (logROut - logRIn) / nPoints;

  for (int i = 0; i < nPoints; ++i) {
    const double logR = logRIn + ((i + 0.5) * dLogR);
    const double r = std::exp(logR);

    const double diskTemp = diskTemperature(r, disk);
    const double bNu = planckFunction(nu, diskTemp);

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
  // Efficiency from the ISCO binding energy of the disk's own spin:
  // 0.0572 at a = 0, 0.3210 at a* = 0.998.
  const double rG = G * disk.mass / C2;
  const double eta = novikovThorneEfficiency(disk.a / rG);

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
  const double x = (3.0 * rG) / r;

  if (x >= 1.0) {
    return 0.0;
  }
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
  const double v = std::sqrt(G * mass / r);
  const double beta = v / C;

  // Velocity component toward observer
  const double sinI = std::sin(inclination);
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
  const double g = diskRedshiftFactor(r, disk.mass);
  const double delta = diskDopplerFactor(r, phi, disk.inclination, disk.mass);

  // Combined factor: I_obs/I_emit = (g*delta)^4 for specific intensity
  const double factor = g * delta;
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
  double r = 0.0;           ///< Radius [cm]
  double rRg = 0.0;         ///< Radius in gravitational radii
  double flux = 0.0;        ///< Surface flux [erg/(cm^2 s)]
  double temperature = 0.0; ///< Temperature [K]
  double vOrb = 0.0;        ///< Orbital velocity [cm/s]
  double omega = 0.0;       ///< Angular velocity [rad/s]
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

  const double rG = G * disk.mass / C2;
  const double logRIn = std::log(disk.rIn);
  const double logROut = std::log(disk.rOut);
  const double dLogR = (logROut - logRIn) / (nPoints - 1);

  for (int i = 0; i < nPoints; ++i) {
    const double logR = logRIn + (i * dLogR);
    const double r = std::exp(logR);

    DiskProfilePoint pt;
    pt.r = r;
    pt.rRg = r / rG;
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
