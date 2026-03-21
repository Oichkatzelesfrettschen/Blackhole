/**
 * @file src/physics/iron_kline.h
 * @brief Relativistically broadened Fe K-alpha emission line profile (Laor 1991).
 *
 * WHY: The Fe K-alpha line at 6.4 keV is the primary observable for black hole
 *      spin measurement in X-ray binaries and AGN.  Gravitational redshift from
 *      the ISCO plus Doppler broadening from disk rotation produce a skewed red
 *      wing whose shape encodes spin.  Without this, the simulation cannot
 *      produce synthetic X-ray spectra for RXTE/XMM/NuSTAR/XRISM comparison.
 *
 * WHAT: Laor (1991) / Cunningham (1975) g-factor for circular equatorial Kerr
 *       orbits.  2D (r, phi) disk integration with power-law emissivity
 *       epsilon(r) ~ r^{-q}.  Returns F(E/E_0) normalized so the integral = 1.
 *
 * HOW:  g-factor (energy shift from disk frame to observer at infinity):
 *
 *   g(r, phi, iota) = sqrt(1 - 3/r + 2*a/r^{3/2})
 *                   / (1 - sin(phi)*sin(iota) / (sqrt(r) + a/r))
 *
 *   where r in units of GM/c^2, a = dimensionless spin in [0, 1),
 *   iota = observer inclination from polar axis [rad].
 *
 *   Derivation: g = 1 / (u^t_em * (1 - Omega * b)),  where
 *     u^t_em = 1/sqrt(f(r)),  f(r) = 1 - 3/r + 2*a/r^{3/2}
 *     Omega  = 1 / (r^{3/2} + a)  [prograde Keplerian angular velocity, M=1]
 *     b      = r * sin(phi) * sin(iota)  [photon impact parameter, far-field]
 *
 *   Flux weighting: g^4 * epsilon(r) * r (from Lorentz invariant I/nu^3 = const
 *   plus photon bunching; see Fabian et al. 1989 MNRAS 238, 729).
 *
 * References:
 *   - Laor (1991) ApJ 376, 90
 *   - Fabian, Rees, Stella & White (1989) MNRAS 238, 729
 *   - Cunningham (1975) ApJ 202, 788
 *   - Reynolds (2021) ARA&A 59, 117  [review of BH spin via Fe K-alpha]
 */

#ifndef PHYSICS_IRON_KLINE_H
#define PHYSICS_IRON_KLINE_H

#include <algorithm>
#include <cassert>
#include <cmath>
#include <numbers>
#include <utility>
#include <vector>

#include "constants.h"
#include "safe_limits.h"

namespace physics {

// ============================================================================
// ISCO in geometrized units (M = G = c = 1)
// ============================================================================

/**
 * @brief Prograde ISCO radius in units of GM/c^2 for dimensionless spin a*.
 *
 * Uses the Bardeen-Press-Teukolsky (1972) formula.
 *
 * @param aStar Dimensionless spin a* = a*c/(G*M) in [0, 1).
 * @return r_isco / M  [dimensionless]
 */
[[nodiscard]] inline double iscoGeom(double aStar) noexcept {
    if (aStar < 0.0 || aStar >= 1.0) {
        return 6.0;  // Schwarzschild limit as safe fallback
    }
    const double z1 = 1.0 + (std::cbrt(1.0 - (aStar * aStar)) *
                             (std::cbrt(1.0 + aStar) + std::cbrt(1.0 - aStar)));
    const double z2 = std::sqrt((3.0 * aStar * aStar) + (z1 * z1));
    return 3.0 + z2 - std::sqrt((3.0 - z1) * (3.0 + z1 + (2.0 * z2)));
}

// ============================================================================
// Disk g-factor
// ============================================================================

/**
 * @brief Energy shift g = E_obs/E_em for a circular Kerr orbit at (r, phi).
 *
 * Valid for r >= r_isco > 0, a in [0, 1), iota in [0, pi/2].
 *
 * @param r     Disk radius [GM/c^2]
 * @param phi   Azimuthal angle [rad] (phi=pi/2 is the approaching side)
 * @param aStar Dimensionless BH spin a* in [0, 1)
 * @param iota  Observer inclination from polar axis [rad]
 * @return g-factor (>0; g<1 = redshifted, g>1 = blueshifted)
 */
[[nodiscard]] inline double kerrDiskGFactor(double r, double phi,
                                             double aStar, double iota) noexcept {
    if (r <= 0.0) {
        return 0.0;
    }
    const double sqrtR = std::sqrt(r);
    // Stability factor f(r) = 1 - 3/r + 2a/r^{3/2}
    const double f = 1.0 - (3.0 / r) + (2.0 * aStar / (r * sqrtR));
    if (f <= 0.0) {
        return 0.0;  // Below or at ISCO (marginally stable orbit)
    }
    // Omega * r = 1 / (sqrt(r) + a/r)
    const double omegaR = 1.0 / (sqrtR + (aStar / r));
    const double denom  = 1.0 - (std::sin(phi) * std::sin(iota) * omegaR);
    if (denom <= 0.0) {
        return 0.0;  // Caustic (unphysical for r >= r_isco)
    }
    return std::sqrt(f) / denom;
}

// ============================================================================
// Line profile computation
// ============================================================================

/**
 * @brief Parameters for the Fe K-alpha line profile.
 */
struct IronKLineParams {
    double aStar         = 0.0;   ///< Dimensionless BH spin a* in [0, 1)
    double inclination   = 0.3;   ///< Observer inclination from polar axis [rad]
    double rIn           = 0.0;   ///< Inner disk radius [M] (0 = ISCO)
    double rOut          = 400.0; ///< Outer disk radius [M]
    double emissivityQ   = 3.0;   ///< Emissivity power-law index (epsilon ~ r^{-q})
    double lineEnergyKeV = 6.4;   ///< Rest-frame line energy [keV] (Fe K-alpha)
    int    nEnergy       = 200;   ///< Number of energy bins
    int    nR            = 200;   ///< Radial quadrature points
    int    nPhi          = 400;   ///< Azimuthal quadrature points
};

/**
 * @brief Compute the relativistically broadened Fe K-alpha line profile.
 *
 * Performs 2-D (r, phi) numerical integration over the disk:
 *
 *   F(g) ∝ sum_{r,phi} g(r,phi)^4 * epsilon(r) * r * Delta_r * Delta_phi
 *
 * The result is normalized so that sum_i F_i * Delta_g_i = 1 (unit integral).
 *
 * @param params  Profile parameters (spin, inclination, emissivity index, ...)
 * @return Vector of (E_obs [keV], normalized_flux) pairs over the line energy range.
 */
[[nodiscard]] inline std::vector<std::pair<double, double>>
ironKLineProfile(const IronKLineParams &params) {
    const double rISCO = iscoGeom(params.aStar);
    const double rIn   = (params.rIn <= 0.0) ? rISCO : std::max(params.rIn, rISCO);
    const double rOut  = std::max(rIn + 1.0, params.rOut);

    const int nR   = std::max(params.nR,   50);
    const int nPhi = std::max(params.nPhi, 100);
    const int nE   = std::max(params.nEnergy, 50);

    // Radial grid: logarithmic spacing from rIn to rOut
    const double logRIn  = std::log(rIn);
    const double logROut = std::log(rOut);
    const double dLogR   = (logROut - logRIn) / static_cast<double>(nR);

    // Azimuthal grid: uniform in [0, 2*pi)
    const double dPhi = (2.0 * std::numbers::pi) / static_cast<double>(nPhi);

    // First pass: determine g range and total weight
    double gMin = 1.0e30;
    double gMax = -1.0e30;
    double totalWeight = 0.0;

    for (int ir = 0; ir < nR; ++ir) {
        const double r          = std::exp(logRIn + ((static_cast<double>(ir) + 0.5) * dLogR));
        const double emissivity = std::pow(r, -params.emissivityQ);
        const double rWeight    = (r * r) * dLogR;  // r*dr = r^2*dLogR for log grid
        for (int ip = 0; ip < nPhi; ++ip) {
            const double phi = (static_cast<double>(ip) + 0.5) * dPhi;
            const double g   = kerrDiskGFactor(r, phi, params.aStar, params.inclination);
            if (g <= 0.0) {
                continue;
            }
            gMin = std::min(gMin, g);
            gMax = std::max(gMax, g);
            totalWeight += ((g * g * g * g) * emissivity * rWeight * dPhi);
        }
    }

    if (totalWeight <= 0.0 || gMin >= gMax) {
        return {};
    }

    // Add 1% margin to avoid edge-bin truncation
    const double gLo = gMin * 0.99;
    const double gHi = gMax * 1.01;
    const double dg  = (gHi - gLo) / static_cast<double>(nE);

    // Initialize flux bins
    std::vector<double> flux(static_cast<std::size_t>(nE), 0.0);

    // Second pass: accumulate flux into bins
    for (int ir = 0; ir < nR; ++ir) {
        const double r          = std::exp(logRIn + ((static_cast<double>(ir) + 0.5) * dLogR));
        const double emissivity  = std::pow(r, -params.emissivityQ);
        const double rWeight    = (r * r) * dLogR;
        for (int ip = 0; ip < nPhi; ++ip) {
            const double phi = ((static_cast<double>(ip) + 0.5) * dPhi);
            const double g   = kerrDiskGFactor(r, phi, params.aStar, params.inclination);
            if (g <= 0.0) {
                continue;
            }
            const int bin = static_cast<int>((g - gLo) / dg);
            if (bin < 0 || bin >= nE) {
                continue;
            }
            flux.at(static_cast<std::size_t>(bin)) +=
                ((g * g * g * g) * emissivity * rWeight * dPhi);
        }
    }

    // Normalize so integral = 1 (sum over bins * dg = 1)
    double integral = 0.0;
    for (const double f : flux) {
        integral += f;
    }
    integral *= dg;

    if (integral <= 0.0) {
        return {};
    }

    const double norm = 1.0 / integral;

    // Build output: (E_obs [keV], normalized_flux)
    std::vector<std::pair<double, double>> result;
    result.reserve(static_cast<std::size_t>(nE));
    for (int i = 0; i < nE; ++i) {
        const double gBin = gLo + ((static_cast<double>(i) + 0.5) * dg);
        const double eObs = gBin * params.lineEnergyKeV;
        result.emplace_back(eObs, flux.at(static_cast<std::size_t>(i)) * norm);
    }

    return result;
}

/**
 * @brief Minimum g-factor (maximum redshift) at the prograde ISCO.
 *
 * For face-on inclination (iota=0), all disk emission at r_isco has:
 *   g_min = sqrt(1 - 3/r_isco + 2*a/r_isco^{3/2})
 *
 * This is the characteristic "red edge" of the Fe K-alpha profile.
 *
 * @param aStar Dimensionless spin in [0, 1)
 * @return g-factor at r_isco, face-on  (in [0, 1])
 */
[[nodiscard]] inline double ironKLineGMin(double aStar) noexcept {
    const double r    = iscoGeom(aStar);
    const double sqrtR = std::sqrt(r);
    const double f    = 1.0 - (3.0 / r) + (2.0 * aStar / (r * sqrtR));
    return (f > 0.0) ? std::sqrt(f) : 0.0;
}

} // namespace physics

#endif /* PHYSICS_IRON_KLINE_H */
