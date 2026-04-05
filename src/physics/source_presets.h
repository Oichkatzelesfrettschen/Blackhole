/**
 * @file source_presets.h
 * @brief EHT source parameter presets for M87* and Sgr A*.
 *
 * Provides SourceParams struct and factory functions for standard
 * EHT calibration targets.  All internal quantities are CGS.
 *
 * References:
 *   - EHT Collaboration, ApJL 875, L6 (2019) -- M87* mass, distance
 *   - GRAVITY Collaboration, A&A 625, L10 (2019) -- Sgr A* distance
 *   - EHT Collaboration, ApJL 930, L12 (2022) -- Sgr A* mass
 */

#ifndef PHYSICS_SOURCE_PRESETS_H
#define PHYSICS_SOURCE_PRESETS_H

#include <string>

#include "constants.h"

namespace physics {

// Radians-to-microarcseconds conversion factor.
// 1 rad = 206264.806" = 206264.806e6 uas
inline constexpr double RAD_TO_UAS = 206264.806e6;

struct SourceParams {
  std::string name;
  double massMsun;       // black hole mass [solar masses]
  double spin;           // dimensionless Kerr parameter a* in [0,1)
  double distanceCm;     // observer distance [cm]
  double inclinationDeg; // observer inclination from spin axis [deg]
  double freqHz;         // observing frequency [Hz] (default 230 GHz)

  // Gravitational radius r_g = GM/c^2 [cm].
  [[nodiscard]] double rG() const { return G * massMsun * M_SUN / C2; }

  // Angular scale of one r_g as seen by the observer [microarcseconds].
  // theta = r_g / D  converted to uas.
  [[nodiscard]] double angularScaleUas() const { return (rG() / distanceCm) * RAD_TO_UAS; }

  // Approximate shadow diameter for a Schwarzschild (a*=0) black hole
  // [microarcseconds].  The photon ring has radius r_ph = 3 r_g giving
  // a critical impact parameter b_c = 3*sqrt(3) r_g ~ 5.196 r_g,
  // so the shadow diameter is ~10.39 r_g.  We use the conventional
  // rounded factor 10.4 r_g following EHT papers.
  [[nodiscard]] double shadowDiameterUas() const { return 10.4 * angularScaleUas(); }
};

// ---- Factory presets --------------------------------------------------------

// M87*: EHT Collaboration (2019).
// M = 6.5e9 Msun, D = 16.8 Mpc, a* = 0.9375 (EHT best-fit),
// inclination 17 deg, EHT band 230 GHz.
inline SourceParams sourceM87() {
  return SourceParams{
      .name = "M87*",
      .massMsun = 6.5e9,
      .spin = 0.9375,
      .distanceCm = 16.8 * MPC,
      .inclinationDeg = 17.0,
      .freqHz = 230.0e9,
  };
}

// Sgr A*: GRAVITY Collaboration (2019), EHT Collaboration (2022).
// M = 4.0e6 Msun, D = 8.178 kpc (GRAVITY 2019),
// a* = 0.5 (fiducial; observational range poorly constrained),
// inclination 30 deg (fiducial; plausible range 25-50 deg),
// EHT band 230 GHz.
inline SourceParams sourceSgra() {
  return SourceParams{
      .name = "Sgr A*",
      .massMsun = 4.0e6,
      .spin = 0.5,
      .distanceCm = 8.178e3 * PARSEC,
      .inclinationDeg = 30.0,
      .freqHz = 230.0e9,
  };
}

} // namespace physics

#endif // PHYSICS_SOURCE_PRESETS_H
