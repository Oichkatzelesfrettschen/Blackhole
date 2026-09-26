/**
 * @file kerr.h
 * @brief Kerr spacetime metric for rotating black holes.
 *
 * The Kerr metric describes spacetime around a rotating, uncharged black hole:
 *
 *   ds^2 = -(1 - r_s r/Sigma)c^2 dt^2 - (2 r_s r a sin^2 theta / Sigma) c dt dphi
 *        + (Sigma/Delta) dr^2 + Sigma dtheta^2
 *        + (r^2 + a^2 + r_s r a^2 sin^2 theta / Sigma) sin^2 theta dphi^2
 *
 * where:
 *   a = J/(Mc) = spin parameter [cm]
 *   Sigma = r^2 + a^2 cos^2 theta
 *   Delta = r^2 - r_s r + a^2
 *   r_s = 2GM/c^2 = Schwarzschild radius
 *
 * Key features:
 *   - Reduces to Schwarzschild when a = 0
 *   - Has inner (r_-) and outer (r_+) horizons
 *   - Ergosphere where frame-dragging is mandatory
 *   - Spin-dependent ISCO and photon orbits
 *
 * References:
 *   - Bardeen, Press, Teukolsky (1972) for ISCO formulas
 *   - Chandrasekhar "Mathematical Theory of Black Holes"
 *
 * Cleanroom implementation based on standard GR textbook formulas.
 */

#ifndef PHYSICS_KERR_H
#define PHYSICS_KERR_H

#include <cmath>
#include <limits>
#include <optional>
#include <utility>

#include "constants.h"
#include "safe_limits.h"
#include "schwarzschild.h"

namespace physics {

// ============================================================================
// Kerr Metric Functions
// ============================================================================

/**
 * @brief Compute spin parameter from angular momentum.
 *
 * a = J/(Mc) where J is angular momentum
 *
 * @param angMomentum Angular momentum [g cm^2/s]
 * @param mass Black hole mass [g]
 * @return Spin parameter a [cm]
 */
[[nodiscard]] inline double spinParameter(double angMomentum, double mass) {
  return angMomentum / (mass * C);
}

/**
 * @brief Compute dimensionless spin from spin parameter.
 *
 * a* = a/M = Jc/(GM^2) where 0 <= |a*| <= 1
 *
 * @param a Spin parameter [cm]
 * @param mass Black hole mass [g]
 * @return Dimensionless spin a* (unitless)
 */
[[nodiscard]] inline double dimensionlessSpin(double a, double mass) {
  const double mGeom = G * mass / C2; // Geometric mass in cm
  return a / mGeom;
}

/**
 * @brief Convert dimensionless spin to physical spin parameter.
 *
 * a = a* * GM/c^2
 *
 * @param mass Black hole mass [g]
 * @param aStar Dimensionless spin (unitless)
 * @return Spin parameter a [cm]
 */
[[nodiscard]] inline double spinFromDimensionless(double mass, double aStar) {
  const double mGeom = G * mass / C2; // Geometric mass in cm
  return aStar * mGeom;
}

/**
 * @brief Compute Kerr metric Sigma function.
 *
 * Sigma = r^2 + a^2 cos^2 theta
 *
 * @param r Radial coordinate [cm]
 * @param a Spin parameter [cm]
 * @param theta Polar angle [rad]
 * @return Sigma [cm^2]
 */
[[nodiscard]] inline double kerrSigma(double r, double a, double theta) {
  const double cosTheta = std::cos(theta);
  return (r * r) + (a * a * cosTheta * cosTheta);
}

/**
 * @brief Compute Kerr metric Delta function.
 *
 * Delta = r^2 - r_s r + a^2 = (r - r_+)(r - r_-)
 *
 * Horizons exist where Delta = 0.
 *
 * @param r Radial coordinate [cm]
 * @param a Spin parameter [cm]
 * @param rS Schwarzschild radius [cm]
 * @return Delta [cm^2]
 */
[[nodiscard]] inline double kerrDelta(double r, double a, double rS) {
  return (r * r) - (rS * r) + (a * a);
}

// ============================================================================
// Horizon Radii
// ============================================================================

/**
 * @brief Compute outer (event) horizon radius.
 *
 * r_+ = (r_s/2) + sqrt((r_s/2)^2 - a^2) = M + sqrt(M^2 - a^2)
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Outer horizon radius [cm], NaN if a > M (naked singularity)
 */
[[nodiscard]] inline double kerrOuterHorizon(double mass, double a) {
  const double mGeom = G * mass / C2; // Geometric mass
  const double discriminant = (mGeom * mGeom) - (a * a);
  if (discriminant < 0) {
    return std::numeric_limits<double>::quiet_NaN(); // Naked singularity
  }
  return mGeom + std::sqrt(discriminant);
}

/**
 * @brief Compute inner (Cauchy) horizon radius.
 *
 * r_- = (r_s/2) - sqrt((r_s/2)^2 - a^2) = M - sqrt(M^2 - a^2)
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Inner horizon radius [cm], NaN if a > M
 */
[[nodiscard]] inline double kerrInnerHorizon(double mass, double a) {
  const double mGeom = G * mass / C2;
  const double discriminant = (mGeom * mGeom) - (a * a);
  if (discriminant < 0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return mGeom - std::sqrt(discriminant);
}

/**
 * @brief Compute Kerr horizon radii.
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Pair {r_outer, r_inner} [cm]
 */
[[nodiscard]] inline std::pair<double, double> kerrHorizons(double mass, double a) {
  return {kerrOuterHorizon(mass, a), kerrInnerHorizon(mass, a)};
}

// ============================================================================
// Ergosphere
// ============================================================================

/**
 * @brief Compute ergosphere outer boundary.
 *
 * r_ergo(theta) = M + sqrt(M^2 - a^2 cos^2 theta)
 *
 * Inside the ergosphere, no static observer can exist.
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @param theta Polar angle [rad]
 * @return Ergosphere radius [cm]
 */
[[nodiscard]] inline double ergosphereRadius(double mass, double a, double theta) {
  const double mGeom = G * mass / C2;
  const double cosTheta = std::cos(theta);
  const double discriminant = (mGeom * mGeom) - (a * a * cosTheta * cosTheta);
  if (discriminant < 0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return mGeom + std::sqrt(discriminant);
}

// ============================================================================
// ISCO (Innermost Stable Circular Orbit) - Bardeen-Press-Teukolsky 1972
// ============================================================================

/**
 * @brief Compute ISCO radius for equatorial orbits.
 *
 * Uses the Bardeen-Press-Teukolsky (1972) formula.
 *
 * r_ISCO/M = 3 + Z2 -/+ sqrt((3 - Z1)(3 + Z1 + 2Z2))
 *
 * where:
 *   Z1 = 1 + (1 - a*^2)^(1/3) * ((1 + a*)^(1/3) + (1 - a*)^(1/3))
 *   Z2 = sqrt(3 a*^2 + Z1^2)
 *
 * Signed-spin convention, shared with kerrPhotonOrbitPrograde/Retrograde and
 * novikov_thorne::iscoRadius: a > 0 rotates about +z, a < 0 about -z, and
 * "prograde" names an orbit with angular momentum along +z. The minus sign
 * applies when the orbit co-rotates with the hole (a * L_z > 0), the plus sign
 * when it counter-rotates, so kerrIscoRadius(m, -a, true) ==
 * kerrIscoRadius(m, a, false). At a* = -0.9 the prograde ISCO is 8.7174 M.
 *
 * @param mass Black hole mass [g]
 * @param a Signed spin parameter [cm]
 * @param prograde true for angular momentum along +z, false along -z
 * @return ISCO radius [cm]
 */
[[nodiscard]] inline double kerrIscoRadius(double mass, double a, bool prograde = true) {
  const double mGeom = G * mass / C2; // Geometric mass in cm
  const double aStar = a / mGeom;     // Dimensionless spin

  if (std::abs(aStar) > 1.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  // BPT formula
  const double oneMinusA2 = 1.0 - (aStar * aStar);
  const double cbrtFactor = std::cbrt(oneMinusA2);
  const double cbrtPlus = std::cbrt(1.0 + aStar);
  const double cbrtMinus = std::cbrt(1.0 - aStar);

  const double z1 = 1.0 + (cbrtFactor * (cbrtPlus + cbrtMinus));
  const double z2 = std::sqrt((3.0 * aStar * aStar) + (z1 * z1));

  const double sqrtTerm = std::sqrt((3.0 - z1) * (3.0 + z1 + (2.0 * z2)));

  // Co-rotating orbit: minus sign; counter-rotating: plus sign. At a* = 0 the
  // square-root term vanishes and both give 6M.
  const bool coRotating = prograde ? (aStar >= 0.0) : (aStar <= 0.0);
  const double rIscoOverM = coRotating ? (3.0 + z2 - sqrtTerm) : (3.0 + z2 + sqrtTerm);

  return rIscoOverM * mGeom;
}

// ============================================================================
// Photon Orbits
// ============================================================================

/**
 * @brief Compute prograde photon orbit radius (angular momentum along +z).
 *
 * r_ph = 2M(1 + cos(2/3 * arccos(-a*)))
 *
 * Signed spin as in kerrIscoRadius: at a* < 0 the +z orbit counter-rotates
 * (3.9103 M at a* = -0.9).
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Prograde photon orbit radius [cm]
 */
[[nodiscard]] inline double kerrPhotonOrbitPrograde(double mass, double a) {
  const double mGeom = G * mass / C2;
  const double aStar = a / mGeom;
  if (std::abs(aStar) > 1.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  const double angle = (2.0 / 3.0) * std::acos(-aStar);
  return 2.0 * mGeom * (1.0 + std::cos(angle));
}

/**
 * @brief Compute retrograde photon orbit radius (angular momentum along -z).
 *
 * r_ph = 2M(1 + cos(2/3 * arccos(a*)))
 *
 * Signed spin as in kerrIscoRadius: at a* < 0 the -z orbit co-rotates.
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Retrograde photon orbit radius [cm]
 */
[[nodiscard]] inline double kerrPhotonOrbitRetrograde(double mass, double a) {
  const double mGeom = G * mass / C2;
  const double aStar = a / mGeom;
  if (std::abs(aStar) > 1.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  const double angle = (2.0 / 3.0) * std::acos(aStar);
  return 2.0 * mGeom * (1.0 + std::cos(angle));
}

/**
 * @brief Photon orbit radius for Kerr.
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @param prograde true for prograde orbit, false for retrograde
 * @return Photon orbit radius [cm]
 */
[[nodiscard]] inline double kerrPhotonOrbit(double mass, double a, bool prograde = true) {
  return prograde ? kerrPhotonOrbitPrograde(mass, a) : kerrPhotonOrbitRetrograde(mass, a);
}

// ============================================================================
// Frame Dragging (Lense-Thirring Effect)
// ============================================================================

/**
 * @brief Compute frame-dragging angular velocity.
 *
 * omega = (2Ma r c) / (Sigma(r^2 + a^2) + 2Ma^2 r sin^2 theta)
 *
 * This is the angular velocity at which local inertial frames are dragged.
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Frame-dragging angular velocity [rad/s]
 */
[[nodiscard]] inline double frameDraggingOmega(double r, double theta, double mass, double a) {
  const double mGeom = G * mass / C2;
  const double sigma = kerrSigma(r, a, theta);
  const double sinTheta = std::sin(theta);
  const double sin2Theta = sinTheta * sinTheta;

  const double r2PlusA2 = (r * r) + (a * a);
  const double numerator = 2.0 * mGeom * a * r * C;
  const double denominator = (sigma * r2PlusA2) + (2.0 * mGeom * a * a * r * sin2Theta);

  if (denominator < 1e-30) {
    return 0.0;
  }

  return numerator / denominator;
}

/**
 * @brief Clock rate dtau/dt of a static observer (fixed r, theta, phi).
 *
 * dtau/dt = sqrt(-g_tt) = sqrt(1 - r_s r / Sigma). A static observer needs
 * -g_tt > 0, so none exists on or inside the ergosurface
 * r_ergo(theta) = M + sqrt(M^2 - a^2 cos^2 theta), which lies outside the
 * horizon for a != 0 off the axis.
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return dtau/dt, or std::nullopt where no static observer exists (g_tt >= 0)
 */
[[nodiscard]] inline std::optional<double> kerrStaticTimeDilation(double r, double theta,
                                                                  double mass, double a) {
  const double rS = schwarzschildRadius(mass);
  const double minusGtt = 1.0 - ((rS * r) / kerrSigma(r, a, theta));
  if (!(minusGtt > 0.0)) {
    return std::nullopt;
  }
  return std::sqrt(minusGtt);
}

/**
 * @brief Lapse of the zero-angular-momentum observer (ZAMO): dtau/dt = sqrt(Sigma Delta / A).
 *
 * A = (r^2 + a^2)^2 - a^2 Delta sin^2 theta. The ZAMO co-rotates with the
 * frame-dragging rate omega = 2 M a r / A and exists everywhere outside the
 * outer horizon, including the ergoregion; the lapse falls to 0 at r_+. At
 * a = 0 it equals the static rate sqrt(1 - r_s / r). game::KerrTimeField uses
 * the same lapse for fleet clocks.
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return dtau/dt in [0, 1]; 0 at or inside the outer horizon (Delta <= 0 or r <= r_+)
 */
[[nodiscard]] inline double kerrZamoLapse(double r, double theta, double mass, double a) {
  const double rS = schwarzschildRadius(mass);
  const double delta = kerrDelta(r, a, rS);
  const double rPlus = 0.5 * rS + std::sqrt(std::fmax(0.0, (0.25 * rS * rS) - (a * a)));
  if (!(delta > 0.0) || !(r > rPlus)) {
    return 0.0;
  }
  const double sinTheta = std::sin(theta);
  const double r2PlusA2 = (r * r) + (a * a);
  const double bigA = (r2PlusA2 * r2PlusA2) - (a * a * delta * sinTheta * sinTheta);
  return std::sqrt(kerrSigma(r, a, theta) * delta / bigA);
}

/**
 * @brief Clock rate dtau/dt = 1/u^t of an equatorial circular geodesic.
 *
 * Bardeen, Press & Teukolsky (1972), eqs. 2.12-2.13, with M the geometric mass:
 *
 *   u^t = (r^{3/2} + s a M^{1/2}) / (r^{3/4} sqrt(r^{3/2} - 3 M r^{1/2} + 2 s a M^{1/2}))
 *
 * where s = +1 for an orbit with angular momentum along +z (prograde) and
 * s = -1 along -z (retrograde), with a signed about +z. Circular geodesics
 * exist only outside the photon orbit of that direction, where the radicand
 * is positive.
 *
 * @param r Equatorial radius [cm]
 * @param mass Black hole mass [g]
 * @param a Signed spin parameter [cm]
 * @param prograde true for angular momentum along +z
 * @return dtau/dt, or std::nullopt at or inside the photon orbit
 */
[[nodiscard]] inline std::optional<double>
kerrCircularOrbitTimeDilation(double r, double mass, double a, bool prograde = true) {
  const double mGeom = G * mass / C2;
  const double signedA = prograde ? a : -a;
  const double sqrtR = std::sqrt(r);
  const double r32 = r * sqrtR;
  const double spinTerm = signedA * std::sqrt(mGeom);
  const double radicand = r32 - (3.0 * mGeom * sqrtR) + (2.0 * spinTerm);
  const double numerator = r32 + spinTerm;
  if (!(r > 0.0) || !(radicand > 0.0) || !(numerator > 0.0)) {
    return std::nullopt;
  }
  return std::sqrt(r32) * std::sqrt(radicand) / numerator;
}

// ============================================================================
// Kerr Redshift
// ============================================================================

/**
 * @brief Redshift z of a photon from a static emitter at (r, theta) to infinity.
 *
 * 1 + z = 1 / sqrt(-g_tt). Undefined on and inside the ergosurface, where no
 * static emitter exists.
 *
 * @return z, or std::nullopt where g_tt >= 0
 */
[[nodiscard]] inline std::optional<double> kerrStaticRedshift(double r, double theta,
                                                              double mass, double a) {
  const std::optional<double> rate = kerrStaticTimeDilation(r, theta, mass, a);
  if (!rate) {
    return std::nullopt;
  }
  return (1.0 / *rate) - 1.0;
}

/**
 * @brief Redshift z to infinity of a zero-angular-momentum photon from a ZAMO emitter.
 *
 * 1 + z = 1 / alpha with alpha = kerrZamoLapse. The photon's zero angular
 * momentum removes the Doppler term, so the redshift is the lapse alone. It
 * is finite through the ergoregion and diverges at the horizon. At a = 0 the
 * ZAMO is the static observer and z = 1/sqrt(1 - r_s/r) - 1; for a != 0 the
 * static-emitter value is kerrStaticRedshift.
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return z >= 0, or +infinity at or inside the outer horizon
 */
[[nodiscard]] inline double kerrRedshift(double r, double theta, double mass, double a) {
  const double lapse = kerrZamoLapse(r, theta, mass, a);
  if (!(lapse > 0.0)) {
    return safeInfinity<double>();
  }
  return (1.0 / lapse) - 1.0;
}

// ============================================================================
// Kerr Geodesics (Null) - Potentials + Mino-time stepping
// ============================================================================

struct KerrGeodesicConsts {
  double e;  // Energy per unit mass
  double lz; // Angular momentum
  double q;  // Carter constant
};

/**
 * @brief Convenience constants for equatorial null rays (q = 0).
 *
 * Impact parameter b = lz / e in geometric units.
 */
[[nodiscard]] inline KerrGeodesicConsts kerrEquatorialConsts(double impactParam,
                                                             double energy = 1.0) {
  KerrGeodesicConsts c{};
  c.e = energy;
  c.lz = impactParam * energy;
  c.q = 0.0;
  return c;
}

struct KerrGeodesicState {
  double r;
  double theta;
  double phi;
  double t;
  double signR;     // +1 or -1
  double signTheta; // +1 or -1
};

/**
 * @brief Initialize equatorial state with sign conventions.
 */
[[nodiscard]] inline KerrGeodesicState kerrEquatorialState(double r, double phi, double signR) {
  KerrGeodesicState s{};
  s.r = r;
  s.theta = 0.5 * PI;
  s.phi = phi;
  s.t = 0.0;
  s.signR = (signR >= 0.0) ? 1.0 : -1.0;
  s.signTheta = 1.0;
  return s;
}

struct KerrPotentials {
  double rPot;
  double dRdr;
  double thetaPot;
  double dThetadtheta;
};

[[nodiscard]] KerrPotentials kerrPotentials(double r, double theta, double mass, double a,
                                            const KerrGeodesicConsts &c);

[[nodiscard]] KerrGeodesicState kerrStepMino(const KerrGeodesicState &state, double mass, double a,
                                             const KerrGeodesicConsts &c, double dlam);

// ============================================================================
// Convenience Class
// ============================================================================

/**
 * @brief Kerr black hole spacetime.
 *
 * Encapsulates rotating black hole calculations.
 */
class Kerr {
public:
  /**
   * @brief Construct Kerr spacetime.
   *
   * @param mass Black hole mass [g]
   * @param spinParam Spin parameter a [cm]
   */
  explicit Kerr(double mass, double spinParam = 0.0)
      : mass_(mass), a_(spinParam), mGeom_(G * mass / C2), rS_(schwarzschildRadius(mass)),
        aStar_(spinParam / (G * mass / C2)) {
    // Clamp to valid spin
    if (std::abs(aStar_) > 1.0) {
      aStar_ = (aStar_ > 0) ? 0.998 : -0.998; // Thorne limit
      a_ = aStar_ * mGeom_;
    }

    rPlus_ = kerrOuterHorizon(mass, a_);
    rMinus_ = kerrInnerHorizon(mass, a_);
    rIscoPro_ = kerrIscoRadius(mass, a_, true);
    rIscoRet_ = kerrIscoRadius(mass, a_, false);
    rPhPro_ = kerrPhotonOrbitPrograde(mass, a_);
    rPhRet_ = kerrPhotonOrbitRetrograde(mass, a_);
  }

  /**
   * @brief Construct from dimensionless spin a*.
   */
  [[nodiscard]] static Kerr fromDimensionlessSpin(double mass, double aStar) {
    const double mGeom = G * mass / C2;
    return Kerr(mass, aStar * mGeom);
  }

  // Accessors
  [[nodiscard]] double mass() const { return mass_; }
  [[nodiscard]] double spin() const { return a_; }
  [[nodiscard]] double dimensionlessSpin() const { return aStar_; }
  [[nodiscard]] double outerHorizon() const { return rPlus_; }
  [[nodiscard]] double innerHorizon() const { return rMinus_; }
  [[nodiscard]] double iscoPrograde() const { return rIscoPro_; }
  [[nodiscard]] double iscoRetrograde() const { return rIscoRet_; }
  [[nodiscard]] double photonOrbitPrograde() const { return rPhPro_; }
  [[nodiscard]] double photonOrbitRetrograde() const { return rPhRet_; }

  // Metric functions at point
  [[nodiscard]] double sigma(double r, double theta) const { return kerrSigma(r, a_, theta); }
  [[nodiscard]] double delta(double r) const { return kerrDelta(r, a_, rS_); }
  [[nodiscard]] double ergosphere(double theta) const { return ergosphereRadius(mass_, a_, theta); }
  [[nodiscard]] double frameDragging(double r, double theta) const {
    return frameDraggingOmega(r, theta, mass_, a_);
  }
  [[nodiscard]] double redshift(double r, double theta) const {
    return kerrRedshift(r, theta, mass_, a_);
  }

  [[nodiscard]] KerrPotentials potentials(double r, double theta,
                                          const KerrGeodesicConsts &c) const {
    return kerrPotentials(r, theta, mass_, a_, c);
  }

  [[nodiscard]] KerrGeodesicState stepMino(const KerrGeodesicState &state,
                                           const KerrGeodesicConsts &c, double dlam) const {
    return kerrStepMino(state, mass_, a_, c, dlam);
  }

  // Check if point is outside horizon
  [[nodiscard]] bool isExterior(double r) const { return r > rPlus_; }

  // Check if point is in ergosphere
  [[nodiscard]] bool inErgosphere(double r, double theta) const {
    return (r < ergosphere(theta)) && (r > rPlus_);
  }

private:
  double mass_;           // Mass [g]
  double a_;              // Spin parameter [cm]
  double mGeom_;          // Geometric mass [cm]
  double rS_;             // Schwarzschild radius [cm]
  double aStar_;          // Dimensionless spin
  double rPlus_ = 0.0;    // Outer horizon [cm]
  double rMinus_ = 0.0;   // Inner horizon [cm]
  double rIscoPro_ = 0.0; // Prograde ISCO [cm]
  double rIscoRet_ = 0.0; // Retrograde ISCO [cm]
  double rPhPro_ = 0.0;   // Prograde photon orbit [cm]
  double rPhRet_ = 0.0;   // Retrograde photon orbit [cm]
};

} // namespace physics

#endif // PHYSICS_KERR_H
