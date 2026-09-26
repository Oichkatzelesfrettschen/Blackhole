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

#include <algorithm>
#include <cmath>
#include <limits>
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
 * Minus sign for prograde (co-rotating), plus for retrograde.
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @param prograde true for prograde orbit, false for retrograde
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

  // Prograde: minus sign; Retrograde: plus sign
  const double rIscoOverM = prograde ? (3.0 + z2 - sqrtTerm) : (3.0 + z2 + sqrtTerm);

  return rIscoOverM * mGeom;
}

// ============================================================================
// Photon Orbits
// ============================================================================

/**
 * @brief Compute prograde photon orbit radius.
 *
 * r_ph = 2M(1 + cos(2/3 * arccos(-a*)))
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
 * @brief Compute retrograde photon orbit radius.
 *
 * r_ph = 2M(1 + cos(2/3 * arccos(a*)))
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
 * @brief Compute gravitational time dilation for Kerr.
 *
 * For a zero-angular-momentum observer (ZAMO):
 * dtau/dt = sqrt(-g_tt - 2 omega g_t_phi - omega^2 g_phi_phi) / c
 *
 * Simplified at equator (theta = pi/2):
 * dtau/dt = sqrt(Delta Sigma) / (r^2 + a^2 + 2Ma^2/r) / c
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Time dilation factor dtau/dt
 */
[[nodiscard]] inline double kerrTimeDilation(double r, double theta, double mass, double a) {
  const double rS = schwarzschildRadius(mass);
  const double sigma = kerrSigma(r, a, theta);
  const double delta = kerrDelta(r, a, rS);

  if ((delta <= 0) || (sigma <= 0)) {
    return 0.0; // Inside horizon
  }

  // g_tt component
  const double gTt = -(1.0 - ((rS * r) / sigma));

  // For static observer (not ZAMO), simpler formula
  return std::sqrt(-gTt);
}

// ============================================================================
// Kerr Redshift
// ============================================================================

/**
 * @brief Compute gravitational redshift for Kerr spacetime.
 *
 * For a photon emitted at radius r and observed at infinity:
 * 1 + z = 1/sqrt(-g_tt) = 1/sqrt(1 - r_s r/Sigma)
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Redshift z
 */
[[nodiscard]] inline double kerrRedshift(double r, double theta, double mass, double a) {
  const double rS = schwarzschildRadius(mass);
  const double sigma = kerrSigma(r, a, theta);

  const double factor = 1.0 - ((rS * r) / sigma);
  if (factor <= 0) {
    return safeInfinity<double>();
  }

  return (1.0 / std::sqrt(factor)) - 1.0;
}

// ============================================================================
// Kerr Geodesics (Null) - Potentials + Mino-time stepping
// ============================================================================

/**
 * @brief Conserved quantities of a Kerr null geodesic.
 *
 * q is Carter's constant in the separation of Carter (1968) and Gralla &
 * Lupsasca, PRD 101, 044032 (2020): Theta(theta) = q + a^2 e^2 cos^2(theta)
 * - lz^2 cot^2(theta) and R(r) = (e(r^2+a^2) - a lz)^2 - Delta (q + (lz - a e)^2).
 * The same q enters both potentials, so R(r0) = (Sigma dr/dtau)^2 and
 * Theta(theta0) = (Sigma dtheta/dtau)^2 hold at the initial point.
 */
struct KerrGeodesicConsts {
  double e{0.0};  // Energy per unit mass
  double lz{0.0}; // Angular momentum
  double q{0.0};  // Carter constant
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

/**
 * @brief Kerr geodesic state in Mino time.
 *
 * vr = dr/dlambda and vtheta = dtheta/dlambda are integrated through the
 * second-order equations d^2r/dlambda^2 = R'(r)/2 and d^2theta/dlambda^2 =
 * Theta'(theta)/2, so turning points need no sign bookkeeping. signR and
 * signTheta seed the velocities (kerrInitMinoVelocities) and afterwards track
 * sign(vr) and sign(vtheta).
 */
struct KerrGeodesicState {
  double r{0.0};
  double theta{0.0};
  double phi{0.0};
  double t{0.0};
  double signR{0.0};     // +1 or -1
  double signTheta{0.0}; // +1 or -1
  double vr{0.0};        // dr/dlambda
  double vtheta{0.0};    // dtheta/dlambda
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

/**
 * @brief Null geodesic (constants plus Mino state) through a point with a given BL direction.
 *
 * kr, ktheta, kphi are the contravariant Boyer-Lindquist spatial components of
 * the photon direction at (r, theta), in any overall scale. The null condition
 * fixes k^t (future root); E = -k_t and lz = k_phi follow, and the result is
 * normalized to E = 1. q is Carter's constant, p_theta^2 - a^2 cos^2 +
 * lz^2 cot^2 with p_theta = Sigma k^theta / E, so that R(r) = vr^2 and
 * Theta(theta) = vtheta^2 hold at the start with vr = Sigma k^r / E. A photon
 * with E <= 0 (inside the ergoregion only) returns state.r = 0, captured. The
 * GPU initializers (kerrInitGeodesic, d_kerr_init_geodesic) compute the same
 * quantities.
 */
struct KerrNullGeodesic {
  KerrGeodesicConsts consts;
  KerrGeodesicState state;
};

[[nodiscard]] inline KerrNullGeodesic kerrNullGeodesicFromBL(double r, double theta, double phi,
                                                            double kr, double ktheta, double kphi,
                                                            double mass, double a) {
  const double mGeom = G * mass / C2;
  const double sinT = std::sin(theta);
  const double cosT = std::cos(theta);
  const double sin2 = sinT * sinT;
  const double cos2 = cosT * cosT;
  const double sigma = (r * r) + (a * a * cos2);
  const double delta = (r * r) - (2.0 * mGeom * r) + (a * a);
  const double f = 2.0 * mGeom * r / sigma;
  const double gtt = -(1.0 - f);
  const double gtphi = -f * a * sin2;
  const double grr = sigma / delta;
  const double gphph = ((r * r) + (a * a) + (f * a * a * sin2)) * sin2;

  // g_tt kt^2 + 2 hb kt + spatial = 0 with hb = g_tphi kphi. The roots have
  // E = -(g_tt kt + hb) = +-sqrt(D), D = hb^2 - g_tt spatial, and in
  // conjugate form
  //   kt(E = +sqrt(D)) = spatial / (sqrt(D) - hb),
  //   kt(E = -sqrt(D)) = -spatial / (sqrt(D) + hb),
  // which divide by g_tt nowhere: on the stationary limit (g_tt = 0) the
  // equation is linear and the first form is its root -spatial / (2 hb),
  // finite for hb < 0, while the other root runs to infinity. A denominator
  // at or below the rounding of sqrt(D) + |hb| marks a root at infinity.
  // Outside the ergoregion (g_tt < 0) the E > 0 root is the future-directed
  // one. Inside it both roots can be future-directed (k^t > 0): the
  // coordinate direction then fixes the physical direction only together
  // with a local observer frame, and the E > 0 root, the one that can
  // connect to infinity, is preferred. D < 0 (inside the ergoregion, for a
  // direction too close to constant phi) has no null completion.
  const double spatial = (grr * kr * kr) + (sigma * ktheta * ktheta) + (gphph * kphi * kphi);
  const double hb = gtphi * kphi;
  const double disc = (hb * hb) - (gtt * spatial);
  const double sqD = std::sqrt(std::max(disc, 0.0));
  const double rootTol = 1e-12 * (sqD + std::abs(hb));
  const bool finitePos = disc >= 0.0 && (sqD - hb) > rootTol;
  const bool finiteNeg = disc >= 0.0 && (sqD + hb) > rootTol;
  const double ktPos = finitePos ? spatial / (sqD - hb) : 0.0;
  const double ktNeg = finiteNeg ? -spatial / (sqD + hb) : 0.0;
  const bool useNeg = finiteNeg && ktNeg > 0.0 && (!finitePos || ktPos <= 0.0);
  const double kt = useNeg ? ktNeg : ktPos;
  const double eRaw = useNeg ? -sqD : sqD;
  const double lzRaw = (gtphi * kt) + (gphph * kphi);

  KerrNullGeodesic g{};
  if (!(finitePos || useNeg) || !(eRaw > 0.0)) {
    // No finite null completion (D < 0, or the only future root at infinity
    // on the stationary limit), or a future-directed photon with E <= 0,
    // which exists only inside the ergoregion and cannot reach infinity:
    // state.r = 0 marks it captured, as the GPU initializers do.
    g.consts.e = 1.0;
    g.state.r = 0.0;
    g.state.theta = theta;
    g.state.phi = phi;
    return g;
  }
  const double invE = 1.0 / eRaw;
  g.consts.e = 1.0;
  g.consts.lz = lzRaw * invE;
  const double pTheta = sigma * ktheta * invE;
  // On the axis lz = 0 exactly and the cotangent term vanishes.
  const double cot2 = (sin2 > 0.0) ? cos2 / sin2 : 0.0;
  g.consts.q = (pTheta * pTheta) - (a * a * cos2) + (g.consts.lz * g.consts.lz * cot2);
  g.state.r = r;
  g.state.theta = theta;
  g.state.phi = phi;
  g.state.t = 0.0;
  g.state.vr = sigma * kr * invE;
  g.state.vtheta = pTheta;
  g.state.signR = (g.state.vr >= 0.0) ? 1.0 : -1.0;
  g.state.signTheta = (g.state.vtheta >= 0.0) ? 1.0 : -1.0;
  return g;
}

/**
 * @brief Seed vr = signR sqrt(R) and vtheta = signTheta sqrt(Theta) from the potentials.
 *
 * A negative potential at the seed point (a state off the geodesic's allowed
 * region) seeds zero velocity; the second-order step then moves the state
 * back into the allowed region along R'(r).
 */
[[nodiscard]] KerrGeodesicState kerrInitMinoVelocities(const KerrGeodesicState &state,
                                                       double mass, double a,
                                                       const KerrGeodesicConsts &c);

/**
 * @brief One classical RK4 step of the second-order Mino-time system.
 *
 * State (r, theta, vr, vtheta, phi, t) with vr' = R'/2, vtheta' = Theta'/2 and
 * Boyer-Lindquist phi' and t'. The step passes radial and polar turning points
 * continuously; a first-order step on +-sqrt(max(R,0)) stalls there because the
 * clamped root is zero on both sides of the turning point.
 */
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

  [[nodiscard]] KerrGeodesicState initMinoVelocities(const KerrGeodesicState &state,
                                                     const KerrGeodesicConsts &c) const {
    return kerrInitMinoVelocities(state, mass_, a_, c);
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
