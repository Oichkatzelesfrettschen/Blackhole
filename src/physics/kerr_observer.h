/**
 * @file kerr_observer.h
 * @brief Equatorial Kerr observers, circular orbits, local tetrads, and
 *        principal-null delay, parameterized by the spin deficit.
 *
 * Units are G = c = M = 1. Every function takes the spin deficit
 * epsilon = 1 - a (a in [-1, 1], so epsilon in [0, 2]) and the radial offset
 * x = r - 1, never (a, r). Near extremal spin the two parameterizations part
 * ways: Gargantua's canon spin 1 - a = 1.33e-14 stored as a double a keeps two
 * significant digits of 1 - a^2, while epsilon keeps all sixteen, and the
 * horizon, ISCO, and orbital clock all live at x ~ 1e-7..1e-5 where r = 1 + x
 * would round the physics away.
 *
 * Horizons sit at x = +-h with h = sqrt(epsilon (2 - epsilon)) = sqrt(1 - a^2),
 * so Delta = r^2 - 2r + a^2 = (x - h)(x + h). The metric enters only through
 * its lapse-shift primitives -- ZAMO lapse alpha, frame-drag rate omega, and
 * cylindrical radius varpi -- because g_tt and g_tphi are each O(1) while the
 * clock they combine into is O(1e-5) at the canon orbit: summing them cancels
 * the answer.
 *
 * OrbitSense is relative to the hole's rotation: a prograde orbit co-rotates
 * with the hole whatever the sign of a. The orbit algebra is written for a
 * hole of spin |a| turning toward +phi, whose deficit is min(epsilon,
 * 2 - epsilon); a counter-rotating orbit is a co-rotating one around -|a|,
 * deficit 2 - min(epsilon, 2 - epsilon); and for a < 0 (epsilon > 1) the
 * mirror phi -> -phi flips every azimuthal sign so the orbit runs with the
 * hole toward -phi.
 *
 * References: Bardeen, Press & Teukolsky 1972 (ApJ 178, 347) for circular
 * orbits; James, von Tunzelmann, Franklin & Thorne 2015 (arXiv:1502.03808,
 * Appendix A) for the FIDO (ZAMO) tetrad and the boosted camera tetrad.
 */

#ifndef BLACKHOLE_PHYSICS_KERR_OBSERVER_H
#define BLACKHOLE_PHYSICS_KERR_OBSERVER_H

#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <numbers>

namespace physics::kerr_observer {

/** @brief Orbital sense relative to the hole's rotation: Prograde
 *         co-rotates with the hole, toward -phi when a < 0. */
enum class OrbitSense : std::uint8_t {
  Prograde = 0,
  Retrograde = 1,
};

/** @brief The deficit whose +phi co-rotating algebra describes this sense:
 *         the deficit of |a|, min(epsilon, 2 - epsilon), for a co-rotating
 *         orbit and 2 minus that (spin -|a|) for a counter-rotating one. */
[[nodiscard]] inline double senseDeficit(double epsilon, OrbitSense sense) {
  const double coRotating = std::fmin(epsilon, 2.0 - epsilon);
  return sense == OrbitSense::Prograde ? coRotating : 2.0 - coRotating;
}

/** @brief Sign of the orbit's azimuthal motion along +phi: +1 for an orbit
 *         along the rotation of a hole with a >= 0, and the mirror for a < 0. */
[[nodiscard]] inline double senseSign(double epsilon, OrbitSense sense) {
  const double holeSign = epsilon > 1.0 ? -1.0 : 1.0;
  return sense == OrbitSense::Prograde ? holeSign : -holeSign;
}

/** @brief h = sqrt(1 - a^2), the outer-horizon offset r_+ - 1. */
[[nodiscard]] inline double horizonOffset(double epsilon) {
  return std::sqrt(epsilon * (2.0 - epsilon));
}

/** @brief Delta = (x - h)(x + h); positive outside the outer horizon. */
[[nodiscard]] inline double kerrDelta(double epsilon, double x) {
  const double h = horizonOffset(epsilon);
  return (x - h) * (x + h);
}

/** @brief Equatorial lapse-shift primitives at one radius. */
struct EquatorialFrame {
  double epsilon = 1.0;
  double x = 0.0;
  double r = 1.0;         ///< 1 + x.
  double spin = 0.0;      ///< a = 1 - epsilon.
  double sqrtDelta = 0.0; ///< sqrt((x - h)(x + h)).
  double bigA = 0.0;      ///< (r^2 + a^2)^2 - a^2 Delta = r^4 + a^2 r^2 + 2 a^2 r.
  double alpha = 0.0;     ///< ZAMO lapse r sqrt(Delta / A); the ZAMO's dtau/dt.
  double omega = 0.0;     ///< Frame-drag angular velocity 2 a r / A.
  double varpi = 0.0;     ///< Cylindrical radius sqrt(A) / r = sqrt(g_phiphi).
};

/** @brief Builds the primitives at x outside the outer horizon (x > h). The
 *         equatorial A is a sum of non-negative terms for every spin, so no
 *         step subtracts nearly equal numbers. */
[[nodiscard]] inline EquatorialFrame equatorialFrame(double epsilon, double x) {
  EquatorialFrame frame;
  frame.epsilon = epsilon;
  frame.x = x;
  frame.r = 1.0 + x;
  frame.spin = 1.0 - epsilon;
  const double r = frame.r;
  const double a2 = frame.spin * frame.spin;
  frame.sqrtDelta = std::sqrt(kerrDelta(epsilon, x));
  frame.bigA = (r * r * ((r * r) + a2)) + (2.0 * a2 * r);
  const double sqrtA = std::sqrt(frame.bigA);
  frame.alpha = r * frame.sqrtDelta / sqrtA;
  frame.omega = 2.0 * frame.spin * r / frame.bigA;
  frame.varpi = sqrtA / r;
  return frame;
}

/** @brief Equatorial circular geodesic of one sense at one radius. */
struct CircularOrbit {
  bool exists = false;          ///< Timelike: outside the photon orbit of this sense.
  double properTimeRate = 0.0;  ///< dtau/dt = 1 / u^t.
  /// Omega = dphi/dt, signed along +phi: a prograde orbit shares the sign of
  /// a (negative for epsilon > 1), a retrograde one the opposite.
  double angularVelocity = 0.0;
  double zamoVelocity = 0.0;    ///< Azimuthal speed measured by the local ZAMO, signed.
};

/**
 * @brief Bardeen-Press-Teukolsky circular orbit in deficit form.
 *
 * With s = sqrt(r) = 1 + y (y = x / (1 + sqrt(1 + x))) and the sense's spin
 * a_s = 1 - e (e = senseDeficit, so a_s = +|a| co-rotating, -|a| counter), the
 * BPT radicand times r^{3/2} is s^3 - 3s + 2 a_s. The
 * identity s^3 - 3s + 2 = (s - 1)^2 (s + 2) turns it into
 *   N = y^2 (y + 3) - 2 e,
 * which keeps full precision where s^3 - 3s + 2 a_s would cancel to zero.
 * Then dtau/dt = r^{3/4} sqrt(N) / (r^{3/2} + a_s) and Omega = 1 / (r^{3/2} + a_s).
 * The ZAMO-frame speed (r^2 - 2 a_s sqrt(r) + a_s^2) / (sqrt(Delta) (r^{3/2} + a_s))
 * uses r - a_s = x + e, so its numerator (x + e)^2 + 2 a_s s y is a sum of
 * non-negative terms for the prograde sense. senseSign carries both onto the
 * +phi coordinate.
 */
[[nodiscard]] inline CircularOrbit circularOrbit(double epsilon, double x, OrbitSense sense) {
  CircularOrbit orbit;
  const double e = senseDeficit(epsilon, sense);
  const double spinSense = 1.0 - e;
  const double r = 1.0 + x;
  const double s = std::sqrt(r);
  const double y = x / (1.0 + s);
  const double radicand = (y * y * (y + 3.0)) - (2.0 * e);
  const double delta = kerrDelta(epsilon, x);
  if (!(radicand > 0.0) || !(delta > 0.0)) {
    return orbit;
  }
  const double r32 = r * s;
  const double denominator = r32 + spinSense;
  const double sign = senseSign(epsilon, sense);
  orbit.exists = true;
  orbit.properTimeRate = std::sqrt(r32) * std::sqrt(radicand) / denominator;
  orbit.angularVelocity = sign / denominator;
  const double rMinusA = x + e;
  const double numerator = (rMinusA * rMinusA) + (2.0 * spinSense * s * y);
  orbit.zamoVelocity = sign * numerator / (std::sqrt(delta) * denominator);
  return orbit;
}

/**
 * @brief ISCO offset x_isco = r_isco - 1 for one sense.
 *
 * The ISCO condition r^2 - 6r + 8 a_s sqrt(r) - 3 a_s^2 = 0 in s = 1 + y with
 * a_s = 1 - e factors through (s - 1)^3 (s + 3) at e = 0 into
 *   F(y) = y^3 (y + 4) - 2 e (1 + 4y) - 3 e^2 = 0,
 * whose root is y ~ (e / 2)^{1/3} near extremal spin with no cancellation.
 * F is convex for y > 0 and F(2) >= 0 for every e in [0, 2] (r_isco <= 9), so
 * Newton from y = 2 descends monotonically onto the root.
 */
[[nodiscard]] inline double iscoOffset(double epsilon, OrbitSense sense) {
  const double e = senseDeficit(epsilon, sense);
  constexpr int maxIterations = 400;
  double y = 2.0;
  for (int iteration = 0; iteration < maxIterations; ++iteration) {
    const double f = (y * y * y * (y + 4.0)) - (2.0 * e * (1.0 + (4.0 * y))) - (3.0 * e * e);
    const double slope = (4.0 * y * y * y) + (12.0 * y * y) - (8.0 * e);
    if (!(slope > 0.0)) {
      break;
    }
    const double next = y - (f / slope);
    if (!(next < y)) {
      break;
    }
    y = next;
  }
  return y * (2.0 + y);
}

/** @brief Marginally bound (E = 1) circular-orbit offset: r_mb - 1 =
 *         e + 2 sqrt(e). A bound circular orbit of this sense exists only
 *         strictly outside it. */
[[nodiscard]] inline double marginallyBoundOffset(double epsilon, OrbitSense sense) {
  const double e = senseDeficit(epsilon, sense);
  return e + (2.0 * std::sqrt(e));
}

/** @brief Circular photon orbit offset. r_ph = 2 (1 + cos(2/3 acos(-a_s))) with
 *         acos(a_s) = 2 asin(sqrt(e/2)) gives r_ph - 1 = 2 sin^2(d/2) + sqrt(3) sin d,
 *         d = (4/3) asin(sqrt(e/2)). */
[[nodiscard]] inline double photonOrbitOffset(double epsilon, OrbitSense sense) {
  const double e = senseDeficit(epsilon, sense);
  const double d = (4.0 / 3.0) * std::asin(std::sqrt(e / 2.0));
  const double halfSin = std::sin(d / 2.0);
  return (2.0 * halfSin * halfSin) + (std::numbers::sqrt3 * std::sin(d));
}

/** @brief atanh(z) / z, equal to 1 at z = 0. */
[[nodiscard]] inline double atanhOverArgument(double z) {
  return z == 0.0 ? 1.0 : std::atanh(z) / z;
}

/**
 * @brief Coordinate time (units of M) for light along the equatorial principal
 *        null congruence between offsets x1 and x2, both outside the horizon.
 *
 * dt/dr = (r^2 + a^2) / Delta = 1 + 2r / Delta. Partial fractions over the
 * horizons x = +-h give, for x1 < x2,
 *   T = (x2 - x1) + ln(Delta2 / Delta1) + 2 w atanh(h w) / (h w),
 *   w = (x2 - x1) / (x1 x2 - h^2).
 * The textbook form divides a difference of logarithms by r_+ - r_- = 2h,
 * which loses log10(1/h) digits (about 6.5 at the canon spin); the atanh form
 * carries that ratio exactly and reaches the extremal limit w at h = 0.
 */
[[nodiscard]] inline double principalNullDelay(double epsilon, double x1, double x2) {
  const double inner = std::fmin(x1, x2);
  const double outer = std::fmax(x1, x2);
  if (inner == outer) {
    return 0.0;
  }
  const double h2 = epsilon * (2.0 - epsilon);
  const double h = std::sqrt(h2);
  const double span = outer - inner;
  const double w = span / ((inner * outer) - h2);
  const double logRatio = std::log(((outer - h) * (outer + h)) / ((inner - h) * (inner + h)));
  return span + logRatio + (2.0 * w * atanhOverArgument(h * w));
}

using Vec3 = std::array<double, 3>;
using Vec4 = std::array<double, 4>;

/**
 * @brief An orthonormal tetrad at an equatorial point.
 *
 * lorentz[a][b] expresses leg a (0 = time, 1 = r, 2 = theta, 3 = phi) in the
 * ZAMO legs b, so the tetrad is a Lorentz transform of the ZAMO (FIDO) frame
 * of James et al. 2015, Appendix A; the ZAMO tetrad itself has the identity.
 */
struct Tetrad {
  EquatorialFrame frame;
  std::array<Vec4, 4> lorentz{
      {{1.0, 0.0, 0.0, 0.0}, {0.0, 1.0, 0.0, 0.0}, {0.0, 0.0, 1.0, 0.0}, {0.0, 0.0, 0.0, 1.0}}};
};

/** @brief ZAMO (FIDO) tetrad: e_t = (d_t + omega d_phi) / alpha,
 *         e_r = sqrt(Delta)/r d_r, e_theta = d_theta / r, e_phi = d_phi / varpi. */
[[nodiscard]] inline Tetrad zamoTetrad(double epsilon, double x) {
  Tetrad tetrad;
  tetrad.frame = equatorialFrame(epsilon, x);
  return tetrad;
}

/** @brief Boyer-Lindquist contravariant components (t, r, theta, phi) of a
 *         vector given by its ZAMO-frame components. */
[[nodiscard]] inline Vec4 zamoToBoyerLindquist(const EquatorialFrame &frame, const Vec4 &zamo) {
  const double timeComponent = zamo.at(0) / frame.alpha;
  return {timeComponent, zamo.at(1) * frame.sqrtDelta / frame.r, zamo.at(2) / frame.r,
          (frame.omega * timeComponent) + (zamo.at(3) / frame.varpi)};
}

/** @brief Boyer-Lindquist components of tetrad leg `leg`. */
[[nodiscard]] inline Vec4 legComponents(const Tetrad &tetrad, std::size_t leg) {
  return zamoToBoyerLindquist(tetrad.frame, tetrad.lorentz.at(leg));
}

/**
 * @brief Tetrad of an observer moving with 3-velocity `velocity` (components
 *        along the base tetrad's r, theta, phi legs, |v| < 1) relative to the
 *        base observer: the pure Lorentz boost of James et al. 2015, Appendix A,
 *          e'_0 = gamma (e_0 + beta n^j e_j),
 *          e'_i = gamma beta n_i e_0 + e_i + (gamma - 1) n_i n^j e_j,
 *        composed onto the base tetrad's own transform from the ZAMO frame.
 *        Orbiting observers boost the ZAMO by their zamoVelocity along phi;
 *        a static observer boosts it by -omega varpi / alpha.
 */
[[nodiscard]] inline Tetrad boostedTetrad(const Tetrad &base, const Vec3 &velocity) {
  const double speed2 = (velocity.at(0) * velocity.at(0)) + (velocity.at(1) * velocity.at(1)) +
                        (velocity.at(2) * velocity.at(2));
  if (speed2 == 0.0) {
    return base;
  }
  const double gamma = 1.0 / std::sqrt(1.0 - speed2);
  // Boost matrix in the base frame: boost[a][c] is leg a' along base leg c.
  std::array<Vec4, 4> boost{};
  boost.at(0).at(0) = gamma;
  for (std::size_t i = 0; i < 3; ++i) {
    boost.at(0).at(i + 1) = gamma * velocity.at(i);
    boost.at(i + 1).at(0) = gamma * velocity.at(i);
    for (std::size_t j = 0; j < 3; ++j) {
      const double kronecker = i == j ? 1.0 : 0.0;
      boost.at(i + 1).at(j + 1) =
          kronecker + ((gamma - 1.0) * velocity.at(i) * velocity.at(j) / speed2);
    }
  }
  Tetrad boosted;
  boosted.frame = base.frame;
  for (std::size_t leg = 0; leg < 4; ++leg) {
    for (std::size_t component = 0; component < 4; ++component) {
      double sum = 0.0;
      for (std::size_t via = 0; via < 4; ++via) {
        sum += boost.at(leg).at(via) * base.lorentz.at(via).at(component);
      }
      boosted.lorentz.at(leg).at(component) = sum;
    }
  }
  return boosted;
}

/** @brief Tetrad of the prograde or retrograde circular geodesic at x. The
 *         orbit must exist (circularOrbit(...).exists). */
[[nodiscard]] inline Tetrad orbitingTetrad(double epsilon, double x, OrbitSense sense) {
  const CircularOrbit orbit = circularOrbit(epsilon, x, sense);
  return boostedTetrad(zamoTetrad(epsilon, x), Vec3{0.0, 0.0, orbit.zamoVelocity});
}

/** @brief Azimuthal ZAMO-frame speed of the static observer (u^phi = 0),
 *         -omega varpi / alpha; its magnitude reaches 1 at the static limit. */
[[nodiscard]] inline double staticObserverVelocity(const EquatorialFrame &frame) {
  return -frame.omega * frame.varpi / frame.alpha;
}

/**
 * @brief Radial potential of a photon with E = 1, R(r) = ((r^2 + a^2) - a lambda)^2
 *        - Delta (eta + (lambda - a)^2), expanded in r:
 *          R = r^4 + c2 r^2 + c1 r + c0,
 *          c2 = 2 (a^2 - a lambda) - Q, c1 = 2 Q, c0 = (a^2 - a lambda)^2 - a^2 Q,
 *        with Q = eta + (lambda - a)^2. Radial motion is allowed where R >= 0;
 *        a zero of R is a radial turning point.
 */
struct RadialPotential {
  double c2 = 0.0;
  double c1 = 0.0;
  double c0 = 0.0;

  [[nodiscard]] double value(double r) const {
    const double r2 = r * r;
    return (r2 * (r2 + c2)) + (c1 * r) + c0;
  }
  [[nodiscard]] double slope(double r) const { return (4.0 * r * r * r) + (2.0 * c2 * r) + c1; }
};

[[nodiscard]] inline RadialPotential radialPotential(double spin, double lambda, double eta) {
  const double shift = (spin * spin) - (spin * lambda);
  const double q = eta + ((lambda - spin) * (lambda - spin));
  return RadialPotential{.c2 = (2.0 * shift) - q, .c1 = 2.0 * q, .c0 = (shift * shift) - (spin * spin * q)};
}

/** @brief What stops a photon's radial motion first in one direction. */
enum class RadialObstacle : std::uint8_t {
  None = 0,      ///< No zero of R: the photon runs through the interval.
  Turning = 1,   ///< A simple zero: the photon reaches it and turns back.
  Asymptote = 2, ///< A double zero (an unstable circular photon orbit): the
                 ///< photon spirals toward it forever and never turns back.
};

/**
 * @brief The first zero of R the photon meets moving from `from` toward
 *        `toward`, classified; `from` itself never counts.
 *
 * R is a quartic with positive leading term, and R >= 0 at the photon, so a
 * zero exists in a direction exactly when some local minimum of R that way
 * sits at or below zero, and the nearest such minimum marks the first
 * obstacle. A minimum clearly below zero lies between two simple zeros, the
 * nearer of which turns the photon; a minimum at zero within roundoff is a
 * double zero, the separatrix of a circular photon orbit, which the photon
 * approaches asymptotically. The tolerance is 64 ulp of the largest term of R
 * at the minimum, far below any physical separation: impact parameters
 * within 1e-9 of critical still resolve to a turning point or to none. Local
 * minima are the roots of the cubic R' where it rises through zero; R' is
 * monotone between the roots of R'' = 12 r^2 + 2 c2 and beyond its Cauchy
 * bound, so each monotone piece holds at most one, found by bisection.
 */
[[nodiscard]] inline RadialObstacle firstRadialObstacle(const RadialPotential &potential,
                                                        double from, double toward) {
  const double lo = std::fmin(from, toward);
  const double hi = std::fmax(from, toward);
  const bool upward = toward > from;
  const double bound = 1.0 + std::fmax(std::fabs(potential.c2) / 2.0, std::fabs(potential.c1) / 4.0);
  // Monotone pieces of R': split at the roots of R'' when it has them.
  const double split = potential.c2 < 0.0 ? std::sqrt(-potential.c2 / 6.0) : 0.0;
  const std::array<double, 4> edges{-bound, -split, split, bound};
  RadialObstacle nearest = RadialObstacle::None;
  for (std::size_t piece = 0; piece + 1 < edges.size(); ++piece) {
    double left = std::fmax(edges.at(piece), lo);
    double right = std::fmin(edges.at(piece + 1), hi);
    if (!(left < right)) {
      continue;
    }
    // A local minimum of R is where R' rises through zero.
    const bool risesThroughZero = potential.slope(left) < 0.0 && potential.slope(right) >= 0.0;
    if (!risesThroughZero) {
      continue;
    }
    constexpr int bisections = 200;
    for (int step = 0; step < bisections; ++step) {
      const double middle = 0.5 * (left + right);
      if (middle <= left || middle >= right) {
        break;
      }
      if (potential.slope(middle) < 0.0) {
        left = middle;
      } else {
        right = middle;
      }
    }
    const double minimum = 0.5 * (left + right);
    if (minimum <= lo || minimum >= hi) {
      continue;
    }
    const double m2 = minimum * minimum;
    const double scale = (m2 * m2) + (std::fabs(potential.c2) * m2) +
                         (std::fabs(potential.c1) * std::fabs(minimum)) + std::fabs(potential.c0);
    const double tolerance = 64.0 * std::numeric_limits<double>::epsilon() * scale;
    const double depth = potential.value(minimum);
    if (depth > tolerance) {
      continue;
    }
    const RadialObstacle kind =
        depth < -tolerance ? RadialObstacle::Turning : RadialObstacle::Asymptote;
    // Pieces run in ascending r: moving up the first hit wins, moving down
    // the last one does.
    if (upward) {
      return kind;
    }
    nearest = kind;
  }
  return nearest;
}

/** @brief Conserved quantities of a photon at an observer's event, fixed by
 *         its propagation direction there; they do not depend on whether the
 *         observer emits or receives it. */
struct PhotonConstants {
  double energy = 0.0;          ///< E = -p_t with the observer-measured energy set to 1.
  double angularMomentum = 0.0; ///< L = p_phi.
  double pTheta = 0.0;          ///< p_theta at the equator.
  double radialMomentum = 0.0;  ///< ZAMO-frame p^r: positive when moving outward.
  bool positiveEnergy = false;  ///< E > 0; false only inside the ergoregion.
  /// Followed forward in time along its propagation, the photon reaches
  /// infinity: E > 0, no radial turning point outside r, and it is moving
  /// outward or has an inner turning point to bounce from.
  bool escapesToInfinity = false;
  /// Followed backward in time, the photon came from infinity: the same test
  /// with the radial direction reversed. A camera's pixel sees the sky only
  /// when this holds; otherwise the ray traces back to the horizon or is
  /// trapped between turning points.
  bool fromInfinity = false;
  double lambda = 0.0; ///< L / E; meaningful only when positiveEnergy.
  double eta = 0.0;    ///< Carter Q / E^2 = p_theta^2 / E^2 at the equator; only when positiveEnergy.
  /// 1 / E: the frequency the observer measures over the frequency at
  /// infinity -- the blueshift of a photon received from infinity, the inverse
  /// of the redshift of one sent there. Only when positiveEnergy.
  double g = 0.0;
};

/**
 * @brief Constants of motion of the photon, normalized to unit local energy,
 *        that propagates along unit direction `direction` at the observer
 *        (components on the tetrad's r, theta, phi legs). A camera looking
 *        along n receives the photon propagating along -n.
 *
 * The momentum in ZAMO components is P = lorentz[0] + n^i lorentz[i]; then
 * p_phi = varpi P^phi, p_theta = r P^theta, and E = alpha P^t + omega varpi P^phi.
 * E <= 0 happens only inside the ergoregion: such a photon connects to
 * infinity in neither direction.
 *
 * Connectivity comes from the radial potential R: with no zero of R in
 * (r, inf) the photon, once moving outward, runs to infinity. Moving outward
 * now it escapes; moving inward it escapes only after bouncing off a simple
 * zero between the outer horizon and r. A double zero -- the separatrix of an
 * unstable circular photon orbit, as for b = 3 sqrt(3) M around a
 * Schwarzschild hole -- is approached asymptotically, so a ray heading toward
 * one neither escapes nor came from infinity in that direction. At P^r = 0
 * the photon sits on a zero: R'(r) > 0 marks a periapsis (it moves outward
 * both ways), R' < 0 an apoapsis inside a potential barrier (trapped both
 * ways), and R' = 0 a circular photon orbit, which escapes in neither
 * direction.
 */
[[nodiscard]] inline PhotonConstants photonConstants(const Tetrad &tetrad, const Vec3 &direction) {
  Vec4 zamo{};
  for (std::size_t component = 0; component < 4; ++component) {
    zamo.at(component) = tetrad.lorentz.at(0).at(component) +
                         (direction.at(0) * tetrad.lorentz.at(1).at(component)) +
                         (direction.at(1) * tetrad.lorentz.at(2).at(component)) +
                         (direction.at(2) * tetrad.lorentz.at(3).at(component));
  }
  const EquatorialFrame &frame = tetrad.frame;
  PhotonConstants constants;
  constants.angularMomentum = frame.varpi * zamo.at(3);
  constants.pTheta = frame.r * zamo.at(2);
  constants.radialMomentum = zamo.at(1);
  constants.energy = (frame.alpha * zamo.at(0)) + (frame.omega * constants.angularMomentum);
  constants.positiveEnergy = constants.energy > 0.0;
  if (!constants.positiveEnergy) {
    return constants;
  }
  constants.lambda = constants.angularMomentum / constants.energy;
  constants.eta = (constants.pTheta * constants.pTheta) / (constants.energy * constants.energy);
  constants.g = 1.0 / constants.energy;

  const RadialPotential potential = radialPotential(frame.spin, constants.lambda, constants.eta);
  const double r = frame.r;
  const double outerHorizon = 1.0 + horizonOffset(frame.epsilon);
  // Outward, any obstacle stops the photon for good: it turns back, or it
  // spirals onto the photon orbit. Inward, only a simple zero above the
  // horizon sends it back out.
  const bool clearAbove =
      firstRadialObstacle(potential, r, std::numeric_limits<double>::max()) ==
      RadialObstacle::None;
  const bool bounceBelow =
      firstRadialObstacle(potential, r, outerHorizon) == RadialObstacle::Turning;
  if (constants.radialMomentum > 0.0) {
    constants.escapesToInfinity = clearAbove;
    constants.fromInfinity = clearAbove && bounceBelow;
  } else if (constants.radialMomentum < 0.0) {
    constants.escapesToInfinity = clearAbove && bounceBelow;
    constants.fromInfinity = clearAbove;
  } else {
    const bool periapsis = potential.slope(r) > 0.0;
    constants.escapesToInfinity = periapsis && clearAbove;
    constants.fromInfinity = constants.escapesToInfinity;
  }
  return constants;
}

} // namespace physics::kerr_observer

#endif // BLACKHOLE_PHYSICS_KERR_OBSERVER_H
