/**
 * @file kerr.cpp
 * @brief Implementation of Kerr geodesic integration (Mino-time RK4).
 */

#include "physics/kerr.h"
#include "physics/constants.h"

#include <algorithm>
#include <cmath>

namespace physics {

namespace {

/**
 * @brief Mino-time derivatives of the second-order Kerr geodesic system.
 */
struct KerrMinoDerivs {
  double dr;
  double dtheta;
  double dvr;
  double dvtheta;
  double dphi;
  double dt;
};

/**
 * @brief Evaluate the second-order Mino-time right-hand side at a state.
 *
 * dr = vr, dtheta = vtheta, dvr = R'(r)/2, dvtheta = Theta'(theta)/2, and the
 * Boyer-Lindquist phi and t rates from Carter's separated equations.
 *
 * @param state Current geodesic state (r, theta, vr, vtheta, phi, t)
 * @param mass  Black hole mass [g]
 * @param a     Spin parameter [cm]
 * @param c     Conserved quantities (E, L_z, Q)
 */
KerrMinoDerivs kerrMinoDerivatives(const KerrGeodesicState& state, double mass, double a,
                                   const KerrGeodesicConsts& c) {
  const double mGeom = G * mass / C2;
  const double r = state.r;
  const double theta = state.theta;
  const KerrPotentials p = kerrPotentials(r, theta, mass, a, c);

  const double sinTheta = std::sin(theta);
  const double sin2 = std::max(sinTheta * sinTheta, 1e-12);
  const double delta = (r * r) - (2.0 * mGeom * r) + (a * a);
  const double aFactor = (((r * r) + (a * a)) * c.e) - (a * c.lz);
  const double deltaSafe = std::max(delta, 1e-12);

  KerrMinoDerivs derivs{};
  derivs.dr = state.vr;
  derivs.dtheta = state.vtheta;
  derivs.dvr = 0.5 * p.dRdr;
  derivs.dvtheta = 0.5 * p.dThetadtheta;
  derivs.dphi = (c.lz / sin2) - (a * c.e) + (a * aFactor / deltaSafe);
  derivs.dt = ((((r * r) + (a * a)) * aFactor) / deltaSafe)
            + (a * (c.lz - (a * c.e * sin2)));
  return derivs;
}

KerrGeodesicState kerrAdvance(const KerrGeodesicState& state, const KerrMinoDerivs& d,
                              double h) {
  KerrGeodesicState out = state;
  out.r += h * d.dr;
  out.theta += h * d.dtheta;
  out.vr += h * d.dvr;
  out.vtheta += h * d.dvtheta;
  out.phi += h * d.dphi;
  out.t += h * d.dt;
  return out;
}
} // namespace

KerrPotentials kerrPotentials(double r, double theta, double mass, double a,
                               const KerrGeodesicConsts& c) {
  const double mGeom = G * mass / C2;  // Geometric mass [cm]
  const double rr = r * r;
  const double aa = a * a;
  const double sinTheta = std::sin(theta);
  const double cosTheta = std::cos(theta);
  const double sin2 = std::max(sinTheta * sinTheta, 1e-12);
  const double cos2 = cosTheta * cosTheta;

  const double delta = rr - (2.0 * mGeom * r) + aa;
  const double aFactor = ((rr + aa) * c.e) - (a * c.lz);
  const double lzMinusAe = c.lz - (a * c.e);

  KerrPotentials p{};
  p.rPot = (aFactor * aFactor) - (delta * (c.q + (lzMinusAe * lzMinusAe)));

  const double dAdR = 2.0 * r * c.e;
  const double dDeltaDr = (2.0 * r) - (2.0 * mGeom);
  p.dRdr = (2.0 * aFactor * dAdR)
         - (dDeltaDr * (c.q + (lzMinusAe * lzMinusAe)));

  // Carter's polar potential carries lz^2 cot^2, not lz^2 / sin^2: the two
  // differ by lz^2, which would leave R short by Delta lz^2 for the same q.
  p.thetaPot = c.q + (aa * c.e * c.e * cos2) - (c.lz * c.lz * cos2 / sin2);
  // An lz = 0 ray reaches the axis, where sin(theta) = 0 exactly; its
  // centrifugal term is zero there rather than 0 / 0.
  const double centrifugal =
      (c.lz == 0.0) ? 0.0 : 2.0 * c.lz * c.lz * cosTheta / (sin2 * sinTheta);
  p.dThetadtheta = -(2.0 * aa * c.e * c.e * cosTheta * sinTheta) + centrifugal;

  return p;
}

KerrGeodesicState kerrInitMinoVelocities(const KerrGeodesicState& state, double mass,
                                         double a, const KerrGeodesicConsts& c) {
  const KerrPotentials p = kerrPotentials(state.r, state.theta, mass, a, c);
  KerrGeodesicState out = state;
  out.vr = ((state.signR >= 0.0) ? 1.0 : -1.0) * std::sqrt(std::max(p.rPot, 0.0));
  out.vtheta = ((state.signTheta >= 0.0) ? 1.0 : -1.0) * std::sqrt(std::max(p.thetaPot, 0.0));
  return out;
}

KerrGeodesicState kerrStepMino(const KerrGeodesicState& state, double mass, double a,
                                const KerrGeodesicConsts& c, double dlam) {
  const KerrMinoDerivs k1 = kerrMinoDerivatives(state, mass, a, c);
  const KerrMinoDerivs k2 = kerrMinoDerivatives(kerrAdvance(state, k1, 0.5 * dlam), mass, a, c);
  const KerrMinoDerivs k3 = kerrMinoDerivatives(kerrAdvance(state, k2, 0.5 * dlam), mass, a, c);
  const KerrMinoDerivs k4 = kerrMinoDerivatives(kerrAdvance(state, k3, dlam), mass, a, c);

  const auto combine = [](double d1, double d2, double d3, double d4) {
    return (d1 + (2.0 * d2) + (2.0 * d3) + d4) / 6.0;
  };
  KerrMinoDerivs sum{};
  sum.dr = combine(k1.dr, k2.dr, k3.dr, k4.dr);
  sum.dtheta = combine(k1.dtheta, k2.dtheta, k3.dtheta, k4.dtheta);
  sum.dvr = combine(k1.dvr, k2.dvr, k3.dvr, k4.dvr);
  sum.dvtheta = combine(k1.dvtheta, k2.dvtheta, k3.dvtheta, k4.dvtheta);
  sum.dphi = combine(k1.dphi, k2.dphi, k3.dphi, k4.dphi);
  sum.dt = combine(k1.dt, k2.dt, k3.dt, k4.dt);

  KerrGeodesicState next = kerrAdvance(state, sum, dlam);
  // Reflect through the pole instead of clamping: theta -> -theta (or
  // 2 pi - theta) with phi -> phi + pi keeps the ray on the same geodesic.
  if (next.theta < 0.0) {
    next.theta = -next.theta;
    next.vtheta = -next.vtheta;
    next.phi += PI;
  } else if (next.theta > PI) {
    next.theta = (2.0 * PI) - next.theta;
    next.vtheta = -next.vtheta;
    next.phi += PI;
  }
  next.signR = (next.vr >= 0.0) ? 1.0 : -1.0;
  next.signTheta = (next.vtheta >= 0.0) ? 1.0 : -1.0;
  return next;
}

} // namespace physics
