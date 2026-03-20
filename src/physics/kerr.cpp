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
 * @brief First-order derivatives of Kerr geodesic coordinates w.r.t. Mino time.
 *
 * Carries dr/dlambda, dtheta/dlambda, dphi/dlambda, dt/dlambda for one RK4 stage.
 */
struct KerrMinoDerivs {
  double dr;
  double dtheta;
  double dphi;
  double dt;
};

/**
 * @brief Evaluate Kerr Mino-time derivatives at a given geodesic state.
 *
 * Computes the right-hand side of the Kerr geodesic ODEs using the effective
 * potentials R(r) and Theta(theta) with the Carter constant Q.
 *
 * @param state Current geodesic state (r, theta, phi, t, sign flags)
 * @param mass  Black hole mass [g]
 * @param a     Spin parameter [cm]
 * @param c     Conserved quantities (E, L_z, Q)
 * @return Mino-time derivatives (dr, dtheta, dphi, dt)
 */
KerrMinoDerivs kerrMinoDerivatives(const KerrGeodesicState& state, double mass, double a,
                                   const KerrGeodesicConsts& c) {
  const double mGeom = G * mass / C2;
  const double r = state.r;
  const double theta = state.theta;
  const KerrPotentials p = kerrPotentials(r, theta, mass, a, c);

  const double rPot = std::max(p.rPot, 0.0);
  const double thetaPot = std::max(p.thetaPot, 0.0);

  const double drDlam = state.signR * std::sqrt(rPot);
  const double dthetaDlam = state.signTheta * std::sqrt(thetaPot);

  const double sinTheta = std::sin(theta);
  const double sin2 = std::max(sinTheta * sinTheta, 1e-12);
  const double delta = (r * r) - (2.0 * mGeom * r) + (a * a);
  const double aFactor = (((r * r) + (a * a)) * c.e) - (a * c.lz);
  const double deltaSafe = std::max(delta, 1e-12);

  KerrMinoDerivs derivs{};
  derivs.dr = drDlam;
  derivs.dtheta = dthetaDlam;
  derivs.dphi = (c.lz / sin2) - (a * c.e) + (a * aFactor / deltaSafe);
  derivs.dt = ((((r * r) + (a * a)) * aFactor) / deltaSafe)
            + (a * (c.lz - (a * c.e * sin2)));
  return derivs;
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

  p.thetaPot = c.q + (aa * c.e * c.e * cos2) - (c.lz * c.lz / sin2);
  p.dThetadtheta =
      -(2.0 * aa * c.e * c.e * cosTheta * sinTheta)
      + (2.0 * c.lz * c.lz * cosTheta / (sin2 * sinTheta));

  return p;
}

KerrGeodesicState kerrStepMino(const KerrGeodesicState& state, double mass, double a,
                                const KerrGeodesicConsts& c, double dlam) {
  KerrGeodesicState next = state;

  const KerrMinoDerivs k1 = kerrMinoDerivatives(state, mass, a, c);

  KerrGeodesicState s2 = state;
  s2.r += 0.5 * dlam * k1.dr;
  s2.theta += 0.5 * dlam * k1.dtheta;
  s2.phi += 0.5 * dlam * k1.dphi;
  s2.t += 0.5 * dlam * k1.dt;
  const KerrMinoDerivs k2 = kerrMinoDerivatives(s2, mass, a, c);

  KerrGeodesicState s3 = state;
  s3.r += 0.5 * dlam * k2.dr;
  s3.theta += 0.5 * dlam * k2.dtheta;
  s3.phi += 0.5 * dlam * k2.dphi;
  s3.t += 0.5 * dlam * k2.dt;
  const KerrMinoDerivs k3 = kerrMinoDerivatives(s3, mass, a, c);

  KerrGeodesicState s4 = state;
  s4.r += dlam * k3.dr;
  s4.theta += dlam * k3.dtheta;
  s4.phi += dlam * k3.dphi;
  s4.t += dlam * k3.dt;
  const KerrMinoDerivs k4 = kerrMinoDerivatives(s4, mass, a, c);

  next.r += dlam * (k1.dr + (2.0 * k2.dr) + (2.0 * k3.dr) + k4.dr) / 6.0;
  next.theta += dlam * (k1.dtheta + (2.0 * k2.dtheta) + (2.0 * k3.dtheta) + k4.dtheta) / 6.0;
  next.phi += dlam * (k1.dphi + (2.0 * k2.dphi) + (2.0 * k3.dphi) + k4.dphi) / 6.0;
  next.t += dlam * (k1.dt + (2.0 * k2.dt) + (2.0 * k3.dt) + k4.dt) / 6.0;

  next.theta = std::clamp(next.theta, 1e-6, PI - 1e-6);

  return next;
}

} // namespace physics
