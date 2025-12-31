#include "physics/kerr.h"

#include <algorithm>
#include <cmath>

namespace physics {

namespace {
struct KerrMinoDerivs {
  double dr;
  double dtheta;
  double dphi;
  double dt;
};

KerrMinoDerivs kerr_mino_derivatives(const KerrGeodesicState &state, double mass, double a,
                                     const KerrGeodesicConsts &c) {
  const double M = G * mass / C2;
  const double r = state.r;
  const double theta = state.theta;
  const KerrPotentials p = kerr_potentials(r, theta, mass, a, c);

  const double R = std::max(p.R, 0.0);
  const double Theta = std::max(p.Theta, 0.0);

  const double dr_dlam = state.sign_r * std::sqrt(R);
  const double dtheta_dlam = state.sign_theta * std::sqrt(Theta);

  const double sin_theta = std::sin(theta);
  const double sin2 = std::max(sin_theta * sin_theta, 1e-12);
  const double Delta = r * r - 2.0 * M * r + a * a;
  const double A = (r * r + a * a) * c.E - a * c.Lz;
  const double delta_safe = std::max(Delta, 1e-12);

  KerrMinoDerivs derivs{};
  derivs.dr = dr_dlam;
  derivs.dtheta = dtheta_dlam;
  derivs.dphi = (c.Lz / sin2) - a * c.E + (a * A / delta_safe);
  derivs.dt = ((r * r + a * a) * A / delta_safe) + a * (c.Lz - a * c.E * sin2);
  return derivs;
}
} // namespace

KerrPotentials kerr_potentials(double r, double theta, double mass, double a,
                               const KerrGeodesicConsts &c) {
  const double M = G * mass / C2; // Geometric mass [cm]
  const double rr = r * r;
  const double aa = a * a;
  const double sin_theta = std::sin(theta);
  const double cos_theta = std::cos(theta);
  const double sin2 = std::max(sin_theta * sin_theta, 1e-12);
  const double cos2 = cos_theta * cos_theta;

  const double Delta = rr - 2.0 * M * r + aa;
  const double A = (rr + aa) * c.E - a * c.Lz;
  const double Lz_minus_aE = c.Lz - a * c.E;

  KerrPotentials p{};
  p.R = A * A - Delta * (c.Q + Lz_minus_aE * Lz_minus_aE);

  const double dA_dr = 2.0 * r * c.E;
  const double dDelta_dr = 2.0 * r - 2.0 * M;
  p.dRdr = 2.0 * A * dA_dr - dDelta_dr * (c.Q + Lz_minus_aE * Lz_minus_aE);

  p.Theta = c.Q + (aa * c.E * c.E * cos2) - (c.Lz * c.Lz / sin2);
  p.dThetadtheta =
      -2.0 * aa * c.E * c.E * cos_theta * sin_theta +
      2.0 * c.Lz * c.Lz * cos_theta / (sin2 * sin_theta);

  return p;
}

KerrGeodesicState kerr_step_mino(const KerrGeodesicState &state, double mass, double a,
                                 const KerrGeodesicConsts &c, double dlam) {
  KerrGeodesicState next = state;

  const KerrMinoDerivs k1 = kerr_mino_derivatives(state, mass, a, c);

  KerrGeodesicState s2 = state;
  s2.r += 0.5 * dlam * k1.dr;
  s2.theta += 0.5 * dlam * k1.dtheta;
  s2.phi += 0.5 * dlam * k1.dphi;
  s2.t += 0.5 * dlam * k1.dt;
  const KerrMinoDerivs k2 = kerr_mino_derivatives(s2, mass, a, c);

  KerrGeodesicState s3 = state;
  s3.r += 0.5 * dlam * k2.dr;
  s3.theta += 0.5 * dlam * k2.dtheta;
  s3.phi += 0.5 * dlam * k2.dphi;
  s3.t += 0.5 * dlam * k2.dt;
  const KerrMinoDerivs k3 = kerr_mino_derivatives(s3, mass, a, c);

  KerrGeodesicState s4 = state;
  s4.r += dlam * k3.dr;
  s4.theta += dlam * k3.dtheta;
  s4.phi += dlam * k3.dphi;
  s4.t += dlam * k3.dt;
  const KerrMinoDerivs k4 = kerr_mino_derivatives(s4, mass, a, c);

  next.r += dlam * (k1.dr + 2.0 * k2.dr + 2.0 * k3.dr + k4.dr) / 6.0;
  next.theta += dlam * (k1.dtheta + 2.0 * k2.dtheta + 2.0 * k3.dtheta + k4.dtheta) / 6.0;
  next.phi += dlam * (k1.dphi + 2.0 * k2.dphi + 2.0 * k3.dphi + k4.dphi) / 6.0;
  next.t += dlam * (k1.dt + 2.0 * k2.dt + 2.0 * k3.dt + k4.dt) / 6.0;

  next.theta = std::clamp(next.theta, 1e-6, PI - 1e-6);

  return next;
}

} // namespace physics
