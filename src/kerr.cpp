#include "kerr.hpp"
#include <cmath>

namespace bh {
static inline double Delta(double r, const KerrParams& k){ return r*r - 2*k.M*r + k.a*k.a; }
static inline double Sigma(double r, double th, const KerrParams& k){ return r*r + k.a*k.a*std::cos(th)*std::cos(th); }

Potentials potentials(double r, double th, const KerrParams& k, const GeodesicConsts& c){
  const double ct = std::cos(th), st = std::sin(th);
  const double a = k.a, M = k.M;
  const double E = c.E, Lz = c.Lz, Q = c.Q;
  const double rr = r*r;
  const double A = (rr + a*a)*E - a*Lz;
  const double Delta_r = rr - 2*M*r + a*a;
  Potentials p{};
  p.R = A*A - (Lz - a*E)*(Lz - a*E) - Q*Delta_r; // simplified for null
  p.dRdr = 2*A*(2*r*E) - ((2*r - 2*M)*Q + 0); // placeholder derivative
  const double C = Q + (Lz - a*E)*(Lz - a*E) - a*a*E*E*ct*ct;
  p.Theta = C - (Lz*Lz/ (st*st));
  p.dThetadth = 0; // TODO: fill exact derivative
  return p;
}

std::array<double,4> step_mino(const std::array<double,4>& s,
                               const KerrParams& k, const GeodesicConsts& c,
                               double dlam){
  // Minimal placeholder: forward Euler in (r,theta) using potential gradients; phi,t unchanged
  auto p = potentials(s[0], s[1], k, c);
  std::array<double,4> n = s;
  n[0] += dlam * p.dRdr; // r
  n[1] += dlam * p.dThetadth; // theta
  return n;
}

double redshift_g(const std::array<double,4>& kvec, const std::array<double,4>& u_em){
  // g = -k_mu u^mu / (k_mu u^mu)obs ; here return numerator only (observer set elsewhere)
  return -(kvec[0]*u_em[0] - kvec[1]*u_em[1] - kvec[2]*u_em[2] - kvec[3]*u_em[3]);
}

Orbits characteristic_orbits(const KerrParams& k){
  // Placeholder: simple Schwarzschild limits when a=0; Kerr needs full root-finding
  Orbits o{};
  if (std::abs(k.a) < 1e-12){ o.r_ph_pro = o.r_ph_ret = 3.0*k.M; o.r_isco_pro = o.r_isco_ret = 6.0*k.M; }
  else { o.r_ph_pro = 3.0*k.M; o.r_ph_ret = 3.0*k.M; o.r_isco_pro = 6.0*k.M; o.r_isco_ret = 6.0*k.M; }
  return o;
}
}
