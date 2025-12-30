#pragma once
#include <array>
#include <optional>

namespace bh {
struct KerrParams { double M; double a; }; // mass M, spin a (|a|<M)
struct GeodesicConsts { double E; double Lz; double Q; };
struct TurnPoints { std::optional<double> r_min, r_max; std::optional<double> th_min, th_max; };

// Radial and polar potentials for null geodesics in Kerr
struct Potentials { double R; double dRdr; double Theta; double dThetadth; };

// Compute potentials given r, theta and constants
Potentials potentials(double r, double th, const KerrParams& k, const GeodesicConsts& c);

// Single adaptive step in Mino time lambda; returns new (r,theta,phi,t)
std::array<double,4> step_mino(const std::array<double,4>& state,
                               const KerrParams& k, const GeodesicConsts& c,
                               double dlam);

// Redshift g = nu_obs/nu_emit using k.u
double redshift_g(const std::array<double,4>& kvec, const std::array<double,4>& u_em);

// Photon ring and ISCO radii (prograde/retrograde)
struct Orbits { double r_ph_pro; double r_ph_ret; double r_isco_pro; double r_isco_ret; };
Orbits characteristic_orbits(const KerrParams& k);
}
