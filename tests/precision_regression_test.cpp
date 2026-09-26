#include <algorithm>
#include <cmath>
#include <iostream>
#include <utility>

#include <boost/multiprecision/mpfr.hpp>

#include "constants.h"
#include "physics/constants.h"
#include "physics/kerr.h"
#include "physics/schwarzschild.h"
#include "schwarzschild.h"

using Mpfr256 =
    boost::multiprecision::number<boost::multiprecision::mpfr_float_backend<256>>;

namespace {

template <typename T>
struct KerrConstsT {
  T e;
  T lz;
  T q;
};

template <typename T>
struct KerrStateT {
  T r;
  T theta;
  T phi;
  T t;
  T vr;
  T vtheta;
};

template <typename T>
struct KerrDerivsT {
  T dr;
  T dtheta;
  T dvr;
  T dvtheta;
  T dphi;
  T dt;
};

template <typename T>
KerrConstsT<T> equatorialConsts(const T &impactParam, const T &energy) {
  KerrConstsT<T> c{};
  c.e = energy;
  c.lz = impactParam * energy;
  c.q = T(0);
  return c;
}

// Second-order Mino-time right-hand side at precision T; mirrors
// physics::kerrStepMino (kerr.cpp) with Carter's polar potential.
template <typename T>
KerrDerivsT<T> kerrDerivsT(const KerrStateT<T> &s, const T &mass, const T &spin,
                           const KerrConstsT<T> &c) {
  using std::cos;
  using std::sin;

  const T m = T(physics::G) * mass / T(physics::C2);
  const T rr = s.r * s.r;
  const T aa = spin * spin;
  const T sinTheta = sin(s.theta);
  const T cosTheta = cos(s.theta);
  T sin2 = sinTheta * sinTheta;
  if (sin2 < T(1e-12)) {
    sin2 = T(1e-12);
  }
  const T delta = rr - (T(2) * m * s.r) + aa;
  const T bigP = ((rr + aa) * c.e) - (spin * c.lz);
  const T lzMinusAE = c.lz - (spin * c.e);
  const T qEff = c.q + (lzMinusAE * lzMinusAE);
  const T deltaSafe = delta > T(1e-12) ? delta : T(1e-12);

  KerrDerivsT<T> d{};
  d.dr = s.vr;
  d.dtheta = s.vtheta;
  d.dvr = (T(2) * s.r * c.e * bigP) - ((s.r - m) * qEff);
  d.dvtheta = (-(aa * c.e * c.e * cosTheta * sinTheta)) +
              (c.lz * c.lz * cosTheta / (sin2 * sinTheta));
  d.dphi = (c.lz / sin2) - (spin * c.e) + (spin * bigP / deltaSafe);
  d.dt = ((rr + aa) * bigP / deltaSafe) + (spin * (c.lz - (spin * c.e * sin2)));
  return d;
}

template <typename T>
KerrStateT<T> advanceT(const KerrStateT<T> &s, const KerrDerivsT<T> &d, const T &h) {
  KerrStateT<T> o = s;
  o.r += h * d.dr;
  o.theta += h * d.dtheta;
  o.vr += h * d.dvr;
  o.vtheta += h * d.dvtheta;
  o.phi += h * d.dphi;
  o.t += h * d.dt;
  return o;
}

template <typename T>
KerrStateT<T> kerrStepMinoT(const KerrStateT<T> &s, const T &mass, const T &spin,
                            const KerrConstsT<T> &c, const T &h) {
  const T half = h / T(2);
  const KerrDerivsT<T> k1 = kerrDerivsT(s, mass, spin, c);
  const KerrDerivsT<T> k2 = kerrDerivsT(advanceT(s, k1, half), mass, spin, c);
  const KerrDerivsT<T> k3 = kerrDerivsT(advanceT(s, k2, half), mass, spin, c);
  const KerrDerivsT<T> k4 = kerrDerivsT(advanceT(s, k3, h), mass, spin, c);
  KerrDerivsT<T> sum{};
  sum.dr = (k1.dr + (T(2) * k2.dr) + (T(2) * k3.dr) + k4.dr) / T(6);
  sum.dtheta = (k1.dtheta + (T(2) * k2.dtheta) + (T(2) * k3.dtheta) + k4.dtheta) / T(6);
  sum.dvr = (k1.dvr + (T(2) * k2.dvr) + (T(2) * k3.dvr) + k4.dvr) / T(6);
  sum.dvtheta = (k1.dvtheta + (T(2) * k2.dvtheta) + (T(2) * k3.dvtheta) + k4.dvtheta) / T(6);
  sum.dphi = (k1.dphi + (T(2) * k2.dphi) + (T(2) * k3.dphi) + k4.dphi) / T(6);
  sum.dt = (k1.dt + (T(2) * k2.dt) + (T(2) * k3.dt) + k4.dt) / T(6);
  return advanceT(s, sum, h);
}

bool approxEqual(double a, double b, double tol) {
  const double diff = std::abs(a - b);
  const double scale = std::max(1.0, std::abs(b));
  return diff <= tol * scale;
}

} // namespace

int main() {
  const double mass = 10.0 * physics::M_SUN;
  const double rS = physics::schwarzschildRadius(mass);
  const double a = 0.3 * (physics::G * mass / physics::C2);
  const double impact = 8.0 * rS;
  const double dlam = 1e-12;
  const int steps = 100;

  const physics::KerrGeodesicConsts c =
      physics::kerrEquatorialConsts(impact, 1.0);
  physics::KerrGeodesicState state = physics::kerrInitMinoVelocities(
      physics::kerrEquatorialState(50.0 * rS, 0.0, -1.0), mass, a, c);

  for (int i = 0; i < steps; ++i) {
    state = physics::kerrStepMino(state, mass, a, c, dlam);
  }

  const Mpfr256 massHp = Mpfr256(mass);
  const Mpfr256 rSHp = Mpfr256(rS);
  const Mpfr256 aHp = Mpfr256(a);
  const Mpfr256 impactHp = Mpfr256(impact);
  const Mpfr256 dlamHp = Mpfr256(dlam);

  const KerrConstsT<Mpfr256> cHp = equatorialConsts(impactHp, Mpfr256(1));
  // Same initial point and velocity as the double-precision run, promoted.
  KerrStateT<Mpfr256> stateHp{};
  stateHp.r = Mpfr256(50) * rSHp;
  stateHp.theta = Mpfr256(0.5) * Mpfr256(physics::PI);
  stateHp.phi = Mpfr256(0);
  stateHp.t = Mpfr256(0);
  stateHp.vr = Mpfr256(physics::kerrInitMinoVelocities(
                           physics::kerrEquatorialState(50.0 * rS, 0.0, -1.0), mass, a, c)
                           .vr);
  stateHp.vtheta = Mpfr256(0);

  for (int i = 0; i < steps; ++i) {
    stateHp = kerrStepMinoT(stateHp, massHp, aHp, cHp, dlamHp);
  }

  const auto rHp = stateHp.r.convert_to<double>();
  const auto thetaHp = stateHp.theta.convert_to<double>();
  const auto phiHp = stateHp.phi.convert_to<double>();

  constexpr double kTol = 1e-9;
  const bool rOk = approxEqual(state.r, rHp, kTol);
  const bool thetaOk = approxEqual(state.theta, thetaHp, kTol);
  const bool phiOk = approxEqual(state.phi, phiHp, kTol);

  if (!rOk || !thetaOk || !phiOk) {
    std::cerr << "precision regression failed\n";
    std::cerr << "r: double=" << state.r << " mpfr=" << rHp << "\n";
    std::cerr << "theta: double=" << state.theta << " mpfr=" << thetaHp << "\n";
    std::cerr << "phi: double=" << state.phi << " mpfr=" << phiHp << "\n";
    return 1;
  }

  std::cout << "precision regression ok\n";
  return 0;
}
