#include <algorithm>
#include <cmath>
#include <iostream>
#include <utility>

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
  T signR;
  T signTheta;
};

template <typename T>
struct KerrPotentialsT {
  T r;
  T dRdr;
  T theta;
  T dThetadtheta;
};

template <typename T>
KerrConstsT<T> equatorialConsts(const T &impactParam, const T &energy) {
  KerrConstsT<T> c{};
  c.e = energy;
  c.lz = impactParam * energy;
  c.q = T(0);
  return c;
}

template <typename T> KerrStateT<T> equatorialState(T r, T phi, const T &signR) {
  KerrStateT<T> s{};
  s.r = std::move(r);
  s.theta = T(0.5) * T(physics::PI);
  s.phi = std::move(phi);
  s.t = T(0);
  s.signR = signR >= T(0) ? T(1) : T(-1);
  s.signTheta = T(1);
  return s;
}

template <typename T>
KerrPotentialsT<T> kerrPotentialsT(const T &r, const T &theta, const T &mass, const T &a,
                                          const KerrConstsT<T> &c) {
  using std::cos;
  using std::sin;
  using std::sqrt;

  const T m = T(physics::G) * mass / T(physics::C2);
  const T rr = r * r;
  const T aa = a * a;
  const T sinTheta = sin(theta);
  const T cosTheta = cos(theta);
  T sin2 = sinTheta * sinTheta;
  if (sin2 < T(1e-12)) {
    sin2 = T(1e-12);
  }
  const T cos2 = cosTheta * cosTheta;

  const T delta = rr - (T(2) * m * r) + aa;
  const T a = ((rr + aa) * c.e) - (a * c.lz);
  const T lzMinusAE = c.lz - (a * c.e);

  KerrPotentialsT<T> p{};
  p.r = (a * a) - (delta * (c.q + (lzMinusAE * lzMinusAE)));

  const T dADr = T(2) * r * c.e;
  const T dDeltaDr = (T(2) * r) - (T(2) * m);
  p.dRdr = (T(2) * a * dADr) - (dDeltaDr * (c.q + (lzMinusAE * lzMinusAE)));

  p.theta = c.q + (aa * c.e * c.e * cos2) - (c.lz * c.lz / sin2);
  p.dThetadtheta = (-T(2) * aa * c.e * c.e * cosTheta * sinTheta) +
                   (T(2) * c.lz * c.lz * cosTheta / (sin2 * sinTheta));

  return p;
}

template <typename T>
KerrStateT<T> kerrStepMinoT(const KerrStateT<T> &state, const T &mass, const T &a,
                                   const KerrConstsT<T> &c, const T &dlam) {
  using std::sin;
  using std::sqrt;

  KerrStateT<T> next = state;

  const T m = T(physics::G) * mass / T(physics::C2);
  const T r = state.r;
  const T theta = state.theta;
  const KerrPotentialsT<T> p = kerrPotentialsT(r, theta, mass, a, c);

  const T r = p.r > T(0) ? p.r : T(0);
  const T theta = p.theta > T(0) ? p.theta : T(0);

  const T drDlam = state.signR * sqrt(r);
  const T dthetaDlam = state.signTheta * sqrt(theta);

  const T sinTheta = sin(theta);
  T sin2 = sinTheta * sinTheta;
  if (sin2 < T(1e-12)) {
    sin2 = T(1e-12);
  }
  const T delta = (r * r) - (T(2) * m * r) + (a * a);
  const T a = (((r * r) + (a * a)) * c.e) - (a * c.lz);
  const T deltaSafe = delta > T(1e-12) ? delta : T(1e-12);

  const T dphiDlam = (c.lz / sin2) - (a * c.e) + (a * a / deltaSafe);
  const T dtDlam = (((r * r) + (a * a)) * a / deltaSafe) + (a * (c.lz - (a * c.e * sin2)));

  next.r += dlam * drDlam;
  next.theta += dlam * dthetaDlam;
  next.phi += dlam * dphiDlam;
  next.t += dlam * dtDlam;

  const T minTheta = T(1e-6);
  const T maxTheta = T(physics::PI) - T(1e-6);
  if (next.theta < minTheta) {
    next.theta = minTheta;
  } else if (next.theta > maxTheta) {
    next.theta = maxTheta;
  }

  return next;
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
  physics::KerrGeodesicState state = physics::kerrEquatorialState(50.0 * rS, 0.0, -1.0);

  for (int i = 0; i < steps; ++i) {
    state = physics::kerrStepMino(state, mass, a, c, dlam);
  }

  const Mpfr256 massHp = Mpfr256(mass);
  const Mpfr256 rSHp = Mpfr256(rS);
  const Mpfr256 aHp = Mpfr256(a);
  const Mpfr256 impactHp = Mpfr256(impact);
  const Mpfr256 dlamHp = Mpfr256(dlam);

  const KerrConstsT<Mpfr256> cHp = equatorialConsts(impactHp, Mpfr256(1));
  KerrStateT<Mpfr256> stateHp = equatorialState(Mpfr256(50) * rSHp, Mpfr256(0), Mpfr256(-1));

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
