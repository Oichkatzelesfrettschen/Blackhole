#include "physics/kerr.h"

#include <boost/multiprecision/mpfr.hpp>
#include <cmath>
#include <iostream>

using Mpfr256 =
    boost::multiprecision::number<boost::multiprecision::mpfr_float_backend<256>>;

template <typename T>
struct KerrConstsT {
  T E;
  T Lz;
  T Q;
};

template <typename T>
struct KerrStateT {
  T r;
  T theta;
  T phi;
  T t;
  T sign_r;
  T sign_theta;
};

template <typename T>
struct KerrPotentialsT {
  T R;
  T dRdr;
  T Theta;
  T dThetadtheta;
};

template <typename T>
static KerrConstsT<T> equatorial_consts(T impact_param, T energy) {
  KerrConstsT<T> c{};
  c.E = energy;
  c.Lz = impact_param * energy;
  c.Q = T(0);
  return c;
}

template <typename T>
static KerrStateT<T> equatorial_state(T r, T phi, T sign_r) {
  KerrStateT<T> s{};
  s.r = r;
  s.theta = T(0.5) * T(physics::PI);
  s.phi = phi;
  s.t = T(0);
  s.sign_r = sign_r >= T(0) ? T(1) : T(-1);
  s.sign_theta = T(1);
  return s;
}

template <typename T>
static KerrPotentialsT<T> kerr_potentials_t(T r, T theta, T mass, T a,
                                            const KerrConstsT<T> &c) {
  using std::cos;
  using std::sin;
  using std::sqrt;

  const T M = T(physics::G) * mass / T(physics::C2);
  const T rr = r * r;
  const T aa = a * a;
  const T sin_theta = sin(theta);
  const T cos_theta = cos(theta);
  T sin2 = sin_theta * sin_theta;
  if (sin2 < T(1e-12)) {
    sin2 = T(1e-12);
  }
  const T cos2 = cos_theta * cos_theta;

  const T Delta = rr - T(2) * M * r + aa;
  const T A = (rr + aa) * c.E - a * c.Lz;
  const T Lz_minus_aE = c.Lz - a * c.E;

  KerrPotentialsT<T> p{};
  p.R = A * A - Delta * (c.Q + Lz_minus_aE * Lz_minus_aE);

  const T dA_dr = T(2) * r * c.E;
  const T dDelta_dr = T(2) * r - T(2) * M;
  p.dRdr = T(2) * A * dA_dr - dDelta_dr * (c.Q + Lz_minus_aE * Lz_minus_aE);

  p.Theta = c.Q + (aa * c.E * c.E * cos2) - (c.Lz * c.Lz / sin2);
  p.dThetadtheta = -T(2) * aa * c.E * c.E * cos_theta * sin_theta +
                   T(2) * c.Lz * c.Lz * cos_theta / (sin2 * sin_theta);

  return p;
}

template <typename T>
static KerrStateT<T> kerr_step_mino_t(const KerrStateT<T> &state, T mass, T a,
                                      const KerrConstsT<T> &c, T dlam) {
  using std::sin;
  using std::sqrt;

  KerrStateT<T> next = state;

  const T M = T(physics::G) * mass / T(physics::C2);
  const T r = state.r;
  const T theta = state.theta;
  const KerrPotentialsT<T> p = kerr_potentials_t(r, theta, mass, a, c);

  const T R = p.R > T(0) ? p.R : T(0);
  const T Theta = p.Theta > T(0) ? p.Theta : T(0);

  const T dr_dlam = state.sign_r * sqrt(R);
  const T dtheta_dlam = state.sign_theta * sqrt(Theta);

  const T sin_theta = sin(theta);
  T sin2 = sin_theta * sin_theta;
  if (sin2 < T(1e-12)) {
    sin2 = T(1e-12);
  }
  const T Delta = r * r - T(2) * M * r + a * a;
  const T A = (r * r + a * a) * c.E - a * c.Lz;
  const T delta_safe = Delta > T(1e-12) ? Delta : T(1e-12);

  const T dphi_dlam = (c.Lz / sin2) - a * c.E + (a * A / delta_safe);
  const T dt_dlam = ((r * r + a * a) * A / delta_safe) +
                    a * (c.Lz - a * c.E * sin2);

  next.r += dlam * dr_dlam;
  next.theta += dlam * dtheta_dlam;
  next.phi += dlam * dphi_dlam;
  next.t += dlam * dt_dlam;

  const T min_theta = T(1e-6);
  const T max_theta = T(physics::PI) - T(1e-6);
  if (next.theta < min_theta) {
    next.theta = min_theta;
  } else if (next.theta > max_theta) {
    next.theta = max_theta;
  }

  return next;
}

static bool approx_equal(double a, double b, double tol) {
  const double diff = std::abs(a - b);
  const double scale = std::max(1.0, std::abs(b));
  return diff <= tol * scale;
}

int main() {
  const double mass = 10.0 * physics::M_SUN;
  const double r_s = physics::schwarzschild_radius(mass);
  const double a = 0.3 * (physics::G * mass / physics::C2);
  const double impact = 8.0 * r_s;
  const double dlam = 1e-12;
  const int steps = 100;

  const physics::KerrGeodesicConsts c =
      physics::kerr_equatorial_consts(impact, 1.0);
  physics::KerrGeodesicState state =
      physics::kerr_equatorial_state(50.0 * r_s, 0.0, -1.0);

  for (int i = 0; i < steps; ++i) {
    state = physics::kerr_step_mino(state, mass, a, c, dlam);
  }

  const Mpfr256 mass_hp = Mpfr256(mass);
  const Mpfr256 r_s_hp = Mpfr256(r_s);
  const Mpfr256 a_hp = Mpfr256(a);
  const Mpfr256 impact_hp = Mpfr256(impact);
  const Mpfr256 dlam_hp = Mpfr256(dlam);

  const KerrConstsT<Mpfr256> c_hp = equatorial_consts(impact_hp, Mpfr256(1));
  KerrStateT<Mpfr256> state_hp =
      equatorial_state(Mpfr256(50) * r_s_hp, Mpfr256(0), Mpfr256(-1));

  for (int i = 0; i < steps; ++i) {
    state_hp = kerr_step_mino_t(state_hp, mass_hp, a_hp, c_hp, dlam_hp);
  }

  const double r_hp = state_hp.r.convert_to<double>();
  const double theta_hp = state_hp.theta.convert_to<double>();
  const double phi_hp = state_hp.phi.convert_to<double>();

  constexpr double kTol = 1e-9;
  const bool r_ok = approx_equal(state.r, r_hp, kTol);
  const bool theta_ok = approx_equal(state.theta, theta_hp, kTol);
  const bool phi_ok = approx_equal(state.phi, phi_hp, kTol);

  if (!r_ok || !theta_ok || !phi_ok) {
    std::cerr << "precision regression failed\n";
    std::cerr << "r: double=" << state.r << " mpfr=" << r_hp << "\n";
    std::cerr << "theta: double=" << state.theta << " mpfr=" << theta_hp << "\n";
    std::cerr << "phi: double=" << state.phi << " mpfr=" << phi_hp << "\n";
    return 1;
  }

  std::cout << "precision regression ok\n";
  return 0;
}
