// Full-K polarized transfer over one constant-coefficient segment:
// Blackhole RK4 (stokesStepFull) vs closed-form Lorentz-group propagator.
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include "physics/stokes_transport.h"
#include "exact2.h"
using physics::StokesVector; using physics::StokesEmission; using physics::FaradayPropagation;

// K' = K - alphaI*1 is an so(1,3) generator (boost eta=(aQ,0,aV), rotation rho=(rQ,0,rV)).
// Its minimal polynomial is (x^2 - L1^2)(x^2 + L2^2) with (L1 + i L2)^2 = (eta + i rho).(eta + i rho),
// the squared norm of the complex (biquaternion / Cl(3,0)) vector w = eta + i rho.
struct Kp { double aQ, aV, rV, rQ; };
static inline void applyKp(const Kp& k, const double v[4], double o[4]) {
  o[0] = k.aQ * v[1] + k.aV * v[3];
  o[1] = k.aQ * v[0] + k.rV * v[2];
  o[2] = -k.rV * v[1] + k.rQ * v[3];
  o[3] = k.aV * v[0] - k.rQ * v[2];
}
static inline double sinhc(double x) { return std::abs(x) < 1e-4 ? 1.0 + x * x / 6.0 : std::sinh(x) / x; }
static inline double sinc(double x) { return std::abs(x) < 1e-4 ? 1.0 - x * x / 6.0 : std::sin(x) / x; }
// Exact S(ds) = Sinf + exp(-aI ds) exp(-K' ds) (S0 - Sinf), Sinf = K^{-1} J.
static StokesVector exactStep(const StokesVector& s, const StokesEmission& em, const FaradayPropagation& p) {
  const Kp k{p.alphaQ, p.alphaV, p.rhoV, p.rhoQ};
  const double e2 = k.aQ * k.aQ + k.aV * k.aV, r2 = k.rV * k.rV + k.rQ * k.rQ;
  const double er = k.aQ * k.rQ + k.aV * k.rV;  // eta.rho
  const double h = 0.5 * (e2 - r2), root = std::sqrt(h * h + er * er);
  const double L1s = std::max(0.0, h + root), L2s = std::max(0.0, root - h);
  const double L1 = std::sqrt(L1s), L2 = std::sqrt(L2s), D = L1s + L2s;
  const double aI = p.alphaI, ds = p.dsCm;
  // Steady state Sinf = (aI + K')^{-1} J by the same minimal-polynomial calculus.
  double J[4] = {em.jI, em.jQ, em.jU, em.jV}, J1[4], J2[4], J3[4];
  applyKp(k, J, J1); applyKp(k, J1, J2); applyKp(k, J2, J3);
  double sinf[4];
  if (D < 1e-300) {
    for (int i = 0; i < 4; ++i) sinf[i] = J[i] / aI;
  } else {
    const double g1 = 1.0 / (aI * aI - L1s), g2 = 1.0 / (aI * aI + L2s);
    const double d2 = aI * (g1 - g2) / D, d0 = aI * (L2s * g1 + L1s * g2) / D;
    const double e3 = -(g1 - g2) / D, e1 = -(L2s * g1 + L1s * g2) / D;
    for (int i = 0; i < 4; ++i) sinf[i] = d0 * J[i] + e1 * J1[i] + d2 * J2[i] + e3 * J3[i];
  }
  double v[4] = {s.i - sinf[0], s.q - sinf[1], s.u - sinf[2], s.v - sinf[3]}, v1[4], v2[4], v3[4];
  applyKp(k, v, v1); applyKp(k, v1, v2); applyKp(k, v2, v3);
  const double ch = std::cosh(L1 * ds), c = std::cos(L2 * ds);
  double a0, a2, b1, b3;
  if (D < 1e-300) { a0 = 1; a2 = 0; b1 = ds; b3 = 0; }
  else {
    const double sh = ds * sinhc(L1 * ds), sn = ds * sinc(L2 * ds);  // sinh(L1 ds)/L1, sin(L2 ds)/L2
    a2 = (ch - c) / D; a0 = (L2s * ch + L1s * c) / D;
    b3 = (sh - sn) / D; b1 = (L2s * sh + L1s * sn) / D;
  }
  const double E = std::exp(-aI * ds);
  double o[4];
  for (int i = 0; i < 4; ++i) o[i] = sinf[i] + E * (a0 * v[i] - b1 * v1[i] + a2 * v2[i] - b3 * v3[i]);
  return {.i = o[0], .q = o[1], .u = o[2], .v = o[3]};
}
static StokesVector exact2Step(const StokesVector& s, const StokesEmission& em, const FaradayPropagation& p) {
  const double S0[4] = {s.i, s.q, s.u, s.v}, J[4] = {em.jI, em.jQ, em.jU, em.jV};
  const auto o = ex2::step(S0, J, p.alphaI, p.alphaQ, p.alphaV, p.rhoV, p.rhoQ, p.dsCm);
  return {.i = o.i, .q = o.q, .u = o.u, .v = o.v};
}
static StokesVector rk4Sub(StokesVector s, const StokesEmission& em, FaradayPropagation p, int n) {
  p.dsCm /= n;
  for (int i = 0; i < n; ++i) s = physics::stokesStepFull(s, em, p);
  return s;
}
struct Case { double tauF; FaradayPropagation p; StokesEmission em; StokesVector s0, ref; };
int main() {
  std::vector<Case> cs; std::ifstream in("ref_mid.csv"); std::string line;
  while (std::getline(in, line)) {
    std::stringstream ss(line); std::string t; std::vector<double> f;
    while (std::getline(ss, t, ',')) f.push_back(std::stod(t));
    Case c{}; c.tauF = f[0];
    c.p.dsCm = f[1]; c.p.alphaI = f[2]; c.p.alphaQ = f[3]; c.p.alphaV = f[4]; c.p.rhoV = f[5]; c.p.rhoQ = f[6];
    c.em = {.jI = f[7], .jQ = f[8], .jU = f[9], .jV = f[10]};
    c.s0 = {.i = f[11], .q = f[12], .u = f[13], .v = f[14]};
    c.ref = {.i = f[15], .q = f[16], .u = f[17], .v = f[18]};
    cs.push_back(c);
  }
  auto err = [](const StokesVector& a, const StokesVector& r) {
    const double d = std::sqrt((a.i - r.i) * (a.i - r.i) + (a.q - r.q) * (a.q - r.q) + (a.u - r.u) * (a.u - r.u) + (a.v - r.v) * (a.v - r.v));
    return d / std::sqrt(r.i * r.i + r.q * r.q + r.u * r.u + r.v * r.v);
  };
  std::puts("tauF | exact(Sinf split) | exact2(direct integral) max_rel | RK4 1 step max_rel | RK4 substeps n=ceil(2*|K|ds) max_rel (mean n)");
  for (double tf : {110.0, 1100.0, 310.0, 1300.0, 1010.0, 2000.0, 3010.0, 4000.0}) {
    double ee2 = 0, ee = 0, e1 = 0, en = 0, nsum = 0; int cnt = 0;
    for (const auto& c : cs) if (std::abs(c.tauF - tf) < 1e-6) {
      ee = std::max(ee, err(exactStep(c.s0, c.em, c.p), c.ref)); ee2 = std::max(ee2, err(exact2Step(c.s0, c.em, c.p), c.ref));
      e1 = std::max(e1, err(physics::stokesStepFull(c.s0, c.em, c.p), c.ref));
      const double kn = std::sqrt(c.p.alphaI * c.p.alphaI + c.p.rhoV * c.p.rhoV + c.p.rhoQ * c.p.rhoQ) * c.p.dsCm;
      const int n = std::max(1, int(std::ceil(2.0 * kn)));
      en = std::max(en, err(rk4Sub(c.s0, c.em, c.p, n), c.ref)); nsum += n; ++cnt;
    }
    std::printf("%7g | %.2e | %.2e | %.2e | %.2e (%.0f)\n", tf, ee, ee2, e1, en, nsum / cnt);
  }

  // Cost per single call (RK4 one step vs exact) over all cases.
  const int reps = 200000 / int(cs.size()) + 1;
  auto t = [&](auto f) {
    double best = 1e30;
    for (int k = 0; k < 5; ++k) {
      volatile double sink = 0; auto t0 = std::chrono::steady_clock::now();
      for (int r = 0; r < reps; ++r) for (const auto& c : cs) { auto o = f(c); sink = sink + o.q; }
      auto t1 = std::chrono::steady_clock::now();
      best = std::min(best, std::chrono::duration<double, std::nano>(t1 - t0).count() / (double(reps) * cs.size()));
    }
    return best;
  };
  std::printf("ns/call (min of 5): RK4 single step %.1f | exact closed form %.1f | simplified stokesStep %.1f | exact2 %.1f\n",
              t([](const Case& c) { return physics::stokesStepFull(c.s0, c.em, c.p); }),
              t([](const Case& c) { return exactStep(c.s0, c.em, c.p); }),
              t([](const Case& c) { return physics::stokesStep(c.s0, c.em, c.p.alphaI, c.p.rhoV, c.p.dsCm); }),
              t([](const Case& c) { return exact2Step(c.s0, c.em, c.p); }));
}
