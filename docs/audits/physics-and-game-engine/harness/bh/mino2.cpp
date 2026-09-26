#include <chrono>
#include <cmath>
#include <cstdio>
#include "physics/kerr.h"
using namespace physics;
// Second-order Mino form built from Blackhole's own kerrPotentials (dRdr, dThetadtheta),
// evolving phi and t with the same RHS kerrMinoDerivatives (kerr.cpp:40-66) uses for
// kerrStepMino, so the two integrators carry the same per-step workload.
struct S2 { double r, th, pr, pth, phi, t; };
static S2 deriv(const S2 &s, double mass, double a, const KerrGeodesicConsts &c) {
  KerrPotentials p = kerrPotentials(s.r, s.th, mass, a, c);
  const double mGeom = G * mass / C2;
  const double sin2 = std::max(std::sin(s.th) * std::sin(s.th), 1e-12);
  const double delta = (s.r * s.r) - (2.0 * mGeom * s.r) + (a * a);
  const double deltaSafe = std::max(delta, 1e-12);
  const double aFactor = (((s.r * s.r) + (a * a)) * c.e) - (a * c.lz);
  const double dphi = (c.lz / sin2) - (a * c.e) + (a * aFactor / deltaSafe);
  const double dt = ((((s.r * s.r) + (a * a)) * aFactor) / deltaSafe)
                   + (a * (c.lz - (a * c.e * sin2)));
  return {s.pr, s.pth, 0.5 * p.dRdr, 0.5 * p.dThetadtheta, dphi, dt};
}
int main() {
  const double mass = C2 / G;  // geometric M = 1 cm
  const double a = 0.9;
  const double rph = 1.5578546274233827;
  const double bc = -(rph * rph * rph - 3.0 * rph * rph + a * a * rph + a * a) / (a * (rph - 1.0));
  for (double fac : {1.001, 1.0001, 0.999}) {
    KerrGeodesicConsts c = kerrEquatorialConsts(bc * fac, 1.0);
    // first-order (raytracer.h rule)
    KerrGeodesicState s = kerrEquatorialState(50.0, 0.0, -1.0);
    const double dl = DL;
    int n1 = 0; double rmin1 = 1e9;
    auto t0 = std::chrono::steady_clock::now();
    for (; n1 < 4000000; ++n1) {
      KerrPotentials p = kerrPotentials(s.r, s.theta, mass, a, c);
      if (p.rPot < 0.0) s.signR = -s.signR;
      s = kerrStepMino(s, mass, a, c, dl);
      rmin1 = std::min(rmin1, s.r);
      if (s.r > 60.0 || s.r < kerrOuterHorizon(mass, a) * 1.001) break;
    }
    auto t1 = std::chrono::steady_clock::now();
    // second-order
    KerrPotentials p0 = kerrPotentials(50.0, 0.5 * PI, mass, a, c);
    S2 y{50.0, 0.5 * PI, -std::sqrt(p0.rPot), 0.0, 0.0, 0.0};
    int n2 = 0; double rmin2 = 1e9, maxRes = 0.0;
    auto t2 = std::chrono::steady_clock::now();
    for (; n2 < 4000000; ++n2) {
      S2 k1 = deriv(y, mass, a, c);
      S2 y2{y.r + 0.5 * dl * k1.r, y.th + 0.5 * dl * k1.th, y.pr + 0.5 * dl * k1.pr, y.pth + 0.5 * dl * k1.pth, y.phi + 0.5 * dl * k1.phi, y.t + 0.5 * dl * k1.t};
      S2 k2 = deriv(y2, mass, a, c);
      S2 y3{y.r + 0.5 * dl * k2.r, y.th + 0.5 * dl * k2.th, y.pr + 0.5 * dl * k2.pr, y.pth + 0.5 * dl * k2.pth, y.phi + 0.5 * dl * k2.phi, y.t + 0.5 * dl * k2.t};
      S2 k3 = deriv(y3, mass, a, c);
      S2 y4{y.r + dl * k3.r, y.th + dl * k3.th, y.pr + dl * k3.pr, y.pth + dl * k3.pth, y.phi + dl * k3.phi, y.t + dl * k3.t};
      S2 k4 = deriv(y4, mass, a, c);
      y.r += dl * (k1.r + 2 * k2.r + 2 * k3.r + k4.r) / 6;
      y.th += dl * (k1.th + 2 * k2.th + 2 * k3.th + k4.th) / 6;
      y.pr += dl * (k1.pr + 2 * k2.pr + 2 * k3.pr + k4.pr) / 6;
      y.pth += dl * (k1.pth + 2 * k2.pth + 2 * k3.pth + k4.pth) / 6;
      y.phi += dl * (k1.phi + 2 * k2.phi + 2 * k3.phi + k4.phi) / 6;
      y.t += dl * (k1.t + 2 * k2.t + 2 * k3.t + k4.t) / 6;
      rmin2 = std::min(rmin2, y.r);
      KerrPotentials p = kerrPotentials(y.r, y.th, mass, a, c);
      maxRes = std::max(maxRes, std::abs(y.pr * y.pr - p.rPot) / (p.rPot + y.pr * y.pr + 1e-300));
      if (y.r > 60.0 || y.r < kerrOuterHorizon(mass, a) * 1.001) break;
    }
    auto t3 = std::chrono::steady_clock::now();
    std::printf("b=%.4f b_c: first-order steps=%d rmin=%.5f final=%.3f (%.0f ns/step) | second-order steps=%d rmin=%.5f final=%.3f max rel |pr^2-R|=%.2e (%.0f ns/step)\n",
                fac, n1, rmin1, s.r, std::chrono::duration<double, std::nano>(t1 - t0).count() / n1, n2, rmin2, y.r, maxRes,
                std::chrono::duration<double, std::nano>(t3 - t2).count() / n2);
  }
}
