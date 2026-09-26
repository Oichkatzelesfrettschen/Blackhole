#include <chrono>
#include <cmath>
#include <cstdio>
#include "physics/gravitational_waves.h"
#include "physics/kerr.h"
#include "physics/kerr_newman.h"
#include "physics/lut.h"
#include "physics/novikov_thorne.h"
#include "physics/thin_disk.h"
#include "physics/verified/kerr_de_sitter.hpp"
#include "physics/verified/kerr_newman.hpp"

using namespace physics;

int main() {
  { const double ms = 1.98847e33; const double m1 = 30*ms, m2 = 30*ms; const double mc = std::pow(m1*m2, 0.6)/std::pow(m1+m2, 0.2); for (double f : {20.0, 100.0}) std::printf("GW gwPhase3p5pn(30+30, f=%g) = %.6e rad\n", f, physics::gwPhase3p5pn(mc, 0.25, f)); }
  const double mSun = 4.0e6;
  const double mass = mSun * M_SUN;
  const double rG = G * mass / C2;
  // 1. NT temperature at r = 9 M, a = 0, mdot = 0.1 Eddington
  double tNt = blackhole::physics::NovikovThorneDisk::diskTemperature(9.0, 0.0, 0.1, mSun);
  DiskParams d = schwarzschildDisk(mSun, 0.1);
  double tThin = diskTemperature(9.0 * rG, d);
  // independent: eta-consistent Mdot, Newtonian f, SI-free CGS
  const double eta = 1.0 - std::sqrt(8.0 / 9.0);
  const double mdot = 0.1 * 1.26e38 * mSun / (eta * C2);
  const double r = 9.0 * rG;
  const double f = 1.0 - std::sqrt(6.0 / 9.0);
  const double tRef = std::pow(3.0 * G * mass * mdot * f / (8.0 * PI * 5.670374419e-5 * r * r * r), 0.25);
  std::printf("NT_T r=9M a=0: NovikovThorneDisk=%.6e K thin_disk=%.6e K independent(Newtonian f, eta=0.0572)=%.6e K ratio=%.4f\n",
              tNt, tThin, tRef, tNt / tRef);
  std::printf("NT eta a=0.998: %.6f\n", blackhole::physics::NovikovThorneDisk::radiativeEfficiency(0.998));
  // 2. Redshift LUT zero bins
  for (double s : {0.0, 0.5, 0.9, 0.998}) {
    auto lut = generateRedshiftLut(256, mSun, s);
    int zeros = 0;
    for (float v : lut.values) zeros += (v == 0.0f);
    std::printf("redshiftLut a=%.3f rMin/rs=%.4f z[0]=%.5f z[128]=%.5f z[255]=%.5f zeroBins=%d/256\n", s, lut.rMin,
                lut.values[0], lut.values[128], lut.values[255], zeros);
  }
  auto eml = generateEmissivityLut(256, mSun, 0.9, 0.1, true);
  int peak = 0;
  for (int i = 0; i < 256; ++i) if (eml.values[i] > eml.values[peak]) peak = i;
  std::printf("emissivityLut a=0.9 peak bin=%d r/risco=%.4f\n", peak, 1.0 + 3.0 * peak / 255.0);
  auto eml0 = generateEmissivityLut(256, mSun, 0.0, 0.1, true);
  peak = 0;
  for (int i = 0; i < 256; ++i) if (eml0.values[i] > eml0.values[peak]) peak = i;
  std::printf("emissivityLut a=0 peak bin=%d r/risco=%.4f\n", peak, 1.0 + 3.0 * peak / 255.0);
  // 3. Spin radii LUT at spin -0.9
  auto sr = generateSpinRadiiLut(199, mSun, -0.99, 0.99);
  for (std::size_t i = 0; i < sr.spins.size(); ++i) {
    if (std::abs(sr.spins[i] + 0.9f) < 0.006f || std::abs(sr.spins[i] - 0.9f) < 0.006f)
      std::printf("spinRadiiLut spin=%.3f rIsco/M=%.4f rPh/M=%.4f\n", sr.spins[i], 2.0 * sr.rIscoOverRs[i],
                  2.0 * sr.rPhOverRs[i]);
  }
  // 4. kerrTimeDilation
  for (double s : {0.0, 0.9}) {
    for (double rr : {1.8, 3.0, 6.0}) {
      if (rr * rG <= kerrOuterHorizon(mass, s * rG)) continue;
      std::printf("kerrTimeDilation a=%.1f r=%.1fM -> %.6f\n", s, rr, kerrTimeDilation(rr * rG, 0.5 * PI, mass, s * rG));
    }
  }
  std::printf("kerrIsco(a=-0.9, prograde=true)=%.4f M  kerrPhotonOrbitPrograde(a=-0.9)=%.4f M\n",
              kerrIscoRadius(mass, -0.9 * rG, true) / rG, kerrPhotonOrbitPrograde(mass, -0.9 * rG) / rG);
  // 5. KN
  std::printf("verified::knIscoRadiusPrograde(1,0,0.5)=%.6f (1,0,0.9)=%.6f\n", verified::knIscoRadiusPrograde(1, 0, 0.5),
              verified::knIscoRadiusPrograde(1, 0, 0.9));
  std::printf("physics::knFrameDragging r=3 a=0.5 Q=0.5: %.6f\n", knFrameDragging(3.0, 0.5 * PI, 1.0, 0.5, 0.5));
  std::printf("knGtph=%.6f verified::knPotentialPhi=%.6f physics::knMagneticPotentialPhi=%.6f\n",
              knGtph(3.0, 0.5 * PI, 1.0, 0.5), verified::knPotentialPhi(3.0, 0.5 * PI, 0.5, 0.5),
              knMagneticPotentialPhi(3.0, 0.5 * PI, 0.5, 0.5));
  // 6. KdS
  for (double L : {1e-4, 1e-2, 0.1}) {
    std::printf("KdS a=0.9 L=%.0e event=%.6f inner=%.6f cosmo=%.6f  g_tt(a=0,r=10,th=pi/2)=%.6f g_rr=%.6f\n", L,
                verified::kdsEventHorizon(1, 0.9, L), verified::kdsInnerHorizon(1, 0.9, L),
                verified::kdsCosmologicalHorizon(L), verified::kdsGTt(10, 0.5 * PI, 1, 0, L),
                verified::kdsGRr(10, 0.5 * PI, 1, 0, L));
  }
  // 7. Mino RK4 conservation: equatorial Kerr null ray near critical
  {
    const double a = 0.9;
    // prograde critical impact b_c for a=0.9: b = -a + 2 r_ph ... use r_ph=1.5579: b = (r^2 - ... ) closed form
    const double rph = 1.5578546274233827;
    const double bc = -(rph * rph * rph - 3.0 * rph * rph + a * a * rph + a * a) / (a * (rph - 1.0));
    KerrGeodesicConsts c = kerrEquatorialConsts(bc * 1.001, 1.0);
    KerrGeodesicState s = kerrEquatorialState(50.0 * rG, 0.0, -1.0);
    // work in geometric-units-with-cm: scale consts by rG
    c.lz *= rG;
    const double dl = 1e-3 / rG;
    auto t0 = std::chrono::steady_clock::now();
    int n = 0;
    double rMin = 1e300;
    for (; n < 200000; ++n) {
      KerrPotentials p = kerrPotentials(s.r, s.theta, mass, a * rG, c);
      if (p.rPot < 0.0) s.signR = -s.signR;
      s = kerrStepMino(s, mass, a * rG, c, dl);
      rMin = std::min(rMin, s.r);
      if (s.r > 60.0 * rG || s.r < kerrOuterHorizon(mass, a * rG)) break;
    }
    auto t1 = std::chrono::steady_clock::now();
    std::printf("kerrStepMino a=0.9 b=1.001 b_c=%.5f: steps=%d rMin=%.5f M final r=%.3f M ns/step=%.1f\n", bc, n,
                rMin / rG, s.r / rG, std::chrono::duration<double, std::nano>(t1 - t0).count() / n);
  }
  return 0;
}
