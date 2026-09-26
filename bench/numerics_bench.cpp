/**
 * @file numerics_bench.cpp
 * @brief Cost and accuracy of the CPU numerics kernels against their baselines.
 *
 * Sections:
 *   stokes  - full-K polarized transfer: one exact step (direct integral and
 *             steady-state split) against the RK4 substeps a 1e-6 relative
 *             error needs, at Faraday depth 1, 100 and 1000.
 *   boost   - Boost.Math jacobi_sn and ellint_1 under the default policy
 *             (double promoted to long double) and under AnalyticKerrPolicy
 *             (promote_double<false>), plus rAnalytic end to end.
 *   carlson - R_F, R_D, R_J by duplication with Carlson's 1995 stopping rule
 *             against Boost.Math ellint_rf/rd/rj under AnalyticKerrPolicy.
 *   kahan   - FP32 RK4 photon orbit, plain against Kahan-compensated state
 *             accumulation: cost per step and roundoff against the double run.
 *
 * Every timing is the minimum over five repetitions of a fixed deterministic
 * workload; the header line records the compiler and library versions. Run
 * pinned for stable numbers: taskset -c 3 ./build/Release/numerics_bench
 */

#ifdef __FAST_MATH__
#error "numerics_bench measures IEEE numerics; -ffast-math folds the Kahan compensation"
#endif

#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <exception>
#include <numbers>
#include <random>
#include <ratio>
#include <vector>

#include <boost/math/special_functions/ellint_1.hpp>
#include <boost/math/special_functions/ellint_rd.hpp>
#include <boost/math/special_functions/ellint_rf.hpp>
#include <boost/math/special_functions/ellint_rj.hpp>
#include <boost/math/special_functions/jacobi_elliptic.hpp>
#include <boost/version.hpp>

#include "analytic_kerr_geodesic.h"
#include "compensated_rk4.h"
#include "elliptic_integrals.h"
#include "stokes_exact.h"
#include "stokes_transport.h"

static_assert(PHYSICS_HAS_BOOST_JACOBI == 1, "The bench measures the Boost Jacobi path");

namespace {

volatile double gSink = 0.0;

/// Minimum over five repetitions of the mean nanoseconds per call of f(i), i in [0, n).
template <typename F> double nsPerCall(std::size_t n, int reps, const F &f) {
  double best = 1.0e300;
  for (int r = 0; r < 5; ++r) {
    double acc = 0.0;
    const auto t0 = std::chrono::steady_clock::now();
    for (int k = 0; k < reps; ++k) {
      for (std::size_t i = 0; i < n; ++i) {
        acc += f(i);
      }
    }
    const auto t1 = std::chrono::steady_clock::now();
    gSink = gSink + acc;
    const double ns = std::chrono::duration<double, std::nano>(t1 - t0).count();
    best = std::min(best, ns / (static_cast<double>(reps) * static_cast<double>(n)));
  }
  return best;
}

void printToolVersions() {
#if defined(__clang__)
  std::printf("compiler: clang %s\n", __clang_version__);
#elif defined(__GNUC__)
  std::printf("compiler: gcc %s\n", __VERSION__);
#endif
  std::printf("boost: %s\n", BOOST_LIB_VERSION);
}

// ---------------------------------------------------------------------------
// Polarized transfer
// ---------------------------------------------------------------------------

struct StokesCase {
  physics::FaradayPropagation k{};
  physics::StokesEmission em{};
  physics::StokesVector s0{};
};

std::vector<StokesCase> stokesCases(double tauF, std::size_t count) {
  // NOLINTNEXTLINE(cert-msc32-c,cert-msc51-cpp,bugprone-random-generator-seed)
  std::mt19937_64 rng(7U); // fixed seed: the same workload on every run and host
  std::uniform_real_distribution<double> unit(0.0, 1.0);
  std::vector<StokesCase> cases;
  cases.reserve(count);
  for (std::size_t n = 0; n < count; ++n) {
    const double aI = 0.01 + (1.99 * unit(rng));
    const double frac = 0.9 * unit(rng);
    const double ang = 2.0 * std::numbers::pi * unit(rng);
    const double rho = tauF * (0.5 + (0.5 * unit(rng)));
    const double th = 0.5 * std::numbers::pi * unit(rng);
    StokesCase c;
    c.k = {.alphaI = aI,
           .alphaQ = aI * frac * std::cos(ang),
           .alphaV = aI * frac * std::sin(ang),
           .rhoV = rho * std::cos(th),
           .rhoQ = rho * std::sin(th),
           .dsCm = 1.0};
    const double jI = 0.1 + (0.9 * unit(rng));
    c.em = {.jI = jI, .jQ = 0.4 * jI, .jU = -0.2 * jI, .jV = 0.05 * jI};
    c.s0 = {.i = 1.0, .q = 0.3, .u = -0.2, .v = 0.1};
    cases.push_back(c);
  }
  return cases;
}

double stokesRelErr(const physics::StokesVector &a, const physics::StokesVector &r) {
  const double d = std::sqrt(((a.i - r.i) * (a.i - r.i)) + ((a.q - r.q) * (a.q - r.q)) +
                             ((a.u - r.u) * (a.u - r.u)) + ((a.v - r.v) * (a.v - r.v)));
  return d / std::sqrt((r.i * r.i) + (r.q * r.q) + (r.u * r.u) + (r.v * r.v));
}

physics::StokesVector rk4Substeps(const StokesCase &c, int n) {
  physics::FaradayPropagation sub = c.k;
  sub.dsCm = c.k.dsCm / n;
  physics::StokesVector s = c.s0;
  for (int i = 0; i < n; ++i) {
    s = physics::stokesStepFullRk4(s, c.em, sub);
  }
  return s;
}

physics::StokesVector exactSplit(const StokesCase &c) {
  const physics::StokesGenerator gen{.alphaI = c.k.alphaI,
                                     .alphaQ = c.k.alphaQ,
                                     .alphaV = c.k.alphaV,
                                     .rhoQ = c.k.rhoQ,
                                     .rhoV = c.k.rhoV};
  const physics::StokesArray out = physics::stokesPropagateExact(
      {c.s0.i, c.s0.q, c.s0.u, c.s0.v}, {c.em.jI, c.em.jQ, c.em.jU, c.em.jV}, gen, c.k.dsCm,
      physics::StokesSourceForm::SteadyStateSplit);
  return {.i = out[0], .q = out[1], .u = out[2], .v = out[3]};
}

void benchStokes() {
  std::printf("\n[stokes] full-K segment, alpha_I ds in [0.01, 2], |eta| <= 0.9 alpha_I\n");
  std::printf("%8s %12s %12s %12s %14s %14s %10s\n", "tauF", "exact ns", "split ns", "rk4 ns",
              "rk4 steps@1e-6", "rk4@1e-6 ns", "exact/rk4");
  constexpr std::size_t count = 64;
  for (const double tauF : {1.0, 100.0, 1000.0}) {
    const std::vector<StokesCase> cases = stokesCases(tauF, count);
    const double exactNs = nsPerCall(count, 2000, [&](std::size_t i) {
      return physics::stokesStepFull(cases[i].s0, cases[i].em, cases[i].k).q;
    });
    const double splitNs =
        nsPerCall(count, 2000, [&](std::size_t i) { return exactSplit(cases[i]).q; });
    const double rk4Ns = nsPerCall(count, 2000, [&](std::size_t i) {
      return physics::stokesStepFullRk4(cases[i].s0, cases[i].em, cases[i].k).q;
    });
    double steps = 0.0;
    for (const StokesCase &c : cases) {
      const physics::StokesVector ref = physics::stokesStepFull(c.s0, c.em, c.k);
      int n = 1;
      while (stokesRelErr(rk4Substeps(c, n), ref) >= 1.0e-6 && n < (1 << 22)) {
        n *= 2;
      }
      steps += n;
    }
    steps /= static_cast<double>(count);
    std::printf("%8.0f %12.1f %12.1f %12.1f %14.0f %14.0f %10.4f\n", tauF, exactNs, splitNs, rk4Ns,
                steps, steps * rk4Ns, exactNs / (steps * rk4Ns));
  }
}

// ---------------------------------------------------------------------------
// Boost precision policy
// ---------------------------------------------------------------------------

void benchBoostPolicy() {
  std::printf("\n[boost] k in [0, 0.999), u in [0.01, 5.01); promoted = default policy\n");
  constexpr std::size_t count = 4096;
  std::vector<double> ks(count);
  std::vector<double> us(count);
  for (std::size_t i = 0; i < count; ++i) {
    ks[i] = 0.999 * static_cast<double>(i % 997U) / 997.0;
    us[i] = 0.01 + (5.0 * static_cast<double>(i % 1009U) / 1009.0);
  }
  const physics::AnalyticKerrPolicy pol;
  double snDiff = 0.0;
  double kDiff = 0.0;
  for (std::size_t i = 0; i < count; ++i) {
    snDiff = std::max(snDiff, std::abs(boost::math::jacobi_sn(ks[i], us[i]) -
                                       boost::math::jacobi_sn(ks[i], us[i], pol)));
    const double kp = boost::math::ellint_1(ks[i]);
    kDiff = std::max(kDiff, std::abs(boost::math::ellint_1(ks[i], pol) - kp) / kp);
  }
  const double snPromoted =
      nsPerCall(count, 20, [&](std::size_t i) { return boost::math::jacobi_sn(ks[i], us[i]); });
  const double snDouble = nsPerCall(
      count, 20, [&](std::size_t i) { return boost::math::jacobi_sn(ks[i], us[i], pol); });
  const double kPromoted =
      nsPerCall(count, 200, [&](std::size_t i) { return boost::math::ellint_1(ks[i]); });
  const double kDouble =
      nsPerCall(count, 200, [&](std::size_t i) { return boost::math::ellint_1(ks[i], pol); });
  physics::RadialRoots roots;
  roots.nReal = 4;
  roots.roots = {{{6.0, 0.0}, {4.0, 0.0}, {1.5, 0.0}, {-0.5, 0.0}}};
  const double rNs =
      nsPerCall(count, 20, [&](std::size_t i) { return physics::rAnalytic(us[i], roots); });
  std::printf("%-10s %14s %14s %9s %16s\n", "call", "promoted ns", "double ns", "speedup",
              "max diff");
  std::printf("%-10s %14.1f %14.1f %9.2f %12.2e abs\n", "jacobi_sn", snPromoted, snDouble,
              snPromoted / snDouble, snDiff);
  std::printf("%-10s %14.1f %14.1f %9.2f %12.2e rel\n", "ellint_1", kPromoted, kDouble,
              kPromoted / kDouble, kDiff);
  const double hpNs =
      nsPerCall(count, 200, [&](std::size_t) { return physics::radialHalfPeriod(roots); });
  std::printf("rAnalytic (double policy) %.1f ns, radialHalfPeriod (AGM) %.1f ns\n", rNs,
              hpNs);
}

// ---------------------------------------------------------------------------
// Carlson symmetric integrals
// ---------------------------------------------------------------------------

void benchCarlson() {
  std::printf("\n[carlson] log-uniform (x, y, z, p) on [1e-3, 1e3]\n");
  constexpr std::size_t count = 1024;
  // NOLINTNEXTLINE(cert-msc32-c,cert-msc51-cpp,bugprone-random-generator-seed)
  std::mt19937_64 rng(11U); // fixed seed: the same workload on every run and host
  std::uniform_real_distribution<double> expo(-3.0, 3.0);
  std::vector<std::array<double, 4>> args(count);
  for (std::array<double, 4> &a : args) {
    std::generate(a.begin(), a.end(), [&] { return std::pow(10.0, expo(rng)); });
  }
  const physics::AnalyticKerrPolicy pol;
  double worst = 0.0;
  for (const std::array<double, 4> &a : args) {
    worst = std::max(
        {worst,
         std::abs(physics::carlsonRf(a[0], a[1], a[2]) - boost::math::ellint_rf(a[0], a[1], a[2])) /
             boost::math::ellint_rf(a[0], a[1], a[2]),
         std::abs(physics::carlsonRd(a[0], a[1], a[2]) - boost::math::ellint_rd(a[0], a[1], a[2])) /
             boost::math::ellint_rd(a[0], a[1], a[2]),
         std::abs(physics::carlsonRj(a[0], a[1], a[2], a[3]) -
                  boost::math::ellint_rj(a[0], a[1], a[2], a[3])) /
             boost::math::ellint_rj(a[0], a[1], a[2], a[3])});
  }
  std::printf("%-4s %12s %16s\n", "", "carlson ns", "boost double ns");
  std::printf("%-4s %12.1f %16.1f\n", "R_F",
              nsPerCall(count, 50,
                        [&](std::size_t i) {
                          return physics::carlsonRf(args[i][0], args[i][1], args[i][2]);
                        }),
              nsPerCall(count, 50, [&](std::size_t i) {
                return boost::math::ellint_rf(args[i][0], args[i][1], args[i][2], pol);
              }));
  std::printf("%-4s %12.1f %16.1f\n", "R_D",
              nsPerCall(count, 50,
                        [&](std::size_t i) {
                          return physics::carlsonRd(args[i][0], args[i][1], args[i][2]);
                        }),
              nsPerCall(count, 50, [&](std::size_t i) {
                return boost::math::ellint_rd(args[i][0], args[i][1], args[i][2], pol);
              }));
  std::printf("%-4s %12.1f %16.1f\n", "R_J",
              nsPerCall(count, 50,
                        [&](std::size_t i) {
                          return physics::carlsonRj(args[i][0], args[i][1], args[i][2], args[i][3]);
                        }),
              nsPerCall(count, 50, [&](std::size_t i) {
                return boost::math::ellint_rj(args[i][0], args[i][1], args[i][2], args[i][3], pol);
              }));
  std::printf("max rel diff vs promoted Boost %.2e\n", worst);
}

// ---------------------------------------------------------------------------
// Compensated FP32 RK4
// ---------------------------------------------------------------------------

template <typename T, physics::Rk4Accumulation Mode>
std::array<T, 6> photonOrbit(double b, double h, int steps, double x0) {
  const std::array<T, 6> y0 = {static_cast<T>(x0), static_cast<T>(b), T(0), T(-1), T(0), T(0)};
  const T h2 = static_cast<T>(b * b);
  physics::Rk4Integrator<T, 6, Mode> rk(y0);
  for (int i = 0; i < steps; ++i) {
    rk.step([&](const std::array<T, 6> &s) { return physics::schwarzschildPhotonRhs(s, T(1), h2); },
            static_cast<T>(h));
  }
  return rk.state();
}

void benchKahan() {
  std::printf(
      "\n[kahan] FP32 RK4, Schwarzschild photon r_s = 1 from x = 30 over affine length 60\n");
  std::printf("%4s %6s %7s %12s %12s %10s %12s %12s\n", "b", "h", "steps", "plain ns", "comp ns",
              "cost", "plain err", "comp err");
  using physics::Rk4Accumulation;
  for (const double b : {3.5, 2.7}) {
    for (const double h : {0.05, 0.01, 0.002}) {
      const int steps = static_cast<int>(std::lround(60.0 / h));
      const auto ref = photonOrbit<double, Rk4Accumulation::Plain>(b, h, steps, 30.0);
      auto err = [&](const std::array<float, 6> &s) {
        const double dx = static_cast<double>(s[0]) - ref[0];
        const double dy = static_cast<double>(s[1]) - ref[1];
        return std::sqrt((dx * dx) + (dy * dy)) / std::sqrt((ref[0] * ref[0]) + (ref[1] * ref[1]));
      };
      const double plainErr = err(photonOrbit<float, Rk4Accumulation::Plain>(b, h, steps, 30.0));
      const double compErr =
          err(photonOrbit<float, Rk4Accumulation::Compensated>(b, h, steps, 30.0));
      constexpr std::size_t rays = 16;
      const int reps = std::max(1, 400000 / steps);
      const double plainNs = nsPerCall(rays, reps, [&](std::size_t i) {
        return static_cast<double>(photonOrbit<float, Rk4Accumulation::Plain>(
            b, h, steps, 30.0 + (1.0e-3 * static_cast<double>(i)))[0]);
      });
      const double compNs = nsPerCall(rays, reps, [&](std::size_t i) {
        return static_cast<double>(photonOrbit<float, Rk4Accumulation::Compensated>(
            b, h, steps, 30.0 + (1.0e-3 * static_cast<double>(i)))[0]);
      });
      std::printf("%4.1f %6g %7d %12.2f %12.2f %9.2fx %12.2e %12.2e\n", b, h, steps,
                  plainNs / steps, compNs / steps, compNs / plainNs, plainErr, compErr);
    }
  }
}

} // namespace

int main() try {
  std::printf("=== Blackhole numerics bench ===\n");
  printToolVersions();
  benchStokes();
  benchBoostPolicy();
  benchCarlson();
  benchKahan();
  std::printf("\nsink %.3e\n", gSink);
  return 0;
} catch (const std::exception &error) {
  return std::fprintf(stderr, "numerics_bench: %s\n", error.what()) < 0 ? 2 : 1;
}
