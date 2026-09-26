/**
 * @file compensated_rk4_test.cpp
 * @brief FP32 RK4 roundoff with plain and Kahan-compensated state accumulation.
 *
 * A Schwarzschild photon (r_s = 1) starts at x = 30 heading -x with impact
 * parameter b and is integrated over affine length 60 in float, plain and
 * compensated, and by the same RK4 scheme in double. The double run carries
 * the same truncation error with roundoff near 1e-13, so the float-minus-double
 * position difference isolates FP32 roundoff. Gates, per (b, h):
 *   - compensated error below plain error by a step-count-dependent factor
 *     (>= 3 at 1200 steps, >= 20 at 6000, >= 100 at 30000);
 *   - compensated error at 30000 steps within 10x of its 1200-step value
 *     (roundoff flat in N, where plain grows about linearly).
 * Ratios, not absolute errors, carry the gate because FMA contraction and the
 * target ISA shift both columns together.
 */

#include <array>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <exception>

#include "compensated_rk4.h"

using namespace physics;

namespace {

int gPass = 0;
int gFail = 0;

void check(bool cond, const char *msg) {
  if (cond) {
    std::printf("  [PASS] %s\n", msg);
    ++gPass;
  } else {
    std::printf("  [FAIL] %s\n", msg);
    ++gFail;
  }
}

template <typename T, Rk4Accumulation Mode>
std::array<T, 6> photonOrbit(double b, double h, int steps) {
  const std::array<T, 6> y0 = {T(30), static_cast<T>(b), T(0), T(-1), T(0), T(0)};
  const T h2 = static_cast<T>(b * b); // |x cross v|^2 with |v| = 1
  const T rs = T(1);
  Rk4Integrator<T, 6, Mode> rk(y0);
  for (int i = 0; i < steps; ++i) {
    rk.step([&](const std::array<T, 6> &s) { return schwarzschildPhotonRhs(s, rs, h2); },
            static_cast<T>(h));
  }
  return rk.state();
}

template <typename T>
double positionError(const std::array<T, 6> &s, const std::array<double, 6> &ref) {
  const double dx = static_cast<double>(s[0]) - ref[0];
  const double dy = static_cast<double>(s[1]) - ref[1];
  const double dz = static_cast<double>(s[2]) - ref[2];
  return std::sqrt((dx * dx) + (dy * dy) + (dz * dz)) /
         std::sqrt((ref[0] * ref[0]) + (ref[1] * ref[1]) + (ref[2] * ref[2]));
}

struct Errors {
  double plain = 0.0;
  double compensated = 0.0;
};

Errors roundoff(double b, double h) {
  const int steps = static_cast<int>(std::lround(60.0 / h));
  const std::array<double, 6> ref = photonOrbit<double, Rk4Accumulation::Plain>(b, h, steps);
  return {.plain = positionError(photonOrbit<float, Rk4Accumulation::Plain>(b, h, steps), ref),
          .compensated =
              positionError(photonOrbit<float, Rk4Accumulation::Compensated>(b, h, steps), ref)};
}

void testCompensationReducesRoundoff() {
  // b = 3.5 passes wide; b = 2.7 grazes the photon sphere (b_c = 2.598 at r_s = 1).
  constexpr std::array<double, 3> steps = {0.05, 0.01, 0.002};
  constexpr std::array<double, 3> minRatio = {3.0, 20.0, 100.0};
  bool ratiosOk = true;
  bool flatOk = true;
  for (const double b : {3.5, 2.7}) {
    std::array<Errors, 3> e{};
    for (std::size_t i = 0; i < steps.size(); ++i) {
      e[i] = roundoff(b, steps[i]);
      const double ratio = e[i].plain / e[i].compensated;
      std::printf("  b=%.1f h=%-5g steps=%-6ld plain %.2e compensated %.2e ratio %.0f\n", b,
                  steps[i], std::lround(60.0 / steps[i]), e[i].plain, e[i].compensated, ratio);
      ratiosOk = ratiosOk && ratio >= minRatio[i];
    }
    flatOk = flatOk && e[2].compensated <= 10.0 * e[0].compensated;
  }
  check(ratiosOk,
        "compensated FP32 roundoff below plain by >= 3x/20x/100x at 1200/6000/30000 steps");
  check(flatOk, "compensated roundoff flat in step count (30000 steps within 10x of 1200)");
}

void testDoubleCompensatedMatchesPlain() {
  // In double both accumulations sit far below the truncation error; they must agree.
  const auto plain = photonOrbit<double, Rk4Accumulation::Plain>(3.5, 0.01, 6000);
  const auto comp = photonOrbit<double, Rk4Accumulation::Compensated>(3.5, 0.01, 6000);
  const double diff = positionError(comp, plain);
  std::printf("  double plain vs compensated rel diff %.2e\n", diff);
  check(diff < 1.0e-12, "double-precision compensated and plain RK4 agree to 1e-12");
}

} // namespace

int main() try {
  std::printf("FP32 RK4 roundoff, Schwarzschild photon over affine length 60:\n");
  testCompensationReducesRoundoff();
  testDoubleCompensatedMatchesPlain();

  std::printf("\n%d/%d tests passed.\n", gPass, gPass + gFail);
  if (gFail > 0) {
    std::printf("[FAILURE] One or more tests failed.\n\n");
    return 1;
  }
  std::printf("[ALL PASS]\n\n");
  return 0;
} catch (const std::exception &error) {
  return std::fprintf(stderr, "[FAIL] Unexpected exception: %s\n", error.what()) < 0 ? 2 : 1;
} catch (...) {
  return std::fprintf(stderr, "[FAIL] Unexpected nonstandard exception\n") < 0 ? 2 : 1;
}
