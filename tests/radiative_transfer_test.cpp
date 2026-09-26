/**
 * @file radiative_transfer_test.cpp
 * @brief src/physics/rte_integrator.h against analytic slab solutions.
 *
 * For a slab with constant emission j and absorption alpha, source function
 * S = j / alpha, optical depth tau = alpha L, and background intensity I0, the
 * transfer equation dI/ds = j - alpha I has the exact solution
 *
 *   I = S (1 - exp(-tau)) + I0 exp(-tau).
 *
 * Every check calls physics::rteStep, physics::integrateRtePath, or
 * physics::rteStepGR and compares with that solution or with the
 * layer-by-layer composition of it.
 *
 * Tolerances: for tau >= 1e-4 rteStep evaluates the exact exponential, so the
 * error is rounding (1e-13 relative). For tau < 1e-4 it uses
 * 1 - exp(-tau) ~ tau (1 - tau/2) and drops the I0 tau^2 / 2 term of the
 * attenuation, so the absolute error bound is I0 tau^2 / 2 + S tau^3 / 6.
 *
 * References:
 * - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics", Ch. 1
 */

#include <cmath>
#include <cstddef>
#include <cstdio>
#include <vector>

#include "../src/physics/rte_integrator.h"
#include "../src/physics/safe_limits.h"

namespace {

int gChecks = 0;
int gFailures = 0;

void check(bool ok, const char *name, double expected, double actual) {
  ++gChecks;
  if (!ok) {
    ++gFailures;
    std::printf("[FAIL] %s: expected %.17g, actual %.17g\n", name, expected, actual);
  }
}

double slabSolution(double source, double tau, double background) {
  return (source * -std::expm1(-tau)) + (background * std::exp(-tau));
}

/** Absolute error bound of one rteStep at optical depth tau (see file comment). */
double stepBound(double source, double tau, double background) {
  const double rounding = 1.0e-13 * (std::abs(source) + std::abs(background));
  if (tau >= 1.0e-4) {
    return rounding;
  }
  return rounding + (0.5 * background * tau * tau) + (source * tau * tau * tau / 6.0);
}

/** Uniform slab in one step, across both sides of the tau = 1e-4 branch. */
void testUniformSlabSingleStep() {
  constexpr double kSource = 2.5;
  constexpr double kLength = 1.0e15;
  for (double const tau : {1.0e-9, 1.0e-6, 5.0e-5, 9.99e-5, 1.0e-4, 2.0e-4, 0.01, 0.5, 1.0, 5.0,
                           30.0}) {
    const double alpha = tau / kLength;
    for (double const background : {0.0, 0.3 * kSource, 4.0 * kSource}) {
      const physics::RteState state =
          physics::rteStep(physics::RteState{background, 0.0, 0.0}, kSource * alpha, alpha, kLength);
      const double expected = slabSolution(kSource, tau, background);
      check(std::abs(state.iNu - expected) <= stepBound(kSource, tau, background),
            "uniform slab I", expected, state.iNu);
      check(std::abs(state.tau - tau) <= 1.0e-15 * tau, "uniform slab tau", tau, state.tau);
      check(state.sCm == kLength, "uniform slab path length", kLength, state.sCm);
    }
  }
}

/** Pure absorption I0 exp(-tau) and pure emission I0 + j L. */
void testPureLimits() {
  constexpr double kBackground = 7.0;
  for (double const tau : {1.0e-3, 0.7, 12.0}) {
    const physics::RteState state =
        physics::rteStep(physics::RteState{kBackground, 0.0, 0.0}, 0.0, tau, 1.0);
    const double expected = kBackground * std::exp(-tau);
    check(std::abs(state.iNu - expected) <= 1.0e-13 * kBackground, "pure absorption", expected,
          state.iNu);
  }
  const physics::RteState emitted =
      physics::rteStep(physics::RteState{kBackground, 0.0, 0.0}, 3.0e-3, 0.0, 250.0);
  check(std::abs(emitted.iNu - (kBackground + 0.75)) <= 1.0e-15, "pure emission", 7.75, emitted.iNu);
  check(emitted.tau == 0.0, "pure emission tau", 0.0, emitted.tau);
}

/**
 * A uniform slab split into N layers composes to the one-layer solution.
 *
 * With segment tau >= 1e-4 each step is exact, so the composition matches to
 * rounding. With segment tau < 1e-4 the dropped I tau_seg^2 / 2 term
 * accumulates to at most tau_total tau_seg max(I0, S) / 2.
 */
void testLayerComposition() {
  constexpr double kSource = 1.0;
  constexpr double kBackground = 3.0;
  struct Case {
    double tauTotal;
    int layers;
  };
  for (const Case c : {Case{3.0, 1000}, Case{0.05, 1000}}) {
    const double tauSegment = c.tauTotal / c.layers;
    const std::vector<physics::RteSample> path(
        static_cast<std::size_t>(c.layers), physics::RteSample{kSource * tauSegment, tauSegment, 1.0});
    const physics::RteState state =
        physics::integrateRtePath(path, physics::RteState{kBackground, 0.0, 0.0});
    const double expected = slabSolution(kSource, c.tauTotal, kBackground);
    const double bound = (tauSegment >= 1.0e-4)
                             ? 1.0e-12 * kBackground
                             : (0.5 * c.tauTotal * tauSegment * kBackground) + 1.0e-12;
    check(std::abs(state.iNu - expected) <= bound, "layer composition", expected, state.iNu);
    check(std::abs(state.tau - c.tauTotal) <= 1.0e-12 * c.tauTotal, "layer composition tau",
          c.tauTotal, state.tau);
  }
}

/** Two slabs, far layer first: I = S2 (1 - e^-t2) + [S1 (1 - e^-t1) + I0 e^-t1] e^-t2. */
void testTwoLayerSlab() {
  constexpr double kBackground = 0.4;
  constexpr double kSourceFar = 5.0;
  constexpr double kTauFar = 1.3;
  constexpr double kSourceNear = 0.8;
  constexpr double kTauNear = 0.6;
  const std::vector<physics::RteSample> path{{kSourceFar * kTauFar / 2.0, kTauFar / 2.0, 2.0},
                                             {kSourceNear * kTauNear / 3.0, kTauNear / 3.0, 3.0}};
  const physics::RteState state =
      physics::integrateRtePath(path, physics::RteState{kBackground, 0.0, 0.0});
  const double afterFar = slabSolution(kSourceFar, kTauFar, kBackground);
  const double expected = slabSolution(kSourceNear, kTauNear, afterFar);
  check(std::abs(state.iNu - expected) <= 1.0e-13 * kSourceFar, "two-layer slab", expected,
        state.iNu);
  check(std::abs(state.sCm - 5.0) <= 1.0e-15, "two-layer path length", 5.0, state.sCm);
}

/**
 * Uniform S with alpha(s) = alpha0 (1 + s / L): the exact result uses
 * tau = 1.5 alpha0 L. Midpoint-sampled layers are exact in tau for a linear
 * profile, and a uniform S makes the layer order irrelevant, so the intensity
 * matches at every resolution.
 */
void testLinearOpacityProfile() {
  constexpr double kSource = 2.0;
  constexpr double kBackground = 0.5;
  constexpr double kAlpha0 = 0.8;
  constexpr double kLength = 1.0;
  for (int const layers : {4, 64}) {
    std::vector<physics::RteSample> path;
    const double ds = kLength / layers;
    for (int i = 0; i < layers; ++i) {
      const double sMid = (static_cast<double>(i) + 0.5) * ds;
      const double alpha = kAlpha0 * (1.0 + (sMid / kLength));
      path.push_back({kSource * alpha, alpha, ds});
    }
    const physics::RteState state =
        physics::integrateRtePath(path, physics::RteState{kBackground, 0.0, 0.0});
    const double tau = 1.5 * kAlpha0 * kLength;
    const double expected = slabSolution(kSource, tau, kBackground);
    check(std::abs(state.iNu - expected) <= 1.0e-13, "linear opacity profile", expected, state.iNu);
    check(std::abs(state.tau - tau) <= 1.0e-13, "linear opacity tau", tau, state.tau);
  }
}

/** Kirchhoff: j = alpha B_nu(T) drives a thick slab to the Planck intensity. */
void testKirchhoffThermalSlab() {
  constexpr double kNu = 2.3e11;
  constexpr double kTemperature = 5.0e9;
  const double planck = physics::planckFunction(kNu, kTemperature);
  constexpr double kAlpha = 1.0e-3;
  const physics::RteState state =
      physics::rteStep(physics::RteState{0.0, 0.0, 0.0}, kAlpha * planck, kAlpha, 5.0e4);
  check(std::abs(state.iNu - planck) <= 1.0e-13 * planck, "Kirchhoff thick slab", planck,
        state.iNu);
}

/**
 * rteStepGR: with j -> g^2 j and alpha -> alpha / g, a thick slab reaches
 * g^3 S (the invariant I_nu / nu^3), and g = 1 reproduces rteStep.
 */
void testGravitationalTransform() {
  constexpr double kSource = 1.7;
  constexpr double kAlpha = 0.02;
  constexpr double kLength = 3.0;
  const physics::RteState start{0.9, 0.0, 0.0};
  const physics::RteState unit = physics::rteStepGR(start, kSource * kAlpha, kAlpha, kLength, 1.0);
  const physics::RteState flat = physics::rteStep(start, kSource * kAlpha, kAlpha, kLength);
  check(unit.iNu == flat.iNu, "rteStepGR g = 1", flat.iNu, unit.iNu);
  for (double const g : {0.4, 1.6}) {
    const physics::RteState slab = physics::rteStepGR(start, kSource * kAlpha, kAlpha, kLength, g);
    const double expected = slabSolution(g * g * g * kSource, kAlpha * kLength / g, start.iNu);
    check(std::abs(slab.iNu - expected) <= 1.0e-13 * expected, "rteStepGR slab", expected,
          slab.iNu);
    const physics::RteState thick = physics::rteStepGR(start, kSource * kAlpha, kAlpha, 1.0e4, g);
    check(std::abs(thick.iNu - (g * g * g * kSource)) <= 1.0e-13 * kSource,
          "rteStepGR thick g^3 S", g * g * g * kSource, thick.iNu);
  }
}

/** The intensity moves monotonically from I0 toward S and stays finite at extreme tau. */
void testBoundedApproach() {
  constexpr double kSource = 10.0;
  for (double const background : {0.0, 25.0}) {
    for (double const tau : {1.0e-30, 1.0e-3, 1.0, 1.0e4}) {
      const physics::RteState state =
          physics::rteStep(physics::RteState{background, 0.0, 0.0}, kSource * tau, tau, 1.0);
      const double lo = std::fmin(background, kSource);
      const double hi = std::fmax(background, kSource);
      check(physics::safeIsfinite(state.iNu) && state.iNu >= lo - 1.0e-12 && state.iNu <= hi + 1.0e-12,
            "bounded approach", kSource, state.iNu);
    }
  }
}

} // namespace

int main() {
  testUniformSlabSingleStep();
  testPureLimits();
  testLayerComposition();
  testTwoLayerSlab();
  testLinearOpacityProfile();
  testKirchhoffThermalSlab();
  testGravitationalTransform();
  testBoundedApproach();
  std::printf("radiative_transfer_test: %d/%d checks passed\n", gChecks - gFailures, gChecks);
  return (gFailures == 0) ? 0 : 1;
}
