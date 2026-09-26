/**
 * @file stokes_exact_test.cpp
 * @brief Closed-form polarized transfer step against a 50-digit referee.
 *
 * Gates:
 *   1. stokesPropagateExact (direct integral) within 1e-12 relative (vector
 *      2-norm) of the mpmath 5x5 matrix-exponential referee on every row of
 *      tests/stokes_exact_reference.inc: Faraday depth 0.01..1000, optical depth
 *      1e-9..800, gain down to -715 (past exp's overflow), Faraday depth to
 *      1e15 along one axis,
 *      alpha_U and rho_U nonzero, and the degenerate limits (zero K, pure
 *      Faraday, pure dichroism, eta || rho, w.w = 0, alpha_I = |eta|, scaled
 *      units). Along a general axis the rounded |rho| ds bounds the error at
 *      4 eps (1 + x2) instead.
 *   2. stokesStepFull, the FaradayPropagation entry point, on the aligned-frame
 *      rows, and no FE_INVALID or FE_DIVBYZERO raised on any row.
 *   3. SteadyStateSplit within its 1e-9 budget for alpha_I ds >= 0.1, and equal
 *      to the direct integral below that depth.
 *   4. Closed forms: rotation by rho_V ds, I +- Q decay at alpha_I +- alpha_Q,
 *      1 - K' + K'^2 / 2 for a null rotation, and pure gain at alpha_I ds = -10.
 *   5. Invariants: I >= |P| for physical K, S0 and J; I^2 - |P|^2 preserved
 *      when alpha_I = 0 and J = 0; two half steps equal one step; agreement
 *      with the simplified-K stokesStep.
 *   6. stokesStepFullRk4 converges to the exact step at fourth order.
 *
 * Regenerate the table with
 *   $PYTHON scripts/gen_stokes_reference.py > tests/stokes_exact_reference.inc
 */

#include <algorithm>
#include <array>
#include <cfenv>
#include <cmath>
#include <cstdio>
#include <exception>
#include <iterator>
#include <limits>
#include <numbers>
#include <random>
#include <string_view>

#include "stokes_exact.h"
#include "stokes_transport.h"

using namespace physics;

namespace {

struct ReferenceRow {
  std::string_view group;
  std::array<double, 7> k{}; // aI, aQ, aU, aV, rQ, rU, rV
  double ds = 0.0;
  StokesArray j{};
  StokesArray s0{};
  StokesArray ref{};
};

constexpr ReferenceRow REFERENCE_ROWS[] = {
#include "stokes_exact_reference.inc"
};

// Direct-integral gate against the referee table.
constexpr double DIRECT_TOL = 1.0e-12;
// SteadyStateSplit contract for alpha_I ds >= 0.1.
constexpr double SPLIT_TOL = 1.0e-9;

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

double norm(const StokesArray &v) {
  return std::sqrt((v[0] * v[0]) + (v[1] * v[1]) + (v[2] * v[2]) + (v[3] * v[3]));
}

double relErr(const StokesArray &got, const StokesArray &ref) {
  // Scaled by the largest reference component so deep-gain rows near 1e307
  // square without overflow.
  const double scale =
      std::max({std::abs(ref[0]), std::abs(ref[1]), std::abs(ref[2]), std::abs(ref[3]), 1.0e-300});
  const StokesArray d = {(got[0] - ref[0]) / scale, (got[1] - ref[1]) / scale,
                         (got[2] - ref[2]) / scale, (got[3] - ref[3]) / scale};
  const StokesArray r = {ref[0] / scale, ref[1] / scale, ref[2] / scale, ref[3] / scale};
  return norm(d) / norm(r);
}

/// Running maximum that keeps a NaN error, which std::max would drop.
double worseOf(double runningMax, double candidate) {
  return (candidate > runningMax || candidate != candidate) ? candidate : runningMax;
}

StokesGenerator generatorOf(const ReferenceRow &row) {
  return {.alphaI = row.k[0],
          .alphaQ = row.k[1],
          .alphaU = row.k[2],
          .alphaV = row.k[3],
          .rhoQ = row.k[4],
          .rhoU = row.k[5],
          .rhoV = row.k[6]};
}

StokesArray toArray(const StokesVector &s) {
  return {s.i, s.q, s.u, s.v};
}

void testReferenceDirect() {
  constexpr std::array<std::string_view, 8> groups = {"generic", "aligned",  "thin",    "split",
                                                      "gain",    "deepgain", "faraday", "limit"};
  double worstAll = 0.0;
  for (const std::string_view group : groups) {
    double worst = 0.0;
    int count = 0;
    for (const ReferenceRow &row : REFERENCE_ROWS) {
      if (row.group != group) {
        continue;
      }
      const StokesArray got = stokesPropagateExact(row.s0, row.j, generatorOf(row), row.ds);
      worst = worseOf(worst, relErr(got, row.ref));
      ++count;
    }
    std::printf("  %-8.*s rows=%2d  max rel err %.3e\n", static_cast<int>(group.size()),
                group.data(), count, worst);
    worstAll = worseOf(worstAll, worst);
  }
  check(worstAll <= DIRECT_TOL, "direct integral within 1e-12 of the 50-digit referee, all rows");
}

void testReferenceFaradayGeneralAxis() {
  // Along a general axis |rho| ds is itself rounded, so the rotation angle x2
  // carries up to eps x2 absolute before any evaluation; the achievable bound
  // is a few eps x2 of the state's norm.
  double worstRatio = 0.0;
  for (const ReferenceRow &row : REFERENCE_ROWS) {
    if (row.group != "faraday3d") {
      continue;
    }
    const StokesArray got = stokesPropagateExact(row.s0, row.j, generatorOf(row), row.ds);
    const double x2 =
        std::sqrt((row.k[4] * row.k[4]) + (row.k[5] * row.k[5]) + (row.k[6] * row.k[6])) * row.ds;
    const double bound = 4.0 * std::numeric_limits<double>::epsilon() * (1.0 + x2);
    worstRatio = worseOf(worstRatio, relErr(got, row.ref) / bound);
  }
  std::printf("  faraday3d max rel err / (4 eps (1 + x2)) %.3f\n", worstRatio);
  check(worstRatio <= 1.0, "general-axis Faraday depth to 1e15 within 4 eps x2 of the referee");
}

void testNoFloatingPointExceptions() {
  // A valid segment raises neither FE_INVALID nor FE_DIVBYZERO: every branch
  // is selected before it divides and each divisor is clamped to the range its
  // branch guarantees, so no discarded 0/0 or x/0 is formed, even in a select
  // whose arms the compiler evaluates both.
  bool clean = true;
  for (const ReferenceRow &row : REFERENCE_ROWS) {
    for (const StokesSourceForm form :
         {StokesSourceForm::DirectIntegral, StokesSourceForm::SteadyStateSplit}) {
      std::feclearexcept(FE_ALL_EXCEPT);
      const StokesArray out = stokesPropagateExact(row.s0, row.j, generatorOf(row), row.ds, form);
      clean = clean && std::fetestexcept(FE_INVALID | FE_DIVBYZERO) == 0 && out[0] == out[0];
    }
  }
  check(clean, "no FE_INVALID or FE_DIVBYZERO on any referee row, either source form");
}

void testReferenceStepFull() {
  double worst = 0.0;
  for (const ReferenceRow &row : REFERENCE_ROWS) {
    if (row.group != "aligned") {
      continue;
    }
    const FaradayPropagation k{.alphaI = row.k[0],
                               .alphaQ = row.k[1],
                               .alphaV = row.k[3],
                               .rhoV = row.k[6],
                               .rhoQ = row.k[4],
                               .dsCm = row.ds};
    const StokesVector got =
        stokesStepFull({.i = row.s0[0], .q = row.s0[1], .u = row.s0[2], .v = row.s0[3]},
                       {.jI = row.j[0], .jQ = row.j[1], .jU = row.j[2], .jV = row.j[3]}, k);
    worst = worseOf(worst, relErr(toArray(got), row.ref));
  }
  std::printf("  stokesStepFull aligned rows max rel err %.3e\n", worst);
  check(worst <= DIRECT_TOL, "stokesStepFull within 1e-12 of the referee in the aligned frame");
}

void testReferenceSplit() {
  double worst = 0.0;
  bool thinIsDirect = true;
  for (const ReferenceRow &row : REFERENCE_ROWS) {
    const StokesGenerator k = generatorOf(row);
    const StokesArray split =
        stokesPropagateExact(row.s0, row.j, k, row.ds, StokesSourceForm::SteadyStateSplit);
    if (row.group == "faraday3d") {
      continue; // the rounded rotation angle bounds these rows; see above
    }
    if (row.k[0] * row.ds >= 0.1) {
      worst = worseOf(worst, relErr(split, row.ref));
    } else if (split != stokesPropagateExact(row.s0, row.j, k, row.ds)) {
      thinIsDirect = false;
    }
  }
  std::printf("  split alpha_I ds >= 0.1 max rel err %.3e\n", worst);
  check(worst <= SPLIT_TOL, "SteadyStateSplit within its 1e-9 budget at alpha_I ds >= 0.1");
  check(thinIsDirect, "SteadyStateSplit evaluates the direct integral below alpha_I ds = 0.1");
}

void testClosedFormLimits() {
  const StokesArray s0 = {1.0, 0.3, -0.2, 0.1};
  const StokesArray zero = {};

  // Pure Faraday rotation: dQ/ds = -rho_V U, dU/ds = rho_V Q.
  const double phi = 123.456;
  const StokesArray rot = stokesPropagateExact(s0, zero, {.rhoV = phi}, 1.0);
  const StokesArray rotRef = {s0[0], (s0[1] * std::cos(phi)) - (s0[2] * std::sin(phi)),
                              (s0[1] * std::sin(phi)) + (s0[2] * std::cos(phi)), s0[3]};
  check(relErr(rot, rotRef) < 1.0e-13, "pure Faraday rotation turns (Q, U) by rho_V ds");

  // Pure linear dichroism along Q: I + Q and I - Q decay at alpha_I +- alpha_Q.
  const double aI = 2.0;
  const double aQ = 1.5;
  const StokesArray di = stokesPropagateExact(s0, zero, {.alphaI = aI, .alphaQ = aQ}, 1.0);
  const double plus = (s0[0] + s0[1]) * std::exp(-(aI + aQ));
  const double minus = (s0[0] - s0[1]) * std::exp(-(aI - aQ));
  const StokesArray diRef = {0.5 * (plus + minus), 0.5 * (plus - minus), s0[2] * std::exp(-aI),
                             s0[3] * std::exp(-aI)};
  check(relErr(di, diRef) < 1.0e-14, "pure dichroism decays I +- Q at alpha_I +- alpha_Q");

  // Null rotation, w.w = 0: e^{-K'} = 1 - K' + K'^2 / 2 exactly.
  const StokesGenerator null{.alphaQ = 3.0, .rhoV = 3.0};
  const StokesArray nl = stokesPropagateExact(s0, zero, null, 1.0);
  const StokesArray k1 = stokes_exact_detail::applyLorentzPart(null, s0);
  const StokesArray k2 = stokes_exact_detail::applyLorentzPart(null, k1);
  const StokesArray nlRef = {s0[0] - k1[0] + (0.5 * k2[0]), s0[1] - k1[1] + (0.5 * k2[1]),
                             s0[2] - k1[2] + (0.5 * k2[2]), s0[3] - k1[3] + (0.5 * k2[3])};
  check(relErr(nl, nlRef) < 1.0e-14, "w.w = 0 null rotation equals 1 - K' + K'^2/2");

  // Pure gain (alpha_I < 0): I = I0 e^{g} + jI (e^{g} - 1) / g with g = -alpha_I ds.
  const StokesArray gain = stokesPropagateExact(s0, {0.8, 0.0, 0.0, 0.0}, {.alphaI = -10.0}, 1.0);
  const double grow = std::exp(10.0);
  check(std::abs(gain[0] - ((s0[0] * grow) + (0.8 * std::expm1(10.0) / 10.0))) <= 1.0e-14 * gain[0],
        "pure gain alpha_I ds = -10 grows I as e^10 plus the emission integral");

  // Zero length leaves the state unchanged.
  check(stokesPropagateExact(s0, s0, {.alphaI = 1.0, .rhoV = 2.0}, 0.0) == s0,
        "ds = 0 returns the entering state");
}

struct RandomSegment {
  StokesGenerator k{};
  StokesArray j{};
  StokesArray s0{};
};

class SegmentSampler {
public:
  explicit SegmentSampler(unsigned seed) : rng_(seed) {}

  StokesArray direction() {
    const double z = uniform(-1.0, 1.0);
    const double phi = uniform(0.0, 2.0 * std::numbers::pi);
    const double s = std::sqrt(1.0 - (z * z));
    return {s * std::cos(phi), s * std::sin(phi), z, 0.0};
  }

  RandomSegment physical(double tauA, double tauF) {
    const StokesArray en = direction();
    const StokesArray rn = direction();
    const double eta = tauA * uniform(0.0, 1.0);
    const StokesArray jn = direction();
    const StokesArray sn = direction();
    const double jI = uniform(0.0, 1.0);
    const double jP = jI * uniform(0.0, 1.0);
    const double sI = uniform(0.0, 1.0);
    const double sP = sI * uniform(0.0, 1.0);
    return {.k = {.alphaI = tauA,
                  .alphaQ = eta * en[0],
                  .alphaU = eta * en[1],
                  .alphaV = eta * en[2],
                  .rhoQ = tauF * rn[0],
                  .rhoU = tauF * rn[1],
                  .rhoV = tauF * rn[2]},
            .j = {jI, jP * jn[0], jP * jn[1], jP * jn[2]},
            .s0 = {sI, sP * sn[0], sP * sn[1], sP * sn[2]}};
  }

  double uniform(double lo, double hi) {
    return std::uniform_real_distribution<double>(lo, hi)(rng_);
  }

private:
  std::mt19937_64 rng_;
};

void testInvariants() {
  SegmentSampler sampler(20260925U);
  constexpr std::array<double, 5> tauAs = {1.0e-6, 1.0e-2, 0.3, 3.0, 30.0};
  constexpr std::array<double, 5> tauFs = {0.0, 0.5, 10.0, 200.0, 1000.0};
  double worstBound = -1.0;
  double worstLorentz = 0.0;
  double worstHalving = 0.0;
  for (const double tauA : tauAs) {
    for (const double tauF : tauFs) {
      for (int n = 0; n < 60; ++n) {
        const RandomSegment seg = sampler.physical(tauA, tauF);
        const StokesArray out = stokesPropagateExact(seg.s0, seg.j, seg.k, 1.0);
        const double pol = std::sqrt((out[1] * out[1]) + (out[2] * out[2]) + (out[3] * out[3]));
        worstBound = worseOf(worstBound, (pol - out[0]) / std::max(out[0], 1.0e-300));

        const StokesArray half = stokesPropagateExact(seg.s0, seg.j, seg.k, 0.5);
        const StokesArray twice = stokesPropagateExact(half, seg.j, seg.k, 0.5);
        worstHalving = worseOf(worstHalving, relErr(twice, out));

        StokesGenerator boostOnly = seg.k;
        boostOnly.alphaI = 0.0;
        const StokesArray lz = stokesPropagateExact(seg.s0, {}, boostOnly, 1.0);
        const double before = (seg.s0[0] * seg.s0[0]) - (seg.s0[1] * seg.s0[1]) -
                              (seg.s0[2] * seg.s0[2]) - (seg.s0[3] * seg.s0[3]);
        const double after = (lz[0] * lz[0]) - (lz[1] * lz[1]) - (lz[2] * lz[2]) - (lz[3] * lz[3]);
        const double scale = std::max(
            (lz[0] * lz[0]) + (lz[1] * lz[1]) + (lz[2] * lz[2]) + (lz[3] * lz[3]), 1.0e-300);
        worstLorentz = worseOf(worstLorentz, std::abs(after - before) / scale);
      }
    }
  }
  std::printf("  (|P| - I)/I max %.3e, Minkowski-norm drift %.3e, halving %.3e\n", worstBound,
              worstLorentz, worstHalving);
  check(worstBound <= 1.0e-12, "I >= |P| preserved for physical K, S0 and J");
  check(worstLorentz <= 1.0e-12, "alpha_I = 0, J = 0: I^2 - |P|^2 preserved (Lorentz transform)");
  check(worstHalving <= 1.0e-12, "two half steps equal one step");
}

void testSimplifiedKAgreement() {
  const StokesVector s0 = {.i = 1.0, .q = 0.3, .u = -0.2, .v = 0.1};
  const StokesEmission em = {.jI = 0.8, .jQ = 0.2, .jU = -0.1, .jV = 0.05};
  double worst = 0.0;
  for (const double tauA : {1.0e-3, 0.1, 2.0, 40.0}) {
    for (const double tauF : {0.0, 0.7, 30.0, 900.0}) {
      const StokesVector simple = stokesStep(s0, em, tauA, tauF, 1.0);
      const FaradayPropagation k{.alphaI = tauA, .rhoV = tauF, .dsCm = 1.0};
      worst = worseOf(worst, relErr(toArray(stokesStepFull(s0, em, k)), toArray(simple)));
    }
  }
  std::printf("  stokesStepFull vs stokesStep max rel diff %.3e\n", worst);
  check(worst <= 1.0e-12, "simplified K: stokesStepFull equals the closed-form stokesStep");
}

void testRk4Converges() {
  const StokesVector s0 = {.i = 1.0, .q = 0.3, .u = -0.2, .v = 0.1};
  const StokesEmission em = {.jI = 0.8, .jQ = 0.2, .jU = -0.1, .jV = 0.05};
  const FaradayPropagation k{
      .alphaI = 0.8, .alphaQ = 0.3, .alphaV = -0.2, .rhoV = 4.0, .rhoQ = 1.5, .dsCm = 1.0};
  const StokesArray exact = toArray(stokesStepFull(s0, em, k));
  auto rk4Error = [&](int n) {
    FaradayPropagation sub = k;
    sub.dsCm = k.dsCm / n;
    StokesVector s = s0;
    for (int i = 0; i < n; ++i) {
      s = stokesStepFullRk4(s, em, sub);
    }
    return relErr(toArray(s), exact);
  };
  const double e32 = rk4Error(32);
  const double e64 = rk4Error(64);
  std::printf("  RK4 error n=32 %.3e, n=64 %.3e, ratio %.2f\n", e32, e64, e32 / e64);
  check(e32 / e64 > 14.0 && e32 / e64 < 18.0, "RK4 converges to the exact step at fourth order");
}

} // namespace

int main() try {
  std::printf("Referee table (%zu rows):\n", std::size(REFERENCE_ROWS));
  testReferenceDirect();
  testReferenceFaradayGeneralAxis();
  testNoFloatingPointExceptions();
  testReferenceStepFull();
  testReferenceSplit();

  std::printf("\nClosed-form limits:\n");
  testClosedFormLimits();

  std::printf("\nInvariants:\n");
  testInvariants();
  testSimplifiedKAgreement();
  testRk4Converges();

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
