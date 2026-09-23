/**
 * tests/glsl_parity_test.cpp
 *
 * PHASE 9.0.5: GPU/CPU Parity Validation Tests
 *
 * Validates that GLSL shader computations produce results within float32 tolerance
 * of C++23 reference implementations. Tests are organized by metric type and
 * span full parameter ranges.
 *
 * Key test categories:
 * 1. Schwarzschild metric (a=0, M=1)
 * 2. Kerr metric (varying a from 0 to 0.998)
 * 3. RK4 integration accuracy
 * 4. Hamiltonian constraint preservation
 * 5. Energy conservation over multiple steps
 *
 * Tolerance: 1e-5 relative error (float32 precision loss)
 *
 * Compilation:
 *   g++ -std=c++23 -O2 -I. tests/glsl_parity_test.cpp -o build/glsl_parity_test
 *
 * Usage:
 *   ./build/glsl_parity_test [filter] [verbose]
 *
 * Examples:
 *   ./build/glsl_parity_test              # Run all tests
 *   ./build/glsl_parity_test "kerr"       # Run Kerr tests only
 *   ./build/glsl_parity_test "rk4" 1      # Run RK4 tests with verbose output
 */

#include <numbers>
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <string>
#include <utility>
#include <vector>


// ============================================================================
// Test Infrastructure
// ============================================================================

namespace {

struct TestResult {
    std::string name;
    bool passed{};
    double relativeError{};
    double absoluteError{};
    std::string message;
};

struct TestStats {
    int total = 0;
    int passed = 0;
    int failed = 0;
    double maxError = 0.0;
};

class TestSuite {
public:
  explicit TestSuite(std::string name) : suite_name_(std::move(name)) {}

  void addResult(const TestResult &result) {
    results_.push_back(result);
    stats_.total++;
    if (result.passed) {
      stats_.passed++;
    } else {
      stats_.failed++;
    }
    stats_.maxError = std::max(stats_.maxError, result.relativeError);
  }

  void printSummary(bool verbose = false) {
    std::cout << "\n" << std::string(70, '=') << "\n";
    std::cout << "Test Suite: " << suite_name_ << "\n";
    std::cout << std::string(70, '=') << "\n";

    if (verbose) {
      for (const auto &result : results_) {
        std::cout << (result.passed ? "[PASS]" : "[FAIL]") << " " << std::setw(40) << std::left
                  << result.name;
        if (!result.passed) {
          std::cout << " (rel_err: " << std::scientific << std::setprecision(2)
                    << result.relativeError << ", " << result.message << ")";
        }
        std::cout << "\n";
      }
    }

    std::cout << "\nSummary:\n";
    std::cout << "  Total:  " << stats_.total << "\n";
    std::cout << "  Passed: " << stats_.passed << "\n";
    std::cout << "  Failed: " << stats_.failed << "\n";
    std::cout << "  Max Error: " << std::scientific << std::setprecision(2) << stats_.maxError
              << "\n";
    std::cout << std::string(70, '=') << "\n";
  }

  [[nodiscard]] int failedCount() const { return stats_.failed; }

private:
  std::string suite_name_;
  std::vector<TestResult> results_;
  TestStats stats_;
};

// ============================================================================
// Test Tolerance Configuration
// ============================================================================

const double PARITY_TOLERANCE = 1e-5;      // 1e-5 relative error tolerance (float32 loss)
const double HAMILTONIAN_TOLERANCE = 1e-6; // Constraint tolerance

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * Compare two floating-point values with relative tolerance
 *
 * @param cpu CPU reference value
 * @param gpu GPU computed value
 * @param tolerance Relative error tolerance
 * @param rel_error Output: relative error percentage
 * @param abs_error Output: absolute error
 * @return True if within tolerance
 */
bool compareValues(double cpu, double gpu, double tolerance, double &relError,
                          double &absError) {
  absError = std::abs(cpu - gpu);

  if (std::abs(cpu) < 1e-10) {
    // For near-zero values, use absolute tolerance
    relError = absError / 1e-10;
    return absError < tolerance * 1e-10;
  }

  relError = absError / std::abs(cpu);
  return relError <= tolerance;
}

/**
 * Simulate GLSL 4.60 float precision
 * Converts double to float and back (simulates shader computation)
 */
double glslPrecision(double value) {
  return static_cast<double>(static_cast<float>(value));
}

// ============================================================================
// Reference Implementations (CPU)
// ============================================================================

/**
 * Schwarzschild metric components
 * Delta = r^2 - 2M*r
 * Sigma = r^2
 */
struct SchwarzschildMetric {
  double delta;
  double sigma;
  double a; // r-dependent term in frame-dragging

  static SchwarzschildMetric compute(double r, double mass) {
    SchwarzschildMetric metric{};
    metric.sigma = r * r;
    metric.delta = metric.sigma - (2.0 * mass * r);
    metric.a = metric.sigma * metric.sigma; // For simplicity in Schwarzschild
    return metric;
  }
};

/**
 * Kerr metric components
 * Sigma = r^2 + a^2*cos(theta)^2
 * Delta = r^2 - 2M*r + a^2
 * A = (r^2 + a^2)^2 - a^2*Delta*sin(theta)^2
 */
struct KerrMetric {
  double sigma;
  double delta;
  double a;

  static KerrMetric compute(double r, double theta, double mass, double spin) {
    KerrMetric metric{};
    double const cosTheta = std::cos(theta);
    double const sinTheta = std::sin(theta);
    double const a2 = spin * spin;
    double const r2 = r * r;

    metric.sigma = r2 + (a2 * cosTheta * cosTheta);
    metric.delta = r2 - (2.0 * mass * r) + a2;
    metric.a = ((r2 + a2) * (r2 + a2)) - (a2 * metric.delta * sinTheta * sinTheta);

    return metric;
  }
};

/**
 * Hamiltonian constraint for null geodesic
 * H = g_mu_nu u^mu u^nu = 0
 *
 * In Boyer-Lindquist coordinates:
 * H = -(Delta/Sigma)*(dt)^2 + (Sigma/Delta)*(dr)^2 +
 *     Sigma*(dtheta)^2 + (A/(Sigma*sin^2(theta)))*(dphi)^2
 */
double computeHamiltonian(double r, double theta, double m, double a, double dt, double dr,
                                 double dtheta, double dphi) {
  KerrMetric const metric = KerrMetric::compute(r, theta, m, a);
  double const sinTheta = std::sin(theta);
  double const sin2Theta = sinTheta * sinTheta;

  double const h =
      (-(metric.delta / metric.sigma) * dt * dt) + ((metric.sigma / metric.delta) * dr * dr) +
      (metric.sigma * dtheta * dtheta) + ((metric.a / (metric.sigma * sin2Theta)) * dphi * dphi);

  return h;
}

/**
 * RK4 step for geodesic in Kerr metric (simplified)
 * Uses explicit RK4 formula with geodesic RHS
 */
struct RayState {
    double t, r, theta, phi;
    double dt, dr, dtheta, dphi;
    double lambda;

    // Schwarzschild geodesic RHS from the exact Christoffel symbols
    // (MTW ch. 25; f = 1 - 2M/r):
    //   d2t     = -(2M / (r^2 f)) dt dr
    //   d2r     = -(M f / r^2) dt^2 + (M / (r^2 f)) dr^2
    //             + r f (dtheta^2 + sin^2(theta) dphi^2)
    //   d2theta = -(2/r) dr dtheta + sin(theta) cos(theta) dphi^2
    //   d2phi   = -(2/r) dr dphi - 2 cot(theta) dtheta dphi
    // The historical "simplified" RHS had the d2t sign flipped and
    // dropped every 1/f factor, so Hamiltonian drift was guaranteed
    // regardless of integrator quality.
    static std::array<double, 4> rhs(const RayState &state, double m, double /*a*/) {
      double const r = state.r;
      double const r2 = r * r;
      double const f = 1.0 - (2.0 * m / r);
      double const sinTheta = std::sin(state.theta);
      double const cosTheta = std::cos(state.theta);

      double const d2t = -(2.0 * m / (r2 * f)) * state.dt * state.dr;
      double const d2r = (-(m * f / r2) * state.dt * state.dt) +
                         ((m / (r2 * f)) * state.dr * state.dr) +
                         ((r * f) * ((state.dtheta * state.dtheta) +
                                     (sinTheta * sinTheta * state.dphi * state.dphi)));
      double const d2theta = (-(2.0 / r) * state.dr * state.dtheta) +
                             (sinTheta * cosTheta * state.dphi * state.dphi);
      double const d2phi = (-(2.0 / r) * state.dr * state.dphi) -
                           (2.0 * (cosTheta / sinTheta) * state.dtheta * state.dphi);

      return {d2t, d2r, d2theta, d2phi};
    }

    // Classic RK4 over the full 8-component state (4 positions + 4
    // velocities). Each intermediate stage advances positions with the
    // STAGE velocities and velocities with the stage accelerations; the
    // historical version added accelerations to positions, advanced r
    // with the t-velocity, and never updated intermediate velocities,
    // so its "drift" measured its own indexing bugs.
    static RayState advanced(const RayState &base, const RayState &vel,
                             const std::array<double, 4> &acc, double h) {
      RayState out = base;
      out.t += vel.dt * h;
      out.r += vel.dr * h;
      out.theta += vel.dtheta * h;
      out.phi += vel.dphi * h;
      out.dt += acc[0] * h;
      out.dr += acc[1] * h;
      out.dtheta += acc[2] * h;
      out.dphi += acc[3] * h;
      return out;
    }

    static RayState step(RayState state, double h, double m, double a) {
      auto const k1 = rhs(state, m, a);
      RayState const s2 = advanced(state, state, k1, h * 0.5);
      auto const k2 = rhs(s2, m, a);
      RayState const s3 = advanced(state, s2, k2, h * 0.5);
      auto const k3 = rhs(s3, m, a);
      RayState const s4 = advanced(state, s3, k3, h);
      auto const k4 = rhs(s4, m, a);

      const double oneSixth = h / 6.0;
      state.t += (state.dt + (2.0 * s2.dt) + (2.0 * s3.dt) + s4.dt) * oneSixth;
      state.r += (state.dr + (2.0 * s2.dr) + (2.0 * s3.dr) + s4.dr) * oneSixth;
      state.theta +=
          (state.dtheta + (2.0 * s2.dtheta) + (2.0 * s3.dtheta) + s4.dtheta) * oneSixth;
      state.phi +=
          (state.dphi + (2.0 * s2.dphi) + (2.0 * s3.dphi) + s4.dphi) * oneSixth;
      state.dt += (k1[0] + (2.0 * k2[0]) + (2.0 * k3[0]) + k4[0]) * oneSixth;
      state.dr += (k1[1] + (2.0 * k2[1]) + (2.0 * k3[1]) + k4[1]) * oneSixth;
      state.dtheta += (k1[2] + (2.0 * k2[2]) + (2.0 * k3[2]) + k4[2]) * oneSixth;
      state.dphi += (k1[3] + (2.0 * k2[3]) + (2.0 * k3[3]) + k4[3]) * oneSixth;
      state.lambda += h;

      return state;
    }
};

// ============================================================================
// Test Cases
// ============================================================================

TestSuite schwarzschildTests("Schwarzschild Metric (a=0)");
TestSuite kerrTests("Kerr Metric (a > 0)");
TestSuite hamiltonianTests("Hamiltonian Constraint Preservation");
TestSuite rk4Tests("RK4 Integration");

// ============================================================================
// Test Execution
// ============================================================================

void runSchwarzschildTests() {
  std::cout << "\n[Running Schwarzschild Tests]\n";

  double const m = 1.0;
  double const a = 0.0;

  // Test 1: Metric components at r=10
  {
    double const r = 10.0;
    auto metric = SchwarzschildMetric::compute(r, m);

    double const expectedSigma = 100.0;
    double const expectedDelta = 80.0; // r^2 - 2Mr = 100 - 20 = 80

    TestResult res;
    res.name = "Schwarzschild Metric at r=10";

    double const cpuSigma = metric.sigma;
    double const gpuSigma = glslPrecision(cpuSigma);
    double const cpuDelta = metric.delta;
    double const gpuDelta = glslPrecision(cpuDelta);

    // Exactness of the double reference plus float32 parity of the
    // simulated GPU values.
    double sigmaRelErr = 0.0;
    double sigmaAbsErr = 0.0;
    double deltaRelErr = 0.0;
    double deltaAbsErr = 0.0;
    res.passed = (std::abs(cpuSigma - expectedSigma) < 1e-10) &&
                 (std::abs(cpuDelta - expectedDelta) < 1e-10) &&
                 compareValues(cpuSigma, gpuSigma, PARITY_TOLERANCE, sigmaRelErr, sigmaAbsErr) &&
                 compareValues(cpuDelta, gpuDelta, PARITY_TOLERANCE, deltaRelErr, deltaAbsErr);

    res.relativeError = std::max(std::abs(cpuSigma - expectedSigma) / expectedSigma,
                                 std::abs(cpuDelta - expectedDelta) / expectedDelta);
    res.absoluteError =
        std::max(std::abs(cpuSigma - expectedSigma), std::abs(cpuDelta - expectedDelta));

    schwarzschildTests.addResult(res);
  }

  // Test 2: Hamiltonian constraint for a null (photon) vector
  {
    double const r = 10.0;
    double const theta = std::numbers::pi / 2.0; // Equatorial plane
    double const dr = 0.5;
    double const dtheta = 0.0;
    double const dphi = 0.5;
    // Solve the Schwarzschild null condition for dt from the closed-form
    // metric: f dt^2 = dr^2/f + r^2 dphi^2 with f = 1 - 2M/r. Evaluating
    // the ported Hamiltonian on this vector cross-checks its g^{mu nu}
    // assembly against the analytic line element. The historical vector
    // (dt = 1) was not null, so H != 0 was the correct answer to a wrong
    // question.
    double const f = 1.0 - (2.0 * m / r);
    double const dt =
        std::sqrt(((dr * dr / f) + (r * r * dphi * dphi)) / f);

    double const h = computeHamiltonian(r, theta, m, a, dt, dr, dtheta, dphi);

    TestResult res;
    res.name = "Hamiltonian constraint (photon)";
    res.relativeError = std::abs(h); // Should be near 0 for null geodesic
    res.absoluteError = std::abs(h);
    res.passed = res.relativeError < HAMILTONIAN_TOLERANCE;
    res.message = (res.passed ? "OK" : "Constraint violated");

    hamiltonianTests.addResult(res);
  }
}

void runKerrTests() {
  std::cout << "\n[Running Kerr Tests]\n";

  double const m = 1.0;
  std::vector<double> const spinValues = {0.1, 0.5, 0.9, 0.998};

  for (double const a : spinValues) {
    // Test: Metric at equator (theta = pi/2)
    double const r = 10.0;
    double const theta = std::numbers::pi / 2.0;

    auto metric = KerrMetric::compute(r, theta, m, a);

    TestResult res;
    res.name = "Kerr Metric at r=10, a=" + std::to_string(a);
    res.passed = (metric.sigma > 0.0) && (std::abs(metric.delta) > 0.0);
    res.relativeError = 0.0; // Placeholder
    res.absoluteError = 0.0;

    kerrTests.addResult(res);
  }
}

void runHamiltonianPreservationTests() {
  std::cout << "\n[Running Hamiltonian Preservation Tests]\n";

  // The RayState RHS integrates Schwarzschild geodesics (exact
  // Christoffels for a = 0), so conservation is measured against the
  // a = 0 Hamiltonian. The historical run stepped Schwarzschild
  // trajectories while measuring a Kerr (a = 0.5) Hamiltonian, a
  // quantity those trajectories do not conserve even in exact
  // arithmetic.
  double const m = 1.0;
  double const a = 0.0;
  int const numSteps = 100;
  double const h = 0.01;

  RayState ray{};
  ray.t = 0.0;
  ray.r = 30.0;
  ray.theta = std::numbers::pi / 2.0;
  ray.phi = 0.0;
  ray.dt = 1.0;
  ray.dr = 0.01;
  ray.dtheta = 0.0;
  ray.dphi = 0.1;
  ray.lambda = 0.0;

  double const initialH =
      computeHamiltonian(ray.r, ray.theta, m, a, ray.dt, ray.dr, ray.dtheta, ray.dphi);

  for (int i = 0; i < numSteps; i++) {
    ray = RayState::step(ray, h, m, a);
  }

  double const finalH =
      computeHamiltonian(ray.r, ray.theta, m, a, ray.dt, ray.dr, ray.dtheta, ray.dphi);

  TestResult res;
  res.name = "Hamiltonian preservation over 100 steps (Schwarzschild)";
  res.relativeError = std::abs(finalH - initialH) / std::max(std::abs(initialH), 1e-10);
  res.absoluteError = std::abs(finalH - initialH);
  res.passed = res.relativeError < 1e-3; // Allow some growth over 100 steps

  hamiltonianTests.addResult(res);
}

void runRk4AccuracyTests() {
  std::cout << "\n[Running RK4 Accuracy Tests]\n";

  double const m = 1.0;
  double const a = 0.0;

  // Test: Single RK4 step shouldn't change rays much
  RayState ray{};
  ray.t = 0.0;
  ray.r = 50.0;
  ray.theta = std::numbers::pi / 4.0;
  ray.phi = 0.0;
  ray.dt = 1.0;
  ray.dr = 0.001;
  ray.dtheta = 0.0001;
  ray.dphi = 0.05;
  ray.lambda = 0.0;

  RayState const rayStepped = RayState::step(ray, 0.01, m, a);

  double const dr = rayStepped.r - ray.r;
  double const dtheta = rayStepped.theta - ray.theta;

  TestResult res;
  res.name = "RK4 step produces reasonable changes";
  res.relativeError = std::abs(dr) / ray.r;
  res.absoluteError = std::abs(dr);
  res.passed = (std::abs(dr) < 0.1) && (std::abs(dtheta) < 0.1);

  rk4Tests.addResult(res);
}

// ============================================================================
// Main Test Runner
// ============================================================================

} // namespace

int main(int argc, char** argv) {
  std::string const filter = (argc > 1) ? argv[1] : "";
  bool const verbose = (argc > 2) ? (std::strtol(argv[2], nullptr, 10) != 0L) : false;

  std::cout << "Phase 9.0.5: GLSL Shader Parity Tests\n";
  std::cout << "======================================\n";
  std::cout << "Precision tolerance: " << PARITY_TOLERANCE << "\n";
  std::cout << "Hamiltonian tolerance: " << HAMILTONIAN_TOLERANCE << "\n\n";

  // Run all test suites
  if (filter.empty() || filter.contains("schwarzschild")) {
    runSchwarzschildTests();
    schwarzschildTests.printSummary(verbose);
  }

  if (filter.empty() || filter.contains("kerr")) {
    runKerrTests();
    kerrTests.printSummary(verbose);
  }

  if (filter.empty() || filter.contains("hamiltonian")) {
    runHamiltonianPreservationTests();
    hamiltonianTests.printSummary(verbose);
  }

  if (filter.empty() || filter.contains("rk4")) {
    runRk4AccuracyTests();
    rk4Tests.printSummary(verbose);
  }

  int const totalFailed = schwarzschildTests.failedCount() + kerrTests.failedCount() +
                          hamiltonianTests.failedCount() + rk4Tests.failedCount();
  return (totalFailed == 0) ? 0 : 1;
}
