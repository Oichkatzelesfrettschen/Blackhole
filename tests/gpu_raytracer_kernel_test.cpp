#include <cmath>
#include <cstddef>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

#include "../src/physics/gpu_raytracer_kernel.hpp"
#include "../src/physics/verified/rk4.hpp"

namespace test {

namespace {

// Helper: Compare floating point values with tolerance
inline bool approxEq(double a, double b, double tol = 1e-10) {
  return std::abs(a - b) < tol;
}

// Test 1: GPUGeodesicState conversion (verified to GPU and back)


int testGeodesicStateConversion() {
  std::cout << "TEST: GPUGeodesicState conversion\n";

  verified::StateVector const initial{
      0.0,    // t
      10.0,   // r
      1.5708, // theta (pi/2 - equatorial)
      0.0,    // phi
      0.0,    // v_t
      0.001,  // v_r
      0.0,    // v_theta
      0.05    // v_phi
  };

  // Convert to GPU format (single precision)
  physics::gpu::GPUGeodesicState const gpuState =
      physics::gpu::GPUGeodesicState::from_verified(initial, 1.0);

  // Verify basic fields match (within float32 precision)
  if (!approxEq(static_cast<double>(gpuState.r), 10.0, 1e-6)) {
    std::cerr << "FAIL: r conversion\n";
    return 1;
  }
  if (!approxEq(static_cast<double>(gpuState.theta), 1.5708, 1e-6)) {
    std::cerr << "FAIL: theta conversion\n";
    return 1;
  }
  if (!approxEq(static_cast<double>(gpuState.dr), 0.001, 1e-8)) {
    std::cerr << "FAIL: dr conversion\n";
    return 1;
  }

  // Convert back to verified format
  verified::StateVector const reconstructed = gpuState.to_verified(0.0, 1.0);

  if (!approxEq(reconstructed.x1, initial.x1, 1e-5)) {
    std::cerr << "FAIL: Reconstructed r mismatch\n";
    return 1;
  }

  std::cout << "  PASS: Conversion preserves data (float32 precision)\n";
  return 0;
}

// Test 2: Kernel configuration parameters
int testKernelConfig() {
  std::cout << "TEST: KernelConfig parameters\n";

  if (physics::gpu::KernelConfig::WARP_SIZE != 32) {
    std::cerr << "FAIL: WARP_SIZE should be 32\n";
    return 1;
  }
  if (physics::gpu::KernelConfig::BLOCK_SIZE != 128) {
    std::cerr << "FAIL: BLOCK_SIZE should be 128\n";
    return 1;
  }
  if (physics::gpu::KernelConfig::STATE_ELEMENTS != 6) {
    std::cerr << "FAIL: STATE_ELEMENTS should be 6\n";
    return 1;
  }

  // Memory check
  size_t const expectedSharedMem = 96UL * 1024UL; // 96 KB
  if (physics::gpu::KernelConfig::SHARED_MEM_SIZE != expectedSharedMem) {
    std::cerr << "FAIL: SHARED_MEM_SIZE incorrect\n";
    return 1;
  }

  std::cout << "  PASS: Configuration valid for NVIDIA V100/A100\n";
  return 0;
}

// Test 3: Batch integration with simple test case
int testBatchIntegration() {
  std::cout << "TEST: GPU batch integration (1 ray, 10 steps)\n";

  // Create single ray in Schwarzschild geometry (a=0)
  std::vector<verified::StateVector> raysIn(1);
  raysIn.at(0) = verified::StateVector{
      0.0,    // t
      10.0,   // r (outside Schwarzschild radius = 2M = 2)
      1.5708, // theta (equatorial)
      0.0,    // phi
      1.0,    // v_t (unit time-like normalization)
      0.0,    // v_r (circular orbit, no radial motion)
      0.0,    // v_theta (equatorial)
      0.05    // v_phi (angular velocity)
  };

  std::vector<verified::StateVector> raysOut(1);

  // Integrate 10 steps with dt = 0.1
  double const m = 1.0; // Schwarzschild mass
  double const a = 0.0; // Non-rotating
  double const h = 0.1; // Step size
  int const maxSteps = 10;

  int const successful =
      physics::gpu::gpu_batch_integrate_geodesics(raysIn, raysOut, m, a, h, maxSteps, 1e-8);

  if (successful != 1) {
    std::cerr << "FAIL: Integration should complete successfully\n";
    return 1;
  }

  // Check output is reasonable (ray shouldn't escape or crash quickly)
  if (raysOut.at(0).x1 < 1.5 || raysOut.at(0).x1 > 50.0) {
    std::cerr << "FAIL: Final radius outside reasonable range: " << raysOut.at(0).x1 << "\n";
    return 1;
  }

  std::cout << "  PASS: Batch integration stable (r_initial=" << raysIn.at(0).x1
            << ", r_final=" << raysOut.at(0).x1 << ")\n";
  return 0;
}

// Test 4: GPU state packing density (should be 24 bytes with float32)
int testStatePacking() {
  std::cout << "TEST: GPUGeodesicState memory packing\n";

  size_t const expectedSize = 6 * sizeof(float); // 6 float32 elements = 24 bytes
  if (sizeof(physics::gpu::GPUGeodesicState) != expectedSize) {
    std::cerr << "FAIL: Expected size " << expectedSize << " bytes, got "
              << sizeof(physics::gpu::GPUGeodesicState) << "\n";
    return 1;
  }

  std::cout << "  PASS: State packed to " << sizeof(physics::gpu::GPUGeodesicState)
            << " bytes (6x float32)\n";
  return 0;
}

// Test 5: Transpose pattern validation (structure to basic structure check)
int testTransposePattern() {
  std::cout << "TEST: In-block transpose memory pattern\n";

  // Create test data
  const int numRays = 8;
  physics::gpu::GPUGeodesicState rays[numRays];

  for (int i = 0; i < numRays; ++i) {
    rays[i] = physics::gpu::GPUGeodesicState{
        .r = static_cast<float>(10.0 + i), // r = 10, 11, 12, ...
        .theta = 1.5708f,                  // theta
        .phi = 0.0f,                       // phi
        .dr = 0.001f,                      // dr
        .dtheta = 0.0f,                    // dtheta
        .dphi = 0.05f + (static_cast<float>(i) * 0.01f)        // dphi (varying)
    };
  }

  // Allocate shared memory buffer
  float sharedMem[physics::gpu::KernelConfig::BLOCK_SIZE *
                  physics::gpu::KernelConfig::STATE_ELEMENTS];

  // Call transpose (CPU-friendly version, no __syncthreads)
  physics::gpu::transpose_ray_state_in_shared_memory(rays, sharedMem, 0, numRays);

  // Validate transposed layout
  // First BLOCK_SIZE elements should contain r and theta values
  for (int i = 0; i < numRays; ++i) {
    // Check r values in transposed layout
    if (sharedMem[static_cast<std::size_t>(i) * 2U] != rays[i].r) {
      std::cerr << "FAIL: Transposed r[" << i << "] mismatch\n";
      return 1;
    }
  }

  std::cout << "  PASS: Transpose pattern correct for coalesced access\n";
  return 0;
}

}  // namespace test

} // namespace

int main() {
    std::cout << "=== GPU Raytracer Kernel Tests (Phase 8.4) ===\n\n";

    int totalTests = 0;
    int passedTests = 0;

    // Run all tests
    std::vector<std::pair<std::string, int (*)()>> const tests{
        {"Kernel Config", test::testKernelConfig},
        {"State Packing", test::testStatePacking},
        {"State Conversion", test::testGeodesicStateConversion},
        {"Transpose Pattern", test::testTransposePattern},
        {"Batch Integration", test::testBatchIntegration}};

    for (const auto& [name, test_fn] : tests) {
      ++totalTests;
      if (test_fn() == 0) {
        ++passedTests;
      }
    }

    std::cout << "\n=== Summary ===\n";
    std::cout << "Passed: " << passedTests << "/" << totalTests << " tests\n";

    if (passedTests == totalTests) {
      std::cout << "Status: ALL TESTS PASSED\n";
      return 0;
    }
    std::cout << "Status: " << (totalTests - passedTests) << " test(s) FAILED\n";
    return 1;
}
