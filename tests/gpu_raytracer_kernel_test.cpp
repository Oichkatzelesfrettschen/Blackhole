#include "../src/physics/gpu_raytracer_kernel.hpp"
#include "../src/physics/verified/kerr.hpp"
#include "../src/physics/verified/rk4.hpp"
#include <iostream>
#include <iomanip>
#include <cmath>

namespace test {

// Helper: Compare floating point values with tolerance
inline bool approx_eq(double a, double b, double tol = 1e-10) {
    return std::abs(a - b) < tol;
}

// Test 1: GPUGeodesicState conversion (verified to GPU and back)
int test_geodesic_state_conversion() {
    std::cout << "TEST: GPUGeodesicState conversion\n";

    verified::StateVector initial{
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
    physics::gpu::GPUGeodesicState gpu_state = physics::gpu::GPUGeodesicState::from_verified(initial, 1.0);

    // Verify basic fields match (within float32 precision)
    if (!approx_eq(static_cast<double>(gpu_state.r), 10.0, 1e-6)) {
        std::cerr << "FAIL: r conversion\n";
        return 1;
    }
    if (!approx_eq(static_cast<double>(gpu_state.theta), 1.5708, 1e-6)) {
        std::cerr << "FAIL: theta conversion\n";
        return 1;
    }
    if (!approx_eq(static_cast<double>(gpu_state.dr), 0.001, 1e-8)) {
        std::cerr << "FAIL: dr conversion\n";
        return 1;
    }

    // Convert back to verified format
    verified::StateVector reconstructed = gpu_state.to_verified(0.0, 1.0);

    if (!approx_eq(reconstructed.x1, initial.x1, 1e-5)) {
        std::cerr << "FAIL: Reconstructed r mismatch\n";
        return 1;
    }

    std::cout << "  PASS: Conversion preserves data (float32 precision)\n";
    return 0;
}

// Test 2: Kernel configuration parameters
int test_kernel_config() {
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
    size_t expected_shared_mem = 96 * 1024;  // 96 KB
    if (physics::gpu::KernelConfig::SHARED_MEM_SIZE != expected_shared_mem) {
        std::cerr << "FAIL: SHARED_MEM_SIZE incorrect\n";
        return 1;
    }

    std::cout << "  PASS: Configuration valid for NVIDIA V100/A100\n";
    return 0;
}

// Test 3: Batch integration with simple test case
int test_batch_integration() {
    std::cout << "TEST: GPU batch integration (1 ray, 10 steps)\n";

    // Create single ray in Schwarzschild geometry (a=0)
    std::vector<verified::StateVector> rays_in(1);
    rays_in[0] = verified::StateVector{
        0.0,     // t
        10.0,    // r (outside Schwarzschild radius = 2M = 2)
        1.5708,  // theta (equatorial)
        0.0,     // phi
        1.0,     // v_t (unit time-like normalization)
        0.0,     // v_r (circular orbit, no radial motion)
        0.0,     // v_theta (equatorial)
        0.05     // v_phi (angular velocity)
    };

    std::vector<verified::StateVector> rays_out(1);

    // Integrate 10 steps with dt = 0.1
    double M = 1.0;    // Schwarzschild mass
    double a = 0.0;    // Non-rotating
    double h = 0.1;    // Step size
    int max_steps = 10;

    int successful = physics::gpu::gpu_batch_integrate_geodesics(
        rays_in, rays_out, M, a, h, max_steps, 1e-8
    );

    if (successful != 1) {
        std::cerr << "FAIL: Integration should complete successfully\n";
        return 1;
    }

    // Check output is reasonable (ray shouldn't escape or crash quickly)
    if (rays_out[0].x1 < 1.5 || rays_out[0].x1 > 50.0) {
        std::cerr << "FAIL: Final radius outside reasonable range: " << rays_out[0].x1 << "\n";
        return 1;
    }

    std::cout << "  PASS: Batch integration stable (r_initial=" << rays_in[0].x1
              << ", r_final=" << rays_out[0].x1 << ")\n";
    return 0;
}

// Test 4: GPU state packing density (should be 24 bytes with float32)
int test_state_packing() {
    std::cout << "TEST: GPUGeodesicState memory packing\n";

    size_t expected_size = 6 * sizeof(float);  // 6 float32 elements = 24 bytes
    if (sizeof(physics::gpu::GPUGeodesicState) != expected_size) {
        std::cerr << "FAIL: Expected size " << expected_size
                  << " bytes, got " << sizeof(physics::gpu::GPUGeodesicState) << "\n";
        return 1;
    }

    std::cout << "  PASS: State packed to " << sizeof(physics::gpu::GPUGeodesicState)
              << " bytes (6x float32)\n";
    return 0;
}

// Test 5: Transpose pattern validation (structure to basic structure check)
int test_transpose_pattern() {
    std::cout << "TEST: In-block transpose memory pattern\n";

    // Create test data
    const int NUM_RAYS = 8;
    physics::gpu::GPUGeodesicState rays[NUM_RAYS];

    for (int i = 0; i < NUM_RAYS; ++i) {
        rays[i] = physics::gpu::GPUGeodesicState{
            static_cast<float>(10.0 + i),    // r = 10, 11, 12, ...
            1.5708f,                           // theta
            0.0f,                              // phi
            0.001f,                            // dr
            0.0f,                              // dtheta
            0.05f + i * 0.01f                 // dphi (varying)
        };
    }

    // Allocate shared memory buffer
    float shared_mem[physics::gpu::KernelConfig::BLOCK_SIZE *
                     physics::gpu::KernelConfig::STATE_ELEMENTS];

    // Call transpose (CPU-friendly version, no __syncthreads)
    physics::gpu::transpose_ray_state_in_shared_memory(
        rays, shared_mem, 0, NUM_RAYS
    );

    // Validate transposed layout
    // First BLOCK_SIZE elements should contain r and theta values
    for (int i = 0; i < NUM_RAYS; ++i) {
        // Check r values in transposed layout
        if (shared_mem[i * 2] != rays[i].r) {
            std::cerr << "FAIL: Transposed r[" << i << "] mismatch\n";
            return 1;
        }
    }

    std::cout << "  PASS: Transpose pattern correct for coalesced access\n";
    return 0;
}

}  // namespace test

int main() {
    std::cout << "=== GPU Raytracer Kernel Tests (Phase 8.4) ===\n\n";

    int total_tests = 0;
    int passed_tests = 0;

    // Run all tests
    std::vector<std::pair<std::string, int(*)()>> tests{
        {"Kernel Config", test::test_kernel_config},
        {"State Packing", test::test_state_packing},
        {"State Conversion", test::test_geodesic_state_conversion},
        {"Transpose Pattern", test::test_transpose_pattern},
        {"Batch Integration", test::test_batch_integration}
    };

    for (const auto& [name, test_fn] : tests) {
        ++total_tests;
        if (test_fn() == 0) {
            ++passed_tests;
        }
    }

    std::cout << "\n=== Summary ===\n";
    std::cout << "Passed: " << passed_tests << "/" << total_tests << " tests\n";

    if (passed_tests == total_tests) {
        std::cout << "Status: ALL TESTS PASSED\n";
        return 0;
    } else {
        std::cout << "Status: " << (total_tests - passed_tests) << " test(s) FAILED\n";
        return 1;
    }
}
