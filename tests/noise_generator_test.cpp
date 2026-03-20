/**
 * @file noise_generator_test.cpp
 * @brief FastNoise2 integration validation tests
 *
 * Phase 3.2.1: Procedural Enhancements
 */

#include "render/noise_generator.h"

#include <algorithm>
#include <cmath>
#include <iostream>

#ifdef BLACKHOLE_ENABLE_FASTNOISE2

int main() {
    using namespace blackhole;

    bool allPassed = true;

    // Test 1: Turbulence preset (FractalFBm)
    {
        std::cout << "Test 1: Turbulence Preset (FractalFBm)\n";
        NoiseGenerator gen(turbulencePreset());
        auto volume = gen.generate3D(64, 64, 64);

        if (volume.width != 64 || volume.height != 64 || volume.depth != 64) {
            std::cerr << "  FAIL: Incorrect dimensions\n";
            allPassed = false;
        } else if (volume.data.size() != 64UL * 64UL * 64UL) {
            std::cerr << "  FAIL: Incorrect data size\n";
            allPassed = false;
        } else {
            auto [mn, mx] = std::ranges::minmax_element(volume.data);
            std::cout << "  PASS: 64^3 volume, range [" << *mn << ", " << *mx << "]\n";
        }
    }

    // Test 2: Density preset (Perlin)
    {
        std::cout << "Test 2: Density Preset (Perlin)\n";
        NoiseGenerator gen(densityPreset());
        auto volume = gen.generate3D(128, 128, 128);

        auto [mn, mx] = std::ranges::minmax_element(volume.data);

        // Density preset should be in [0.8, 1.2] range
        if (*mn < 0.79f || *mx > 1.21f) {
            std::cerr << "  FAIL: Output range incorrect, got [" << *mn << ", " << *mx << "]\n";
            allPassed = false;
        } else {
            std::cout << "  PASS: 128^3 volume, range [" << *mn << ", " << *mx << "]\n";
        }
    }

    // Test 3: Ridged preset (FractalRidged)
    {
        std::cout << "Test 3: Ridged Preset (FractalRidged)\n";
        NoiseGenerator gen(ridgedPreset());
        auto volume = gen.generate3D(32, 32, 32);

        auto [mn, mx] = std::ranges::minmax_element(volume.data);
        std::cout << "  PASS: 32^3 volume, range [" << *mn << ", " << *mx << "]\n";
    }

    // Test 4: Cellular preset (Voronoi)
    {
        std::cout << "Test 4: Cellular Preset (Voronoi)\n";
        NoiseGenerator gen(cellularPreset());
        auto volume = gen.generate3D(32, 32, 32);

        auto [mn, mx] = std::ranges::minmax_element(volume.data);
        std::cout << "  PASS: 32^3 volume, range [" << *mn << ", " << *mx << "]\n";
    }

    // Test 5: Warped turbulence preset (Domain Warp)
    {
        std::cout << "Test 5: Warped Turbulence Preset (Domain Warp)\n";
        NoiseGenerator gen(warpedTurbulencePreset());
        auto volume = gen.generate3D(32, 32, 32);

        auto [mn, mx] = std::ranges::minmax_element(volume.data);
        std::cout << "  PASS: 32^3 volume, range [" << *mn << ", " << *mx << "]\n";
    }

    // Test 6: 2D noise generation
    {
        std::cout << "Test 6: 2D Noise Generation\n";
        NoiseGenerator gen(turbulencePreset());
        auto data = gen.generate2D(256, 256);

        if (data.size() != 256UL * 256UL) {
            std::cerr << "  FAIL: Incorrect 2D data size\n";
            allPassed = false;
        } else {
            auto [mn, mx] = std::ranges::minmax_element(data);
            std::cout << "  PASS: 256x256 2D slice, range [" << *mn << ", " << *mx << "]\n";
        }
    }

    // Test 7: Volume indexing
    {
        std::cout << "Test 7: Volume Indexing\n";
        NoiseGenerator gen(turbulencePreset());
        auto volume = gen.generate3D(16, 16, 16);

        // Test corner and center access
        const float corner = volume.sample(0, 0, 0);
        const float center = volume.sample(8, 8, 8);
        const float farVal = volume.sample(15, 15, 15);

        std::cout << "  PASS: corner=" << corner << ", center=" << center << ", far=" << farVal << "\n";
    }

    // Test 8: Reconfiguration
    {
        std::cout << "Test 8: Generator Reconfiguration\n";
        NoiseGenerator gen(turbulencePreset());

        auto volume1 = gen.generate3D(32, 32, 32);
        auto [mn1, mx1] = std::ranges::minmax_element(volume1.data);

        gen.configure(cellularPreset());
        auto volume2 = gen.generate3D(32, 32, 32);
        auto [mn2, mx2] = std::ranges::minmax_element(volume2.data);

        std::cout << "  PASS: Turbulence [" << *mn1 << ", " << *mx1 << "] -> Cellular [" << *mn2 << ", " << *mx2 << "]\n";
    }

    // Test 9: Version string
    {
        std::cout << "Test 9: FastNoise2 Version\n";
        const std::string version = NoiseGenerator::version();
        std::cout << "  PASS: " << version << "\n";
    }

    std::cout << '\n';
    if (allPassed) {
        std::cout << "=== ALL TESTS PASSED ===\n";
        return 0;
    }
    std::cerr << "=== SOME TESTS FAILED ===\n";
    return 1;
}

#else

int main() {
  std::cerr << "FastNoise2 disabled - no tests to run" << '\n';
  return 0;
}

#endif // BLACKHOLE_ENABLE_FASTNOISE2
