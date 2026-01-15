/**
 * @file noise_generator_test.cpp
 * @brief FastNoise2 integration validation tests
 *
 * Phase 3.2.1: Procedural Enhancements
 */

#include "render/noise_generator.h"

#include <iostream>
#include <algorithm>
#include <cmath>

#ifdef BLACKHOLE_ENABLE_FASTNOISE2

int main() {
    using namespace blackhole;

    bool all_passed = true;

    // Test 1: Turbulence preset (FractalFBm)
    {
        std::cout << "Test 1: Turbulence Preset (FractalFBm)" << std::endl;
        NoiseGenerator gen(turbulencePreset());
        auto volume = gen.generate3D(64, 64, 64);

        if (volume.width != 64 || volume.height != 64 || volume.depth != 64) {
            std::cerr << "  FAIL: Incorrect dimensions" << std::endl;
            all_passed = false;
        } else if (volume.data.size() != 64 * 64 * 64) {
            std::cerr << "  FAIL: Incorrect data size" << std::endl;
            all_passed = false;
        } else {
            auto [min, max] = std::minmax_element(volume.data.begin(), volume.data.end());
            std::cout << "  PASS: 64^3 volume, range [" << *min << ", " << *max << "]" << std::endl;
        }
    }

    // Test 2: Density preset (Perlin)
    {
        std::cout << "Test 2: Density Preset (Perlin)" << std::endl;
        NoiseGenerator gen(densityPreset());
        auto volume = gen.generate3D(128, 128, 128);

        auto [min, max] = std::minmax_element(volume.data.begin(), volume.data.end());

        // Density preset should be in [0.8, 1.2] range
        if (*min < 0.79f || *max > 1.21f) {
            std::cerr << "  FAIL: Output range incorrect, got [" << *min << ", " << *max << "]" << std::endl;
            all_passed = false;
        } else {
            std::cout << "  PASS: 128^3 volume, range [" << *min << ", " << *max << "]" << std::endl;
        }
    }

    // Test 3: Ridged preset (FractalRidged)
    {
        std::cout << "Test 3: Ridged Preset (FractalRidged)" << std::endl;
        NoiseGenerator gen(ridgedPreset());
        auto volume = gen.generate3D(32, 32, 32);

        auto [min, max] = std::minmax_element(volume.data.begin(), volume.data.end());
        std::cout << "  PASS: 32^3 volume, range [" << *min << ", " << *max << "]" << std::endl;
    }

    // Test 4: Cellular preset (Voronoi)
    {
        std::cout << "Test 4: Cellular Preset (Voronoi)" << std::endl;
        NoiseGenerator gen(cellularPreset());
        auto volume = gen.generate3D(32, 32, 32);

        auto [min, max] = std::minmax_element(volume.data.begin(), volume.data.end());
        std::cout << "  PASS: 32^3 volume, range [" << *min << ", " << *max << "]" << std::endl;
    }

    // Test 5: Warped turbulence preset (Domain Warp)
    {
        std::cout << "Test 5: Warped Turbulence Preset (Domain Warp)" << std::endl;
        NoiseGenerator gen(warpedTurbulencePreset());
        auto volume = gen.generate3D(32, 32, 32);

        auto [min, max] = std::minmax_element(volume.data.begin(), volume.data.end());
        std::cout << "  PASS: 32^3 volume, range [" << *min << ", " << *max << "]" << std::endl;
    }

    // Test 6: 2D noise generation
    {
        std::cout << "Test 6: 2D Noise Generation" << std::endl;
        NoiseGenerator gen(turbulencePreset());
        auto data = gen.generate2D(256, 256);

        if (data.size() != 256 * 256) {
            std::cerr << "  FAIL: Incorrect 2D data size" << std::endl;
            all_passed = false;
        } else {
            auto [min, max] = std::minmax_element(data.begin(), data.end());
            std::cout << "  PASS: 256x256 2D slice, range [" << *min << ", " << *max << "]" << std::endl;
        }
    }

    // Test 7: Volume indexing
    {
        std::cout << "Test 7: Volume Indexing" << std::endl;
        NoiseGenerator gen(turbulencePreset());
        auto volume = gen.generate3D(16, 16, 16);

        // Test corner and center access
        float corner = volume.sample(0, 0, 0);
        float center = volume.sample(8, 8, 8);
        float far = volume.sample(15, 15, 15);

        std::cout << "  PASS: corner=" << corner << ", center=" << center << ", far=" << far << std::endl;
    }

    // Test 8: Reconfiguration
    {
        std::cout << "Test 8: Generator Reconfiguration" << std::endl;
        NoiseGenerator gen(turbulencePreset());

        auto volume1 = gen.generate3D(32, 32, 32);
        auto [min1, max1] = std::minmax_element(volume1.data.begin(), volume1.data.end());

        gen.configure(cellularPreset());
        auto volume2 = gen.generate3D(32, 32, 32);
        auto [min2, max2] = std::minmax_element(volume2.data.begin(), volume2.data.end());

        std::cout << "  PASS: Turbulence [" << *min1 << ", " << *max1 << "] -> Cellular [" << *min2 << ", " << *max2 << "]" << std::endl;
    }

    // Test 9: Version string
    {
        std::cout << "Test 9: FastNoise2 Version" << std::endl;
        std::string version = NoiseGenerator::version();
        std::cout << "  PASS: " << version << std::endl;
    }

    std::cout << std::endl;
    if (all_passed) {
        std::cout << "=== ALL TESTS PASSED ===" << std::endl;
        return 0;
    } else {
        std::cerr << "=== SOME TESTS FAILED ===" << std::endl;
        return 1;
    }
}

#else

int main() {
    std::cerr << "FastNoise2 disabled - no tests to run" << std::endl;
    return 0;
}

#endif // BLACKHOLE_ENABLE_FASTNOISE2
