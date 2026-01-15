/**
 * @file noise_generator.h
 * @brief FastNoise2-based procedural noise generation for accretion disk turbulence
 *
 * Phase 3.2.1: Procedural Enhancements
 *
 * Generates 3D noise textures for:
 * - Accretion disk turbulence and detail
 * - Volumetric density variations
 * - Multi-octave fractal noise (fBm, Ridged, Billow)
 *
 * Workflow:
 * 1. Configure noise generator (type, frequency, octaves, lacunarity)
 * 2. Generate 3D noise volume (128³ or 256³)
 * 3. Upload to GL_TEXTURE_3D for GPU sampling
 * 4. Shader samples noise(uvw) for disk turbulence
 */

#pragma once

#ifdef BLACKHOLE_ENABLE_FASTNOISE2

#include <FastNoise/FastNoise.h>
#include <memory>
#include <vector>
#include <string>
#include <cstdint>

namespace blackhole {

/**
 * @brief Noise generator configuration
 */
struct NoiseConfig {
    // === Generator Type ===
    enum class Type {
        OpenSimplex2,       // Smooth, fast, good for clouds/turbulence
        OpenSimplex2S,      // Even smoother variant
        Perlin,             // Classic Perlin noise
        ValueCubic,         // Value noise with cubic interpolation
        Cellular,           // Voronoi/cellular patterns (good for disk cells)
        FractalFBm,         // Fractal Brownian Motion (layered octaves)
        FractalRidged,      // Ridged multi-fractal (mountain-like features)
        FractalPingPong,    // Oscillating fractal (waves, ripples)
    };

    Type type = Type::FractalFBm;

    // === Base Frequency ===
    float frequency = 1.0f;  // Higher = more detail/smaller features

    // === Fractal Parameters (for Fractal types) ===
    int octaves = 4;            // Number of noise layers (1-8 typical)
    float lacunarity = 2.0f;    // Frequency multiplier per octave (2.0 = doubling)
    float gain = 0.5f;          // Amplitude multiplier per octave (0.5 = halving)
    float weightedStrength = 0.0f;  // Fractal weighting strength (0.0-1.0)

    // === Domain Warping (optional) ===
    bool enableDomainWarp = false;
    float warpAmplitude = 1.0f;
    float warpFrequency = 0.5f;

    // === Cellular Parameters (if type = Cellular) ===
    enum class CellularDistanceFunc {
        Euclidean,
        EuclideanSq,
        Manhattan,
        Hybrid,
    };
    CellularDistanceFunc cellularDistance = CellularDistanceFunc::EuclideanSq;
    float cellularJitter = 1.0f;  // 0.0 = regular grid, 1.0 = full randomness

    // === Output Remapping ===
    float outputMin = 0.0f;  // Remap noise from [-1,1] to [outputMin, outputMax]
    float outputMax = 1.0f;

    // === Seed ===
    int seed = 1337;
};

/**
 * @brief 3D noise volume descriptor
 */
struct NoiseVolume {
    std::vector<float> data;  // Flattened [z][y][x] data
    uint32_t width = 0;
    uint32_t height = 0;
    uint32_t depth = 0;

    // Linear index: z * (width * height) + y * width + x
    inline size_t index(uint32_t x, uint32_t y, uint32_t z) const {
        return z * (width * height) + y * width + x;
    }

    inline float sample(uint32_t x, uint32_t y, uint32_t z) const {
        return data[index(x, y, z)];
    }

    inline void set(uint32_t x, uint32_t y, uint32_t z, float value) {
        data[index(x, y, z)] = value;
    }

    size_t sizeBytes() const {
        return data.size() * sizeof(float);
    }
};

/**
 * @brief FastNoise2-based procedural noise generator
 */
class NoiseGenerator {
public:
    /**
     * @brief Construct noise generator with configuration
     */
    explicit NoiseGenerator(const NoiseConfig& config = NoiseConfig{});

    /**
     * @brief Reconfigure the noise generator
     */
    void configure(const NoiseConfig& config);

    /**
     * @brief Generate 3D noise volume
     *
     * @param width  X resolution (power of 2 recommended: 64, 128, 256)
     * @param height Y resolution (typically == width)
     * @param depth  Z resolution (typically == width)
     * @param xOffset Spatial offset in X (for tiling/scrolling)
     * @param yOffset Spatial offset in Y
     * @param zOffset Spatial offset in Z
     *
     * @return Noise volume with data in [outputMin, outputMax]
     */
    NoiseVolume generate3D(
        uint32_t width,
        uint32_t height,
        uint32_t depth,
        float xOffset = 0.0f,
        float yOffset = 0.0f,
        float zOffset = 0.0f
    );

    /**
     * @brief Generate 2D noise slice (for testing/preview)
     *
     * @param width  X resolution
     * @param height Y resolution
     * @param zSlice Z coordinate for slice
     *
     * @return 2D noise data (row-major: y * width + x)
     */
    std::vector<float> generate2D(
        uint32_t width,
        uint32_t height,
        float zSlice = 0.0f
    );

    /**
     * @brief Get current configuration
     */
    const NoiseConfig& config() const { return config_; }

    /**
     * @brief Get FastNoise2 version string
     */
    static std::string version();

private:
    /**
     * @brief Build FastNoise2 node tree from config
     */
    FastNoise::SmartNode<> buildNoiseTree(const NoiseConfig& config);

    /**
     * @brief Apply output remapping: [-1,1] → [outputMin, outputMax]
     */
    void remapOutput(NoiseVolume& volume) const;

    NoiseConfig config_;
    FastNoise::SmartNode<> generator_;
};

// ============================================================================
// Preset Configurations
// ============================================================================

/**
 * @brief Turbulent accretion disk noise (high-frequency detail)
 *
 * Use case: Fine-scale turbulence in disk, alpha-viscosity sub-grid detail
 * Frequency: High (2.5)
 * Octaves: 5 (multi-scale detail)
 * Type: FractalFBm (classic turbulence)
 */
inline NoiseConfig turbulencePreset() {
    NoiseConfig cfg;
    cfg.type = NoiseConfig::Type::FractalFBm;
    cfg.frequency = 2.5f;
    cfg.octaves = 5;
    cfg.lacunarity = 2.0f;
    cfg.gain = 0.5f;
    cfg.outputMin = 0.0f;
    cfg.outputMax = 1.0f;
    cfg.seed = 42;
    return cfg;
}

/**
 * @brief Large-scale density variations (spiral arm structure)
 *
 * Use case: Modulate disk density on large scales (spiral shocks, warps)
 * Frequency: Low (0.5)
 * Octaves: 3 (smooth gradients)
 * Type: Perlin (smooth transitions)
 */
inline NoiseConfig densityPreset() {
    NoiseConfig cfg;
    cfg.type = NoiseConfig::Type::Perlin;
    cfg.frequency = 0.5f;
    cfg.octaves = 3;
    cfg.lacunarity = 2.0f;
    cfg.gain = 0.6f;
    cfg.outputMin = 0.8f;  // Don't go to zero (preserve base density)
    cfg.outputMax = 1.2f;  // ±20% modulation
    cfg.seed = 1337;
    return cfg;
}

/**
 * @brief Ridged features (shock fronts, accretion streams)
 *
 * Use case: Sharp density gradients at shocks, stream boundaries
 * Frequency: Medium (1.5)
 * Octaves: 4
 * Type: FractalRidged (creates sharp ridges)
 */
inline NoiseConfig ridgedPreset() {
    NoiseConfig cfg;
    cfg.type = NoiseConfig::Type::FractalRidged;
    cfg.frequency = 1.5f;
    cfg.octaves = 4;
    cfg.lacunarity = 2.5f;
    cfg.gain = 0.4f;
    cfg.outputMin = 0.0f;
    cfg.outputMax = 1.0f;
    cfg.seed = 9001;
    return cfg;
}

/**
 * @brief Cellular/voronoi pattern (magnetic field domains, blob structure)
 *
 * Use case: Discrete regions, magnetic reconnection zones, blob ejection
 * Frequency: Medium (1.0)
 * Type: Cellular
 */
inline NoiseConfig cellularPreset() {
    NoiseConfig cfg;
    cfg.type = NoiseConfig::Type::Cellular;
    cfg.frequency = 1.0f;
    cfg.cellularJitter = 0.8f;
    cfg.outputMin = 0.0f;
    cfg.outputMax = 1.0f;
    cfg.seed = 31415;
    return cfg;
}

/**
 * @brief Domain-warped turbulence (advected by flow, non-stationary)
 *
 * Use case: Turbulence advected by Keplerian shear, realistic fluid motion
 * Frequency: High (2.0)
 * Octaves: 4
 * Type: FractalFBm with domain warp
 */
inline NoiseConfig warpedTurbulencePreset() {
    NoiseConfig cfg;
    cfg.type = NoiseConfig::Type::FractalFBm;
    cfg.frequency = 2.0f;
    cfg.octaves = 4;
    cfg.lacunarity = 2.0f;
    cfg.gain = 0.5f;
    cfg.enableDomainWarp = true;
    cfg.warpAmplitude = 0.3f;
    cfg.warpFrequency = 0.5f;
    cfg.outputMin = 0.0f;
    cfg.outputMax = 1.0f;
    cfg.seed = 271828;
    return cfg;
}

} // namespace blackhole

#else // BLACKHOLE_ENABLE_FASTNOISE2

namespace blackhole {

// Stub implementation when FastNoise2 is disabled
struct NoiseConfig {};
struct NoiseVolume {
    std::vector<float> data;
    uint32_t width = 0, height = 0, depth = 0;
};

class NoiseGenerator {
public:
    explicit NoiseGenerator(const NoiseConfig& = NoiseConfig{}) {}
    void configure(const NoiseConfig&) {}
    NoiseVolume generate3D(uint32_t, uint32_t, uint32_t, float = 0, float = 0, float = 0) {
        return NoiseVolume{};
    }
    std::vector<float> generate2D(uint32_t, uint32_t, float = 0) { return {}; }
    const NoiseConfig& config() const { static NoiseConfig cfg; return cfg; }
    static std::string version() { return "FastNoise2 disabled"; }
};

inline NoiseConfig turbulencePreset() { return NoiseConfig{}; }
inline NoiseConfig densityPreset() { return NoiseConfig{}; }
inline NoiseConfig ridgedPreset() { return NoiseConfig{}; }
inline NoiseConfig cellularPreset() { return NoiseConfig{}; }
inline NoiseConfig warpedTurbulencePreset() { return NoiseConfig{}; }

} // namespace blackhole

#endif // BLACKHOLE_ENABLE_FASTNOISE2
