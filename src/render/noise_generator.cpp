/**
 * @file noise_generator.cpp
 * @brief FastNoise2-based procedural noise generation implementation
 *
 * Phase 3.2.1: Procedural Enhancements
 */

#include "noise_generator.h"

#ifdef BLACKHOLE_ENABLE_FASTNOISE2

#include <FastNoise/FastNoise.h>
#include <algorithm>
#include <cmath>

namespace blackhole {

NoiseGenerator::NoiseGenerator(const NoiseConfig& config)
    : config_(config)
{
    generator_ = buildNoiseTree(config_);
}

void NoiseGenerator::configure(const NoiseConfig& config) {
    config_ = config;
    generator_ = buildNoiseTree(config_);
}

FastNoise::SmartNode<> NoiseGenerator::buildNoiseTree(const NoiseConfig& config) {
    using namespace FastNoise;

    SmartNode<> baseGenerator;

    // Create base generator based on type
    switch (config.type) {
        case NoiseConfig::Type::OpenSimplex2:
            baseGenerator = New<OpenSimplex2>();
            break;

        case NoiseConfig::Type::OpenSimplex2S:
            baseGenerator = New<OpenSimplex2S>();
            break;

        case NoiseConfig::Type::Perlin:
            baseGenerator = New<Perlin>();
            break;

        case NoiseConfig::Type::ValueCubic:
            baseGenerator = New<Value>();
            break;

        case NoiseConfig::Type::Cellular: {
            auto cellular = New<CellularValue>();

            // Set distance function
            switch (config.cellularDistance) {
                case NoiseConfig::CellularDistanceFunc::Euclidean:
                    cellular->SetDistanceFunction(DistanceFunction::Euclidean);
                    break;
                case NoiseConfig::CellularDistanceFunc::EuclideanSq:
                    cellular->SetDistanceFunction(DistanceFunction::EuclideanSquared);
                    break;
                case NoiseConfig::CellularDistanceFunc::Manhattan:
                    cellular->SetDistanceFunction(DistanceFunction::Manhattan);
                    break;
                case NoiseConfig::CellularDistanceFunc::Hybrid:
                    cellular->SetDistanceFunction(DistanceFunction::Hybrid);
                    break;
            }

            cellular->SetJitterModifier(config.cellularJitter);
            baseGenerator = cellular;
            break;
        }

        case NoiseConfig::Type::FractalFBm: {
            auto simplex = New<OpenSimplex2>();
            auto fractal = New<FractalFBm>();
            fractal->SetSource(simplex);
            fractal->SetOctaveCount(config.octaves);
            fractal->SetLacunarity(config.lacunarity);
            fractal->SetGain(config.gain);
            fractal->SetWeightedStrength(config.weightedStrength);
            baseGenerator = fractal;
            break;
        }

        case NoiseConfig::Type::FractalRidged: {
            auto simplex = New<OpenSimplex2>();
            auto fractal = New<FractalRidged>();
            fractal->SetSource(simplex);
            fractal->SetOctaveCount(config.octaves);
            fractal->SetLacunarity(config.lacunarity);
            fractal->SetGain(config.gain);
            fractal->SetWeightedStrength(config.weightedStrength);
            baseGenerator = fractal;
            break;
        }

        case NoiseConfig::Type::FractalPingPong: {
            auto simplex = New<OpenSimplex2>();
            auto fractal = New<FractalPingPong>();
            fractal->SetSource(simplex);
            fractal->SetOctaveCount(config.octaves);
            fractal->SetLacunarity(config.lacunarity);
            fractal->SetGain(config.gain);
            fractal->SetWeightedStrength(config.weightedStrength);
            fractal->SetPingPongStrength(2.0f);  // Default strength
            baseGenerator = fractal;
            break;
        }

        default:
            // Fallback to OpenSimplex2
            baseGenerator = New<OpenSimplex2>();
            break;
    }

    // Apply domain warping if enabled
    if (config.enableDomainWarp) {
        auto domainWarp = New<DomainWarpGradient>();
        domainWarp->SetSource(baseGenerator);
        domainWarp->SetWarpAmplitude(config.warpAmplitude);
        domainWarp->SetWarpFrequency(config.warpFrequency);

        baseGenerator = domainWarp;
    }

    return baseGenerator;
}

NoiseVolume NoiseGenerator::generate3D(
    uint32_t width,
    uint32_t height,
    uint32_t depth,
    float xOffset,
    float yOffset,
    float zOffset
) {
    NoiseVolume volume;
    volume.width = width;
    volume.height = height;
    volume.depth = depth;
    volume.data.resize(width * height * depth);

    // Set generator frequency and seed
    generator_->GenUniformGrid3D(
        volume.data.data(),
        static_cast<int>(xOffset),
        static_cast<int>(yOffset),
        static_cast<int>(zOffset),
        static_cast<int>(width),
        static_cast<int>(height),
        static_cast<int>(depth),
        config_.frequency,
        config_.seed
    );

    // Remap output range
    remapOutput(volume);

    return volume;
}

std::vector<float> NoiseGenerator::generate2D(
    uint32_t width,
    uint32_t height,
    [[maybe_unused]] float zSlice
) {
    std::vector<float> data(width * height);

    // Generate 2D slice at specified Z
    generator_->GenUniformGrid2D(
        data.data(),
        0,  // xStart
        0,  // yStart
        static_cast<int>(width),
        static_cast<int>(height),
        config_.frequency,
        config_.seed
    );

    // Remap output range
    for (auto& value : data) {
        value = config_.outputMin + (value + 1.0f) * 0.5f * (config_.outputMax - config_.outputMin);
    }

    return data;
}

void NoiseGenerator::remapOutput(NoiseVolume& volume) const {
    // FastNoise2 outputs in [-1, 1], remap to [outputMin, outputMax]
    const float scale = (config_.outputMax - config_.outputMin) * 0.5f;
    const float offset = config_.outputMin + scale;

    for (auto& value : volume.data) {
        value = offset + value * scale;
    }
}

std::string NoiseGenerator::version() {
    return "FastNoise2 v0.10.0-alpha";
}

} // namespace blackhole

#endif // BLACKHOLE_ENABLE_FASTNOISE2
