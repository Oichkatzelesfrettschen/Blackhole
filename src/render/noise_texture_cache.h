/**
 * @file noise_texture_cache.h
 * @brief GPU texture cache for 3D procedural noise LUTs
 *
 * Phase 3.2.2: Procedural Enhancements - GPU Upload
 *
 * Manages GL_TEXTURE_3D resources for accretion disk turbulence sampling.
 * Generates noise volumes using FastNoise2 and uploads to GPU as 3D textures
 * with trilinear filtering for smooth shader sampling.
 *
 * Usage:
 *   NoiseTextureCache cache;
 *   cache.initialize();  // Generate and upload all preset LUTs
 *
 *   // In shader setup:
 *   glActiveTexture(GL_TEXTURE0 + cache.getTurbulenceUnit());
 *   glBindTexture(GL_TEXTURE_3D, cache.getTurbulenceTexture());
 *   glUniform1i(turbulence_sampler_location, cache.getTurbulenceUnit());
 */

#pragma once

#include "gl_loader.h"
#include "noise_generator.h"

#include <string>
#include <memory>

namespace blackhole {

/**
 * @brief Cache of 3D noise textures for GPU sampling
 *
 * Preloads common noise patterns as GL_TEXTURE_3D for efficient
 * shader access. Manages texture lifetime and provides uniform
 * binding helpers.
 */
class NoiseTextureCache {
public:
    NoiseTextureCache() = default;
    ~NoiseTextureCache();

    // Disable copy, enable move
    NoiseTextureCache(const NoiseTextureCache&) = delete;
    NoiseTextureCache& operator=(const NoiseTextureCache&) = delete;
    NoiseTextureCache(NoiseTextureCache && /*other*/) noexcept;
    NoiseTextureCache &operator=(NoiseTextureCache && /*other*/) noexcept;

    /**
     * @brief Initialize cache and generate all preset noise LUTs
     *
     * Generates and uploads:
     * - Turbulence (FractalFBm, 128³, high frequency)
     * - Density (Perlin, 128³, low frequency modulation)
     * - Ridged (FractalRidged, 64³, sharp features)
     * - Cellular (Voronoi, 64³, discrete cells)
     *
     * @return true on success, false if OpenGL context invalid
     */
    bool initialize();

    /**
     * @brief Free all GPU resources
     */
    void cleanup();

    /**
     * @brief Check if cache is initialized
     */
    [[nodiscard]] bool isInitialized() const { return initialized_; }

    // ========================================================================
    // Texture Access
    // ========================================================================

    /**
     * @brief Get turbulence texture (FractalFBm, 128³)
     * Primary disk turbulence detail
     */
    [[nodiscard]] GLuint getTurbulenceTexture() const { return texture_turbulence_; }

    /**
     * @brief Get density texture (Perlin, 128³)
     * Large-scale density modulation
     */
    [[nodiscard]] GLuint getDensityTexture() const { return texture_density_; }

    /**
     * @brief Get ridged texture (FractalRidged, 64³)
     * Sharp shock fronts and features
     */
    [[nodiscard]] GLuint getRidgedTexture() const { return texture_ridged_; }

    /**
     * @brief Get cellular texture (Voronoi, 64³)
     * Discrete cell structure
     */
    [[nodiscard]] GLuint getCellularTexture() const { return texture_cellular_; }

    // ========================================================================
    // Texture Unit Binding Helpers
    // ========================================================================

    /**
     * @brief Bind all noise textures to consecutive texture units
     *
     * Binds:
     * - turbulence -> baseUnit + 0
     * - density    -> baseUnit + 1
     * - ridged     -> baseUnit + 2
     * - cellular   -> baseUnit + 3
     *
     * @param baseUnit Starting texture unit (e.g., 10)
     */
    void bindAll(GLint baseUnit) const;

    /**
     * @brief Get recommended texture unit for turbulence
     * Default: 10 (leaves 0-9 for albedo, normal, etc.)
     */
    static constexpr GLint turbulenceUnit() { return 10; }

    /**
     * @brief Get recommended texture unit for density
     */
    static constexpr GLint densityUnit() { return 11; }

    /**
     * @brief Get recommended texture unit for ridged
     */
    static constexpr GLint ridgedUnit() { return 12; }

    /**
     * @brief Get recommended texture unit for cellular
     */
    static constexpr GLint cellularUnit() { return 13; }

    // ========================================================================
    // Diagnostics
    // ========================================================================

    /**
     * @brief Get total GPU memory usage (bytes)
     */
    [[nodiscard]] size_t getMemoryUsageBytes() const;

    /**
     * @brief Print cache statistics to stdout
     */
    void printStatistics() const;

private:
    /**
     * @brief Upload single noise volume to GL_TEXTURE_3D
     *
     * Creates texture with:
     * - Internal format: GL_R32F (single-channel float)
     * - Filtering: GL_LINEAR (trilinear)
     * - Wrap: GL_REPEAT (tileable)
     *
     * @param volume Noise data to upload
     * @return OpenGL texture name, or 0 on failure
     */
  static GLuint uploadNoiseVolume(const NoiseVolume &volume);

  bool initialized_ = false;

  // Texture handles
  GLuint texture_turbulence_ = 0;
  GLuint texture_density_ = 0;
  GLuint texture_ridged_ = 0;
  GLuint texture_cellular_ = 0;

  // Noise generators (kept alive for potential runtime regeneration)
  std::unique_ptr<NoiseGenerator> gen_turbulence_;
  std::unique_ptr<NoiseGenerator> gen_density_;
  std::unique_ptr<NoiseGenerator> gen_ridged_;
  std::unique_ptr<NoiseGenerator> gen_cellular_;
};

} // namespace blackhole
