/**
 * @file noise_texture_cache.cpp
 * @brief GPU texture cache for 3D procedural noise LUTs implementation
 *
 * Phase 3.2.2: Procedural Enhancements - GPU Upload
 */

#include "noise_texture_cache.h"

#include <iostream>
#include <iomanip>

namespace blackhole {

NoiseTextureCache::~NoiseTextureCache() {
    cleanup();
}

NoiseTextureCache::NoiseTextureCache(NoiseTextureCache&& other) noexcept
    : initialized_(other.initialized_)
    , texture_turbulence_(other.texture_turbulence_)
    , texture_density_(other.texture_density_)
    , texture_ridged_(other.texture_ridged_)
    , texture_cellular_(other.texture_cellular_)
    , gen_turbulence_(std::move(other.gen_turbulence_))
    , gen_density_(std::move(other.gen_density_))
    , gen_ridged_(std::move(other.gen_ridged_))
    , gen_cellular_(std::move(other.gen_cellular_))
{
    other.initialized_ = false;
    other.texture_turbulence_ = 0;
    other.texture_density_ = 0;
    other.texture_ridged_ = 0;
    other.texture_cellular_ = 0;
}

NoiseTextureCache& NoiseTextureCache::operator=(NoiseTextureCache&& other) noexcept {
    if (this != &other) {
        cleanup();

        initialized_ = other.initialized_;
        texture_turbulence_ = other.texture_turbulence_;
        texture_density_ = other.texture_density_;
        texture_ridged_ = other.texture_ridged_;
        texture_cellular_ = other.texture_cellular_;
        gen_turbulence_ = std::move(other.gen_turbulence_);
        gen_density_ = std::move(other.gen_density_);
        gen_ridged_ = std::move(other.gen_ridged_);
        gen_cellular_ = std::move(other.gen_cellular_);

        other.initialized_ = false;
        other.texture_turbulence_ = 0;
        other.texture_density_ = 0;
        other.texture_ridged_ = 0;
        other.texture_cellular_ = 0;
    }
    return *this;
}

bool NoiseTextureCache::initialize() {
    if (initialized_) {
        std::cerr << "NoiseTextureCache: Already initialized" << std::endl;
        return true;
    }

#ifdef BLACKHOLE_ENABLE_FASTNOISE2
    std::cout << "NoiseTextureCache: Initializing 3D noise LUTs..." << std::endl;

    // ========================================================================
    // 1. Turbulence (FractalFBm, 128³, high frequency)
    // ========================================================================
    {
        std::cout << "  Generating turbulence (FractalFBm, 128³)..." << std::flush;
        gen_turbulence_ = std::make_unique<NoiseGenerator>(turbulencePreset());
        auto volume = gen_turbulence_->generate3D(128, 128, 128);

        texture_turbulence_ = uploadNoiseVolume(volume);
        if (texture_turbulence_ == 0) {
            std::cerr << "\n  ERROR: Failed to upload turbulence texture" << std::endl;
            return false;
        }
        std::cout << " OK (" << (volume.sizeBytes() / 1024 / 1024) << " MB)" << std::endl;
    }

    // ========================================================================
    // 2. Density (Perlin, 128³, low frequency modulation)
    // ========================================================================
    {
        std::cout << "  Generating density (Perlin, 128³)..." << std::flush;
        gen_density_ = std::make_unique<NoiseGenerator>(densityPreset());
        auto volume = gen_density_->generate3D(128, 128, 128);

        texture_density_ = uploadNoiseVolume(volume);
        if (texture_density_ == 0) {
            std::cerr << "\n  ERROR: Failed to upload density texture" << std::endl;
            cleanup();
            return false;
        }
        std::cout << " OK (" << (volume.sizeBytes() / 1024 / 1024) << " MB)" << std::endl;
    }

    // ========================================================================
    // 3. Ridged (FractalRidged, 64³, sharp features)
    // ========================================================================
    {
        std::cout << "  Generating ridged (FractalRidged, 64³)..." << std::flush;
        gen_ridged_ = std::make_unique<NoiseGenerator>(ridgedPreset());
        auto volume = gen_ridged_->generate3D(64, 64, 64);

        texture_ridged_ = uploadNoiseVolume(volume);
        if (texture_ridged_ == 0) {
            std::cerr << "\n  ERROR: Failed to upload ridged texture" << std::endl;
            cleanup();
            return false;
        }
        std::cout << " OK (" << (volume.sizeBytes() / 1024) << " KB)" << std::endl;
    }

    // ========================================================================
    // 4. Cellular (Voronoi, 64³, discrete cells)
    // ========================================================================
    {
        std::cout << "  Generating cellular (Voronoi, 64³)..." << std::flush;
        gen_cellular_ = std::make_unique<NoiseGenerator>(cellularPreset());
        auto volume = gen_cellular_->generate3D(64, 64, 64);

        texture_cellular_ = uploadNoiseVolume(volume);
        if (texture_cellular_ == 0) {
            std::cerr << "\n  ERROR: Failed to upload cellular texture" << std::endl;
            cleanup();
            return false;
        }
        std::cout << " OK (" << (volume.sizeBytes() / 1024) << " KB)" << std::endl;
    }

    initialized_ = true;
    std::cout << "NoiseTextureCache: Initialization complete" << std::endl;
    printStatistics();

    return true;

#else
    std::cerr << "NoiseTextureCache: FastNoise2 disabled, no textures generated" << std::endl;
    return false;
#endif
}

void NoiseTextureCache::cleanup() {
    if (!initialized_) {
        return;
    }

    std::cout << "NoiseTextureCache: Cleaning up GPU resources..." << std::endl;

    if (texture_turbulence_ != 0) {
        glDeleteTextures(1, &texture_turbulence_);
        texture_turbulence_ = 0;
    }

    if (texture_density_ != 0) {
        glDeleteTextures(1, &texture_density_);
        texture_density_ = 0;
    }

    if (texture_ridged_ != 0) {
        glDeleteTextures(1, &texture_ridged_);
        texture_ridged_ = 0;
    }

    if (texture_cellular_ != 0) {
        glDeleteTextures(1, &texture_cellular_);
        texture_cellular_ = 0;
    }

    gen_turbulence_.reset();
    gen_density_.reset();
    gen_ridged_.reset();
    gen_cellular_.reset();

    initialized_ = false;
}

GLuint NoiseTextureCache::uploadNoiseVolume(const NoiseVolume& volume) {
    if (volume.data.empty()) {
        std::cerr << "NoiseTextureCache: Empty volume, cannot upload" << std::endl;
        return 0;
    }

    GLuint texture = 0;
    glGenTextures(1, &texture);
    if (texture == 0) {
        std::cerr << "NoiseTextureCache: glGenTextures failed" << std::endl;
        return 0;
    }

    glBindTexture(GL_TEXTURE_3D, texture);

    // Upload data
    // Internal format: GL_R32F (single-channel 32-bit float)
    // Format: GL_RED (single channel)
    // Type: GL_FLOAT
    glTexImage3D(
        GL_TEXTURE_3D,
        0,  // mipmap level
        GL_R32F,  // internal format
        static_cast<GLsizei>(volume.width),
        static_cast<GLsizei>(volume.height),
        static_cast<GLsizei>(volume.depth),
        0,  // border (must be 0)
        GL_RED,  // format
        GL_FLOAT,  // type
        volume.data.data()
    );

    // Check for errors
    GLenum error = glGetError();
    if (error != GL_NO_ERROR) {
        std::cerr << "NoiseTextureCache: glTexImage3D failed with error 0x"
                  << std::hex << static_cast<unsigned int>(error) << std::dec << std::endl;
        glDeleteTextures(1, &texture);
        return 0;
    }

    // Set filtering: trilinear (linear in X, Y, Z)
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);

    // Set wrapping: repeat (tileable noise)
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_S, GL_REPEAT);
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_T, GL_REPEAT);
    glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_R, GL_REPEAT);

    glBindTexture(GL_TEXTURE_3D, 0);

    return texture;
}

void NoiseTextureCache::bindAll(GLint base_unit) {
    if (!initialized_) {
        std::cerr << "NoiseTextureCache: Cannot bind, not initialized" << std::endl;
        return;
    }

    // Turbulence
    glActiveTexture(GL_TEXTURE0 + static_cast<unsigned int>(base_unit));
    glBindTexture(GL_TEXTURE_3D, texture_turbulence_);

    // Density
    glActiveTexture(GL_TEXTURE0 + static_cast<unsigned int>(base_unit + 1));
    glBindTexture(GL_TEXTURE_3D, texture_density_);

    // Ridged
    glActiveTexture(GL_TEXTURE0 + static_cast<unsigned int>(base_unit + 2));
    glBindTexture(GL_TEXTURE_3D, texture_ridged_);

    // Cellular
    glActiveTexture(GL_TEXTURE0 + static_cast<unsigned int>(base_unit + 3));
    glBindTexture(GL_TEXTURE_3D, texture_cellular_);
}

size_t NoiseTextureCache::getMemoryUsageBytes() const {
    if (!initialized_) {
        return 0;
    }

    size_t total = 0;

    // Turbulence: 128³ × 4 bytes/float
    total += 128 * 128 * 128 * sizeof(float);

    // Density: 128³ × 4 bytes/float
    total += 128 * 128 * 128 * sizeof(float);

    // Ridged: 64³ × 4 bytes/float
    total += 64 * 64 * 64 * sizeof(float);

    // Cellular: 64³ × 4 bytes/float
    total += 64 * 64 * 64 * sizeof(float);

    return total;
}

void NoiseTextureCache::printStatistics() const {
    std::cout << "NoiseTextureCache Statistics:" << std::endl;
    std::cout << "  Turbulence: " << (texture_turbulence_ != 0 ? "OK" : "FAIL")
              << " (128³, " << (128*128*128*4 / 1024 / 1024) << " MB)" << std::endl;
    std::cout << "  Density:    " << (texture_density_ != 0 ? "OK" : "FAIL")
              << " (128³, " << (128*128*128*4 / 1024 / 1024) << " MB)" << std::endl;
    std::cout << "  Ridged:     " << (texture_ridged_ != 0 ? "OK" : "FAIL")
              << " (64³, " << (64*64*64*4 / 1024) << " KB)" << std::endl;
    std::cout << "  Cellular:   " << (texture_cellular_ != 0 ? "OK" : "FAIL")
              << " (64³, " << (64*64*64*4 / 1024) << " KB)" << std::endl;
    std::cout << "  Total GPU memory: " << (getMemoryUsageBytes() / 1024 / 1024)
              << " MB" << std::endl;
    std::cout << "  Recommended texture units: "
              << turbulenceUnit() << "-" << cellularUnit() << std::endl;
}

} // namespace blackhole
