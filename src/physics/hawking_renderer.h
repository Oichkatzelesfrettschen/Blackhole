/**
 * @file hawking_renderer.h
 * @brief Hawking Radiation GPU Renderer Interface
 *
 * Phase 10.1: Hawking Radiation Thermal Glow
 *
 * Provides C++ interface for loading Hawking radiation LUTs and
 * configuring GPU shader uniforms for thermal glow rendering.
 *
 * Features:
 * - Load temperature and spectrum LUTs from CSV files
 * - Upload LUT data to GPU as 1D textures
 * - Set shader uniforms for Hawking glow parameters
 * - Manage visualization presets (physical/primordial/extreme)
 *
 * Usage:
 *   HawkingRenderer renderer;
 *   renderer.loadLUTs("assets/luts");
 *   renderer.setShaderUniforms(shaderProgram, blackHoleMass);
 *
 * Created: 2026-01-02
 */

#ifndef PHYSICS_HAWKING_RENDERER_H
#define PHYSICS_HAWKING_RENDERER_H

#include <string>
#include <vector>
#include <filesystem>
#include "gl_loader.h"
#include "hawking.h"

namespace physics {

/**
 * @brief Visualization preset for Hawking radiation.
 *
 * Presets adjust temperature scaling and intensity for
 * pedagogical visualization.
 */
enum class HawkingPreset {
    Physical,      // T_scale = 1.0 (invisible for solar mass)
    Primordial,    // T_scale = 1e6 (visible X-ray glow)
    Extreme        // T_scale = 1e9 (pedagogical exaggeration)
};

/**
 * @brief Hawking glow rendering parameters.
 */
struct HawkingGlowParams {
    bool enabled = false;               // Enable Hawking glow rendering
    float tempScale = 1.0f;             // Temperature scaling factor
    float intensity = 1.0f;             // Glow intensity multiplier [0, 5]
    bool useLUTs = true;                // Use LUTs vs direct calculation
    HawkingPreset preset = HawkingPreset::Physical;
};

/**
 * @brief Hawking Radiation GPU Renderer.
 *
 * Manages LUT textures and shader uniform setup for
 * Hawking thermal glow visualization.
 */
class HawkingRenderer {
public:
    HawkingRenderer();
    ~HawkingRenderer();

    // Prevent copying (OpenGL texture handles)
    HawkingRenderer(const HawkingRenderer&) = delete;
    HawkingRenderer& operator=(const HawkingRenderer&) = delete;

    // Allow moving
    HawkingRenderer(HawkingRenderer&& other) noexcept;
    HawkingRenderer& operator=(HawkingRenderer&& other) noexcept;

    /**
     * @brief Load Hawking LUTs from directory.
     *
     * Loads:
     * - hawking_temp_lut.csv: Temperature T_H(M)
     * - hawking_spectrum_lut.csv: Blackbody RGB spectrum
     *
     * @param lutDirectory Path to LUT directory (e.g., "assets/luts")
     * @return true if both LUTs loaded successfully
     */
    bool loadLUTs(const std::filesystem::path& lutDirectory);

    /**
     * @brief Set shader uniforms for current frame.
     *
     * Binds LUT textures and sets all Hawking glow parameters.
     *
     * @param shaderProgram OpenGL shader program
     * @param blackHoleMass Black hole mass [g]
     * @param params Rendering parameters
     */
    void setShaderUniforms(GLuint shaderProgram, double blackHoleMass,
                          const HawkingGlowParams& params) const;

    /**
     * @brief Apply visualization preset.
     *
     * @param preset Preset to apply
     * @return Updated parameters
     */
    static HawkingGlowParams applyPreset(HawkingPreset preset);

    /**
     * @brief Get recommended temperature scale for mass.
     *
     * Returns scale factor to make glow visible:
     * - Solar mass: 1e9 (extreme pedagogical)
     * - Primordial (~5e14 g): 1.0 (physical, visible)
     *
     * @param mass Black hole mass [g]
     * @return Recommended temperature scale
     */
    static float getRecommendedTempScale(double mass);

    /**
     * @brief Check if LUTs are loaded and ready.
     *
     * @return true if both LUTs are loaded
     */
    bool isReady() const {
        return tempLUTLoaded_ && spectrumLUTLoaded_;
    }

    /**
     * @brief Get temperature LUT texture ID.
     *
     * @return OpenGL texture handle (0 if not loaded)
     */
    GLuint getTempLUTTexture() const { return tempLUTTexture_; }

    /**
     * @brief Get spectrum LUT texture ID.
     *
     * @return OpenGL texture handle (0 if not loaded)
     */
    GLuint getSpectrumLUTTexture() const { return spectrumLUTTexture_; }

private:
    // OpenGL texture handles
    GLuint tempLUTTexture_ = 0;       // Temperature T_H(M) LUT
    GLuint spectrumLUTTexture_ = 0;   // Blackbody RGB spectrum LUT

    // Load status
    bool tempLUTLoaded_ = false;
    bool spectrumLUTLoaded_ = false;

    /**
     * @brief Load temperature LUT from CSV.
     *
     * CSV format: Mass_g, Temperature_K, Radius_cm
     *
     * @param csvPath Path to hawking_temp_lut.csv
     * @return true if loaded successfully
     */
    bool loadTemperatureLUT(const std::filesystem::path& csvPath);

    /**
     * @brief Load spectrum LUT from CSV.
     *
     * CSV format: Temperature_K, Red, Green, Blue
     *
     * @param csvPath Path to hawking_spectrum_lut.csv
     * @return true if loaded successfully
     */
    bool loadSpectrumLUT(const std::filesystem::path& csvPath);

    /**
     * @brief Create 1D texture from float data.
     *
     * @param data Float vector
     * @param channels Number of channels (1=R, 3=RGB, 4=RGBA)
     * @return OpenGL texture handle (0 on error)
     */
    static GLuint createTexture1D(const std::vector<float>& data, int channels);

    /**
     * @brief Parse CSV file into float vectors.
     *
     * Skips comment lines (starting with #).
     * Parses numeric values from each row.
     *
     * @param csvPath Path to CSV file
     * @param columns Output columns (each column is a vector)
     * @param skipHeader Skip first non-comment line (header row)
     * @return true if parsed successfully
     */
    static bool parseCSV(const std::filesystem::path& csvPath,
                        std::vector<std::vector<float>>& columns,
                        bool skipHeader = true);

    /**
     * @brief Free OpenGL resources.
     */
    void cleanup();
};

/**
 * @brief Convert preset enum to human-readable string.
 *
 * @param preset Preset enum
 * @return String description
 */
inline const char* presetToString(HawkingPreset preset) {
    switch (preset) {
        case HawkingPreset::Physical:   return "Physical (T_scale=1.0)";
        case HawkingPreset::Primordial: return "Primordial (T_scale=1e6)";
        case HawkingPreset::Extreme:    return "Extreme (T_scale=1e9)";
        default:                        return "Unknown";
    }
}

} // namespace physics

#endif // PHYSICS_HAWKING_RENDERER_H
