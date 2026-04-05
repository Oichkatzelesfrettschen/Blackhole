/**
 * @file hawking_renderer.cpp
 * @brief Hawking Radiation GPU Renderer Implementation
 *
 * Phase 10.1: Hawking Radiation Thermal Glow
 *
 * Implementation of HawkingRenderer class for loading LUTs from
 * CSV files and configuring GPU shaders.
 *
 * Created: 2026-01-02
 */

#include "hawking_renderer.h"

#include <algorithm>
#include <cstddef>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions-patches.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

namespace physics {

// ============================================================================
// Constructor / Destructor
// ============================================================================

HawkingRenderer::HawkingRenderer() = default;

HawkingRenderer::~HawkingRenderer() {
  cleanup();
}

HawkingRenderer::HawkingRenderer(HawkingRenderer &&other) noexcept
    : tempLUTTexture_(other.tempLUTTexture_), spectrumLUTTexture_(other.spectrumLUTTexture_),
      tempLUTLoaded_(other.tempLUTLoaded_), spectrumLUTLoaded_(other.spectrumLUTLoaded_) {
  other.tempLUTTexture_ = 0;
  other.spectrumLUTTexture_ = 0;
  other.tempLUTLoaded_ = false;
  other.spectrumLUTLoaded_ = false;
}

HawkingRenderer &HawkingRenderer::operator=(HawkingRenderer &&other) noexcept {
  if (this != &other) {
    cleanup();
    tempLUTTexture_ = other.tempLUTTexture_;
    spectrumLUTTexture_ = other.spectrumLUTTexture_;
    tempLUTLoaded_ = other.tempLUTLoaded_;
    spectrumLUTLoaded_ = other.spectrumLUTLoaded_;
    other.tempLUTTexture_ = 0;
    other.spectrumLUTTexture_ = 0;
    other.tempLUTLoaded_ = false;
    other.spectrumLUTLoaded_ = false;
  }
  return *this;
}

void HawkingRenderer::cleanup() {
  if (tempLUTTexture_ != 0) {
    glDeleteTextures(1, &tempLUTTexture_);
    tempLUTTexture_ = 0;
  }
  if (spectrumLUTTexture_ != 0) {
    glDeleteTextures(1, &spectrumLUTTexture_);
    spectrumLUTTexture_ = 0;
  }
  tempLUTLoaded_ = false;
  spectrumLUTLoaded_ = false;
}

// ============================================================================
// CSV Parsing
// ============================================================================

bool HawkingRenderer::parseCSV(const std::filesystem::path &csvPath,
                               std::vector<std::vector<float>> &columns, bool skipHeader) {
  std::ifstream file(csvPath);
  if (!file.is_open()) {
    std::cerr << "Failed to open CSV file: " << csvPath << '\n';
    return false;
  }

  std::string line;
  (void)skipHeader; // Unused parameter - headers detected automatically

  while (std::getline(file, line)) {
    // Skip comment lines and empty lines
    if (line.empty() || line.at(0) == '#' || line.at(0) == '"') {
      continue;
    }

    // Parse numeric values
    std::istringstream iss(line);
    std::string token;
    std::vector<float> row;
    bool isHeaderRow = false;

    while (std::getline(iss, token, ',')) {
      // Skip rows that contain non-numeric headers (letters except 'e' for scientific notation)
      // Allow: digits, '.', '+', '-', 'e', 'E' (for numbers like 1.23e+45)
      if (token.find_first_of("abcdfghijklmnopqrstuvwxyzABCDFGHIJKLMNOPQRSTUVWXYZ_") !=
          std::string::npos) {
        isHeaderRow = true;
        break;
      }

      try {
        // Use double for intermediate parsing to handle large exponents (e.g., 1e42)
        double const valueD = std::stod(token);
        // If the value is finite but too large for float, we can either clamp or store log.
        // For this renderer, we likely want the raw value if it fits, or max float.
        // However, T_H ~ 1/M. If M is 1e42, T is tiny.
        // If the CSV contains mass, 1e42 is possible.
        // If we store it in a float texture, we WILL lose precision or overflow.
        // Assuming the shader expects log values or normalized values if the range is huge.
        // But looking at the shader code, it does log10(mass) itself if using LUT?
        // Actually hawking_luts.glsl does: float log_mass = log(mass) / log(10.0);
        // This implies 'mass' must be a value that fits in float?
        // Float max is ~3.4e38. 1e42 overflows.
        // We should store log10 values in the texture if the range is > 1e38.
        // BUT, the texture loading logic (createTexture1D) just uploads raw floats.
        // FIX: Detect if we are loading the Mass column and it's huge?
        // Or just clamp to FLT_MAX?
        // Let's use double and cast, letting it go to infinity if needed, but avoiding the throw.
        auto const value = static_cast<float>(valueD);
        row.push_back(value);
      } catch (const std::exception &e) {
        // Ignore parse errors (likely header text or comments)
        // std::cerr << "Failed to parse value: " << token << " (" << e.what() << ")" << std::endl;
        continue;
      }
    }

    if (isHeaderRow) {
      continue; // Skip this entire row
    }

    // Grow columns vector if needed
    if (columns.empty()) {
      columns.resize(row.size());
    }

    // Add values to respective columns
    for (size_t i = 0; i < row.size() && i < columns.size(); ++i) {
      columns.at(i).push_back(row.at(i));
    }
  }

  return !columns.empty();
}

// ============================================================================
// Texture Creation
// ============================================================================

GLuint HawkingRenderer::createTexture1D(const std::vector<float> &data, int channels) {
  if (data.empty() || channels < 1 || channels > 4) {
    std::cerr << "Invalid texture data: size=" << data.size() << ", channels=" << channels << '\n';
    return 0;
  }

  // Calculate texture width
  size_t const width = data.size() / static_cast<size_t>(channels);
  if (width == 0) {
    std::cerr << "Texture width is zero" << '\n';
    return 0;
  }

  // Select format based on channel count
  GLenum format;
  GLenum internalFormat;
  switch (channels) {
  case 1:
    format = GL_RED;
    internalFormat = GL_R32F;
    break;
  case 3:
    format = GL_RGB;
    internalFormat = GL_RGB32F;
    break;
  case 4:
    format = GL_RGBA;
    internalFormat = GL_RGBA32F;
    break;
  default:
    std::cerr << "Unsupported channel count: " << channels << '\n';
    return 0;
  }

  // Create OpenGL texture
  GLuint texture;
  glGenTextures(1, &texture);
  glBindTexture(GL_TEXTURE_2D, texture); // Store as 2D texture with height=1

  // Upload data
  glTexImage2D(GL_TEXTURE_2D, 0, internalFormat, static_cast<GLsizei>(width), 1, 0, format,
               GL_FLOAT, data.data());

  // Set filtering and wrapping
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);

  glBindTexture(GL_TEXTURE_2D, 0);

  std::cout << "Created 1D texture: width=" << width << ", channels=" << channels
            << ", texture=" << texture << '\n';

  return texture;
}

// ============================================================================
// LUT Loading
// ============================================================================

bool HawkingRenderer::loadTemperatureLUT(const std::filesystem::path &csvPath) {
  std::cout << "Loading temperature LUT: " << csvPath << '\n';

  std::vector<std::vector<float>> columns;
  if (!parseCSV(csvPath, columns, true)) {
    std::cerr << "Failed to parse temperature CSV" << '\n';
    return false;
  }

  // Expected columns: Mass_g, Temperature_K, Radius_cm
  if (columns.size() < 2) {
    std::cerr << "Temperature CSV has insufficient columns: " << columns.size() << '\n';
    return false;
  }

  // Extract temperature column (column 1)
  const std::vector<float> &temperatures = columns.at(1);

  if (temperatures.empty()) {
    std::cerr << "Temperature column is empty" << '\n';
    return false;
  }

  // Create 1D texture (single channel: temperature)
  tempLUTTexture_ = createTexture1D(temperatures, 1);
  if (tempLUTTexture_ == 0) {
    std::cerr << "Failed to create temperature LUT texture" << '\n';
    return false;
  }

  tempLUTLoaded_ = true;
  std::cout << "Temperature LUT loaded: " << temperatures.size() << " samples" << '\n';
  return true;
}

bool HawkingRenderer::loadSpectrumLUT(const std::filesystem::path &csvPath) {
  std::cout << "Loading spectrum LUT: " << csvPath << '\n';

  std::vector<std::vector<float>> columns;
  if (!parseCSV(csvPath, columns, true)) {
    std::cerr << "Failed to parse spectrum CSV" << '\n';
    return false;
  }

  // Expected columns: Temperature_K, Red, Green, Blue
  if (columns.size() < 4) {
    std::cerr << "Spectrum CSV has insufficient columns: " << columns.size() << '\n';
    return false;
  }

  // Extract RGB columns (columns 1, 2, 3)
  const std::vector<float> &red = columns.at(1);
  const std::vector<float> &green = columns.at(2);
  const std::vector<float> &blue = columns.at(3);

  if (red.size() != green.size() || red.size() != blue.size()) {
    std::cerr << "RGB columns have mismatched sizes" << '\n';
    return false;
  }

  // Interleave RGB data
  std::vector<float> rgbData;
  rgbData.reserve(red.size() * 3);
  for (size_t i = 0; i < red.size(); ++i) {
    rgbData.push_back(red.at(i));
    rgbData.push_back(green.at(i));
    rgbData.push_back(blue.at(i));
  }

  // Create 1D texture (3 channels: RGB)
  spectrumLUTTexture_ = createTexture1D(rgbData, 3);
  if (spectrumLUTTexture_ == 0) {
    std::cerr << "Failed to create spectrum LUT texture" << '\n';
    return false;
  }

  spectrumLUTLoaded_ = true;
  std::cout << "Spectrum LUT loaded: " << red.size() << " samples" << '\n';
  return true;
}

bool HawkingRenderer::loadLUTs(const std::filesystem::path &lutDirectory) {
  std::cout << "Loading Hawking LUTs from: " << lutDirectory << '\n';

  auto tempPath = lutDirectory / "hawking_temp_lut.csv";
  auto specPath = lutDirectory / "hawking_spectrum_lut.csv";

  bool const tempOk = loadTemperatureLUT(tempPath);
  bool const specOk = loadSpectrumLUT(specPath);

  if (tempOk && specOk) {
    std::cout << "All Hawking LUTs loaded successfully" << '\n';
    return true;
  }
  std::cerr << "Failed to load some Hawking LUTs: temp=" << tempOk << ", spectrum=" << specOk
            << '\n';
  return false;
}

// ============================================================================
// Shader Uniform Setup
// ============================================================================

void HawkingRenderer::setShaderUniforms(GLuint shaderProgram, double blackHoleMass,
                                        const HawkingGlowParams &params) const {
  if (!isReady()) {
    std::cerr << "Hawking LUTs not loaded, cannot set uniforms" << '\n';
    return;
  }

  // Set scalar uniforms
  glUniform1f(glGetUniformLocation(shaderProgram, "hawkingGlowEnabled"),
              params.enabled ? 1.0f : 0.0f);
  glUniform1f(glGetUniformLocation(shaderProgram, "hawkingTempScale"), params.tempScale);
  glUniform1f(glGetUniformLocation(shaderProgram, "hawkingGlowIntensity"), params.intensity);
  glUniform1f(glGetUniformLocation(shaderProgram, "useHawkingLUTs"), params.useLUTs ? 1.0f : 0.0f);
  glUniform1f(glGetUniformLocation(shaderProgram, "blackHoleMass"),
              static_cast<float>(blackHoleMass));

  // Bind LUT textures to texture units
  // Temperature LUT -> texture unit 10
  glActiveTexture(GL_TEXTURE0 + 10);
  glBindTexture(GL_TEXTURE_2D, tempLUTTexture_);
  glUniform1i(glGetUniformLocation(shaderProgram, "hawkingTempLUT"), 10);

  // Spectrum LUT -> texture unit 11
  glActiveTexture(GL_TEXTURE0 + 11);
  glBindTexture(GL_TEXTURE_2D, spectrumLUTTexture_);
  glUniform1i(glGetUniformLocation(shaderProgram, "hawkingSpectrumLUT"), 11);

  // Reset to texture unit 0
  glActiveTexture(GL_TEXTURE0);
}

// ============================================================================
// Preset Management
// ============================================================================

HawkingGlowParams HawkingRenderer::applyPreset(HawkingPreset preset) {
  HawkingGlowParams params;
  params.enabled = true;
  params.useLUTs = true;

  switch (preset) {
  case HawkingPreset::Physical:
    params.tempScale = 1.0f;
    params.intensity = 1.0f;
    break;

  case HawkingPreset::Primordial:
    params.tempScale = 1e6f;
    params.intensity = 2.0f;
    break;

  case HawkingPreset::Extreme:
    params.tempScale = 1e9f;
    params.intensity = 5.0f;
    break;
  }

  params.preset = preset;
  return params;
}

float HawkingRenderer::getRecommendedTempScale(double mass) {
  // For masses below primordial (~5e14 g), physical scale is visible
  if (mass < 1e15) {
    return 1.0f;
  }

  // For solar mass and above, scale based on inverse temperature
  // T_H ∝ 1/M, so scaling needs to be M/M_primordial
  constexpr double mPrimordial = 5e14; // Primordial BH mass [g]
  auto scale = static_cast<float>(mass / mPrimordial);

  // Clamp to reasonable range [1, 1e9]
  scale = std::max(scale, 1.0f);
  scale = std::min(scale, 1e9f);

  return scale;
}

} // namespace physics
