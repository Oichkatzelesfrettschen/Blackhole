/**
 * @file lut_manager.cpp
 * @brief Radiative-transfer LUT lifecycle: asset loading, generation, and the
 *        per-parameter texture reconciliation the frame loop drives.
 */

#include "render/lut_manager.h"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iostream>

#include "physics/lut.h"
#include "platform/resource_paths.h"
#include "render.h"
#include "render/render_state.h"

namespace blackhole {
namespace {

/** @brief Parses a numeric value for a quoted JSON key by string scanning; the
 *         LUT meta files are flat enough that a full JSON parse is unwarranted. */
bool parseJsonNumber(const std::string &text, const std::string &key, double &out) {
  std::string const needle = "\"" + key + "\"";
  std::size_t pos = text.find(needle);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find(':', pos);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find_first_of("+-0123456789.", pos);
  if (pos == std::string::npos) {
    return false;
  }
  const char *start = text.c_str() + pos;
  char *end = nullptr;
  out = std::strtod(start, &end);
  return end != start;
}

/** @brief Reads the second CSV column of every non-header row into values;
 *         returns false when nothing parsed. */
bool loadLutCsv(const std::string &path, std::vector<float> &values) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::string line;
  bool first = true;
  while (std::getline(file, line)) {
    if (first) {
      first = false;
      continue;
    }
    if (line.empty()) {
      continue;
    }
    std::size_t const comma = line.find(',');
    if (comma == std::string::npos) {
      continue;
    }
    const char *start = line.c_str() + comma + 1;
    char *end = nullptr;
    double value = std::strtod(start, &end);
    if (end == start) {
      continue;
    }
    values.push_back(static_cast<float>(value));
  }
  return !values.empty();
}

/** @brief Loads the baked emissivity/redshift LUTs and their radius/spin meta;
 *         the emissivity and redshift tables share one radius domain. */
bool loadLutAssets(physics::Lut1D &emissivity, physics::Lut1D &redshift, float &spinOut) {
  std::vector<float> emissivityValues;
  std::vector<float> redshiftValues;
  if (!loadLutCsv(platform::resourcePath("assets/luts/emissivity_lut.csv"), emissivityValues)) {
    return false;
  }
  if (!loadLutCsv(platform::resourcePath("assets/luts/redshift_lut.csv"), redshiftValues)) {
    return false;
  }
  std::string metaText;
  if (!platform::readTextFile(platform::resourcePath("assets/luts/lut_meta.json"), metaText)) {
    return false;
  }
  double rInOverRs = 0.0;
  double rOutOverRs = 0.0;
  double spin = 0.0;
  if (!parseJsonNumber(metaText, "r_in_over_rs", rInOverRs)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_out_over_rs", rOutOverRs)) {
    return false;
  }
  parseJsonNumber(metaText, "spin", spin);

  emissivity.values = std::move(emissivityValues);
  emissivity.rMin = static_cast<float>(rInOverRs);
  emissivity.rMax = static_cast<float>(rOutOverRs);
  redshift.values = std::move(redshiftValues);
  redshift.rMin = static_cast<float>(rInOverRs);
  redshift.rMax = static_cast<float>(rOutOverRs);
  spinOut = static_cast<float>(spin);
  return true;
}

} // namespace

bool loadSpectralLutAssets(std::vector<float> &values, float &wavelengthMin, float &wavelengthMax) {
  values.clear();
  if (!loadLutCsv(platform::resourcePath("assets/luts/rt_spectrum_lut.csv"), values)) {
    return false;
  }
  std::string metaText;
  if (!platform::readTextFile(platform::resourcePath("assets/luts/rt_spectrum_meta.json"), metaText)) {
    return false;
  }
  double waveMin = 0.0;
  double waveMax = 0.0;
  if (!parseJsonNumber(metaText, "wavelength_min_angstrom", waveMin)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "wavelength_max_angstrom", waveMax)) {
    return false;
  }
  wavelengthMin = static_cast<float>(waveMin);
  wavelengthMax = static_cast<float>(waveMax);
  return true;
}

bool loadGrbModulationLutAssets(std::vector<float> &values, float &timeMin, float &timeMax) {
  values.clear();
  if (!loadLutCsv(platform::resourcePath("assets/luts/grb_modulation_lut.csv"), values)) {
    return false;
  }
  std::string metaText;
  if (!platform::readTextFile(platform::resourcePath("assets/luts/grb_modulation_meta.json"), metaText)) {
    return false;
  }
  double tMin = 0.0;
  double tMax = 0.0;
  if (!parseJsonNumber(metaText, "t_min", tMin)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "t_max", tMax)) {
    return false;
  }
  timeMin = static_cast<float>(tMin);
  timeMax = static_cast<float>(tMax);
  return true;
}

void updateLuts(RenderState &rs, float spin, float densityV) {
  spin = std::clamp(spin, -0.99f, 0.99f);
  if (!rs.luts.lutAssetsTried) {
    rs.luts.lutAssetsTried = true;
    rs.luts.lutAssetsLoaded = loadLutAssets(rs.luts.lutAssetEmissivity, rs.luts.lutAssetRedshift, rs.luts.lutAssetSpin);
  }

  bool const useAssetLuts = rs.luts.lutAssetsLoaded && std::abs(spin - rs.luts.lutAssetSpin) <= 1e-3f &&
                            !rs.luts.lutAssetEmissivity.values.empty() &&
                            !rs.luts.lutAssetRedshift.values.empty();
  if (useAssetLuts) {
    if (!rs.luts.lutInitialized || !rs.luts.lutFromAssets) {
      if (rs.luts.texEmissivityLUT != 0) {
        glDeleteTextures(1, &rs.luts.texEmissivityLUT);
        rs.luts.texEmissivityLUT = 0;
      }
      if (rs.luts.texRedshiftLUT != 0) {
        glDeleteTextures(1, &rs.luts.texRedshiftLUT);
        rs.luts.texRedshiftLUT = 0;
      }
      if (rs.luts.texPhotonGlowLUT != 0) {
        glDeleteTextures(1, &rs.luts.texPhotonGlowLUT);
        rs.luts.texPhotonGlowLUT = 0;
      }
      if (rs.luts.texDiskDensityLUT != 0) {
        glDeleteTextures(1, &rs.luts.texDiskDensityLUT);
        rs.luts.texDiskDensityLUT = 0;
      }

      int const lutSize = static_cast<int>(rs.luts.lutAssetEmissivity.values.size());
      rs.luts.texEmissivityLUT = createFloatTexture2D(lutSize, 1, rs.luts.lutAssetEmissivity.values);
      rs.luts.texRedshiftLUT = createFloatTexture2D(lutSize, 1, rs.luts.lutAssetRedshift.values);

#if BLACKHOLE_HAS_CUDA
      /* Share asset LUTs with CUDA backend (slot 0=emissivity, 1=redshift) */
      rs.dispatch.cudaManager.registerLut(0, rs.luts.texEmissivityLUT, static_cast<unsigned int>(GL_TEXTURE_2D));
      rs.dispatch.cudaManager.registerLut(1, rs.luts.texRedshiftLUT,   static_cast<unsigned int>(GL_TEXTURE_2D));
#endif

      rs.luts.lutRadiusMin = rs.luts.lutAssetEmissivity.rMin;
      rs.luts.lutRadiusMax = rs.luts.lutAssetEmissivity.rMax;
      rs.luts.redshiftRadiusMin = rs.luts.lutAssetRedshift.rMin;
      rs.luts.redshiftRadiusMax = rs.luts.lutAssetRedshift.rMax;
      rs.luts.lutSpin = rs.luts.lutAssetSpin;
      rs.luts.lutFromAssets = true;
      rs.luts.lutInitialized = true;
    }
    return;
  }

  if (rs.luts.lutAssetOnly) {
    if (!rs.luts.lutAssetOnlyWarned) {
      std::cout << "LUT asset-only mode active; skipping generated LUT fallback.\n";
      rs.luts.lutAssetOnlyWarned = true;
    }
    if (rs.luts.texEmissivityLUT != 0) {
      glDeleteTextures(1, &rs.luts.texEmissivityLUT);
      rs.luts.texEmissivityLUT = 0;
    }
    if (rs.luts.texRedshiftLUT != 0) {
      glDeleteTextures(1, &rs.luts.texRedshiftLUT);
      rs.luts.texRedshiftLUT = 0;
    }
    if (rs.luts.texPhotonGlowLUT != 0) {
      glDeleteTextures(1, &rs.luts.texPhotonGlowLUT);
      rs.luts.texPhotonGlowLUT = 0;
    }
    rs.luts.lutInitialized = false;
    rs.luts.lutFromAssets = false;
    return;
  }

  // Only regenerate if parameters changed or not initialized
  if (!rs.luts.lutInitialized || std::abs(spin - rs.luts.lutSpin) > 1e-3f ||
      std::abs(densityV - rs.luts.lutAdiskDensityV) > 1e-3f || rs.luts.lutFromAssets) {
    // Cleanup existing textures
    if (rs.luts.texEmissivityLUT != 0) {
      glDeleteTextures(1, &rs.luts.texEmissivityLUT);
      rs.luts.texEmissivityLUT = 0;
    }
    if (rs.luts.texRedshiftLUT != 0) {
      glDeleteTextures(1, &rs.luts.texRedshiftLUT);
      rs.luts.texRedshiftLUT = 0;
    }
    if (rs.luts.texPhotonGlowLUT != 0) {
      glDeleteTextures(1, &rs.luts.texPhotonGlowLUT);
      rs.luts.texPhotonGlowLUT = 0;
    }
    if (rs.luts.texDiskDensityLUT != 0) {
      glDeleteTextures(1, &rs.luts.texDiskDensityLUT);
      rs.luts.texDiskDensityLUT = 0;
    }

    constexpr int kLutSize = 256;
    constexpr double kMassSolar = 4.0e6;
    constexpr double kMdotEdd = 0.1;

    auto emissivityLut = physics::generateEmissivityLut(
        kLutSize, kMassSolar, static_cast<double>(spin), kMdotEdd, true);
    auto redshiftLut =
        physics::generateRedshiftLut(kLutSize, kMassSolar, static_cast<double>(spin));

    rs.luts.texEmissivityLUT = createFloatTexture2D(kLutSize, 1, emissivityLut.values);
    rs.luts.texRedshiftLUT = createFloatTexture2D(kLutSize, 1, redshiftLut.values);

#if BLACKHOLE_HAS_CUDA
    /* Share generated LUTs with CUDA backend (slot 0=emissivity, 1=redshift) */
    rs.dispatch.cudaManager.registerLut(0, rs.luts.texEmissivityLUT, static_cast<unsigned int>(GL_TEXTURE_2D));
    rs.dispatch.cudaManager.registerLut(1, rs.luts.texRedshiftLUT,   static_cast<unsigned int>(GL_TEXTURE_2D));
#endif

    auto photonGlowLut = physics::generatePhotonGlowLut(256);
    rs.luts.texPhotonGlowLUT = createFloatTexture2D(256, 1, photonGlowLut.values);

    // Connect adiskDensityV to LUT generation
    // Use densityV as the exponent or scale factor for the density profile
    double const densityScale = static_cast<double>(std::max(0.1f, densityV));
    auto diskDensityLut = physics::generateDiskDensityLut(256, densityScale);
    rs.luts.texDiskDensityLUT = createFloatTexture2D(256, 1, diskDensityLut.values);

    rs.luts.lutRadiusMin = emissivityLut.rMin;
    rs.luts.lutRadiusMax = emissivityLut.rMax;
    rs.luts.redshiftRadiusMin = redshiftLut.rMin;
    rs.luts.redshiftRadiusMax = redshiftLut.rMax;
    rs.luts.lutSpin = spin;
    rs.luts.lutAdiskDensityV = densityV;
    rs.luts.lutFromAssets = false;
    rs.luts.lutInitialized = true;
    std::cout << "LUTs regenerated. Spin: " << spin << ", DensityV: " << densityV << '\n';
  }
}

} // namespace blackhole
