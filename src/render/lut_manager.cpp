/**
 * @file lut_manager.cpp
 * @brief Radiative-transfer LUT lifecycle: asset loading, generation, and the
 *        per-parameter texture reconciliation the frame loop drives.
 */

#include "render/lut_manager.h"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <vector>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>

#include "physics/lut.h"
#include "physics/synchrotron.h"
#include "platform/resource_paths.h"
#include "render.h"
#include "render/render_state.h"

using namespace gl;
using platform::resourcePath;

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

void loadGrbModulationLut(RenderState &rs) {
  if (!rs.luts.grbModulationTried) {
    rs.luts.grbModulationTried = true;
    rs.luts.grbModulationLoaded =
        loadGrbModulationLutAssets(rs.luts.grbModulationValues, rs.luts.grbTimeMin, rs.luts.grbTimeMax);
    if (rs.luts.grbModulationLoaded) {
      if (rs.luts.texGrbModulationLUT != 0) {
        glDeleteTextures(1, &rs.luts.texGrbModulationLUT);
        rs.luts.texGrbModulationLUT = 0;
      }
      int const lutSize = static_cast<int>(rs.luts.grbModulationValues.size());
      rs.luts.texGrbModulationLUT = createFloatTexture2D(lutSize, 1, rs.luts.grbModulationValues);
      rs.luts.grbTimeManualValue = rs.luts.grbTimeMin;
    }
  }
}

void loadSpectralSynchHawkingLuts(RenderState &rs) {
  if (!rs.luts.spectralLutTried) {
    rs.luts.spectralLutTried = true;
    rs.luts.spectralLutLoaded = loadSpectralLutAssets(rs.luts.spectralLutValues, rs.luts.spectralWavelengthMin,
                                              rs.luts.spectralWavelengthMax);
    if (rs.luts.spectralLutLoaded && !rs.luts.spectralLutValues.empty()) {
      if (rs.luts.texSpectralLUT != 0) {
        glDeleteTextures(1, &rs.luts.texSpectralLUT);
        rs.luts.texSpectralLUT = 0;
      }
      int const lutSize = static_cast<int>(rs.luts.spectralLutValues.size());
      rs.luts.texSpectralLUT = createFloatTexture2D(lutSize, 1, rs.luts.spectralLutValues);
#if BLACKHOLE_HAS_CUDA
      /* Share spectral LUT with CUDA backend (slot 2=spectral) */
      rs.dispatch.cudaManager.registerLut(2, rs.luts.texSpectralLUT, static_cast<unsigned int>(GL_TEXTURE_2D));
#endif
      rs.luts.spectralRadiusMin = rs.luts.lutRadiusMin;
      rs.luts.spectralRadiusMax = rs.luts.lutRadiusMax;
      if (rs.luts.spectralRadiusMax <= rs.luts.spectralRadiusMin) {
        rs.luts.spectralRadiusMin = 0.0f;
        rs.luts.spectralRadiusMax = 1.0f;
      }
    }
  }

  /* Generate synchrotron G(x)=x*K_{2/3}(x) LUT once (task E5).
   * Stored as GL_TEXTURE_2D (width=256, height=1) so the same handle
   * can be registered for CUDA-GL interop via cudaGraphicsGLRegisterImage,
   * which does not support GL_TEXTURE_1D.  The GLSL path samples it
   * via sampler2D with y=0.5; the CUDA path uses tex2D at v=0.5. */
  if (!rs.luts.synchGLutCreated) {
    // The G(x) domain is single-sourced across C++, CUDA, and GLSL via
    // shader/include/synchrotron_lut_domain.h; every consumer reads the
    // same macros, so no cross-file pinning asserts are needed here.
    rs.luts.synchGLutCreated = true;
    constexpr int kSynchGLutSize = SYNCH_G_LUT_DOMAIN_ENTRIES;
    std::vector<float> synchGData(static_cast<std::size_t>(kSynchGLutSize));
    physics::synchrotronGGenerateLut(synchGData.data(), kSynchGLutSize,
                                     static_cast<double>(physics::SYNCH_G_LUT_X_MIN),
                                     static_cast<double>(physics::SYNCH_G_LUT_X_MAX));
    if (rs.luts.texSynchGLut != 0) {
      glDeleteTextures(1, &rs.luts.texSynchGLut);
      rs.luts.texSynchGLut = 0;
    }
    rs.luts.texSynchGLut = createFloatTexture2D(kSynchGLutSize, 1, synchGData);
#if BLACKHOLE_HAS_CUDA
    rs.dispatch.cudaManager.registerLut(6 /*BhLutSynchG*/, rs.luts.texSynchGLut,
                            static_cast<unsigned int>(GL_TEXTURE_2D));
#endif
  }

  // Load Hawking radiation LUTs
  if (!rs.hawking.hawkingLutsLoaded) {
    std::filesystem::path const lutPath = resourcePath("assets/luts");
    if (std::filesystem::exists(lutPath)) {
      rs.hawking.hawkingLutsLoaded = rs.hawking.hawkingRenderer.loadLUTs(lutPath);
      if (rs.hawking.hawkingLutsLoaded) {
        std::cout << "Hawking radiation LUTs loaded successfully" << '\n';
      } else {
        std::cerr << "Failed to load Hawking radiation LUTs" << '\n';
      }
    }
  }
}

} // namespace blackhole
