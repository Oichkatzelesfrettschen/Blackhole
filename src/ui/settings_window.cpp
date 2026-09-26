/**
 * @file settings_window.cpp
 * @brief Main Settings tab-bar window (Visuals / GRMHD / Physics / Compute)
 *        and the in-loop overlay panels: curve overlay, bloom, tonemap, and
 *        depth effects.
 */

#include "settings_window.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <numbers>
#include <string>
#include <vector>

#include <glbinding/gl/functions.h>
#include <imgui.h>

#include "constants.h"
#include "grmhd_packed_loader.h"
#include "grmhd_streaming.h"
#include "kerr.h"
#include "overlay.h"
#include "physics/hawking_renderer.h"
#include "render/render_state.h"
#include "schwarzschild.h"
#include "settings.h"
#include "shader_manager.h"
#include "tools/compare_harness.h"

using namespace gl;

#if BLACKHOLE_HAS_CUDA
#include <glbinding/gl/enum.h>
#endif

namespace {
#if defined(BLACKHOLE_APP_VARIANT_CUDA_ONLY) && BLACKHOLE_APP_VARIANT_CUDA_ONLY
constexpr bool K_APP_VARIANT_CUDA_ONLY = true;
#else
constexpr bool K_APP_VARIANT_CUDA_ONLY = false;
#endif
} // anonymous namespace

namespace ui {

using blackhole::K_COMPARE_PRESETS;
using blackhole::K_MAX_BLOOM_ITERATIONS;
using blackhole::RenderState;

namespace {

// adiskLit, dopplerStrength and enableRedshift feed only the legacy fragment
// tracer's disk (adiskColor in blackhole_main.frag); the Kerr tracer on every
// backend shades the disk from the traced photon's g-factor
// (bhDiskEmission, d_disk_emission). Each control is disabled while the
// physical tracer is on and names the path it drives.
void legacyTracerControlTooltip() {
  if (ImGui::IsItemHovered(ImGuiHoveredFlags_AllowWhenDisabled)) {
    ImGui::SetTooltip("Legacy fragment tracer only (Physical Kerr ray tracer off).\n"
                      "The Kerr tracer shades the disk with the orbiting-emitter g-factor.");
  }
}

void drawCurvePlot(const OverlayCurve2D &curve, const ImVec2 &size) {
  ImDrawList *drawList = ImGui::GetWindowDrawList();
  ImVec2 const p0 = ImGui::GetCursorScreenPos();
  ImVec2 const p1 = ImVec2(p0.x + size.x, p0.y + size.y);

  ImGui::InvisibleButton("curve_plot", size);

  drawList->AddRectFilled(p0, p1, IM_COL32(20, 20, 20, 255), 0.0f);
  drawList->AddRect(p0, p1, IM_COL32(200, 200, 200, 255), 0.0f);

  float xSpan = curve.max.x - curve.min.x;
  float ySpan = curve.max.y - curve.min.y;
  if (xSpan == 0.0f) {
    xSpan = 1.0f;
  }
  if (ySpan == 0.0f) {
    ySpan = 1.0f;
  }

  const float pad = 6.0f;
  ImVec2 const q0 = ImVec2(p0.x + pad, p0.y + pad);
  ImVec2 const q1 = ImVec2(p1.x - pad, p1.y - pad);
  float const w = std::max(1.0f, q1.x - q0.x);
  float const h = std::max(1.0f, q1.y - q0.y);

  std::vector<ImVec2> pts;
  pts.reserve(curve.points.size());
  for (const auto &pt : curve.points) {
    float const nx = (pt.x - curve.min.x) / xSpan;
    float const ny = (pt.y - curve.min.y) / ySpan;
    float const px = q0.x + (nx * w);
    float const py = q1.y - (ny * h);
    pts.emplace_back(px, py);
  }

  if (pts.size() >= 2) {
    drawList->AddPolyline(pts.data(), static_cast<int>(pts.size()), IM_COL32(80, 200, 255, 255), 0,
                          2.0f);
  }

  ImGui::Text("x:[%.4g, %.4g]  y:[%.4g, %.4g]  n=%d", static_cast<double>(curve.min.x),
              static_cast<double>(curve.max.x), static_cast<double>(curve.min.y),
              static_cast<double>(curve.max.y), static_cast<int>(curve.points.size()));
}

/** @brief Loads a packed GRMHD dataset into rs.grmhd and registers the CUDA LUT. */
bool loadGrmhdPacked(RenderState &rs, const std::string &path) {
  std::string error;
  if (!loadGrmhdPackedTexture(path, rs.grmhd.grmhdTexture, error, true, true)) {
    rs.grmhd.grmhdLoadError = error;
    rs.grmhd.grmhdLoaded = false;
    return false;
  }
  rs.grmhd.grmhdLoadError.clear();
  rs.grmhd.grmhdLoaded = true;
  /* Wire BL radial extent from grid header into the Cartesian bounds uniforms.
   * The grid is spherical so the conservative bounding box is [-rMax, rMax]^3. */
  const float r = rs.grmhd.grmhdTexture.rMax;
  rs.grmhd.grmhdBoundsMin = glm::vec3(-r, -r, -r);
  rs.grmhd.grmhdBoundsMax = glm::vec3( r,  r,  r);
  /* Register GRMHD volume as CUDA texture object (slot 5 = BhLutGrmhd).
   * Registration is non-fatal: CUDA kernel falls back to no GRMHD sampling
   * if the backend is not active or registration fails. */
#if BLACKHOLE_HAS_CUDA
  if (rs.grmhd.grmhdTexture.texture != 0) {
    rs.dispatch.cudaManager.registerLut(5 /*BhLutGrmhd*/, rs.grmhd.grmhdTexture.texture,
                            static_cast<unsigned int>(GL_TEXTURE_3D));
  }
#endif
  return true;
}

void renderVisualSettings(RenderState &rs, Settings &settings) {
  ImGui::Checkbox("gravitationalLensing", &rs.disk.gravitationalLensing);
  ImGui::SliderInt("Bloom Iterations", &rs.post.bloomIterations, 1, K_MAX_BLOOM_ITERATIONS);
  settings.bloomIterations = rs.post.bloomIterations;
  ImGui::Checkbox("renderBlackHole", &rs.disk.renderBlackHole);
  ImGui::Checkbox("adiskEnabled", &rs.disk.adiskEnabled);
  ImGui::Checkbox("adiskParticle", &rs.disk.adiskParticle);
  ImGui::SliderFloat("adiskDensityV", &rs.disk.adiskDensityV, 0.0f, 10.0f);
  ImGui::SliderFloat("adiskDensityH", &rs.disk.adiskDensityH, 0.0f, 10.0f);
  ImGui::SliderFloat("adiskHeight", &rs.disk.adiskHeight, 0.0f, 1.0f);
  ImGui::BeginDisabled(rs.physicsCore.physicalRayTracer);
  ImGui::SliderFloat("adiskLit", &rs.disk.adiskLit, 0.0f, 4.0f);
  ImGui::EndDisabled();
  legacyTracerControlTooltip();
  ImGui::SliderFloat("adiskNoiseLOD", &rs.disk.adiskNoiseLOD, 1.0f, 12.0f);
  ImGui::SliderFloat("adiskNoiseScale", &rs.disk.adiskNoiseScale, 0.0f, 10.0f);
  ImGui::Checkbox("Noise Texture", &rs.disk.useNoiseTexture);
  ImGui::SliderFloat("Noise Tex Scale", &rs.disk.noiseTextureScale, 0.05f, 2.0f);
  ImGui::SliderFloat("adiskSpeed", &rs.disk.adiskSpeed, 0.0f, 1.0f);
  ImGui::BeginDisabled(rs.physicsCore.physicalRayTracer);
  ImGui::SliderFloat("dopplerStrength", &rs.disk.dopplerStrength, 0.0f, 5.0f);
  ImGui::EndDisabled();
  legacyTracerControlTooltip();

  ImGui::Separator();
  ImGui::Text("Volumetric RTE (D2)");
  ImGui::Checkbox("Volumetric RTE", &rs.rte.rteVolumetricEnabled);
  if (rs.rte.rteVolumetricEnabled) {
    ImGui::SliderFloat("RTE Opacity Scale", &rs.rte.rteOpacityScale, 0.0f, 5.0f);
  }

  ImGui::Separator();
  ImGui::Text("Polarized Stokes IQUV (D4)");
  ImGui::Checkbox("Stokes Transport", &rs.stokes.stokesEnabled);
  if (rs.stokes.stokesEnabled) {
    ImGui::SliderFloat("B Field Angle (rad)", &rs.stokes.stokesBFieldAngle,
                       -std::numbers::pi_v<float>, std::numbers::pi_v<float>);
    ImGui::SliderFloat("Faraday Ne Scale", &rs.stokes.stokesNeScale, 0.0f, 5.0f);
  }
}

void renderGrmhdDatasetControls(RenderState &rs) {
  // Load/Unload buttons
  if (ImGui::Button("Load Time-Series")) {
    /* Shut down any previously loaded dataset */
    if (rs.grmhd.grmhdStreamer) {
      rs.grmhd.grmhdStreamer->shutdown();
      rs.grmhd.grmhdStreamer.reset();
      rs.grmhd.grmhdTimeSeriesLoaded = false;
    }
    std::string const jsonPath(rs.grmhd.grmhdTimeSeriesJsonBuffer.data());
    std::string const binPath(rs.grmhd.grmhdTimeSeriesBinBuffer.data());
    if (!jsonPath.empty()) {
      rs.grmhd.grmhdStreamer = std::make_unique<blackhole::GRMHDStreamer>(jsonPath, binPath);
      if (rs.grmhd.grmhdStreamer->init()) {
        rs.grmhd.grmhdTimeSeriesLoaded = true;
        rs.grmhd.grmhdMaxFrame =
            static_cast<int>(rs.grmhd.grmhdStreamer->metadata().frameCount) - 1;
        rs.grmhd.grmhdCurrentFrame = 0;
        rs.grmhd.grmhdStreamer->seekFrame(0);
        /* Initialize PBOUploader with the grid dimensions from metadata.
         * Shuts down any previous allocation first. */
        const auto &meta = rs.grmhd.grmhdStreamer->metadata();
        if (rs.grmhd.grmhdPboUploader.texture() != 0) {
          rs.grmhd.grmhdPboUploader.shutdown();
        }
        rs.grmhd.grmhdPboUploader.init(static_cast<int>(meta.gridX), static_cast<int>(meta.gridY),
                                       static_cast<int>(meta.gridZ));
        /* Initialize the right-frame uploader with matching grid dimensions. */
        if (rs.grmhd.grmhdPboUploaderRight.texture() != 0) {
          rs.grmhd.grmhdPboUploaderRight.shutdown();
        }
        rs.grmhd.grmhdPboUploaderRight.init(static_cast<int>(meta.gridX),
                                            static_cast<int>(meta.gridY),
                                            static_cast<int>(meta.gridZ));
      } else {
        rs.grmhd.grmhdStreamer.reset();
      }
    }
  }
  ImGui::SameLine();
  if (ImGui::Button("Unload Time-Series")) {
    if (rs.grmhd.grmhdStreamer) {
      rs.grmhd.grmhdStreamer->shutdown();
      rs.grmhd.grmhdStreamer.reset();
    }
    rs.grmhd.grmhdPboUploader.shutdown();
    rs.grmhd.grmhdPboUploaderRight.shutdown(); /* Release the right-frame upload resources. */
    rs.grmhd.grmhdFrameAlpha = 0.0f;
    rs.grmhd.grmhdTimeSeriesLoaded = false;
    rs.grmhd.grmhdCurrentFrame = 0;
    rs.grmhd.grmhdMaxFrame = 0;
    rs.grmhd.grmhdPlaying = false;
    rs.grmhd.grmhdCacheHitRate = 0.0;
    rs.grmhd.grmhdQueueDepth = 0;
  }
}

void renderGrmhdTimeSeriesSettings(RenderState &rs) {
  ImGui::Separator();
  ImGui::TextColored(ImVec4(0.3f, 0.9f, 0.9f, 1.0f), "GRMHD Time-Series");
  ImGui::Checkbox("Enable Time-Series Playback", &rs.grmhd.grmhdTimeSeriesEnabled);

  ImGui::BeginDisabled(!rs.grmhd.grmhdTimeSeriesEnabled);

  // File paths
  ImGui::InputText("JSON Metadata", rs.grmhd.grmhdTimeSeriesJsonBuffer.data(),
                   rs.grmhd.grmhdTimeSeriesJsonBuffer.size());
  ImGui::InputText("Binary Data", rs.grmhd.grmhdTimeSeriesBinBuffer.data(),
                   rs.grmhd.grmhdTimeSeriesBinBuffer.size());

  renderGrmhdDatasetControls(rs);

  ImGui::BeginDisabled(!rs.grmhd.grmhdTimeSeriesLoaded);

  // Frame control
  ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Playback");
  if (ImGui::SliderInt("Frame", &rs.grmhd.grmhdCurrentFrame, 0, rs.grmhd.grmhdMaxFrame)) {
    if (rs.grmhd.grmhdStreamer) {
      rs.grmhd.grmhdStreamer->seekFrame(static_cast<uint32_t>(rs.grmhd.grmhdCurrentFrame));
    }
  }
  ImGui::Text("Time: %.2f s", static_cast<double>(rs.grmhd.grmhdCurrentFrame) / 30.0);

  // Play/Pause button
  if (rs.grmhd.grmhdPlaying) {
    if (ImGui::Button("Pause")) {
      rs.grmhd.grmhdPlaying = false;
      if (rs.grmhd.grmhdStreamer) {
        rs.grmhd.grmhdStreamer->pause();
      }
    }
  } else {
    if (ImGui::Button("Play")) {
      rs.grmhd.grmhdPlaying = true;
      if (rs.grmhd.grmhdStreamer) {
        rs.grmhd.grmhdStreamer->play();
      }
    }
  }
  ImGui::SameLine();
  if (ImGui::Button("Reset")) {
    rs.grmhd.grmhdCurrentFrame = 0;
    if (rs.grmhd.grmhdStreamer) {
      rs.grmhd.grmhdStreamer->seekFrame(0);
    }
  }

  // Playback speed
  if (ImGui::SliderFloat("Playback Speed", &rs.grmhd.grmhdPlaybackSpeed, 0.1f, 4.0f)) {
    if (rs.grmhd.grmhdStreamer) {
      rs.grmhd.grmhdStreamer->setPlaybackSpeed(static_cast<double>(rs.grmhd.grmhdPlaybackSpeed));
    }
  }

  // Cache statistics
  /* Refresh cache stats from live streamer each frame */
  if (rs.grmhd.grmhdStreamer) {
    rs.grmhd.grmhdCacheHitRate = rs.grmhd.grmhdStreamer->cacheHitRate();
    rs.grmhd.grmhdQueueDepth = static_cast<int>(rs.grmhd.grmhdStreamer->queueDepth());
    /* Mirror current frame from streamer (updated by background thread) */
    rs.grmhd.grmhdCurrentFrame = static_cast<int>(rs.grmhd.grmhdStreamer->currentFrame());
  }

  ImGui::Separator();
  ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Cache Statistics");
  ImGui::Text("Hit Rate: %.1f%%", rs.grmhd.grmhdCacheHitRate * 100.0);
  ImGui::Text("Queue Depth: %d", rs.grmhd.grmhdQueueDepth);

  // Progress indicator for queue
  if (rs.grmhd.grmhdQueueDepth > 0) {
    ImGui::ProgressBar(static_cast<float>(rs.grmhd.grmhdQueueDepth) / 10.0f, ImVec2(-1.0f, 0.0f),
                       nullptr);
  }

  // Performance targets reference
  ImGui::Separator();
  ImGui::TextDisabled("Performance Targets:");
  ImGui::TextDisabled("  Cache hit rate: >90%%");
  ImGui::TextDisabled("  Frame load time: <16ms (60 fps)");
  ImGui::TextDisabled("  Memory footprint: <4GB");

  ImGui::EndDisabled(); // !grmhdTimeSeriesLoaded
  ImGui::EndDisabled(); // !grmhdTimeSeriesEnabled
}

void renderGrmhdSettings(RenderState &rs) {
  ImGui::Text("GRMHD Packed");
  ImGui::Checkbox("Use GRMHD Field", &rs.grmhd.useGrmhd);
  ImGui::InputText("GRMHD Meta", rs.grmhd.grmhdPathBuffer.data(), rs.grmhd.grmhdPathBuffer.size());
  if (ImGui::Button("Load GRMHD")) {
    loadGrmhdPacked(rs, rs.grmhd.grmhdPathBuffer.data());
  }
  ImGui::SameLine();
  if (ImGui::Button("Unload GRMHD")) {
    destroyGrmhdPackedTexture(rs.grmhd.grmhdTexture);
    rs.grmhd.grmhdLoaded = false;
    rs.grmhd.grmhdLoadError.clear();
  }
  if (!rs.grmhd.grmhdLoadError.empty()) {
    ImGui::TextColored(ImVec4(1.0f, 0.35f, 0.35f, 1.0f), "%s", rs.grmhd.grmhdLoadError.c_str());
  }
  if (rs.grmhd.grmhdLoaded) {
    ImGui::Text("GRMHD grid: %d x %d x %d", rs.grmhd.grmhdTexture.width,
                rs.grmhd.grmhdTexture.height, rs.grmhd.grmhdTexture.depth);
  }
  ImGui::SliderFloat3("GRMHD Bounds Min", &rs.grmhd.grmhdBoundsMin.x, -50.0f, 50.0f);
  ImGui::SliderFloat3("GRMHD Bounds Max", &rs.grmhd.grmhdBoundsMax.x, -50.0f, 50.0f);
  ImGui::BeginDisabled(!rs.grmhd.grmhdLoaded);
  ImGui::Checkbox("Show GRMHD Slice", &rs.grmhd.grmhdSliceEnabled);
  const char *const axisLabels[] = {"X", "Y", "Z"};
  ImGui::Combo("Slice Axis", &rs.grmhd.grmhdSliceAxis, axisLabels, 3);
  ImGui::SliderFloat("Slice Coord", &rs.grmhd.grmhdSliceCoord, 0.0f, 1.0f);
  ImGui::SliderInt("Slice Channel", &rs.grmhd.grmhdSliceChannel, 0, 3);
  if (rs.grmhd.grmhdLoaded && rs.grmhd.grmhdSliceChannel >= 0 &&
      static_cast<std::size_t>(rs.grmhd.grmhdSliceChannel) <
          rs.grmhd.grmhdTexture.channels.size()) {
    auto const channelIndex = static_cast<std::size_t>(rs.grmhd.grmhdSliceChannel);
    ImGui::Text("Channel: %s", rs.grmhd.grmhdTexture.channels.at(channelIndex).c_str());
  }
  ImGui::Checkbox("Slice Auto Range", &rs.grmhd.grmhdSliceAutoRange);
  if (!rs.grmhd.grmhdSliceAutoRange) {
    ImGui::InputFloat("Slice Min", &rs.grmhd.grmhdSliceMin);
    ImGui::InputFloat("Slice Max", &rs.grmhd.grmhdSliceMax);
  }
  ImGui::Checkbox("Slice Color Map", &rs.grmhd.grmhdSliceUseColorMap);
  ImGui::SliderInt("Slice Size", &rs.grmhd.grmhdSliceSize, 64, 1024);
  if (rs.grmhd.texGrmhdSlice != 0) {
    auto const sliceId = static_cast<ImTextureID>(static_cast<uintptr_t>(rs.grmhd.texGrmhdSlice));
    ImGui::Image(sliceId, ImVec2(192.0f, 192.0f));
  }
  ImGui::EndDisabled();

  renderGrmhdTimeSeriesSettings(rs);
}

void renderPhysicsSettings(RenderState &rs) {
  ImGui::Text("Physics Parameters");

  // Black hole mass in solar masses (scaled for visualization)
  ImGui::SliderFloat("blackHoleMass", &rs.physicsCore.blackHoleMass, 0.1f, 10.0f);
  // Kerr spin a/M up to Thorne's 0.998 limit for an accreting hole
  // (Thorne 1974). Positive spin rotates counterclockwise about +z, the axis
  // the ray tracer uses as the spin axis.
  ImGui::SliderFloat("kerrSpin(a/M)", &rs.physicsCore.kerrSpin, -0.998f, 0.998f, "%.3f");
  if (ImGui::Button("Gargantua render spin (a = 0.6)")) {
    rs.physicsCore.kerrSpin = 0.6f;
  }
  if (ImGui::IsItemHovered()) {
    ImGui::SetTooltip("Interstellar rendered Gargantua at a/M = 0.6 for visual reasons;\n"
                      "its time dilation requires 1 - a/M ~ 1e-14 (James et al. 2015,\n"
                      "arXiv:1502.03808). The campaign clocks use the physics spin.");
  }

  ImGui::Checkbox("Physical Kerr ray tracer", &rs.physicsCore.physicalRayTracer);
  if (ImGui::IsItemHovered()) {
    ImGui::SetTooltip("On: trace Kerr null geodesics (Carter constants, Mino-time leapfrog).\n"
                      "Off: legacy artistic tracer (Schwarzschild bending, spin shown by tint).");
  }
  const char *const diskTransferLabels[] = {"Physical", "Interstellar (film)"};
  ImGui::Combo("Disk transfer", &rs.disk.diskTransferMode, diskTransferLabels, 2);
  if (ImGui::IsItemHovered()) {
    ImGui::SetTooltip("Physical: Doppler, gravitational and transverse shifts of an orbiting\n"
                      "disk seen from infinity: bolometric beaming g^4 F / F_peak, with the\n"
                      "chroma of a blackbody at g T_emit.\n"
                      "Interstellar: g = 1 with lensing kept, the unshifted disk James et al.\n"
                      "(2015, arXiv:1502.03808 sec. 4.2) describe for Gargantua.");
  }
  ImGui::SliderFloat("Disk peak temperature (K)", &rs.disk.diskPeakTemperature, 2000.0f,
                     40000.0f, "%.0f", ImGuiSliderFlags_Logarithmic);
  ImGui::SliderFloat("Disk brightness", &rs.disk.diskBrightness, 0.01f, 100.0f, "%.2f",
                     ImGuiSliderFlags_Logarithmic);

  // Physics visualization toggles
  ImGui::Checkbox("enablePhotonSphere", &rs.physicsCore.enablePhotonSphere);
  ImGui::BeginDisabled(rs.physicsCore.physicalRayTracer);
  ImGui::Checkbox("enableRedshift", &rs.physicsCore.enableRedshift);
  ImGui::EndDisabled();
  legacyTracerControlTooltip();

  ImGui::Separator();
  ImGui::Text("Hawking Radiation Glow");
  ImGui::Checkbox("Enable Hawking Glow", &rs.hawking.hawkingGlowEnabled);

  if (rs.hawking.hawkingGlowEnabled) {
    // Preset buttons
    const char *const presetLabels[] = {"Physical", "Primordial", "Extreme"};
    if (ImGui::Combo("Preset", &rs.hawking.hawkingPreset, presetLabels, 3)) {
      // Apply preset
      auto const preset = static_cast<physics::HawkingPreset>(rs.hawking.hawkingPreset);
      physics::HawkingGlowParams const params = physics::HawkingRenderer::applyPreset(preset);
      rs.hawking.hawkingTempScale = params.tempScale;
      rs.hawking.hawkingGlowIntensity = params.intensity;
    }

    // Manual controls
    ImGui::SliderFloat("Temp Scale", &rs.hawking.hawkingTempScale, 1.0f, 1e9f, "%.1e",
                       ImGuiSliderFlags_Logarithmic);
    ImGui::TextDisabled("1=physical, 1e6=primordial, 1e9=extreme");
    ImGui::SliderFloat("Glow Intensity", &rs.hawking.hawkingGlowIntensity, 0.0f, 5.0f);
    ImGui::Checkbox("Use LUTs", &rs.hawking.hawkingUseLUTs);

    if (rs.hawking.hawkingLutsLoaded) {
      ImGui::TextColored(ImVec4(0.0f, 1.0f, 0.0f, 1.0f), "LUTs loaded");
    } else {
      ImGui::TextColored(ImVec4(1.0f, 0.35f, 0.35f, 1.0f), "LUTs not loaded");
    }
  }

  ImGui::Separator();
  ImGui::Text("Spectral LUT");
  ImGui::Checkbox("Use Spectral LUT", &rs.luts.useSpectralLut);
  if (rs.luts.spectralLutLoaded) {
    ImGui::Text("Wavelength: %.0f - %.0f A", static_cast<double>(rs.luts.spectralWavelengthMin),
                static_cast<double>(rs.luts.spectralWavelengthMax));
  } else {
    ImGui::TextDisabled("rt_spectrum_lut.csv not loaded");
  }
  if (ImGui::Button("Reload Spectral LUT")) {
    rs.luts.spectralLutTried = false;
    rs.luts.spectralLutLoaded = false;
    rs.luts.spectralLutValues.clear();
    if (rs.luts.texSpectralLUT != 0) {
      glDeleteTextures(1, &rs.luts.texSpectralLUT);
      rs.luts.texSpectralLUT = 0;
    }
  }

  ImGui::Separator();
  ImGui::Text("GRB Modulation");
  ImGui::Checkbox("Use GRB Modulation", &rs.luts.useGrbModulation);
  if (rs.luts.grbModulationLoaded) {
    ImGui::Text("Time: %.2f - %.2f s", static_cast<double>(rs.luts.grbTimeMin),
                static_cast<double>(rs.luts.grbTimeMax));
  } else {
    ImGui::TextDisabled("grb_modulation_lut.csv not loaded");
  }
  ImGui::BeginDisabled(!rs.luts.grbModulationLoaded);
  ImGui::Checkbox("Manual GRB Time", &rs.luts.grbTimeManual);
  if (rs.luts.grbTimeManual) {
    ImGui::SliderFloat("GRB Time", &rs.luts.grbTimeManualValue, rs.luts.grbTimeMin,
                       rs.luts.grbTimeMax);
  }
  ImGui::EndDisabled();
  if (ImGui::Button("Reload GRB LUT")) {
    rs.luts.grbModulationTried = false;
    rs.luts.grbModulationLoaded = false;
    rs.luts.grbModulationValues.clear();
    if (rs.luts.texGrbModulationLUT != 0) {
      glDeleteTextures(1, &rs.luts.texGrbModulationLUT);
      rs.luts.texGrbModulationLUT = 0;
    }
  }
  ImGui::SliderFloat("Spectral Radius Min", &rs.luts.spectralRadiusMin, 0.0f, 50.0f);
  ImGui::SliderFloat("Spectral Radius Max", &rs.luts.spectralRadiusMax, 0.0f, 50.0f);

  const double referenceMass = physics::M_SUN;
  const double referenceRs = physics::schwarzschildRadius(referenceMass);
  const double referenceRg = physics::G * referenceMass / physics::C2;
  const double referenceA = static_cast<double>(rs.physicsCore.kerrSpin) * referenceRg;
  const bool progradeSpin = rs.physicsCore.kerrSpin >= 0.0f;
  const double iscoRatio =
      physics::kerrIscoRadius(referenceMass, referenceA, progradeSpin) / referenceRs;
  const double photonRatio =
      (progradeSpin ? physics::kerrPhotonOrbitPrograde
                    : physics::kerrPhotonOrbitRetrograde)(referenceMass, referenceA) /
      referenceRs;

  float const schwarzschildRadius = 2.0f * rs.physicsCore.blackHoleMass;
  float const photonSphereRadius = static_cast<float>(photonRatio) * schwarzschildRadius;
  float const iscoRadius = static_cast<float>(iscoRatio) * schwarzschildRadius;
  ImGui::Text("r_s = %.2f, r_ph = %.2f, r_ISCO = %.2f", static_cast<double>(schwarzschildRadius),
              static_cast<double>(photonSphereRadius), static_cast<double>(iscoRadius));
}

void renderComputeComparisonSettings(RenderState &rs) {
  if (!K_APP_VARIANT_CUDA_ONLY) {
    ImGui::Checkbox("Compare Compute vs Fragment", &rs.compare.compareComputeFragment);
  }
  if (rs.compare.compareComputeFragment && !K_APP_VARIANT_CUDA_ONLY) {
    ImGui::SliderInt("Compare Sample Size", &rs.compare.compareSampleSize, 4, 64);
    ImGui::SliderInt("Compare Frame Stride", &rs.compare.compareFrameStride, 1, 60);
    if (rs.compare.compareStats.valid) {
      ImGui::Text("Diff mean=%.6f max=%.6f", static_cast<double>(rs.compare.compareStats.meanAbs),
                  static_cast<double>(rs.compare.compareStats.maxAbs));
    } else {
      ImGui::TextDisabled("Diff metrics unavailable");
    }
    if (rs.compare.compareFullStats.valid) {
      ImGui::Text("Full diff mean=%.6f rms=%.6f max=%.6f",
                  static_cast<double>(rs.compare.compareFullStats.meanAbs),
                  static_cast<double>(rs.compare.compareFullStats.rms),
                  static_cast<double>(rs.compare.compareFullStats.maxAbs));
    }
    ImGui::Checkbox("Write Snapshot PPMs", &rs.compare.compareWriteOutputs);
    ImGui::Checkbox("Write Diff PPM", &rs.compare.compareWriteDiff);
    ImGui::Checkbox("Write Summary CSV", &rs.compare.compareWriteSummary);
    ImGui::SliderFloat("Diff Scale", &rs.compare.compareDiffScale, 0.1f, 32.0f);
    ImGui::SliderFloat("Max Diff Threshold", &rs.compare.compareThreshold, 0.0f, 0.5f);
    rs.compare.compareThreshold = std::max(rs.compare.compareThreshold, 0.0f);
    ImGui::SliderInt("Allowed Outliers", &rs.compare.compareMaxOutliers, 0, 50000);
    ImGui::SliderFloat("Allowed Outlier Frac", &rs.compare.compareMaxOutlierFrac, 0.0f, 0.01f,
                       "%.5f");
    rs.compare.compareMaxOutlierFrac = std::max(rs.compare.compareMaxOutlierFrac, 0.0f);
    ImGui::Checkbox("Compare Baseline (disable extras)", &rs.compare.compareBaselineEnabled);
    if (ImGui::Checkbox("Compare Overrides", &rs.compare.compareOverridesEnabled)) {
      if (rs.compare.compareOverridesEnabled) {
        if (rs.compare.compareMaxStepsOverride <= 0) {
          rs.compare.compareMaxStepsOverride = rs.dispatch.computeMaxSteps;
        }
        if (rs.compare.compareStepSizeOverride <= 0.0f) {
          rs.compare.compareStepSizeOverride = rs.dispatch.computeStepSize;
        }
      }
    }
    ImGui::BeginDisabled(!rs.compare.compareOverridesEnabled);
    ImGui::SliderInt("Compare Max Steps Override", &rs.compare.compareMaxStepsOverride, 0, 1000);
    ImGui::SliderFloat("Compare Step Size Override", &rs.compare.compareStepSizeOverride, 0.0f,
                       2.0f);
    ImGui::EndDisabled();
    ImGui::Separator();
    ImGui::Text("Integrator Debug");
    bool debugNan = (rs.compare.integratorDebugFlags &
                     RenderState::CompareGroup::K_INTEGRATOR_DEBUG_NAN_FLAG) != 0;
    bool debugRange = (rs.compare.integratorDebugFlags &
                       RenderState::CompareGroup::K_INTEGRATOR_DEBUG_RANGE_FLAG) != 0;
    bool debugMaxSteps = (rs.compare.integratorDebugFlags &
                          RenderState::CompareGroup::K_INTEGRATOR_DEBUG_MAXSTEPS_FLAG) != 0;
    ImGui::Checkbox("Flag NaN/Inf", &debugNan);
    ImGui::SameLine();
    ImGui::Checkbox("Flag Out-of-Range", &debugRange);
    ImGui::SameLine();
    ImGui::Checkbox("Flag Max-Step Exhaustion", &debugMaxSteps);
    rs.compare.integratorDebugFlags =
        (debugNan ? RenderState::CompareGroup::K_INTEGRATOR_DEBUG_NAN_FLAG : 0) |
        (debugRange ? RenderState::CompareGroup::K_INTEGRATOR_DEBUG_RANGE_FLAG : 0) |
        (debugMaxSteps ? RenderState::CompareGroup::K_INTEGRATOR_DEBUG_MAXSTEPS_FLAG : 0);
    ImGui::Text("Threshold failures: %d", rs.compare.compareFailureCount);
    if (rs.compare.compareFullStats.valid) {
      ImGui::Text("Last capture: %s", rs.compare.compareLastExceeded ? "FAIL" : "PASS");
      ImGui::Text("Outliers: %d (limit %d)", rs.compare.compareLastOutliers,
                  rs.compare.compareLastOutlierLimit);
    }
    if (ImGui::Checkbox("Auto Capture", &rs.compare.compareAutoCapture)) {
      rs.compare.compareAutoRemaining =
          rs.compare.compareAutoCapture ? std::max(rs.compare.compareAutoCount, 1) : 0;
      rs.compare.compareAutoStrideCounter = 0;
    }
    ImGui::SliderInt("Auto Capture Count", &rs.compare.compareAutoCount, 1, 120);
    ImGui::SliderInt("Auto Capture Stride", &rs.compare.compareAutoStride, 1, 600);
    if (rs.compare.compareAutoCapture) {
      ImGui::Text("Auto remaining: %d", rs.compare.compareAutoRemaining);
    }
    if (ImGui::Button("Capture Preset Sweep")) {
      rs.compare.comparePresetSweep = true;
      rs.compare.comparePresetIndex = 0;
      rs.compare.comparePresetFrameCounter = 0;
      rs.compare.compareAutoCapture = false;
      rs.compare.compareAutoRemaining = 0;
      rs.compare.compareRestorePending = false;
    }
    ImGui::SliderInt("Preset Settle Frames", &rs.compare.comparePresetSettleFrames, 1, 10);
    if (rs.compare.comparePresetSweep) {
      std::size_t const presetCount = K_COMPARE_PRESETS.size();
      int const displayIndex =
          std::clamp(rs.compare.comparePresetIndex + 1, 1, static_cast<int>(presetCount));
      auto const labelIndex = static_cast<std::size_t>(displayIndex - 1);
      const char *label = K_COMPARE_PRESETS.at(labelIndex).label;
      ImGui::Text("Preset sweep: %s (%d/%d)", label, displayIndex, static_cast<int>(presetCount));
    }
    if (ImGui::Button("Capture A/B Snapshot")) {
      rs.compare.captureCompareSnapshot = true;
    }
  }
}

void renderComputeSettings(RenderState &rs) {
  ImGui::Text("Compute Raytracer");
  bool const computeAvailable = ShaderManager::instance().canUseComputeShaders();
  if (!computeAvailable) {
    ImGui::TextDisabled("Compute shaders unavailable");
    rs.dispatch.useComputeRaytracer = false;
    rs.compare.compareComputeFragment = false;
  }
  if (K_APP_VARIANT_CUDA_ONLY) {
    rs.dispatch.useComputeRaytracer = false;
    rs.compare.compareComputeFragment = false;
    ImGui::TextDisabled("Compute/fragment comparison is disabled in BlackholeCUDA.");
  } else {
    ImGui::Checkbox("Use Compute Raytracer", &rs.dispatch.useComputeRaytracer);
  }
  if (rs.dispatch.useComputeRaytracer && !K_APP_VARIANT_CUDA_ONLY) {
    ImGui::SliderInt("Compute Steps", &rs.dispatch.computeMaxSteps, 50, 600);
    ImGui::SliderFloat("Compute Step Size", &rs.dispatch.computeStepSize, 0.01f, 1.0f);
    ImGui::Checkbox("Compute Tiled", &rs.dispatch.computeTiled);
    if (rs.dispatch.computeTiled) {
      ImGui::SliderInt("Compute Tile Size", &rs.dispatch.computeTileSize, 64, 1024);
    }
  }
#if BLACKHOLE_HAS_CUDA
  ImGui::Separator();
  ImGui::Text("CUDA Backend");
  {
    bool cudaEnabled = rs.dispatch.cudaManager.isEnabled();
    if (ImGui::Checkbox("Use CUDA Raytracer", &cudaEnabled)) {
      rs.dispatch.cudaManager.setEnabled(cudaEnabled);
    }
  }
  if (rs.dispatch.cudaManager.isEnabled()) {
    const char *const variantNames[] = {"FP32 Baseline", "FP32 Coarsened (2 ray/thread)",
                                        "FP16 Storage", "FP16 H2 ILP (2 ray/thread)", "Auto"};
    int variantUI =
        rs.dispatch.cudaManager.kernelVariant() < 0 ? 4 : rs.dispatch.cudaManager.kernelVariant();
    if (ImGui::Combo("Kernel Variant", &variantUI, variantNames, 5)) {
      rs.dispatch.cudaManager.setKernelVariant((variantUI >= 4) ? -1 : variantUI);
    }
    if (rs.dispatch.cudaManager.isReady()) {
      int const actual = rs.dispatch.cudaManager.activeVariant();
      if (actual >= 0 && actual < BH_KERNEL_COUNT) {
        ImGui::TextDisabled("Active: %s", variantNames[actual]);
      }
    } else if (rs.dispatch.cudaManager.wasInitAttempted()) {
      ImGui::TextColored(ImVec4(1.f, 0.4f, 0.4f, 1.f), "Init failed -- toggle checkbox to retry");
    } else {
      ImGui::TextDisabled("Will init on next frame");
    }
  }
  ImGui::Separator();
#endif
  renderComputeComparisonSettings(rs);
}

} // anonymous namespace

void renderSettingsWindow(RenderState &rs) {
  auto &settings = SettingsManager::instance().get();
  ImGui::SetNextWindowSize(ImVec2(450, 700), ImGuiCond_FirstUseEver);
  ImGui::Begin("Settings", nullptr, ImGuiWindowFlags_NoCollapse);
  if (ImGui::BeginTabBar("MainTabs")) {
    if (ImGui::BeginTabItem("Visuals")) {
      renderVisualSettings(rs, settings);
      ImGui::EndTabItem();
    }
    if (ImGui::BeginTabItem("GRMHD")) {
      renderGrmhdSettings(rs);
      ImGui::EndTabItem();
    }
    if (ImGui::BeginTabItem("Physics")) {
      renderPhysicsSettings(rs);
      ImGui::EndTabItem();
    }
    if (ImGui::BeginTabItem("Compute")) {
      renderComputeSettings(rs);
      ImGui::EndTabItem();
    }
    ImGui::EndTabBar();
  }
  ImGui::End();
}

void renderCurveOverlayWindow(RenderState &rs, const std::string &curveTsvPath) {
  if (!rs.overlays.curveOverlayWindowOpen) {
    return;
  }
  ImGui::Begin("Curve Overlay", &rs.overlays.curveOverlayWindowOpen);
  ImGui::Checkbox("Enabled", &rs.overlays.curveOverlayEnabled);
  if (ImGui::Button("Reload") && !curveTsvPath.empty()) {
    rs.overlays.curveOverlayLoaded = rs.overlays.curveOverlay.loadFromTsv(curveTsvPath);
  }
  if (!curveTsvPath.empty()) {
    ImGui::SameLine();
    ImGui::Text("%s", curveTsvPath.c_str());
  }

  if (curveTsvPath.empty()) {
    ImGui::Text("Pass --curve-tsv <path> to plot a 2-column TSV.");
  } else if (!rs.overlays.curveOverlayLoaded) {
    ImGui::Text("Load error: %s", rs.overlays.curveOverlay.lastError.c_str());
  } else if (rs.overlays.curveOverlayEnabled) {
    ImVec2 plotSize = ImGui::GetContentRegionAvail();
    plotSize.y = std::max(plotSize.y, 220.0f);
    drawCurvePlot(rs.overlays.curveOverlay, plotSize);
  }

  ImGui::End();
}

void renderBloomPanel(RenderState &rs) {
  auto &settings = SettingsManager::instance().get();
  ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
  ImGui::SliderFloat("bloomStrength",  &rs.post.bloomStrength, 0.0f, 1.0f);
  ImGui::SliderFloat("bloomThreshold", &rs.post.bloomThreshold, 0.0f, 2.0f);
  ImGui::SliderFloat("bloomKnee",      &rs.post.bloomKnee, 0.0f, 0.5f);
  ImGui::SliderFloat("bloomTone",      &rs.post.bloomTone, 0.0f, 2.0f);
  settings.bloomStrength = rs.post.bloomStrength;
  ImGui::End();
}

void renderTonemapPanel(RenderState &rs) {
  auto &settings = SettingsManager::instance().get();
  ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
  ImGui::Checkbox("tonemappingEnabled", &rs.post.tonemappingEnabled);
  ImGui::SliderFloat("exposure", &rs.post.toneExposure, 0.01f, 2.0f, "%.2f", ImGuiSliderFlags_Logarithmic);
  ImGui::SliderFloat("gamma", &rs.post.gamma, 1.0f, 4.0f);
  settings.tonemappingEnabled = rs.post.tonemappingEnabled;
  settings.gamma = rs.post.gamma;
  ImGui::End();
}

void renderDepthEffectsPanel(RenderState &rs) {
  ImGui::Begin("Depth Effects", nullptr, ImGuiWindowFlags_NoCollapse);
  ImGui::Checkbox("Enable Depth Effects", &rs.depthFx.depthEffectsEnabled);
  ImGui::SliderFloat("Depth Far", &rs.display.depthFar, 10.0f, 200.0f);
  if (ImGui::Button("Preset: Subtle")) {
    rs.depthFx.depthEffectsEnabled = true;
    rs.depthFx.fogEnabled = true;
    rs.depthFx.fogDensity = 0.08f;
    rs.depthFx.fogStart = 0.6f;
    rs.depthFx.fogEnd = 0.98f;
    rs.depthFx.fogColor[0] = 0.06f;
    rs.depthFx.fogColor[1] = 0.06f;
    rs.depthFx.fogColor[2] = 0.10f;
    rs.depthFx.edgeOutlinesEnabled = false;
    rs.depthFx.edgeThreshold = 0.5f;
    rs.depthFx.edgeWidth = 1.0f;
    rs.depthFx.depthDesatEnabled = true;
    rs.depthFx.desatStrength = 0.10f;
    rs.depthFx.chromaDepthEnabled = false;
    rs.depthFx.motionParallaxHint = false;
    rs.depthFx.dofEnabled = false;
    rs.depthFx.dofFocusNear = 0.3f;
    rs.depthFx.dofFocusFar = 0.9f;
    rs.depthFx.dofMaxRadius = 2.0f;
    rs.depthFx.depthCurve = 1.0f;
    rs.display.depthFar = 100.0f;
  }
  ImGui::SameLine();
  if (ImGui::Button("Preset: Cinematic")) {
    rs.depthFx.depthEffectsEnabled = true;
    rs.depthFx.fogEnabled = true;
    rs.depthFx.fogDensity = 0.3f;
    rs.depthFx.fogStart = 0.25f;
    rs.depthFx.fogEnd = 0.85f;
    rs.depthFx.fogColor[0] = 0.08f;
    rs.depthFx.fogColor[1] = 0.08f;
    rs.depthFx.fogColor[2] = 0.12f;
    rs.depthFx.edgeOutlinesEnabled = true;
    rs.depthFx.edgeThreshold = 0.5f;
    rs.depthFx.edgeWidth = 1.2f;
    rs.depthFx.depthDesatEnabled = true;
    rs.depthFx.desatStrength = 0.35f;
    rs.depthFx.chromaDepthEnabled = true;
    rs.depthFx.motionParallaxHint = false;
    rs.depthFx.dofEnabled = true;
    rs.depthFx.dofFocusNear = 0.25f;
    rs.depthFx.dofFocusFar = 0.75f;
    rs.depthFx.dofMaxRadius = 5.0f;
    rs.depthFx.depthCurve = 0.95f;
    rs.display.depthFar = 100.0f;
  }
  ImGui::SameLine();
  if (ImGui::Button("Preset: Clarity")) {
    rs.depthFx.depthEffectsEnabled = true;
    rs.depthFx.fogEnabled = true;
    rs.depthFx.fogDensity = 0.12f;
    rs.depthFx.fogStart = 0.45f;
    rs.depthFx.fogEnd = 0.95f;
    rs.depthFx.fogColor[0] = 0.05f;
    rs.depthFx.fogColor[1] = 0.05f;
    rs.depthFx.fogColor[2] = 0.08f;
    rs.depthFx.edgeOutlinesEnabled = true;
    rs.depthFx.edgeThreshold = 0.42f;
    rs.depthFx.edgeWidth = 1.4f;
    rs.depthFx.depthDesatEnabled = true;
    rs.depthFx.desatStrength = 0.15f;
    rs.depthFx.chromaDepthEnabled = false;
    rs.depthFx.motionParallaxHint = false;
    rs.depthFx.dofEnabled = false;
    rs.depthFx.dofFocusNear = 0.35f;
    rs.depthFx.dofFocusFar = 0.95f;
    rs.depthFx.dofMaxRadius = 2.5f;
    rs.depthFx.depthCurve = 1.15f;
    rs.display.depthFar = 100.0f;
  }
  ImGui::Separator();

  ImGui::Checkbox("Fog", &rs.depthFx.fogEnabled);
  ImGui::SliderFloat("Fog Density", &rs.depthFx.fogDensity, 0.0f, 1.0f);
  ImGui::SliderFloat("Fog Start", &rs.depthFx.fogStart, 0.0f, 1.0f);
  ImGui::SliderFloat("Fog End", &rs.depthFx.fogEnd, 0.0f, 1.0f);
  rs.depthFx.fogStart = std::min(rs.depthFx.fogStart, rs.depthFx.fogEnd);
  ImGui::ColorEdit3("Fog Color", rs.depthFx.fogColor);

  ImGui::Separator();
  ImGui::Checkbox("Edge Outlines", &rs.depthFx.edgeOutlinesEnabled);
  ImGui::SliderFloat("Edge Threshold", &rs.depthFx.edgeThreshold, 0.0f, 1.0f);
  ImGui::SliderFloat("Edge Width", &rs.depthFx.edgeWidth, 0.5f, 3.0f);
  ImGui::ColorEdit3("Edge Color", rs.depthFx.edgeColor);

  ImGui::Separator();
  ImGui::Checkbox("Depth Desaturation", &rs.depthFx.depthDesatEnabled);
  ImGui::SliderFloat("Desaturation", &rs.depthFx.desatStrength, 0.0f, 1.0f);
  ImGui::Checkbox("Chroma Depth", &rs.depthFx.chromaDepthEnabled);
  ImGui::Checkbox("Motion Parallax Hint", &rs.depthFx.motionParallaxHint);

  ImGui::Separator();
  ImGui::Checkbox("Depth of Field", &rs.depthFx.dofEnabled);
  ImGui::SliderFloat("DoF Focus Near", &rs.depthFx.dofFocusNear, 0.0f, 1.0f);
  ImGui::SliderFloat("DoF Focus Far", &rs.depthFx.dofFocusFar, 0.0f, 1.0f);
  rs.depthFx.dofFocusNear = std::min(rs.depthFx.dofFocusNear, rs.depthFx.dofFocusFar);
  ImGui::SliderFloat("DoF Max Radius", &rs.depthFx.dofMaxRadius, 0.0f, 12.0f);
  ImGui::SliderFloat("Depth Curve", &rs.depthFx.depthCurve, 0.5f, 2.0f);
  ImGui::End();
}

} // namespace ui
