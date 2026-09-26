/**
 * @file record_mode.cpp
 * @brief Showcase-orbit composition table, lookup, and beauty-wiregrid tuning.
 */

#include "render/record_mode.h"

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <format>
#include <iostream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

#include <GLFW/glfw3.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <stb_image_write.h>

#include <glm/ext/vector_float4.hpp>

#include "cinematic.h" // K_CINEMATIC_KEYFRAMES / DURATION / FPS
#include "input.h"     // InputManager, CameraState, CameraMode
#include "platform/cli_options.h"
#include "render/render_state.h"   // RenderState, WiregridParams
#include "settings.h"              // SettingsManager
#include "tools/compare_harness.h" // readTextureRGBA, writePfmRgb

using namespace gl;

namespace blackhole {
namespace {

float compositionValue(const ShowcaseOrbitComposition *composition,
                       float ShowcaseOrbitComposition::*member, float defaultValue) {
  return composition == nullptr ? defaultValue : composition->*member;
}

/**
 * @brief Downloads a tonemapped RGB texture into a top-to-bottom byte buffer.
 *
 * Queries the texture's stored dimensions (falling back to the render size) and
 * reads GL_RGB/GL_UNSIGNED_BYTE with GL_PACK_ALIGNMENT set to 1: the default
 * alignment of 4 pads each row to a 4-byte boundary, so for a width like 1343
 * the row stride would be 4032 rather than 4029 and glGetTexImage would write
 * past the tightly-sized buffer, corrupting the next heap chunk. glGetTexImage
 * returns rows bottom-to-top, so the copy flips them for image output. Returns
 * false when the texture is unset.
 */
bool readTonemappedRgb(gl::GLuint texTonemapped, int fallbackWidth, int fallbackHeight,
                       std::vector<unsigned char> &flipped, int &outWidth, int &outHeight) {
  if (texTonemapped == 0) {
    return false;
  }
  glBindTexture(GL_TEXTURE_2D, texTonemapped);
  GLint texW = 0;
  GLint texH = 0;
  glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_WIDTH, &texW);
  glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_HEIGHT, &texH);
  int const w = (texW > 0) ? texW : fallbackWidth;
  int const h = (texH > 0) ? texH : fallbackHeight;
  std::vector<unsigned char> px(static_cast<size_t>(w) * static_cast<size_t>(h) * 3);
  glPixelStorei(GL_PACK_ALIGNMENT, 1);
  glGetTexImage(GL_TEXTURE_2D, 0, GL_RGB, GL_UNSIGNED_BYTE, px.data());
  glPixelStorei(GL_PACK_ALIGNMENT, 4);
  glBindTexture(GL_TEXTURE_2D, 0);
  flipped.assign(px.size(), 0);
  for (int row = 0; row < h; ++row) {
    std::memcpy(flipped.data() + static_cast<size_t>(row) * static_cast<size_t>(w) * 3,
                px.data() + static_cast<size_t>(h - 1 - row) * static_cast<size_t>(w) * 3,
                static_cast<size_t>(w) * 3);
  }
  outWidth = w;
  outHeight = h;
  return true;
}

// above-disk, the default, frames the hole from outside the disk's 100 r_s
// outer edge, 10 degrees above the plane (the default desktop camera); the
// other five sit inside the disk's radial extent near the plane, where the
// disk fills the view.
constexpr std::array<ShowcaseOrbitComposition, 6> K_SHOWCASE_ORBIT_COMPOSITIONS = {{
    {"above-disk", "nasa_deep_starmap_galactic", 0.0f, 0.0f, 10.0f, 240.0f, 20.0f, 9.14f, 0.80f, 26.0f, 8.0f, 0.00f, 0.00f, 8.0f},
    {"centered", "nasa_deep_starmap_galactic", 0.0f, 0.0f, -8.0f, 21.0f, 32.2042f, 1.23f, 0.74f, -18.0f, 6.0f, 0.00f, 0.00f, 8.0f},
    {"left-third", "nasa_deep_starmap", 0.36f, 0.06f, -8.0f, 23.0f, 30.9819f, 3.60f, 0.76f, -34.0f, 7.0f, 0.05f, -0.02f, 7.0f},
    {"right-third", "nasa_deep_starmap_galactic", -0.36f, 0.06f, -8.0f, 23.0f, 30.9819f, 1.24f, 0.76f, 18.0f, 7.0f, -0.05f, -0.02f, 7.0f},
    {"wide-left", "eso_milkyway_brunier", 0.24f, -0.04f, -7.0f, 27.5f, 28.5856f, 1.73f, 0.70f, -42.0f, 8.0f, 0.08f, -0.03f, 6.0f},
    {"wide-right", "nasa_deep_starmap_galactic", -0.24f, -0.04f, -7.0f, 27.5f, 28.5856f, 1.31f, 0.80f, 26.0f, 8.0f, -0.08f, -0.03f, 6.0f},
}};

} // namespace

const ShowcaseOrbitComposition *findShowcaseOrbitComposition(std::string_view name) {
  // inside-disk names the in-disk framing wide-right.
  std::string_view const key = name == "inside-disk" ? std::string_view("wide-right") : name;
  const auto *const composition =
      std::ranges::find_if(K_SHOWCASE_ORBIT_COMPOSITIONS,
                           [key](const auto &candidate) { return key == candidate.name; });
  return composition == K_SHOWCASE_ORBIT_COMPOSITIONS.end() ? nullptr : composition;
}

void applyShowcaseBeautyWiregridTuning(std::string_view compositionArg, WiregridParams &params,
                                       glm::vec4 &color) {
  if (params.mode != WiregridParams::Mode::Beauty) {
    return;
  }
  const ShowcaseOrbitComposition *const resolved = findShowcaseOrbitComposition(compositionArg);
  std::string_view const compositionName =
      resolved != nullptr ? std::string_view(resolved->name) : compositionArg;

  if (compositionName == "wide-right") {
    params.gridScale = 0.78f;
    params.motionScale = 0.48f;
    params.infallScale = 0.16f;
    params.strength = 0.48f;
    params.scenePreserve = 1.0f;
    color = glm::vec4(0.19f, 0.58f, 0.90f, 0.11f);
    return;
  }
  if (compositionName == "right-third") {
    params.gridScale = 0.84f;
    params.motionScale = 0.54f;
    params.infallScale = 0.20f;
    params.strength = 0.56f;
    params.scenePreserve = 1.0f;
    color = glm::vec4(0.20f, 0.60f, 0.91f, 0.12f);
    return;
  }
  if (compositionName == "wide-left") {
    params.gridScale = 0.82f;
    params.motionScale = 0.50f;
    params.infallScale = 0.18f;
    params.strength = 0.52f;
    params.scenePreserve = 1.0f;
    color = glm::vec4(0.19f, 0.58f, 0.89f, 0.11f);
  }
}

bool applyRecordProfileSetup(RenderState &rs, const platform::CliOptions &cli, InputManager &input,
                             GLFWwindow *window) {
  std::error_code recordDirEc;
  std::filesystem::create_directories(cli.recordFramesDir, recordDirEc);
  if (recordDirEc) {
    std::cerr << "record output directory create failed: " << cli.recordFramesDir << " ("
              << recordDirEc.message() << ")\n";
    return false;
  }
  rs.recording.recordInitDone     = true;
  int recordWidth = 1920;
  int recordHeight = 1080;
  if (char const *const envWidth = std::getenv("BLACKHOLE_RECORD_WIDTH")) {
    int const parsed = std::atoi(envWidth); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c) -- env override, invalid input keeps default
    if (parsed > 0) {
      recordWidth = parsed;
    }
  }
  if (char const *const envHeight = std::getenv("BLACKHOLE_RECORD_HEIGHT")) {
    int const parsed = std::atoi(envHeight); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c) -- env override, invalid input keeps default
    if (parsed > 0) {
      recordHeight = parsed;
    }
  }
  glfwSetWindowSize(window, recordWidth, recordHeight);
  glfwSwapInterval(0);
  rs.display.swapInterval       = 0;
  if (cli.recordProfile == "compare-orbit-near") {
    rs.disk.adiskEnabled       = false;
    rs.disk.adiskParticle      = false;
    rs.physicsCore.enableRedshift     = false;
    rs.physicsCore.enablePhotonSphere = false;
    rs.hawking.hawkingGlowEnabled = false;
    rs.rte.rteVolumetricEnabled = false;
    rs.stokes.stokesEnabled      = false;
    rs.disk.useNoiseTexture    = false;
    rs.disk.noiseTextureReady  = true;
    rs.disk.adiskNoiseLOD      = 3.0f;
    rs.disk.adiskNoiseScale    = 0.5f;
    rs.disk.adiskDensityV      = 2.0f;
    rs.disk.adiskLit           = 0.25f;
    rs.disk.dopplerStrength    = 1.0f;
    rs.disk.photonSphereGlowStrength = 1.0f;
    rs.post.bloomIterations    = 4;
    rs.post.bloomStrength      = 0.08f;
    rs.post.tonemappingEnabled = true;
    // The record exposure rule's sky target: the raw sky's 99th-percentile
    // luminance, 0.0704, reaches display 0.8.
    rs.post.toneExposure       = 6.6f;
    rs.post.gamma              = 2.35f;
    rs.dispatch.computeMaxSteps    = 1000;
    rs.dispatch.computeStepSize    = 0.02f;
    rs.display.depthFar           = 154.367004f;
    rs.physicsCore.kerrSpin           = 0.0f;
    SettingsManager::instance().get().backgroundId = "eso_milkyway_brunier";
    SettingsManager::instance().get().backgroundEnabled = true;
    SettingsManager::instance().get().backgroundIntensity = 0.8f;
    CameraState &camMutable = input.camera();
    camMutable = CameraState{.yaw = -90.0f, .pitch = 0.0f, .roll = 0.0f, .distance = 10.0f, .fov = 90.0f};
    rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
  } else if (cli.recordProfile == "showcase-orbit") {
    const ShowcaseOrbitComposition *const composition =
        findShowcaseOrbitComposition(cli.recordComposition);
    rs.disk.adiskEnabled       = true;
    rs.disk.adiskParticle      = false;
    rs.physicsCore.enableRedshift     = true;
    rs.physicsCore.enablePhotonSphere = true;
    rs.hawking.hawkingGlowEnabled = false;
    rs.rte.rteVolumetricEnabled = false;
    rs.stokes.stokesEnabled      = false;
    rs.disk.useNoiseTexture    = false;
    rs.disk.noiseTextureReady  = true;
    rs.disk.adiskNoiseLOD      = 3.0f;
    rs.disk.adiskNoiseScale    = 0.35f;
    rs.disk.adiskDensityV      = 1.6f;
    rs.disk.adiskDensityH      = 2.1f;
    rs.disk.adiskHeight        = 0.42f;
    rs.disk.adiskLit           = 0.24f;
    // The interactive default: the bloom bright pass thresholds the raw
    // frame at 0.4, so only g^4 F / F_peak above about 1.6 (the approaching
    // side's beaming) blooms. The composition exposure, set below, follows
    // the record exposure rule (record_mode.h).
    rs.disk.diskBrightness     = 0.25f;
    rs.disk.dopplerStrength    = 1.15f;
    rs.disk.photonSphereGlowStrength = 1.15f;
    rs.post.bloomIterations    = 5;
    rs.post.bloomStrength      = 0.055f;
    rs.post.tonemappingEnabled = true;
    rs.post.toneExposure       = 1.0f;
    rs.post.gamma              = 2.35f;
    rs.dispatch.computeMaxSteps    = 1000;
    rs.dispatch.computeStepSize    = 0.016f;
    // Beyond every composition's camera distance plus the disk's 200-unit
    // outer radius: depth cues normalize a disk hit below 1, and a ray leaving
    // outward is traced past the disk's outer edge before it escapes.
    rs.display.depthFar           = K_DEFAULT_DEPTH_FAR;
    rs.physicsCore.kerrSpin           = K_SHOWCASE_ORBIT_SPIN;
    const char *defaultBackground =
        composition != nullptr ? composition->backgroundId : "nasa_deep_starmap_galactic";
    SettingsManager::instance().get().backgroundId =
        cli.hasRecordBackgroundId ? cli.recordBackgroundId : defaultBackground;
    SettingsManager::instance().get().backgroundEnabled = true;
    SettingsManager::instance().get().backgroundIntensity =
        composition != nullptr ? composition->backgroundIntensity : 0.72f;
    CameraState &camMutable = input.camera();
    camMutable = CameraState{
        .yaw = cli.hasRecordYaw ? cli.recordYawDeg : -90.0f,
        .pitch = cli.hasRecordPitch
                     ? cli.recordPitchDeg
                     : compositionValue(composition, &ShowcaseOrbitComposition::pitchDeg, -6.0f),
        .roll = 0.0f,
        .distance = cli.hasRecordDistance
                        ? cli.recordDistance
                        : compositionValue(composition, &ShowcaseOrbitComposition::distance, 14.0f),
        .fov = cli.hasRecordFov
                   ? cli.recordFovDeg
                   : compositionValue(composition, &ShowcaseOrbitComposition::fovDeg, 37.2738f)};
    rs.post.toneExposure =
        composition != nullptr ? composition->exposure : K_SHOWCASE_ORBIT_FALLBACK_EXPOSURE;
    rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
  } else {
    // Physics: on, but not everything -- avoids noise pileup / fuzz
    rs.disk.adiskEnabled       = true;
    rs.disk.adiskParticle      = false;  // particle mode adds visual noise
    rs.physicsCore.enableRedshift     = true;
    rs.physicsCore.enablePhotonSphere = true;
    rs.hawking.hawkingGlowEnabled = false;  // haze effect competes with disk shading
    rs.rte.rteVolumetricEnabled = false; // volumetric fog washes out fine detail
    rs.stokes.stokesEnabled      = false;
    // Skip noise texture LUT generation in record mode: FastNoise2
    // SIMD code has a heap double-free at >= 128^3 on this system.
    // The disk looks clean without it.
    rs.disk.useNoiseTexture    = false;
    rs.disk.noiseTextureReady  = true;   // mark done so we never call initialize()
    rs.disk.adiskNoiseLOD      = 3.0f;
    rs.disk.adiskNoiseScale    = 0.5f;
    rs.disk.adiskDensityV      = 1.4f;
    rs.disk.adiskLit           = 0.08f;
    rs.disk.dopplerStrength    = 1.0f;
    rs.disk.photonSphereGlowStrength = 1.0f;
    // Post-processing: preserve ring detail instead of washing it out
    rs.post.bloomIterations    = 3;
    rs.post.bloomStrength      = 0.03f;
    rs.post.tonemappingEnabled = true;
    // The record exposure rule over the nine keyframes at their spin 0.998
    // gives 3.1-267 (L99 = 0.30 at 78 s, 0.0035 at 180 s: from far out the
    // bright annulus near the ISCO covers few pixels); 14.4 is their median.
    rs.disk.diskBrightness     = 0.25f;
    rs.post.toneExposure       = 14.4f;
    rs.post.gamma              = 2.25f;
    // Integration quality
    rs.dispatch.computeMaxSteps    = 500;   // more steps for wide shots at 350+ rs
    rs.dispatch.computeStepSize    = 0.08f;
    // Escape radius must exceed the maximum camera distance (380 rs).
    // depthFar is passed as interop.depthFar and used as the ray max_dist.
    rs.display.depthFar           = 500.0f;
    rs.physicsCore.kerrSpin           = K_CINEMATIC_KEYFRAMES[0].kerrSpin;
    // Background: override to the ESO Milky Way panorama which ships as a real
    // JPEG (not a Git LFS pointer) -- the default "nasa_pia22085" is LFS-tracked.
    SettingsManager::instance().get().backgroundId = "eso_milkyway_brunier";
    SettingsManager::instance().get().backgroundEnabled = true;
    // The record exposure rule's sky target at exposure 14.4 on the
    // sky-heaviest keyframe (180 s, 20% sky): raw sky L99 0.0332 x 14.4 =
    // 0.48. The escaped-sky shaping (d_shape_escaped_background) is not
    // linear in the intensity; 0.8 gave L99 0.191.
    SettingsManager::instance().get().backgroundIntensity = 0.32f;
  }
#if BLACKHOLE_HAS_CUDA
  // Keep legacy record profiles on the CUDA path in the hybrid app, but let
  // showcase-orbit remain a true GLSL lane for apples-to-apples captures.
  if (cli.recordProfile != "showcase-orbit") {
    // isEnabled() gates the CUDA dispatch path (line ~4295). It is normally set
    // via the ImGui "Use CUDA Raytracer" checkbox; record mode must set it directly.
    // useComputeRaytracer alone is insufficient -- it only controls the GLSL compute
    // path, not the CUDA path.
    rs.dispatch.cudaManager.setEnabled(true);
  } else {
    rs.dispatch.cudaManager.setEnabled(false);
    rs.dispatch.useComputeRaytracer = false;
    rs.compare.compareComputeFragment = false;
  }
#endif
  std::printf("Record mode: dir=%s  frames=%d  duration=%.0f s @ %d fps\n",
              cli.recordFramesDir.c_str(), cli.recordFramesTotal,
              static_cast<double>(K_CINEMATIC_DURATION_S), K_CINEMATIC_FPS);
  // --record-exposure overrides every profile's exposure.
  if (cli.hasRecordExposure) {
    rs.post.toneExposure = cli.recordExposure;
  }
  std::printf("Record profile: %s\n", cli.recordProfile.c_str());
  return true;
}

void applyRecordCameraPath(RenderState &rs, const platform::CliOptions &cli, InputManager &input) {
  if (cli.recordFramesDir.empty()) {
    return;
  }
  if (cli.recordProfile == "compare-orbit-near") {
    float const denom = static_cast<float>(std::max(cli.recordFramesTotal - 1, 1));
    float const progress =
        static_cast<float>(rs.recording.recordFrameIndex - cli.recordStartFrame) / denom;
    CameraState &camMutable = input.camera();
    camMutable.yaw = -90.0f + progress * 18.0f;
    camMutable.pitch = 0.0f;
    camMutable.roll = 0.0f;
    camMutable.distance = 10.0f;
    camMutable.fov = 90.0f;
    rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
    rs.physicsCore.kerrSpin = 0.0f;
  } else if (cli.recordProfile == "showcase-orbit") {
    const ShowcaseOrbitComposition *const composition =
        findShowcaseOrbitComposition(cli.recordComposition);
    float const denom = static_cast<float>(std::max(cli.recordFramesTotal - 1, 1));
    float const progress =
        static_cast<float>(rs.recording.recordFrameIndex - cli.recordStartFrame) / denom;
    float const baseYaw = cli.hasRecordYaw ? cli.recordYawDeg : -90.0f;
    float const sweepDeg =
        cli.hasRecordSweep
            ? cli.recordSweepDeg
            : compositionValue(composition, &ShowcaseOrbitComposition::sweepDeg, 10.0f);
    CameraState &camMutable = input.camera();
    camMutable.yaw = baseYaw + progress * sweepDeg;
    camMutable.pitch =
        cli.hasRecordPitch
            ? cli.recordPitchDeg
            : compositionValue(composition, &ShowcaseOrbitComposition::pitchDeg, -6.0f);
    camMutable.roll = 0.0f;
    camMutable.distance =
        cli.hasRecordDistance
            ? cli.recordDistance
            : compositionValue(composition, &ShowcaseOrbitComposition::distance, 14.0f);
    camMutable.fov = cli.hasRecordFov
                         ? cli.recordFovDeg
                         : compositionValue(composition, &ShowcaseOrbitComposition::fovDeg, 37.2738f);
    rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
    rs.physicsCore.kerrSpin = K_SHOWCASE_ORBIT_SPIN;
    rs.recording.recordCurrentKf = CamKeyframe{
        .timeSec = static_cast<float>(rs.recording.recordFrameIndex - cli.recordStartFrame) /
                   static_cast<float>(K_CINEMATIC_FPS),
        .cam = camMutable,
        .kerrSpin = rs.physicsCore.kerrSpin,
        .caption = "Showcase orbit",
    };
  } else {
    rs.recording.recordCurrentKf = CinematicPath::evaluate(rs.recording.recordCinematic);
    CameraState &camMutable = input.camera();
    camMutable   = rs.recording.recordCurrentKf.cam;
    rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
    rs.physicsCore.kerrSpin     = rs.recording.recordCurrentKf.kerrSpin;
  }
  // Every profile writes its own spin above; --record-spin overrides it last.
  if (cli.hasRecordSpin) {
    rs.physicsCore.kerrSpin = std::clamp(cli.recordSpin, -0.998f, 0.998f);
    rs.recording.recordCurrentKf.kerrSpin = rs.physicsCore.kerrSpin;
  }
}

void captureRecordFrame(RenderState &rs, const platform::CliOptions &cli) {
  // glfwSetWindowSize() is asynchronous; the resize callback fires in
  // glfwPollEvents(). Wait 15 warmup frames (~250ms) for the window and render
  // targets to settle at the requested size before capturing. If the WM caps
  // the window smaller, accept whatever size it settled at.
  if (cli.recordFramesDir.empty() || rs.recording.recordWarmup < 15 ||
      rs.targets.texTonemapped == 0 || rs.targets.renderWidth <= 0 || rs.targets.renderHeight <= 0) {
    return;
  }
  // Capture the tonemapped scene texture rather than the default framebuffer,
  // which is mostly ImGui chrome. The cinematic HUD is composited later by
  // ffmpeg drawtext; it is drawn in the ImGui frame for live preview only.
  std::vector<unsigned char> flipped;
  int w = 0;
  int h = 0;
  if (!readTonemappedRgb(rs.targets.texTonemapped, rs.targets.renderWidth, rs.targets.renderHeight,
                         flipped, w, h)) {
    return;
  }
  const std::string framePath =
      std::format("{}/frame_{:06d}.png", cli.recordFramesDir, rs.recording.recordFrameIndex);
  if (stbi_write_png(framePath.c_str(), w, h, 3, flipped.data(), w * 3) == 0) {
    throw std::runtime_error("Failed to write recorded frame: " + framePath);
  }
  if (rs.recording.recordFrameIndex == cli.recordStartFrame) {
    // The post settings this frame rendered with, so a capture records the
    // profile it actually used.
    std::printf("Record post: exposure=%.3f bloom=%.3f x%d gamma=%.2f tonemap=%d\n",
                static_cast<double>(rs.post.toneExposure), static_cast<double>(rs.post.bloomStrength),
                rs.post.bloomIterations, static_cast<double>(rs.post.gamma),
                rs.post.tonemappingEnabled ? 1 : 0);
  }
  if (rs.recording.recordFrameIndex % K_CINEMATIC_FPS == 0) {
    std::printf("Record: frame %d / %d  (t = %.1f s)  [%dx%d]\n",
                rs.recording.recordFrameIndex, cli.recordFramesTotal,
                static_cast<double>(rs.recording.recordCinematic), w, h);
  }
  ++rs.recording.recordFrameIndex;
  rs.recording.recordCinematic = static_cast<float>(rs.recording.recordFrameIndex) / static_cast<float>(K_CINEMATIC_FPS);
}

void exportFrameOnce(RenderState &rs, const platform::CliOptions &cli) {
  if (cli.exportFramePath.empty() && cli.exportRawFramePath.empty()) {
    return;
  }
  // Warm up 5 frames so the scene has settled, then export once.
  if (++rs.exporting.exportWarmup < 5 || rs.exporting.exportPerformed ||
      rs.targets.renderWidth <= 0 || rs.targets.renderHeight <= 0) {
    return;
  }
  if (!cli.exportFramePath.empty()) {
    std::vector<unsigned char> flipped;
    int w = 0;
    int h = 0;
    if (readTonemappedRgb(rs.targets.texTonemapped, rs.targets.renderWidth, rs.targets.renderHeight,
                          flipped, w, h)) {
      stbi_write_png(cli.exportFramePath.c_str(), w, h, 3, flipped.data(), w * 3);
      std::printf("Exported frame: %s (%dx%d)\n", cli.exportFramePath.c_str(), w, h);
    }
  }

  if (!cli.exportRawFramePath.empty() && rs.targets.texBlackhole != 0) {
    GLint texW = 0;
    GLint texH = 0;
    glBindTexture(GL_TEXTURE_2D, rs.targets.texBlackhole);
    glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_WIDTH, &texW);
    glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_HEIGHT, &texH);
    glBindTexture(GL_TEXTURE_2D, 0);
    int const w = (texW > 0) ? texW : rs.targets.renderWidth;
    int const h = (texH > 0) ? texH : rs.targets.renderHeight;
    std::vector<float> raw;
    if (readTextureRGBA(rs.targets.texBlackhole, w, h, raw) &&
        writePfmRgb(cli.exportRawFramePath, raw, w, h)) {
      std::printf("Exported raw frame: %s (%dx%d)\n", cli.exportRawFramePath.c_str(), w, h);
    } else {
      std::cerr << "Failed to export raw frame: " << cli.exportRawFramePath << '\n';
    }
  }
  rs.exporting.exportPerformed = true;
}

} // namespace blackhole
