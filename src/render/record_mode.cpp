/**
 * @file record_mode.cpp
 * @brief Showcase-orbit composition table, lookup, and beauty-wiregrid tuning.
 */

#include "render/record_mode.h"

#include <array>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <system_error>

#include <GLFW/glfw3.h>

#include "cinematic.h"           // K_CINEMATIC_KEYFRAMES / DURATION / FPS
#include "input.h"               // InputManager, CameraState, CameraMode
#include "platform/cli_options.h"
#include "render/render_state.h" // RenderState, WiregridParams
#include "settings.h"            // SettingsManager

namespace blackhole {
namespace {

constexpr std::array<ShowcaseOrbitComposition, 5> K_SHOWCASE_ORBIT_COMPOSITIONS = {{
    {"centered", "nasa_deep_starmap_galactic", 0.0f, 0.0f, -8.0f, 21.0f, 60.0f, 3.05f, 0.74f, -18.0f, 6.0f, 0.00f, 0.00f, 8.0f},
    {"left-third", "nasa_deep_starmap", 0.18f, 0.03f, -8.0f, 23.0f, 58.0f, 2.95f, 0.76f, -34.0f, 7.0f, 0.05f, -0.02f, 7.0f},
    {"right-third", "nasa_deep_starmap_galactic", -0.18f, 0.03f, -8.0f, 23.0f, 58.0f, 2.95f, 0.76f, 18.0f, 7.0f, -0.05f, -0.02f, 7.0f},
    {"wide-left", "eso_milkyway_brunier", 0.12f, -0.02f, -7.0f, 27.5f, 54.0f, 2.75f, 0.70f, -42.0f, 8.0f, 0.08f, -0.03f, 6.0f},
    {"wide-right", "nasa_deep_starmap_galactic", -0.12f, -0.02f, -7.0f, 27.5f, 54.0f, 2.9f, 0.80f, 26.0f, 8.0f, -0.08f, -0.03f, 6.0f},
}};

} // namespace

const ShowcaseOrbitComposition *findShowcaseOrbitComposition(std::string_view name) {
  for (const auto &composition : K_SHOWCASE_ORBIT_COMPOSITIONS) {
    if (name == composition.name) {
      return &composition;
    }
  }
  return nullptr;
}

void applyShowcaseBeautyWiregridTuning(std::string_view compositionName, WiregridParams &params,
                                       glm::vec4 &color) {
  if (params.mode != WiregridParams::Mode::Beauty) {
    return;
  }

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
    std::fprintf(stderr, "record output directory create failed: %s (%s)\n",
                 cli.recordFramesDir.c_str(), recordDirEc.message().c_str());
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
    rs.post.toneExposure       = 6.0f;
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
    rs.disk.dopplerStrength    = 1.15f;
    rs.disk.photonSphereGlowStrength = 1.15f;
    rs.post.bloomIterations    = 5;
    rs.post.bloomStrength      = 0.055f;
    rs.post.tonemappingEnabled = true;
    rs.post.toneExposure       = 1.0f;
    rs.post.gamma              = 2.35f;
    rs.dispatch.computeMaxSteps    = 1000;
    rs.dispatch.computeStepSize    = 0.016f;
    rs.display.depthFar           = 154.367004f;
    rs.physicsCore.kerrSpin           = 0.62f;
    SettingsManager::instance().get().backgroundId =
        cli.hasRecordBackgroundId
            ? cli.recordBackgroundId
            : (composition != nullptr ? composition->backgroundId
                                      : "nasa_deep_starmap_galactic");
    SettingsManager::instance().get().backgroundEnabled = true;
    SettingsManager::instance().get().backgroundIntensity =
        composition != nullptr ? composition->backgroundIntensity : 0.72f;
    CameraState &camMutable = input.camera();
    camMutable = CameraState{
        .yaw = cli.hasRecordYaw ? cli.recordYawDeg : -90.0f,
        .pitch = cli.hasRecordPitch ? cli.recordPitchDeg
                                    : (composition != nullptr ? composition->pitchDeg : -6.0f),
        .roll = 0.0f,
        .distance = cli.hasRecordDistance ? cli.recordDistance
                                          : (composition != nullptr ? composition->distance
                                                                    : 14.0f),
        .fov = cli.hasRecordFov ? cli.recordFovDeg
                                : (composition != nullptr ? composition->fovDeg : 68.0f)};
    if (cli.hasRecordExposure) {
      rs.post.toneExposure = cli.recordExposure;
    } else if (composition != nullptr) {
      rs.post.toneExposure = composition->exposure;
    }
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
    rs.post.toneExposure       = 0.02f;
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
    SettingsManager::instance().get().backgroundIntensity = 0.8f;
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
        cli.hasRecordSweep ? cli.recordSweepDeg
                           : (composition != nullptr ? composition->sweepDeg : 10.0f);
    CameraState &camMutable = input.camera();
    camMutable.yaw = baseYaw + progress * sweepDeg;
    camMutable.pitch = cli.hasRecordPitch ? cli.recordPitchDeg
                                          : (composition != nullptr ? composition->pitchDeg
                                                                    : -6.0f);
    camMutable.roll = 0.0f;
    camMutable.distance = cli.hasRecordDistance ? cli.recordDistance
                                                : (composition != nullptr
                                                       ? composition->distance
                                                       : 14.0f);
    camMutable.fov = cli.hasRecordFov ? cli.recordFovDeg
                                      : (composition != nullptr ? composition->fovDeg : 68.0f);
    rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
    rs.physicsCore.kerrSpin = 0.0f;
    rs.recording.recordCurrentKf = CamKeyframe{
        .t_sec = static_cast<float>(rs.recording.recordFrameIndex - cli.recordStartFrame) /
                 static_cast<float>(K_CINEMATIC_FPS),
        .cam = camMutable,
        .kerrSpin = rs.physicsCore.kerrSpin,
        .caption = "Showcase orbit",
    };
  } else {
    rs.recording.recordCurrentKf = rs.recording.recordPath.evaluate(rs.recording.recordCinematic);
    CameraState &camMutable = input.camera();
    camMutable   = rs.recording.recordCurrentKf.cam;
    rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
    rs.physicsCore.kerrSpin     = rs.recording.recordCurrentKf.kerrSpin;
  }
}

} // namespace blackhole
