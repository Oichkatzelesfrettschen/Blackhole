/**
 * @file camera_math_test.cpp
 * @brief Unit tests for the render-loop camera pose math.
 *
 * cameraPositionFromYawPitch and buildCameraBasis are pure; selectCameraPosition
 * reads and clamps RenderState camera fields, so these tests link the test-only
 * blackhole_testcore library to construct RenderState without the app
 * executables. They assert the spherical placement identities, the orthonormal
 * basis (including the world-up degeneracy fallback and roll), and each
 * CameraMode branch plus the mode/orbit clamps, and the distance scaling of the
 * zoom rates.
 */

#include <cmath>
#include <filesystem>
#include <fstream>
#include <memory>
#include <sstream>
#include <string>
#include <system_error>

#include <gtest/gtest.h>

#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/geometric.hpp>

#include "input.h"
#include "platform/cli_options.h"
#include "render/camera_math.h"
#include "render/record_mode.h"
#include "render/render_state.h"
#include "render/renderer_contract.h"

using blackhole::buildCameraBasis;
using blackhole::cameraPositionFromYawPitch;
using blackhole::RenderState;
using blackhole::selectCameraPosition;

namespace {

constexpr float K_TOL = 1e-4f;

void expectVecNear(const glm::vec3 &actual, const glm::vec3 &expected, float tol = K_TOL) {
  EXPECT_NEAR(actual.x, expected.x, tol);
  EXPECT_NEAR(actual.y, expected.y, tol);
  EXPECT_NEAR(actual.z, expected.z, tol);
}

std::string sourceText(const char *relativePath) {
  const auto root = std::filesystem::path(__FILE__).parent_path().parent_path();
  const std::ifstream input(root / relativePath);
  EXPECT_TRUE(input.good()) << relativePath;
  std::ostringstream contents;
  contents << input.rdbuf();
  return contents.str();
}

} // namespace

TEST(RendererContract, StartupAndReferenceBudget) {
  const blackhole::RendererContract contract;
  EXPECT_EQ(contract.backend, blackhole::RenderBackend::Fragment);
  EXPECT_EQ(contract.geodesic, blackhole::GeodesicModel::KerrReference);
  EXPECT_EQ(contract.radiative, blackhole::RadiativeModel::ThinSurface);
  EXPECT_EQ(contract.quality, blackhole::QualityTier::Balanced);
  // Reference covers twice the selected affine range at step 0.02, and at
  // least 40: 300 x 0.1 = 30 -> 60 -> 3001 steps; 500 x 0.04 = 20 -> 40.
  EXPECT_EQ(blackhole::rendererStepBudget(blackhole::QualityTier::Reference, 300, 0.1f), 3001);
  EXPECT_EQ(blackhole::rendererStepBudget(blackhole::QualityTier::Reference, 500, 0.04f), 2001);
  EXPECT_EQ(blackhole::rendererStepBudget(blackhole::QualityTier::Reference, 1, 0.01f), 2001);
  EXPECT_EQ(blackhole::rendererStepBudget(blackhole::QualityTier::Reference, 100000, 1.0f),
            blackhole::K_REFERENCE_MAX_STEPS);
  EXPECT_FLOAT_EQ(blackhole::rendererStepSize(blackhole::QualityTier::Reference, 0.1f), 0.02f);
  EXPECT_EQ(blackhole::rendererStepBudget(blackhole::QualityTier::Interactive, 500, 0.04f), 300);
  EXPECT_FLOAT_EQ(blackhole::rendererStepSize(blackhole::QualityTier::Interactive, 0.02f), 0.1f);
  blackhole::RendererContract legacy = contract;
  legacy.geodesic = blackhole::GeodesicModel::LegacyBeauty;
  EXPECT_EQ(blackhole::rendererStepBudget(legacy, 1000, 0.02f), 300);
  EXPECT_FLOAT_EQ(blackhole::rendererStepSize(legacy, 0.02f), 0.1f);
  legacy.backend = blackhole::RenderBackend::Cuda;
  blackhole::normalizeRendererContract(legacy);
  EXPECT_EQ(legacy.geodesic, blackhole::GeodesicModel::KerrReference);
}

TEST(CameraMath, PhysicsFrameAndBackendProjectionContract) {
  const std::string glslTrace = sourceText("shader/include/interop_trace.glsl");
  const std::string glslKerr = sourceText("shader/include/kerr.glsl");
  const std::string cudaPhysics = sourceText("src/cuda/device_physics.cuh");
  EXPECT_NE(glslTrace.find("vec3(v.x, -v.z, v.y)"), std::string::npos);
  EXPECT_NE(cudaPhysics.find("make_f3(v.x, -v.z, v.y)"), std::string::npos);
  EXPECT_NE(glslTrace.find("vec3(v.x, v.z, -v.y)"), std::string::npos);
  EXPECT_NE(cudaPhysics.find("make_f3(v.x, v.z, -v.y)"), std::string::npos);
  EXPECT_NE(glslKerr.find("r * sinTheta * cos(phi)"), std::string::npos);
  EXPECT_NE(glslKerr.find("r * sinTheta * sin(phi)"), std::string::npos);
  EXPECT_NE(glslKerr.find("r * cos(theta)"), std::string::npos);
  EXPECT_NE(cudaPhysics.find("r * sin_t * cos_p"), std::string::npos);
  EXPECT_NE(cudaPhysics.find("r * sin_t * sin_p"), std::string::npos);
  EXPECT_NE(cudaPhysics.find("r * cos_t"), std::string::npos);
}

TEST(CameraMath, SpinDependentIscoUniformContract) {
  EXPECT_NE(sourceText("shader/blackhole_main.frag").find("uniform float iscoRadius"),
            std::string::npos);
  EXPECT_NE(sourceText("shader/geodesic_trace.comp").find("uniform float iscoRadius"),
            std::string::npos);
}

// Yaw 0 looks down +Z; yaw 90 swings to +X; pitch 90 points straight up. Radius
// scales the unit direction.
TEST(CameraMath, YawPitchPlacement) {
  expectVecNear(cameraPositionFromYawPitch(0.0f, 0.0f, 5.0f), glm::vec3(0.0f, 0.0f, 5.0f));
  expectVecNear(cameraPositionFromYawPitch(90.0f, 0.0f, 5.0f), glm::vec3(5.0f, 0.0f, 0.0f));
  expectVecNear(cameraPositionFromYawPitch(0.0f, 90.0f, 5.0f), glm::vec3(0.0f, 5.0f, 0.0f));
  // Radius is the norm of the returned vector for any angle.
  glm::vec3 const p = cameraPositionFromYawPitch(37.0f, -21.0f, 8.0f);
  EXPECT_NEAR(glm::length(p), 8.0f, K_TOL);
}

// The basis columns are unit length, mutually orthogonal, and forward points
// from the camera toward the target.
TEST(CameraMath, BasisOrthonormal) {
  glm::mat3 const basis = buildCameraBasis(glm::vec3(0.0f, 0.0f, 10.0f), glm::vec3(0.0f), 0.0f);
  glm::vec3 const right = basis[0];
  glm::vec3 const up = basis[1];
  glm::vec3 const forward = basis[2];
  EXPECT_NEAR(glm::length(right), 1.0f, K_TOL);
  EXPECT_NEAR(glm::length(up), 1.0f, K_TOL);
  EXPECT_NEAR(glm::length(forward), 1.0f, K_TOL);
  EXPECT_NEAR(glm::dot(right, up), 0.0f, K_TOL);
  EXPECT_NEAR(glm::dot(right, forward), 0.0f, K_TOL);
  EXPECT_NEAR(glm::dot(up, forward), 0.0f, K_TOL);
  expectVecNear(forward, glm::vec3(0.0f, 0.0f, -1.0f));
}

// Looking straight down (forward nearly parallel to world-up) still yields an
// orthonormal basis via the +Z world-axis fallback.
TEST(CameraMath, BasisWorldUpDegeneracy) {
  glm::mat3 const basis = buildCameraBasis(glm::vec3(0.0f, 10.0f, 0.0f), glm::vec3(0.0f), 0.0f);
  EXPECT_NEAR(glm::length(basis[0]), 1.0f, K_TOL);
  EXPECT_NEAR(glm::length(basis[1]), 1.0f, K_TOL);
  EXPECT_NEAR(glm::dot(basis[0], basis[1]), 0.0f, K_TOL);
  expectVecNear(basis[2], glm::vec3(0.0f, -1.0f, 0.0f));
}

// A 90-degree roll rotates right onto the old up direction.
TEST(CameraMath, BasisRoll) {
  glm::mat3 const noRoll = buildCameraBasis(glm::vec3(0.0f, 0.0f, 10.0f), glm::vec3(0.0f), 0.0f);
  glm::mat3 const rolled = buildCameraBasis(glm::vec3(0.0f, 0.0f, 10.0f), glm::vec3(0.0f), 90.0f);
  expectVecNear(rolled[0], noRoll[1]);
  expectVecNear(rolled[2], noRoll[2]); // forward is unchanged by roll
}

// Input mode places the camera at the yaw/pitch offset from the focus target.
TEST(CameraMath, SelectInputMode) {
  const auto rsStorage = std::make_unique<RenderState>();
  RenderState &rs = *rsStorage;
  rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
  CameraState const cam{.yaw = 90.0f, .pitch = 0.0f, .roll = 0.0f, .distance = 5.0f, .fov = 45.0f};
  glm::vec3 const focus(1.0f, 2.0f, 3.0f);
  expectVecNear(selectCameraPosition(rs, cam, focus), focus + glm::vec3(5.0f, 0.0f, 0.0f));
}

// Front and Top are fixed offsets from the focus target.
TEST(CameraMath, SelectFixedModes) {
  const auto rsStorage = std::make_unique<RenderState>();
  RenderState &rs = *rsStorage;
  CameraState const cam{};
  glm::vec3 const focus(0.0f, 0.0f, 0.0f);

  rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Front);
  expectVecNear(selectCameraPosition(rs, cam, focus), glm::vec3(10.0f, 1.0f, 10.0f));

  rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Top);
  expectVecNear(selectCameraPosition(rs, cam, focus), glm::vec3(15.0f, 15.0f, 0.0f));
}

// Orbit at time 0 sits at radius on -X (cos 0 = 1) with y and z zero (sin 0 = 0).
TEST(CameraMath, SelectOrbitMode) {
  const auto rsStorage = std::make_unique<RenderState>();
  RenderState &rs = *rsStorage;
  rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Orbit);
  rs.camera.orbitRadius = 9.0f;
  rs.camera.orbitSpeed = 3.0f;
  rs.camera.orbitTime = 0.0f;
  CameraState const cam{};
  expectVecNear(selectCameraPosition(rs, cam, glm::vec3(0.0f)), glm::vec3(-9.0f, 0.0f, 0.0f));
}

// Out-of-range mode and sub-floor orbit fields are clamped in place.
TEST(CameraMath, SelectClampsFields) {
  const auto rsStorage = std::make_unique<RenderState>();
  RenderState &rs = *rsStorage;
  rs.camera.cameraModeIndex = 99; // clamps to 3 (Orbit)
  rs.camera.orbitRadius = 0.5f;   // clamps to 2.0
  rs.camera.orbitSpeed = -4.0f;   // clamps to 0.0
  rs.camera.orbitTime = 0.0f;
  CameraState const cam{};

  glm::vec3 const pos = selectCameraPosition(rs, cam, glm::vec3(0.0f));

  EXPECT_EQ(rs.camera.cameraModeIndex, 3);
  EXPECT_FLOAT_EQ(rs.camera.orbitRadius, 2.0f);
  EXPECT_FLOAT_EQ(rs.camera.orbitSpeed, 0.0f);
  // Orbit at speed 0, radius 2: angle 0 -> position (-2, 0, 0).
  expectVecNear(pos, glm::vec3(-2.0f, 0.0f, 0.0f));
}

// Zoom rates scale with distance: unchanged at the reference distance,
// proportional beyond it, and floored at the minimum camera distance.
TEST(CameraMath, ZoomRateScalesWithDistance) {
  EXPECT_FLOAT_EQ(zoomRateScale(K_ZOOM_RATE_REFERENCE_DISTANCE), 1.0f);
  EXPECT_FLOAT_EQ(zoomRateScale(240.0f), 16.0f);
  EXPECT_FLOAT_EQ(zoomRateScale(0.0f), K_CAMERA_MIN_DISTANCE / K_ZOOM_RATE_REFERENCE_DISTANCE);
  // The distance range reaches past the disk's 100 r_s = 200 unit outer edge.
  EXPECT_GT(K_CAMERA_MAX_DISTANCE, 200.0f);
}

// The showcase-orbit camera path drives the profile's spin every frame, and
// --record-spin replaces it.
TEST(RecordCameraPath, ShowcaseFramesUseTheProfileSpin) {
  const auto rsStorage = std::make_unique<RenderState>();
  RenderState &rs = *rsStorage;
  platform::CliOptions cli;
  cli.recordFramesDir = "frames";
  cli.recordProfile = "showcase-orbit";
  rs.physicsCore.kerrSpin = 0.0f;
  blackhole::applyRecordCameraPath(rs, cli, InputManager::instance());
  EXPECT_FLOAT_EQ(rs.physicsCore.kerrSpin, blackhole::K_SHOWCASE_ORBIT_SPIN);
  EXPECT_FLOAT_EQ(rs.recording.recordCurrentKf.kerrSpin, blackhole::K_SHOWCASE_ORBIT_SPIN);

  cli.hasRecordSpin = true;
  cli.recordSpin = 0.9f;
  blackhole::applyRecordCameraPath(rs, cli, InputManager::instance());
  EXPECT_FLOAT_EQ(rs.physicsCore.kerrSpin, 0.9f);
}

// depthFar normalizes the traced depth and bounds the gizmo frustum, so every
// showcase composition's camera distance plus the disk's 200-unit outer radius
// must fit inside it.
TEST(RecordProfileSetup, ShowcaseDepthFarHoldsTheCameraAndTheDisk) {
  const auto frames = std::filesystem::path(testing::TempDir()) / "record-depth-far";
  for (const char *const name : {"above-disk", "inside-disk", "centered", "left-third",
                                 "right-third", "wide-left", "wide-right"}) {
    const auto rsStorage = std::make_unique<RenderState>();
    RenderState &rs = *rsStorage;
    platform::CliOptions cli;
    cli.recordFramesDir = frames.string();
    cli.recordProfile = "showcase-orbit";
    cli.recordComposition = name;
    InputManager &input = InputManager::instance();
    ASSERT_TRUE(blackhole::applyRecordProfileSetup(rs, cli, input, nullptr)) << name;
    EXPECT_GT(rs.display.depthFar, input.camera().distance + 200.0f) << name;
  }
  std::error_code ignored;
  std::filesystem::remove_all(frames, ignored);
}
