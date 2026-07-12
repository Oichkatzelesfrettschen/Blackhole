/**
 * @file camera_math.cpp
 * @brief Camera pose math: spherical placement, orthonormal basis, per-mode select.
 */

#include "render/camera_math.h"

#include <algorithm>
#include <cmath>

#include "input.h"               // CameraState, CameraMode
#include "render/render_state.h" // RenderState

namespace blackhole {

glm::vec3 cameraPositionFromYawPitch(float yawDeg, float pitchDeg, float radius) {
  float const yawRad = glm::radians(yawDeg);
  float const pitchRad = glm::radians(pitchDeg);
  return {radius * std::cos(pitchRad) * std::sin(yawRad), radius * std::sin(pitchRad),
          radius * std::cos(pitchRad) * std::cos(yawRad)};
}

glm::mat3 buildCameraBasis(const glm::vec3 &cameraPos, const glm::vec3 &target, float rollDeg) {
  glm::vec3 const forward = glm::normalize(target - cameraPos);
  glm::vec3 worldUp(0.0f, 1.0f, 0.0f);
  if (std::abs(glm::dot(forward, worldUp)) > 0.99f) {
    worldUp = glm::vec3(0.0f, 0.0f, 1.0f);
  }

  glm::vec3 right = glm::normalize(glm::cross(forward, worldUp));
  glm::vec3 up = glm::normalize(glm::cross(right, forward));

  if (std::abs(rollDeg) > 0.001f) {
    float const rollRad = glm::radians(rollDeg);
    float const cosRoll = std::cos(rollRad);
    float const sinRoll = std::sin(rollRad);
    glm::vec3 const rolledRight = right * cosRoll + up * sinRoll;
    glm::vec3 const rolledUp = -right * sinRoll + up * cosRoll;
    right = rolledRight;
    up = rolledUp;
  }

  return {right, up, forward};
}

glm::vec3 selectCameraPosition(RenderState &rs, const CameraState &cam, const glm::vec3 &focusTarget) {
  rs.camera.cameraModeIndex = std::clamp(rs.camera.cameraModeIndex, 0, 3);
  rs.camera.orbitRadius = std::max(rs.camera.orbitRadius, 2.0f);
  rs.camera.orbitSpeed = std::max(rs.camera.orbitSpeed, 0.0f);

  auto const cameraMode = static_cast<CameraMode>(rs.camera.cameraModeIndex);
  switch (cameraMode) {
  case CameraMode::Front:
    return focusTarget + glm::vec3(10.0f, 1.0f, 10.0f);
  case CameraMode::Top:
    return focusTarget + glm::vec3(15.0f, 15.0f, 0.0f);
  case CameraMode::Orbit: {
    float const angle = rs.camera.orbitTime * glm::radians(rs.camera.orbitSpeed);
    return focusTarget + glm::vec3(-std::cos(angle) * rs.camera.orbitRadius, std::sin(angle) * rs.camera.orbitRadius,
                                   std::sin(angle) * rs.camera.orbitRadius);
  }
  case CameraMode::Input:
  default:
    return focusTarget + cameraPositionFromYawPitch(cam.yaw, cam.pitch, cam.distance);
  }
}

} // namespace blackhole
