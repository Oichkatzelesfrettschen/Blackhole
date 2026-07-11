/**
 * @file camera_math.h
 * @brief Camera pose math for the render loop: spherical placement, orthonormal
 *        basis, and per-mode camera-position selection.
 *
 * cameraPositionFromYawPitch and buildCameraBasis are pure functions of their
 * arguments (no RenderState). selectCameraPosition clamps the RenderState camera
 * mode/orbit fields and returns the world-space camera position for the active
 * CameraMode about a focus target; the caller advances orbitTime and computes
 * the focus target (gizmo-dependent) before calling it.
 */

#ifndef BLACKHOLE_RENDER_CAMERA_MATH_H
#define BLACKHOLE_RENDER_CAMERA_MATH_H

#include <glm/glm.hpp>

struct CameraState;

namespace blackhole {

struct RenderState;

/** @brief World-space camera position on a sphere of the given radius from
 *         yaw/pitch in degrees (yaw 0 = +Z, positive pitch above the equator). */
glm::vec3 cameraPositionFromYawPitch(float yawDeg, float pitchDeg, float radius);

/** @brief Orthonormal camera basis with columns [right, up, forward] looking
 *         from cameraPos to target, with rollDeg applied about forward. Falls
 *         back to the +Z world axis when forward is nearly parallel to world-up. */
glm::mat3 buildCameraBasis(const glm::vec3 &cameraPos, const glm::vec3 &target, float rollDeg);

/** @brief Clamps rs.camera mode/orbit fields to their valid ranges and returns
 *         the camera position for the active CameraMode about focusTarget.
 *         orbitTime is read as-is (the caller advances it for the frame). */
glm::vec3 selectCameraPosition(RenderState &rs, const CameraState &cam, const glm::vec3 &focusTarget);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_CAMERA_MATH_H
