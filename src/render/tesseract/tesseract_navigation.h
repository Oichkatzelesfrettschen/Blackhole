/**
 * @file tesseract_navigation.h
 * @brief Free-fly camera and 4D slice rotation state of the tesseract scene.
 *
 * The camera looks along forward(yaw, pitch) = (sin yaw cos pitch, sin pitch,
 * cos yaw cos pitch): yaw 0, pitch 0 looks along +z, positive yaw turns
 * toward +x, positive pitch looks up (+y). navigationBasis returns the
 * columns (right, up, forward) of buildCameraBasis (src/render/camera_math.cpp)
 * for that direction with world up +y, so right = normalize(cross(forward, +y)).
 *
 * The 4D rotation is R_xw(a0) R_yw(a1) R_zw(a2): Givens rotations in the planes
 * spanned by the slice axis k and the w axis (index 3), acting on the
 * row-major Mat4<double> of so4.h. It is applied to the slice frame after the
 * scene's own SO(4) blend, so the user turns the hyperplane through the
 * fourth dimension independent of the scene rotation.
 *
 * The header is GL-free.
 */

#ifndef BLACKHOLE_RENDER_TESSERACT_TESSERACT_NAVIGATION_H
#define BLACKHOLE_RENDER_TESSERACT_TESSERACT_NAVIGATION_H

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <numbers>

#include <glm/ext/matrix_double3x3.hpp>
#include <glm/ext/vector_double3.hpp>
#include <glm/geometric.hpp>
#include <glm/trigonometric.hpp>

#include "render/tesseract/so4.h"

namespace blackhole::tesseract {

/// Pitch limit in degrees; the basis stays away from the +y pole.
inline constexpr double NAVIGATION_MAX_PITCH_DEG = 89.0;

/** @brief One frame of navigation input. */
struct NavigationInput {
  double forward = 0; ///< [-1, 1] along forward.
  double right = 0;   ///< [-1, 1] along right.
  double up = 0;      ///< [-1, 1] along up.
  double lookYawDeg = 0;   ///< Yaw delta this frame, degrees.
  double lookPitchDeg = 0; ///< Pitch delta this frame, degrees.
  std::array<double, 3> wRate{}; ///< xw, yw, zw plane rates, each in [-1, 1].
};

/** @brief Accumulated free-fly pose and 4D plane angles. */
struct NavigationState {
  double yawDeg = 0;
  double pitchDeg = 0;
  glm::dvec3 offset{0.0};        ///< World-space displacement from the start pose.
  std::array<double, 3> wAngles{}; ///< xw, yw, zw plane angles, radians in (-pi, pi].
};

/** @brief Columns (right, up, forward) for @p yawDeg and @p pitchDeg (see file comment). */
inline glm::dmat3 navigationBasis(double yawDeg, double pitchDeg) {
  const double yaw = glm::radians(yawDeg);
  const double pitch = glm::radians(pitchDeg);
  const glm::dvec3 forward(std::sin(yaw) * std::cos(pitch), std::sin(pitch),
                           std::cos(yaw) * std::cos(pitch));
  const glm::dvec3 right = glm::normalize(glm::cross(forward, glm::dvec3(0.0, 1.0, 0.0)));
  const glm::dvec3 up = glm::cross(right, forward);
  return {right, up, forward};
}

/**
 * @brief Advance @p state by @p input over @p dtSeconds.
 *
 * Yaw adds its look delta and wraps into (-180, 180]; pitch adds its delta,
 * clamped to +-NAVIGATION_MAX_PITCH_DEG;
 * the offset moves along the basis of the updated look at @p moveSpeed world
 * units per second; each w angle advances by wRate * wTurnRate * dt radians
 * and wraps into (-pi, pi].
 */
inline void advanceNavigation(NavigationState &state, const NavigationInput &input,
                              double dtSeconds, double moveSpeed, double wTurnRate) {
  state.yawDeg = std::remainder(state.yawDeg + input.lookYawDeg, 360.0);
  if (state.yawDeg <= -180.0) {
    state.yawDeg += 360.0;
  }
  state.pitchDeg = std::clamp(state.pitchDeg + input.lookPitchDeg, -NAVIGATION_MAX_PITCH_DEG,
                              NAVIGATION_MAX_PITCH_DEG);
  const glm::dmat3 basis = navigationBasis(state.yawDeg, state.pitchDeg);
  state.offset += basis * glm::dvec3(input.right, input.up, input.forward) * (moveSpeed * dtSeconds);
  constexpr double pi = std::numbers::pi;
  for (std::size_t k = 0; k < state.wAngles.size(); ++k) {
    double angle = state.wAngles.at(k) + (input.wRate.at(k) * wTurnRate * dtSeconds);
    angle = std::remainder(angle, 2.0 * pi);
    if (angle <= -pi) {
      angle += 2.0 * pi;
    }
    state.wAngles.at(k) = angle;
  }
}

/** @brief R_xw(a0) R_yw(a1) R_zw(a2), orthogonal with determinant +1. */
inline Mat4<double> wPlaneRotation(const std::array<double, 3> &wAngles) {
  const auto givens = [](std::size_t axis, double angle) {
    Mat4<double> m{};
    for (std::size_t i = 0; i < 4; ++i) {
      m.at(i).at(i) = 1.0;
    }
    const double c = std::cos(angle);
    const double s = std::sin(angle);
    m.at(axis).at(axis) = c;
    m.at(axis).at(3) = -s;
    m.at(3).at(axis) = s;
    m.at(3).at(3) = c;
    return m;
  };
  return multiply(multiply(givens(0, wAngles.at(0)), givens(1, wAngles.at(1))),
                  givens(2, wAngles.at(2)));
}

} // namespace blackhole::tesseract

#endif // BLACKHOLE_RENDER_TESSERACT_TESSERACT_NAVIGATION_H
