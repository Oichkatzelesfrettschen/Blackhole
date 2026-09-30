/**
 * @file tesseract_navigation_test.cpp
 * @brief Free-fly basis, 4D plane rotation, navigation stepping, and the user
 *        rotation of the slice frame.
 *
 * Tolerances: 1e-12 for double arithmetic on unit-scale quantities; the
 * buildCameraBasis comparison runs against float outputs and uses 1e-6.
 */

#include <array>
#include <cmath>
#include <cstddef>
#include <numbers>
#include <random>

#include <glm/glm.hpp>
#include <gtest/gtest.h>

#include "render/camera_math.h"
#include "render/tesseract/so4.h"
#include "render/tesseract/tesseract_navigation.h"
#include "render/tesseract/tesseract_renderer.h"

namespace {

using blackhole::tesseract::advanceNavigation;
using blackhole::tesseract::Mat4;
using blackhole::tesseract::NavigationInput;
using blackhole::tesseract::NavigationState;
using blackhole::tesseract::navigationBasis;
using blackhole::tesseract::wPlaneRotation;

constexpr double TIGHT = 1e-12;
constexpr double PI = std::numbers::pi;

double det4(const Mat4<double> &m) {
  // Laplace expansion along the first row over 3x3 minors.
  double det = 0.0;
  for (std::size_t c = 0; c < 4; ++c) {
    std::array<std::array<double, 3>, 3> minor{};
    for (std::size_t r = 1; r < 4; ++r) {
      std::size_t mc = 0;
      for (std::size_t k = 0; k < 4; ++k) {
        if (k != c) {
          minor.at(r - 1).at(mc++) = m.at(r).at(k);
        }
      }
    }
    const double d3 =
        (minor[0][0] * ((minor[1][1] * minor[2][2]) - (minor[1][2] * minor[2][1]))) -
        (minor[0][1] * ((minor[1][0] * minor[2][2]) - (minor[1][2] * minor[2][0]))) +
        (minor[0][2] * ((minor[1][0] * minor[2][1]) - (minor[1][1] * minor[2][0])));
    det += (c % 2 == 0 ? 1.0 : -1.0) * m.at(0).at(c) * d3;
  }
  return det;
}

void expectOrthogonal(const Mat4<double> &m) {
  for (std::size_t i = 0; i < 4; ++i) {
    for (std::size_t j = 0; j < 4; ++j) {
      double dot = 0.0;
      for (std::size_t k = 0; k < 4; ++k) {
        dot += m.at(k).at(i) * m.at(k).at(j);
      }
      EXPECT_NEAR(dot, i == j ? 1.0 : 0.0, TIGHT) << i << "," << j;
    }
  }
  EXPECT_NEAR(det4(m), 1.0, TIGHT);
}

std::array<double, 3> randomAngles(std::mt19937 &rng) {
  std::uniform_real_distribution<double> dist(-PI, PI);
  return {dist(rng), dist(rng), dist(rng)};
}

// The columns (right, up, forward) with right = cross(forward, +y) form a
// left-handed frame, determinant -1, exactly as buildCameraBasis does; the
// shader's bhRayDir convention fixes that handedness.
TEST(TesseractNavigation, BasisIsOrthonormalAndMatchesTheCameraHandedness) {
  for (double yaw = -360.0; yaw <= 360.0; yaw += 37.0) {
    for (double pitch = -89.0; pitch <= 89.0; pitch += 22.25) {
      const glm::dmat3 b = navigationBasis(yaw, pitch);
      const glm::dmat3 gram = glm::transpose(b) * b;
      for (int i = 0; i < 3; ++i) {
        for (int j = 0; j < 3; ++j) {
          EXPECT_NEAR(gram[i][j], i == j ? 1.0 : 0.0, TIGHT) << yaw << "," << pitch;
        }
      }
      EXPECT_NEAR(glm::determinant(b), -1.0, TIGHT) << yaw << "," << pitch;
    }
  }
}

TEST(TesseractNavigation, BasisMatchesBuildCameraBasis) {
  const std::array<std::array<double, 2>, 5> cases{
      {{0.0, 0.0}, {90.0, 0.0}, {-45.0, 30.0}, {170.0, -60.0}, {33.0, 45.0}}};
  for (const auto &angles : cases) {
    const glm::dmat3 b = navigationBasis(angles[0], angles[1]);
    const glm::vec3 forward(b[2]);
    const glm::mat3 reference =
        blackhole::buildCameraBasis(glm::vec3(0.0f), forward, 0.0f);
    for (int c = 0; c < 3; ++c) {
      for (int r = 0; r < 3; ++r) {
        EXPECT_NEAR(b[c][r], static_cast<double>(reference[c][r]), 1e-6)
            << angles[0] << "," << angles[1] << " col " << c;
      }
    }
  }
}

TEST(TesseractNavigation, DocumentedAxes) {
  const glm::dmat3 zero = navigationBasis(0.0, 0.0);
  EXPECT_NEAR(zero[2].z, 1.0, TIGHT);
  const glm::dmat3 yawed = navigationBasis(90.0, 0.0);
  EXPECT_NEAR(yawed[2].x, 1.0, TIGHT);
  const glm::dmat3 pitched = navigationBasis(0.0, 45.0);
  EXPECT_NEAR(pitched[2].y, std::sqrt(0.5), TIGHT);
  EXPECT_NEAR(pitched[1].y, std::sqrt(0.5), TIGHT);
  EXPECT_NEAR(pitched[1].z, -std::sqrt(0.5), TIGHT);
}

TEST(TesseractNavigation, WPlaneRotationIsSpecialOrthogonal) {
  std::mt19937 rng(20240611U);
  for (int i = 0; i < 50; ++i) {
    expectOrthogonal(wPlaneRotation(randomAngles(rng)));
  }
}

TEST(TesseractNavigation, EachPlaneRotationFixesTheOtherAxes) {
  constexpr double ANGLE = 0.7;
  for (std::size_t k = 0; k < 3; ++k) {
    std::array<double, 3> angles{};
    angles.at(k) = ANGLE;
    const Mat4<double> m = wPlaneRotation(angles);
    for (std::size_t axis = 0; axis < 3; ++axis) {
      if (axis == k) {
        continue;
      }
      for (std::size_t r = 0; r < 4; ++r) {
        EXPECT_NEAR(m.at(r).at(axis), r == axis ? 1.0 : 0.0, TIGHT) << k << "," << axis;
      }
    }
    EXPECT_NEAR(m.at(k).at(k), std::cos(ANGLE), TIGHT);
    EXPECT_NEAR(m.at(3).at(k), std::sin(ANGLE), TIGHT);
  }
}

blackhole::tesseract::Quat<double> randomUnitQuat(std::mt19937 &rng) {
  std::normal_distribution<double> dist(0.0, 1.0);
  return blackhole::tesseract::normalized(
      blackhole::tesseract::Quat<double>{.w = dist(rng), .x = dist(rng), .y = dist(rng), .z = dist(rng)});
}

TEST(TesseractNavigation, SliceFrameWithUserRotationStaysOrthonormal) {
  std::mt19937 rng(7U);
  for (int i = 0; i < 20; ++i) {
    const auto rotation = blackhole::tesseract::toColumnMajor(
        blackhole::tesseract::so4FromPair(randomUnitQuat(rng), randomUnitQuat(rng)));
    const auto slice = blackhole::tesseractSliceFrame(rotation, 1.3f, 12.0f,
                                                      glm::vec3(0.4f, -0.3f, 8.0f),
                                                      glm::dvec3(1.0, 2.0, 3.0),
                                                      wPlaneRotation(randomAngles(rng)));
    for (std::size_t a = 0; a < 3; ++a) {
      for (std::size_t b = 0; b < 3; ++b) {
        double dot = 0.0;
        for (std::size_t r = 0; r < 4; ++r) {
          dot += slice.axes.at(a).at(r) * slice.axes.at(b).at(r);
        }
        EXPECT_NEAR(dot, a == b ? 1.0 : 0.0, TIGHT) << a << "," << b;
      }
    }
  }
}

TEST(TesseractNavigation, IdentityUserRotationReproducesTheSliceFrameExactly) {
  std::mt19937 rng(11U);
  const auto rotation = blackhole::tesseract::toColumnMajor(
      blackhole::tesseract::so4FromPair(randomUnitQuat(rng), randomUnitQuat(rng)));
  const glm::vec3 eye(0.4f, -0.3f, 8.0f);
  const glm::dvec3 drift(1.0, 2.0, 3.0);
  const auto plain = blackhole::tesseractSliceFrame(rotation, 1.3f, 12.0f, eye, drift);
  const auto withIdentity = blackhole::tesseractSliceFrame(
      rotation, 1.3f, 12.0f, eye, drift, wPlaneRotation({0.0, 0.0, 0.0}));
  EXPECT_EQ(plain.axes, withIdentity.axes);
  EXPECT_EQ(plain.eye, withIdentity.eye);
}

TEST(TesseractNavigation, ForwardFlightIsDeterministic) {
  NavigationState state;
  NavigationInput input;
  input.forward = 1.0;
  advanceNavigation(state, input, 2.0, 3.0, 0.6);
  EXPECT_NEAR(state.offset.x, 0.0, TIGHT);
  EXPECT_NEAR(state.offset.y, 0.0, TIGHT);
  EXPECT_NEAR(state.offset.z, 6.0, TIGHT);
}

TEST(TesseractNavigation, RightAndUpFollowTheBasisColumns) {
  NavigationState state;
  NavigationInput input;
  input.right = 1.0;
  input.up = 1.0;
  advanceNavigation(state, input, 1.0, 2.0, 0.6);
  const glm::dmat3 basis = navigationBasis(0.0, 0.0);
  const glm::dvec3 expected = (basis[0] + basis[1]) * 2.0;
  EXPECT_NEAR(state.offset.x, expected.x, TIGHT);
  EXPECT_NEAR(state.offset.y, expected.y, TIGHT);
  EXPECT_NEAR(state.offset.z, expected.z, TIGHT);
}

TEST(TesseractNavigation, YawThenForwardMovesAlongPlusX) {
  NavigationState state;
  NavigationInput turn;
  turn.lookYawDeg = 90.0;
  advanceNavigation(state, turn, 0.0, 1.0, 0.6);
  NavigationInput fly;
  fly.forward = 1.0;
  advanceNavigation(state, fly, 1.0, 5.0, 0.6);
  EXPECT_NEAR(state.offset.x, 5.0, TIGHT);
  EXPECT_NEAR(state.offset.z, 0.0, TIGHT);
}

TEST(TesseractNavigation, WAnglesWrapIntoHalfOpenInterval) {
  NavigationState state;
  NavigationInput input;
  input.wRate = {1.0, -1.0, 1.0};
  for (int i = 0; i < 400; ++i) {
    advanceNavigation(state, input, 0.1, 0.0, 1.0);
    for (const double angle : state.wAngles) {
      EXPECT_GT(angle, -PI);
      EXPECT_LE(angle, PI);
    }
  }
  NavigationState exact;
  exact.wAngles = {-PI + 0.1, 0.0, 0.0};
  NavigationInput back;
  back.wRate = {-1.0, 0.0, 0.0};
  advanceNavigation(exact, back, 0.1, 0.0, 1.0);
  EXPECT_NEAR(exact.wAngles[0], PI, TIGHT);
}

// Yaw wraps into (-180, 180] however far the look turns, and the wrapped
// pose keeps the basis of the unwrapped one.
TEST(TesseractNavigation, YawWrapsIntoHalfOpenInterval) {
  NavigationState state;
  NavigationInput look;
  look.lookYawDeg = 50.0;
  for (int i = 0; i < 40; ++i) {
    advanceNavigation(state, look, 0.0, 0.0, 0.0);
    EXPECT_GT(state.yawDeg, -180.0);
    EXPECT_LE(state.yawDeg, 180.0);
  }
  // 40 * 50 = 2000 degrees = 5 turns + 200 degrees, which wraps to -160.
  EXPECT_NEAR(state.yawDeg, -160.0, 1e-9);
  const glm::dmat3 wrapped = navigationBasis(state.yawDeg, 0.0);
  const glm::dmat3 unwrapped = navigationBasis(2000.0, 0.0);
  for (int c = 0; c < 3; ++c) {
    for (int r = 0; r < 3; ++r) {
      EXPECT_NEAR(wrapped[c][r], unwrapped[c][r], 1e-9);
    }
  }
}

TEST(TesseractNavigation, PitchClampsAtEightyNine) {
  NavigationState state;
  NavigationInput input;
  input.lookPitchDeg = 500.0;
  advanceNavigation(state, input, 0.0, 1.0, 0.6);
  EXPECT_DOUBLE_EQ(state.pitchDeg, 89.0);
  input.lookPitchDeg = -1000.0;
  advanceNavigation(state, input, 0.0, 1.0, 0.6);
  EXPECT_DOUBLE_EQ(state.pitchDeg, -89.0);
}

} // namespace
