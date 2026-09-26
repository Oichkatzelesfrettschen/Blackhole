/**
 * @file so4_test.cpp
 * @brief SO(4) quaternion-pair rotations: orthogonality, composition, the
 *        double-cover sign, isoclinic split round trip, simple-plane
 *        rotations, and the SO(3) subgroup fixing the w axis.
 *
 * Tolerance 1e-14 applies to double-precision matrix entries built from O(1)
 * products of unit-quaternion components; each entry accumulates at most
 * sixteen roundings of magnitude <= 1, well inside 1e-14.
 */

#include <array>
#include <cmath>
#include <cstddef>
#include <numbers>

#include <gtest/gtest.h>

#include "render/tesseract/so4.h"

namespace {

using blackhole::tesseract::applyMatrix;
using blackhole::tesseract::compose;
using blackhole::tesseract::determinant;
using blackhole::tesseract::isoclinicSplit;
using blackhole::tesseract::multiply;
using blackhole::tesseract::normalized;
using blackhole::tesseract::so4FromPair;
using blackhole::tesseract::transpose;

using Quat = blackhole::tesseract::Quat<double>;
using Mat4 = blackhole::tesseract::Mat4<double>;
using Vec4 = blackhole::tesseract::Vec4<double>;
using Pair = blackhole::tesseract::So4Pair<double>;

constexpr double K_TOL = 1e-14;

Quat unitQuat(double w, double x, double y, double z) {
  return normalized(Quat{.w = w, .x = x, .y = y, .z = z});
}

// Fixed pseudo-random unit quaternions spanning all four components.
const std::array<Quat, 4> &sampleQuats() {
  static const std::array<Quat, 4> quats = {
      unitQuat(0.3, -0.7, 0.2, 0.6), unitQuat(-0.9, 0.1, 0.35, -0.25),
      unitQuat(0.05, 0.5, -0.8, 0.3), unitQuat(0.6, 0.6, 0.1, -0.5)};
  return quats;
}

Mat4 identity() {
  Mat4 m{};
  for (std::size_t i = 0; i < 4; ++i) {
    m.at(i).at(i) = 1.0;
  }
  return m;
}

void expectMatNear(const Mat4 &a, const Mat4 &b, double tol) {
  for (std::size_t r = 0; r < 4; ++r) {
    for (std::size_t c = 0; c < 4; ++c) {
      EXPECT_NEAR(a.at(r).at(c), b.at(r).at(c), tol) << "entry (" << r << "," << c << ")";
    }
  }
}

/** Givens rotation by angle theta in the coordinate plane (p, q). */
Mat4 planeRotation(std::size_t p, std::size_t q, double theta) {
  Mat4 m = identity();
  m.at(p).at(p) = std::cos(theta);
  m.at(q).at(q) = std::cos(theta);
  m.at(p).at(q) = -std::sin(theta);
  m.at(q).at(p) = std::sin(theta);
  return m;
}

TEST(So4, RotationIsOrthogonalWithUnitDeterminant) {
  for (const Quat &qL : sampleQuats()) {
    for (const Quat &qR : sampleQuats()) {
      const Mat4 r = so4FromPair(qL, qR);
      expectMatNear(multiply(transpose(r), r), identity(), K_TOL);
      EXPECT_NEAR(determinant(r), 1.0, K_TOL);
    }
  }
}

TEST(So4, MatrixMatchesQuaternionSandwich) {
  const Quat qL = sampleQuats().at(0);
  const Quat qR = sampleQuats().at(1);
  const Vec4 v = {0.4, -1.2, 0.7, 2.0};
  const Vec4 viaMatrix = applyMatrix(so4FromPair(qL, qR), v);
  const Quat viaQuat = qL * blackhole::tesseract::toQuat(v) * blackhole::tesseract::conj(qR);
  const Vec4 expected = blackhole::tesseract::toVec4(viaQuat);
  for (std::size_t i = 0; i < 4; ++i) {
    EXPECT_NEAR(viaMatrix.at(i), expected.at(i), K_TOL);
  }
}

TEST(So4, CompositionMatchesMatrixProduct) {
  const Pair a{.left = sampleQuats().at(0), .right = sampleQuats().at(1)};
  const Pair b{.left = sampleQuats().at(2), .right = sampleQuats().at(3)};
  expectMatNear(so4FromPair(compose(a, b)), multiply(so4FromPair(a), so4FromPair(b)), K_TOL);
}

TEST(So4, JointSignFlipGivesIdenticalMatrix) {
  for (const Quat &qL : sampleQuats()) {
    for (const Quat &qR : sampleQuats()) {
      const Quat nL{.w = -qL.w, .x = -qL.x, .y = -qL.y, .z = -qL.z};
      const Quat nR{.w = -qR.w, .x = -qR.x, .y = -qR.y, .z = -qR.z};
      expectMatNear(so4FromPair(qL, qR), so4FromPair(nL, nR), 0.0);
    }
  }
}

double quatDot(const Quat &a, const Quat &b) {
  return (a.w * b.w) + (a.x * b.x) + (a.y * b.y) + (a.z * b.z);
}

void expectQuatNear(const Quat &actual, const Quat &expected, double sign) {
  EXPECT_NEAR(actual.w, sign * expected.w, K_TOL);
  EXPECT_NEAR(actual.x, sign * expected.x, K_TOL);
  EXPECT_NEAR(actual.y, sign * expected.y, K_TOL);
  EXPECT_NEAR(actual.z, sign * expected.z, K_TOL);
}

TEST(So4, IsoclinicSplitRoundTrip) {
  for (const Quat &qL : sampleQuats()) {
    for (const Quat &qR : sampleQuats()) {
      const Mat4 r = so4FromPair(qL, qR);
      const Pair split = isoclinicSplit(r);
      expectMatNear(so4FromPair(split), r, K_TOL);
      // The recovered pair equals the input up to one joint sign.
      const double sign = quatDot(split.left, qL) >= 0.0 ? 1.0 : -1.0;
      expectQuatNear(split.left, qL, sign);
      expectQuatNear(split.right, qR, sign);
    }
  }
}

TEST(So4, SimplePlaneRotationFixesComplementaryPlane) {
  const double theta = 0.83;
  // Every coordinate plane of R^4 ordered (x, y, z, w).
  for (std::size_t p = 0; p < 4; ++p) {
    for (std::size_t q = p + 1; q < 4; ++q) {
      const Mat4 givens = planeRotation(p, q, theta);
      const Pair split = isoclinicSplit(givens);
      const Mat4 rebuilt = so4FromPair(split);
      expectMatNear(rebuilt, givens, K_TOL);
      for (std::size_t k = 0; k < 4; ++k) {
        if (k == p || k == q) {
          continue;
        }
        Vec4 e{};
        e.at(k) = 1.0;
        const Vec4 image = applyMatrix(rebuilt, e);
        for (std::size_t i = 0; i < 4; ++i) {
          EXPECT_NEAR(image.at(i), e.at(i), K_TOL) << "plane (" << p << "," << q << ") axis " << k;
        }
      }
    }
  }
}

TEST(So4, EqualPairIsSo3SubgroupFixingRealAxis) {
  for (const Quat &q : sampleQuats()) {
    const Mat4 r = so4FromPair(q, q);
    const Vec4 wAxis = {0.0, 0.0, 0.0, 1.0};
    const Vec4 image = applyMatrix(r, wAxis);
    for (std::size_t i = 0; i < 4; ++i) {
      EXPECT_NEAR(image.at(i), wAxis.at(i), K_TOL);
    }
    // The xyz block is itself a proper rotation, with zero coupling to w.
    for (std::size_t i = 0; i < 3; ++i) {
      EXPECT_NEAR(r.at(3).at(i), 0.0, K_TOL);
      EXPECT_NEAR(r.at(i).at(3), 0.0, K_TOL);
    }
    // The xyz block turns by 2 acos(w): trace 1 + 2 cos(2 acos w) = 4 w^2 - 1.
    const double trace3 = r.at(0).at(0) + r.at(1).at(1) + r.at(2).at(2);
    EXPECT_NEAR(trace3, (4.0 * q.w * q.w) - 1.0, K_TOL);
  }
}

TEST(So4, OppositeExponentsGiveSimpleRotationInWXPlane) {
  const double theta = std::numbers::pi / 5.0;
  const Quat qL = blackhole::tesseract::quatExp(theta / 2.0, 0.0, 0.0);
  const Quat qR = blackhole::tesseract::quatExp(-theta / 2.0, 0.0, 0.0);
  const Mat4 r = so4FromPair(qL, qR);
  // The (y, z) plane is fixed; the (w, x) plane turns by theta.
  EXPECT_NEAR(r.at(1).at(1), 1.0, K_TOL);
  EXPECT_NEAR(r.at(2).at(2), 1.0, K_TOL);
  EXPECT_NEAR(r.at(0).at(0), std::cos(theta), K_TOL);
  EXPECT_NEAR(r.at(3).at(3), std::cos(theta), K_TOL);
  EXPECT_NEAR(std::abs(r.at(0).at(3)), std::sin(theta), K_TOL);
}

TEST(So4, ColumnMajorLayoutPlacesRowColumnEntry) {
  const Mat4 r = so4FromPair(sampleQuats().at(0), sampleQuats().at(2));
  const std::array<float, 16> packed = blackhole::tesseract::toColumnMajor(r);
  for (std::size_t row = 0; row < 4; ++row) {
    for (std::size_t col = 0; col < 4; ++col) {
      EXPECT_EQ(packed.at((col * 4) + row), static_cast<float>(r.at(row).at(col)));
    }
  }
}

} // namespace
