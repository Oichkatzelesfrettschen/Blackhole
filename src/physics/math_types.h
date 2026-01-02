#pragma once

/**
 * math_types.h
 *
 * Small, header-only compatibility layer that centralises math type aliases
 * used throughout the codebase. Prefer `math::Vec3`, `math::Mat4`, `math::Quat` etc
 * to make it straightforward to switch between GLM and Eigen where appropriate.
 *
 * How it works:
 * - If Eigen headers are available and the build defines `BLACKHOLE_USE_EIGEN`,
 *   the aliases map to Eigen types (VectorXf/MatrixXf/Quaternionf).
 * - Otherwise the aliases map to GLM types (vecX/matX/quat) which are the
 *   repository default.
 */

#include <array>
#include <glm/glm.hpp>
#include <glm/gtc/quaternion.hpp>
#include <glm/gtc/type_ptr.hpp>

#if __has_include(<Eigen/Core>)
#include <Eigen/Core>
#include <Eigen/Geometry>
#define BLACKHOLE_HAS_EIGEN 1
#else
#define BLACKHOLE_HAS_EIGEN 0
#endif

namespace math {

// Build-time selection flag: both header presence (BLACKHOLE_HAS_EIGEN)
// and an explicit opt-in macro `BLACKHOLE_USE_EIGEN` are required to
// switch aliases to Eigen. This keeps the default behaviour GLM-centric.
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
using Float = float;
using Vec2 = Eigen::Vector2f;
using Vec3 = Eigen::Vector3f;
using Vec4 = Eigen::Vector4f;
using Mat2 = Eigen::Matrix2f;
using Mat3 = Eigen::Matrix3f;
using Mat4 = Eigen::Matrix4f;
using Quat = Eigen::Quaternionf;
static constexpr bool kUsingEigen = true;
#else
using Float = float;
using Vec2 = glm::vec2;
using Vec3 = glm::vec3;
using Vec4 = glm::vec4;
using Mat2 = glm::mat2;
using Mat3 = glm::mat3;
using Mat4 = glm::mat4;
using Quat = glm::quat;
static constexpr bool kUsingEigen = false;
#endif

// Common additional aliases (GLM integer/double companions are handy in places)
using IVec2 = glm::ivec2;
using IVec3 = glm::ivec3;

// Double-precision types for physics accuracy
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
using Double = double;
using Vec2d = Eigen::Vector2d;
using Vec3d = Eigen::Vector3d;
using Vec4d = Eigen::Vector4d;
using Mat3d = Eigen::Matrix3d;
using Mat4d = Eigen::Matrix4d;
static constexpr bool kUsingEigenDouble = true;
#else
using Double = double;
using Vec2d = glm::dvec2;
using Vec3d = glm::dvec3;
using Vec4d = glm::dvec4;
using Mat3d = glm::dmat3;
using Mat4d = glm::dmat4;
static constexpr bool kUsingEigenDouble = false;
#endif

// Helper accessors for raw pointers (column-major ordering)
inline const Float *dataPtr(const Vec2 &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);
#endif
}

inline const Float *dataPtr(const Vec3 &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);
#endif
}

inline const Float *dataPtr(const Vec4 &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);
#endif
}

inline const Float *dataPtr(const Mat4 &m) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return m.data();
#else
  return glm::value_ptr(m);
#endif
}

// Double-precision accessors for physics
inline const Double *dataPtrd(const Vec3d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);
#endif
}

inline const Double *dataPtrd(const Vec4d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);
#endif
}

inline const Double *dataPtrd(const Mat4d &m) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return m.data();
#else
  return glm::value_ptr(m);
#endif
}

// Convert std::array<double,3> to/from Vec3d for legacy compatibility
inline Vec3d toVec3d(const std::array<double, 3> &arr) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return Vec3d(arr[0], arr[1], arr[2]);
#else
  return Vec3d(arr[0], arr[1], arr[2]);
#endif
}

inline std::array<double, 3> toArray3(const Vec3d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return {v[0], v[1], v[2]};
#else
  return {v.x, v.y, v.z};
#endif
}

// Vector operations (unified interface for GLM and Eigen)
inline double dot(const Vec3d &a, const Vec3d &b) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return a.dot(b);
#else
  return glm::dot(a, b);
#endif
}

inline Vec3d cross(const Vec3d &a, const Vec3d &b) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return a.cross(b);
#else
  return glm::cross(a, b);
#endif
}

inline double length(const Vec3d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.norm();
#else
  return glm::length(v);
#endif
}

inline Vec3d normalize(const Vec3d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.normalized();
#else
  return glm::normalize(v);
#endif
}

} // namespace math
