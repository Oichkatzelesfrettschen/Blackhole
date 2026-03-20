/**
 * @file math_types.h
 * @brief Math type aliases that unify GLM and Eigen across the codebase.
 *
 * Prefer math::Vec3, math::Mat4, math::Quat etc. so that switching between
 * GLM (default) and Eigen (opt-in via BLACKHOLE_USE_EIGEN) requires no
 * call-site changes.
 *
 * Selection rules:
 * - If Eigen headers are present AND BLACKHOLE_USE_EIGEN is defined, aliases
 *   map to Eigen types (VectorXf/MatrixXf/Quaternionf).
 * - Otherwise aliases map to GLM types (vecX/matX/quat).
 */

#ifndef PHYSICS_MATH_TYPES_H
#define PHYSICS_MATH_TYPES_H

#include <array>
// NOLINTBEGIN(misc-include-cleaner)
// WHY: glm/glm.hpp, quaternion.hpp, type_ptr.hpp are umbrella headers for GLM;
// include-cleaner cannot resolve umbrella headers to per-symbol sub-headers.
#include <glm/glm.hpp>
#include <glm/gtc/quaternion.hpp>
#include <glm/gtc/type_ptr.hpp>
// NOLINTEND(misc-include-cleaner)

#if __has_include(<Eigen/Core>)
#include <Eigen/Core>
#include <Eigen/Geometry>
// NOLINTNEXTLINE(cppcoreguidelines-macro-usage)
// WHY: BLACKHOLE_HAS_EIGEN is a preprocessor token used in #if guards; must be a macro.
#define BLACKHOLE_HAS_EIGEN 1
#else
// NOLINTNEXTLINE(cppcoreguidelines-macro-usage)
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
static constexpr bool USING_EIGEN = true;
#else
using Float = float;
// NOLINTBEGIN(misc-include-cleaner)
// WHY: glm types (vec2..mat4, quat) are defined in glm/glm.hpp umbrella header.
using Vec2 = glm::vec2;
using Vec3 = glm::vec3;
using Vec4 = glm::vec4;
using Mat2 = glm::mat2;
using Mat3 = glm::mat3;
using Mat4 = glm::mat4;
using Quat = glm::quat;
// NOLINTEND(misc-include-cleaner)
static constexpr bool USING_EIGEN = false;
#endif

// Common additional aliases (GLM integer/double companions are handy in places)
// NOLINTBEGIN(misc-include-cleaner)
using IVec2 = glm::ivec2;
using IVec3 = glm::ivec3;
// NOLINTEND(misc-include-cleaner)

// Double-precision types for physics accuracy
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
using Double = double;
using Vec2d = Eigen::Vector2d;
using Vec3d = Eigen::Vector3d;
using Vec4d = Eigen::Vector4d;
using Mat3d = Eigen::Matrix3d;
using Mat4d = Eigen::Matrix4d;
static constexpr bool USING_EIGEN_DOUBLE = true;
#else
using Double = double;
// NOLINTBEGIN(misc-include-cleaner)
using Vec2d = glm::dvec2;
using Vec3d = glm::dvec3;
using Vec4d = glm::dvec4;
using Mat3d = glm::dmat3;
using Mat4d = glm::dmat4;
// NOLINTEND(misc-include-cleaner)
static constexpr bool USING_EIGEN_DOUBLE = false;
#endif

// Helper accessors for raw pointers (column-major ordering)
/** @brief Return raw const pointer to Vec2 data. */
inline const Float *dataPtr(const Vec2 &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);  // NOLINT(misc-include-cleaner)
#endif
}

/** @brief Return raw const pointer to Vec3 data. */
inline const Float *dataPtr(const Vec3 &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);  // NOLINT(misc-include-cleaner)
#endif
}

/** @brief Return raw const pointer to Vec4 data. */
inline const Float *dataPtr(const Vec4 &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);  // NOLINT(misc-include-cleaner)
#endif
}

/** @brief Return raw const pointer to Mat4 data (column-major). */
inline const Float *dataPtr(const Mat4 &m) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return m.data();
#else
  return glm::value_ptr(m);  // NOLINT(misc-include-cleaner)
#endif
}

// Double-precision accessors for physics
/** @brief Return raw const pointer to Vec3d data. */
inline const Double *dataPtrd(const Vec3d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);  // NOLINT(misc-include-cleaner)
#endif
}

/** @brief Return raw const pointer to Vec4d data. */
inline const Double *dataPtrd(const Vec4d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.data();
#else
  return glm::value_ptr(v);  // NOLINT(misc-include-cleaner)
#endif
}

/** @brief Return raw const pointer to Mat4d data (column-major). */
inline const Double *dataPtrd(const Mat4d &m) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return m.data();
#else
  return glm::value_ptr(m);  // NOLINT(misc-include-cleaner)
#endif
}

// Convert std::array<double,3> to/from Vec3d for legacy compatibility
/** @brief Convert std::array<double,3> to Vec3d. */
inline Vec3d toVec3d(const std::array<double, 3> &arr) {
  return {arr.at(0), arr.at(1), arr.at(2)};
}

/** @brief Convert Vec3d to std::array<double,3>. */
inline std::array<double, 3> toArray3(const Vec3d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return {v[0], v[1], v[2]};
#else
  return {v.x, v.y, v.z};
#endif
}

// Vector operations (unified interface for GLM and Eigen)
// NOLINTBEGIN(misc-include-cleaner)
// WHY: glm::dot, cross, length, normalize come from glm/glm.hpp umbrella header.
/** @brief Dot product of two Vec3d vectors. */
inline double dot(const Vec3d &a, const Vec3d &b) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return a.dot(b);
#else
  return glm::dot(a, b);
#endif
}

/** @brief Cross product of two Vec3d vectors. */
inline Vec3d cross(const Vec3d &a, const Vec3d &b) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return a.cross(b);
#else
  return glm::cross(a, b);
#endif
}

/** @brief Euclidean length of a Vec3d. */
inline double length(const Vec3d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.norm();
#else
  return glm::length(v);
#endif
}

/** @brief Return unit-length Vec3d in the direction of v. */
inline Vec3d normalize(const Vec3d &v) {
#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  return v.normalized();
#else
  return glm::normalize(v);
#endif
}
// NOLINTEND(misc-include-cleaner)

} // namespace math

#endif // PHYSICS_MATH_TYPES_H
