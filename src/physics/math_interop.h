/**
 * @file math_interop.h
 * @brief GLM <-> Eigen conversion utilities for math types.
 *
 * Provides overloaded toEigen() and toGlm() helpers for vec2/3/4,
 * mat3/4, and quat. All functions are compiled out when Eigen is
 * not present (BLACKHOLE_HAS_EIGEN == 0).
 */

#ifndef PHYSICS_MATH_INTEROP_H
#define PHYSICS_MATH_INTEROP_H

// NOLINTBEGIN(misc-include-cleaner)
// WHY: glm/glm.hpp and glm/gtc/quaternion.hpp are umbrella headers for GLM;
// include-cleaner cannot resolve umbrella headers to per-symbol sub-headers.
#include <glm/glm.hpp>
#include <glm/gtc/quaternion.hpp>
// NOLINTEND(misc-include-cleaner)

#if __has_include(<Eigen/Core>)
#include <Eigen/Core>
#include <Eigen/Geometry>
// NOLINTNEXTLINE(cppcoreguidelines-macro-usage)
// WHY: BLACKHOLE_HAS_EIGEN is a preprocessor token used in #if guards; it must
// be a macro, not a constexpr constant.
#define BLACKHOLE_HAS_EIGEN 1
#else
// NOLINTNEXTLINE(cppcoreguidelines-macro-usage)
#define BLACKHOLE_HAS_EIGEN 0
#endif

namespace math {

#if BLACKHOLE_HAS_EIGEN
/** @brief Convert glm::vec2 to Eigen::Vector2f. */
inline Eigen::Vector2f toEigen(const glm::vec2 &v) {
  return Eigen::Vector2f(v.x, v.y);
}
/** @brief Convert Eigen::Vector2f to glm::vec2. */
inline glm::vec2 toGlm(const Eigen::Vector2f &v) {
  return glm::vec2(v.x(), v.y());
}

/** @brief Convert glm::vec3 to Eigen::Vector3f. */
inline Eigen::Vector3f toEigen(const glm::vec3 &v) {
  return Eigen::Vector3f(v.x, v.y, v.z);
}
/** @brief Convert Eigen::Vector3f to glm::vec3. */
inline glm::vec3 toGlm(const Eigen::Vector3f &v) {
  return glm::vec3(v.x(), v.y(), v.z());
}

/** @brief Convert glm::vec4 to Eigen::Vector4f. */
inline Eigen::Vector4f toEigen(const glm::vec4 &v) {
  return Eigen::Vector4f(v.x, v.y, v.z, v.w);
}
/** @brief Convert Eigen::Vector4f to glm::vec4. */
inline glm::vec4 toGlm(const Eigen::Vector4f &v) {
  return glm::vec4(v.x(), v.y(), v.z(), v.w());
}

/** @brief Convert glm::mat3 to Eigen::Matrix3f (column-major). */
inline Eigen::Matrix3f toEigen(const glm::mat3 &m) {
  Eigen::Matrix3f out;
  out.col(0) = Eigen::Vector3f(m[0].x, m[0].y, m[0].z);
  out.col(1) = Eigen::Vector3f(m[1].x, m[1].y, m[1].z);
  out.col(2) = Eigen::Vector3f(m[2].x, m[2].y, m[2].z);
  return out;
}
/** @brief Convert Eigen::Matrix3f to glm::mat3. */
inline glm::mat3 toGlm(const Eigen::Matrix3f &m) {
  glm::mat3 out(1.0f);
  out[0] = glm::vec3(m(0, 0), m(1, 0), m(2, 0));
  out[1] = glm::vec3(m(0, 1), m(1, 1), m(2, 1));
  out[2] = glm::vec3(m(0, 2), m(1, 2), m(2, 2));
  return out;
}

/** @brief Convert glm::mat4 to Eigen::Matrix4f (column-major). */
inline Eigen::Matrix4f toEigen(const glm::mat4 &m) {
  Eigen::Matrix4f out;
  out.col(0) = Eigen::Vector4f(m[0].x, m[0].y, m[0].z, m[0].w);
  out.col(1) = Eigen::Vector4f(m[1].x, m[1].y, m[1].z, m[1].w);
  out.col(2) = Eigen::Vector4f(m[2].x, m[2].y, m[2].z, m[2].w);
  out.col(3) = Eigen::Vector4f(m[3].x, m[3].y, m[3].z, m[3].w);
  return out;
}
/** @brief Convert Eigen::Matrix4f to glm::mat4. */
inline glm::mat4 toGlm(const Eigen::Matrix4f &m) {
  glm::mat4 out(1.0f);
  out[0] = glm::vec4(m(0, 0), m(1, 0), m(2, 0), m(3, 0));
  out[1] = glm::vec4(m(0, 1), m(1, 1), m(2, 1), m(3, 1));
  out[2] = glm::vec4(m(0, 2), m(1, 2), m(2, 2), m(3, 2));
  out[3] = glm::vec4(m(0, 3), m(1, 3), m(2, 3), m(3, 3));
  return out;
}

/** @brief Convert glm::quat to Eigen::Quaternionf (w,x,y,z order). */
inline Eigen::Quaternionf toEigen(const glm::quat &q) {
  // Eigen quaternion order is (w, x, y, z)
  return Eigen::Quaternionf(q.w, q.x, q.y, q.z);
}
/** @brief Convert Eigen::Quaternionf to glm::quat. */
inline glm::quat toGlm(const Eigen::Quaternionf &q) {
  return glm::quat(q.w(), q.x(), q.y(), q.z());
}
#endif

} // namespace math

#endif // PHYSICS_MATH_INTEROP_H
