#pragma once

#include <glm/glm.hpp>
#include <glm/gtc/quaternion.hpp>

#if __has_include(<Eigen/Core>)
#include <Eigen/Core>
#include <Eigen/Geometry>
#define BLACKHOLE_HAS_EIGEN 1
#else
#define BLACKHOLE_HAS_EIGEN 0
#endif

namespace math {

#if BLACKHOLE_HAS_EIGEN
// Vec2
inline Eigen::Vector2f toEigen(const glm::vec2 &v) {
  return Eigen::Vector2f(v.x, v.y);
}
inline glm::vec2 toGlm(const Eigen::Vector2f &v) {
  return glm::vec2(v.x(), v.y());
}

// Vec3 (existing)
inline Eigen::Vector3f toEigen(const glm::vec3 &v) {
  return Eigen::Vector3f(v.x, v.y, v.z);
}
inline glm::vec3 toGlm(const Eigen::Vector3f &v) {
  return glm::vec3(v.x(), v.y(), v.z());
}

// Vec4
inline Eigen::Vector4f toEigen(const glm::vec4 &v) {
  return Eigen::Vector4f(v.x, v.y, v.z, v.w);
}
inline glm::vec4 toGlm(const Eigen::Vector4f &v) {
  return glm::vec4(v.x(), v.y(), v.z(), v.w());
}

// Mat3 (existing)
inline Eigen::Matrix3f toEigen(const glm::mat3 &m) {
  Eigen::Matrix3f out;
  out.col(0) = Eigen::Vector3f(m[0].x, m[0].y, m[0].z);
  out.col(1) = Eigen::Vector3f(m[1].x, m[1].y, m[1].z);
  out.col(2) = Eigen::Vector3f(m[2].x, m[2].y, m[2].z);
  return out;
}
inline glm::mat3 toGlm(const Eigen::Matrix3f &m) {
  glm::mat3 out(1.0f);
  out[0] = glm::vec3(m(0, 0), m(1, 0), m(2, 0));
  out[1] = glm::vec3(m(0, 1), m(1, 1), m(2, 1));
  out[2] = glm::vec3(m(0, 2), m(1, 2), m(2, 2));
  return out;
}

// Mat4
inline Eigen::Matrix4f toEigen(const glm::mat4 &m) {
  Eigen::Matrix4f out;
  out.col(0) = Eigen::Vector4f(m[0].x, m[0].y, m[0].z, m[0].w);
  out.col(1) = Eigen::Vector4f(m[1].x, m[1].y, m[1].z, m[1].w);
  out.col(2) = Eigen::Vector4f(m[2].x, m[2].y, m[2].z, m[2].w);
  out.col(3) = Eigen::Vector4f(m[3].x, m[3].y, m[3].z, m[3].w);
  return out;
}
inline glm::mat4 toGlm(const Eigen::Matrix4f &m) {
  glm::mat4 out(1.0f);
  out[0] = glm::vec4(m(0, 0), m(1, 0), m(2, 0), m(3, 0));
  out[1] = glm::vec4(m(0, 1), m(1, 1), m(2, 1), m(3, 1));
  out[2] = glm::vec4(m(0, 2), m(1, 2), m(2, 2), m(3, 2));
  out[3] = glm::vec4(m(0, 3), m(1, 3), m(2, 3), m(3, 3));
  return out;
}

// Quaternion
inline Eigen::Quaternionf toEigen(const glm::quat &q) {
  // Eigen quaternion order is (w, x, y, z)
  return Eigen::Quaternionf(q.w, q.x, q.y, q.z);
}
inline glm::quat toGlm(const Eigen::Quaternionf &q) {
  return glm::quat(q.w(), q.x(), q.y(), q.z());
}
#endif

} // namespace math
