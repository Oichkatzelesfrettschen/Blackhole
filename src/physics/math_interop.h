#pragma once

#include <glm/glm.hpp>

#if __has_include(<Eigen/Core>)
#include <Eigen/Core>
#define BLACKHOLE_HAS_EIGEN 1
#else
#define BLACKHOLE_HAS_EIGEN 0
#endif

namespace math {

#if BLACKHOLE_HAS_EIGEN
inline Eigen::Vector3f toEigen(const glm::vec3 &v) {
  return Eigen::Vector3f(v.x, v.y, v.z);
}

inline glm::vec3 toGlm(const Eigen::Vector3f &v) {
  return glm::vec3(v.x(), v.y(), v.z());
}

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
#endif

} // namespace math
