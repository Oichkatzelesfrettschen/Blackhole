#include "physics/math_types.h"
#include "physics/math_interop.h"
#include "physics/safe_limits.h"

#include <glm/glm.hpp>
#include <glm/gtc/quaternion.hpp>
#include <random>
#include <iostream>
#include <cmath>
#include <limits>

[[maybe_unused]] static bool approx_eq(float a, float b, float tol = 1e-5f) {
  if (physics::safe_isnan(a) && physics::safe_isnan(b)) return true;
  if (physics::safe_isinf(a) && physics::safe_isinf(b) && (std::signbit(a) == std::signbit(b))) return true;
  return std::abs(a - b) <= tol * std::max(1.0f, std::abs(b));
}

int main() {
#if defined(BLACKHOLE_HAS_EIGEN) && BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  const int vec_iters = std::atoi(std::getenv("MATH_PARITY_VEC_ITERS") ?: "2000");
  const int mat_iters = std::atoi(std::getenv("MATH_PARITY_MAT_ITERS") ?: "500");
  const int quat_iters = std::atoi(std::getenv("MATH_PARITY_QUAT_ITERS") ?: "500");

  std::mt19937 rng(123456);
  std::uniform_real_distribution<float> d(-1e6f, 1e6f);

  // Round-trip test helper for arbitrary floats including edge values
  auto edge_values = []() {
    std::vector<float> v;
    v.push_back(0.0f);
    v.push_back(1.0f);
    v.push_back(-1.0f);
    v.push_back(std::numeric_limits<float>::min());
    v.push_back(std::numeric_limits<float>::max());
    v.push_back(std::numeric_limits<float>::denorm_min());
    v.push_back(std::numeric_limits<float>::infinity());
    v.push_back(-std::numeric_limits<float>::infinity());
    v.push_back(std::numeric_limits<float>::quiet_NaN());
    return v;
  }();

  // Vec2 / Vec4
  for (int i = 0; i < vec_iters; ++i) {
    glm::vec2 v2;
    glm::vec4 v4;
    if (i < (int)edge_values.size()) {
      v2 = glm::vec2(edge_values[i], edge_values[(i+1) % edge_values.size()]);
      v4 = glm::vec4(edge_values[i], edge_values[(i+1) % edge_values.size()], edge_values[(i+2) % edge_values.size()], edge_values[(i+3) % edge_values.size()]);
    } else {
      v2 = glm::vec2(d(rng), d(rng));
      v4 = glm::vec4(d(rng), d(rng), d(rng), d(rng));
    }
    auto e2 = math::toEigen(v2);
    auto v2b = math::toGlm(e2);
    if (!approx_eq(v2.x, v2b.x) || !approx_eq(v2.y, v2b.y)) {
      std::cerr << "Vec2 roundtrip mismatch\n";
      return 2;
    }
    auto e4 = math::toEigen(v4);
    auto v4b = math::toGlm(e4);
    if (!approx_eq(v4.x, v4b.x) || !approx_eq(v4.y, v4b.y) || !approx_eq(v4.z, v4b.z) || !approx_eq(v4.w, v4b.w)) {
      std::cerr << "Vec4 roundtrip mismatch\n";
      return 3;
    }
  }

  // Mat3
  for (int i = 0; i < mat_iters; ++i) {
    glm::mat3 m;
    for (int c = 0; c < 3; ++c)
      for (int r = 0; r < 3; ++r)
        m[c][r] = (i < (int)edge_values.size()) ? edge_values[(c*3 + r) % edge_values.size()] : d(rng);
    auto em = math::toEigen(m);
    auto m2 = math::toGlm(em);
    for (int c = 0; c < 3; ++c)
      for (int r = 0; r < 3; ++r)
        if (!approx_eq(m[c][r], m2[c][r])) {
          std::cerr << "Mat3 roundtrip mismatch\n";
          return 4;
        }
  }

  // Mat4 (added)
  for (int i = 0; i < mat_iters; ++i) {
    glm::mat4 m;
    for (int c = 0; c < 4; ++c)
      for (int r = 0; r < 4; ++r)
        m[c][r] = (i < (int)edge_values.size()) ? edge_values[(c*4 + r) % edge_values.size()] : d(rng);
    auto em = math::toEigen(m);
    auto m2 = math::toGlm(em);
    for (int c = 0; c < 4; ++c)
      for (int r = 0; r < 4; ++r)
        if (!approx_eq(m[c][r], m2[c][r])) {
          std::cerr << "Mat4 roundtrip mismatch\n";
          return 5;
        }
  }

  // Quaternions
  for (int i = 0; i < quat_iters; ++i) {
    glm::quat q;
    if (i < (int)edge_values.size()) {
      q = glm::quat(edge_values[i], edge_values[(i+1)%edge_values.size()], edge_values[(i+2)%edge_values.size()], edge_values[(i+3)%edge_values.size()]);
    } else {
      q = glm::quat(d(rng), d(rng), d(rng), d(rng));
    }
    auto eq = math::toEigen(q);
    auto q2 = math::toGlm(eq);
    if (!approx_eq(q.x, q2.x) || !approx_eq(q.y, q2.y) || !approx_eq(q.z, q2.z) || !approx_eq(q.w, q2.w)) {
      std::cerr << "Quat roundtrip mismatch\n";
      return 6;
    }
  }

  std::cout << "Eigen<->GLM parity tests passed\n";
  return 0;
#else
  std::cout << "Eigen not enabled; parity test skipped (define ENABLE_EIGEN to run)\n";
  return 0;
#endif
}
