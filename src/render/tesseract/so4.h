/**
 * @file so4.h
 * @brief SO(4) rotations as unit-quaternion pairs acting on R^4 = H.
 *
 * A point v = (x, y, z, w) of R^4 is the quaternion w + x i + y j + z k, so
 * the real part sits on the w axis. Every rotation of R^4 is the map
 * v -> qL v conj(qR) for a pair of unit quaternions (qL, qR), unique up to the
 * joint sign flip (qL, qR) -> (-qL, -qR); S^3 x S^3 is the double cover of
 * SO(4). The pair qL = qR = q reduces to the SO(3) sandwich v -> q v conj(q)
 * that fixes the w axis, the construction of open_gororoba's quat_rotation.rs
 * (claims C-876, C-911, C-912).
 *
 * Matrices are row-major and act on column vectors ordered (x, y, z, w). The
 * header is GL-free and templated on the scalar type so tests run in double
 * and the renderer in float.
 */

#ifndef BLACKHOLE_RENDER_TESSERACT_SO4_H
#define BLACKHOLE_RENDER_TESSERACT_SO4_H

#include <array>
#include <cmath>
#include <concepts>
#include <cstddef>
#include <limits>
#include <optional>

namespace blackhole::tesseract {

/** @brief Quaternion w + x i + y j + z k. */
template <std::floating_point T> struct Quat {
  T w{1};
  T x{0};
  T y{0};
  T z{0};
};

/** @brief Point of R^4 ordered (x, y, z, w). */
template <std::floating_point T> using Vec4 = std::array<T, 4>;

/** @brief Row-major 4x4 matrix acting on column vectors. */
template <std::floating_point T> using Mat4 = std::array<std::array<T, 4>, 4>;

/** @brief Hamilton product a * b. */
template <std::floating_point T> constexpr Quat<T> operator*(const Quat<T> &a, const Quat<T> &b) {
  return {.w = a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z,
          .x = a.w * b.x + a.x * b.w + a.y * b.z - a.z * b.y,
          .y = a.w * b.y - a.x * b.z + a.y * b.w + a.z * b.x,
          .z = a.w * b.z + a.x * b.y - a.y * b.x + a.z * b.w};
}

/** @brief Quaternion conjugate w - x i - y j - z k. */
template <std::floating_point T> constexpr Quat<T> conj(const Quat<T> &q) {
  return {.w = q.w, .x = -q.x, .y = -q.y, .z = -q.z};
}

/** @brief Euclidean norm |q|. */
template <std::floating_point T> T norm(const Quat<T> &q) {
  return std::sqrt(q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z);
}

/** @brief q / |q|; the identity for a zero quaternion. */
template <std::floating_point T> Quat<T> normalized(const Quat<T> &q) {
  const T n = norm(q);
  if (n <= T{0}) {
    return Quat<T>{};
  }
  return {.w = q.w / n, .x = q.x / n, .y = q.y / n, .z = q.z / n};
}

/**
 * @brief exp(v) of the pure quaternion v = vx i + vy j + vz k.
 *
 * exp(v) = cos|v| + sin|v| v/|v|, a unit quaternion; the exponential map
 * turns a constant angular rate into a one-parameter subgroup of S^3.
 */
template <std::floating_point T> Quat<T> quatExp(T vx, T vy, T vz) {
  const T angle = std::sqrt(vx * vx + vy * vy + vz * vz);
  if (angle <= T{0}) {
    return Quat<T>{};
  }
  const T s = std::sin(angle) / angle;
  return {.w = std::cos(angle), .x = vx * s, .y = vy * s, .z = vz * s};
}

/** @brief Quaternion for the point v = (x, y, z, w) of R^4. */
template <std::floating_point T> constexpr Quat<T> toQuat(const Vec4<T> &v) {
  return {.w = v.at(3), .x = v.at(0), .y = v.at(1), .z = v.at(2)};
}

/** @brief Point (x, y, z, w) of R^4 for the quaternion q. */
template <std::floating_point T> constexpr Vec4<T> toVec4(const Quat<T> &q) {
  return {q.x, q.y, q.z, q.w};
}

/** @brief Matrix whose column k is f(e_k) for a linear map f on R^4. */
template <std::floating_point T, typename F> constexpr Mat4<T> matrixOf(const F &f) {
  Mat4<T> m{};
  for (std::size_t col = 0; col < 4; ++col) {
    Vec4<T> basis{};
    basis.at(col) = T{1};
    const Vec4<T> image = f(basis);
    for (std::size_t row = 0; row < 4; ++row) {
      m.at(row).at(col) = image.at(row);
    }
  }
  return m;
}

/** @brief Left-multiplication matrix L(q): v -> q v. */
template <std::floating_point T> constexpr Mat4<T> leftMatrix(const Quat<T> &q) {
  return matrixOf<T>([&q](const Vec4<T> &v) { return toVec4(q * toQuat(v)); });
}

/** @brief Right-multiplication matrix R(q): v -> v q. */
template <std::floating_point T> constexpr Mat4<T> rightMatrix(const Quat<T> &q) {
  return matrixOf<T>([&q](const Vec4<T> &v) { return toVec4(toQuat(v) * q); });
}

/** @brief Matrix product a b. */
template <std::floating_point T> constexpr Mat4<T> multiply(const Mat4<T> &a, const Mat4<T> &b) {
  Mat4<T> m{};
  for (std::size_t r = 0; r < 4; ++r) {
    for (std::size_t c = 0; c < 4; ++c) {
      T sum{0};
      for (std::size_t k = 0; k < 4; ++k) {
        sum += a.at(r).at(k) * b.at(k).at(c);
      }
      m.at(r).at(c) = sum;
    }
  }
  return m;
}

/** @brief Matrix-vector product m v. */
template <std::floating_point T> constexpr Vec4<T> applyMatrix(const Mat4<T> &m, const Vec4<T> &v) {
  Vec4<T> out{};
  for (std::size_t r = 0; r < 4; ++r) {
    T sum{0};
    for (std::size_t k = 0; k < 4; ++k) {
      sum += m.at(r).at(k) * v.at(k);
    }
    out.at(r) = sum;
  }
  return out;
}

/** @brief Transpose m^T. */
template <std::floating_point T> constexpr Mat4<T> transpose(const Mat4<T> &m) {
  Mat4<T> t{};
  for (std::size_t r = 0; r < 4; ++r) {
    for (std::size_t c = 0; c < 4; ++c) {
      t.at(c).at(r) = m.at(r).at(c);
    }
  }
  return t;
}

/** @brief Determinant by cofactor expansion along the first row. */
template <std::floating_point T> constexpr T determinant(const Mat4<T> &m) {
  auto minor3 = [&m](std::size_t skipCol) {
    std::array<std::array<T, 3>, 3> s{};
    for (std::size_t r = 1; r < 4; ++r) {
      std::size_t c3 = 0;
      for (std::size_t c = 0; c < 4; ++c) {
        if (c != skipCol) {
          s.at(r - 1).at(c3) = m.at(r).at(c);
          ++c3;
        }
      }
    }
    return s.at(0).at(0) * (s.at(1).at(1) * s.at(2).at(2) - s.at(1).at(2) * s.at(2).at(1)) -
           s.at(0).at(1) * (s.at(1).at(0) * s.at(2).at(2) - s.at(1).at(2) * s.at(2).at(0)) +
           s.at(0).at(2) * (s.at(1).at(0) * s.at(2).at(1) - s.at(1).at(1) * s.at(2).at(0));
  };
  T det{0};
  T sign{1};
  for (std::size_t c = 0; c < 4; ++c) {
    det += sign * m.at(0).at(c) * minor3(c);
    sign = -sign;
  }
  return det;
}

/**
 * @brief Column-major float copy of m for glUniformMatrix4fv(transpose = false).
 *
 * Element [c * 4 + r] holds m[r][c], the layout glm::make_mat4 and GLSL mat4
 * expect; a transposed upload would render the inverse rotation.
 */
template <std::floating_point T> constexpr std::array<float, 16> toColumnMajor(const Mat4<T> &m) {
  std::array<float, 16> out{};
  for (std::size_t c = 0; c < 4; ++c) {
    for (std::size_t r = 0; r < 4; ++r) {
      out.at((c * 4) + r) = static_cast<float>(m.at(r).at(c));
    }
  }
  return out;
}

/** @brief Unit-quaternion pair (qL, qR) naming the rotation v -> qL v conj(qR). */
template <std::floating_point T> struct So4Pair {
  Quat<T> left{};
  Quat<T> right{};
};

/**
 * @brief Rotation matrix of v -> qL v conj(qR).
 *
 * Built as L(qL) R(conj qR); left and right multiplication commute by
 * associativity, so the order of the two factors is immaterial.
 */
template <std::floating_point T>
constexpr Mat4<T> so4FromPair(const Quat<T> &qL, const Quat<T> &qR) {
  return multiply(leftMatrix(qL), rightMatrix(conj(qR)));
}

/** @brief so4FromPair for a stored pair. */
template <std::floating_point T> constexpr Mat4<T> so4FromPair(const So4Pair<T> &p) {
  return so4FromPair(p.left, p.right);
}

/**
 * @brief Pair of the composite rotation a o b (apply b, then a).
 *
 * qL1 (qL2 v conj qR2) conj qR1 = (qL1 qL2) v conj(qR1 qR2), so
 * so4FromPair(compose(a, b)) == multiply(so4FromPair(a), so4FromPair(b)).
 */
template <std::floating_point T>
constexpr So4Pair<T> compose(const So4Pair<T> &a, const So4Pair<T> &b) {
  return {.left = a.left * b.left, .right = a.right * b.right};
}

/**
 * @brief Tolerance of isSpecialOrthogonal: sqrt(epsilon) of the scalar type.
 *
 * About 1.5e-8 in double and 3.5e-4 in float, far above the rounding of a
 * product of unit-quaternion matrices and far below any non-rotation's error.
 */
template <std::floating_point T> T so4Tolerance() {
  return std::sqrt(std::numeric_limits<T>::epsilon());
}

/**
 * @brief True when m^T m = I entrywise and det m = +1, both within @p tol.
 */
template <std::floating_point T>
bool isSpecialOrthogonal(const Mat4<T> &m, T tol = so4Tolerance<T>()) {
  const Mat4<T> gram = multiply(transpose(m), m);
  for (std::size_t r = 0; r < 4; ++r) {
    for (std::size_t c = 0; c < 4; ++c) {
      const T expected = r == c ? T{1} : T{0};
      if (std::abs(gram.at(r).at(c) - expected) > tol) {
        return false;
      }
    }
  }
  return std::abs(determinant(m) - T{1}) <= tol;
}

/**
 * @brief Recover (qL, qR), up to joint sign, from a rotation matrix M.
 *
 * The sixteen matrices K_ij = L(e_i) R(conj e_j) over the quaternion units
 * e_0..e_3 = 1, i, j, k are orthogonal and mutually orthogonal under the
 * Frobenius product, with <K_ij, K_kl> = 4 delta_ik delta_jl. Expanding
 * M = sum a_i b_j K_ij gives the associate matrix A_ij = <M, K_ij> / 4 =
 * a_i b_j of Van Elfrinkhof, a rank-one outer product for M in SO(4). The
 * row of A with the largest norm fixes b up to sign; a = A b then carries
 * the matching sign, so the returned pair is +-(qL, qR).
 *
 * Only a member of SO(4) has such a pair. The split returns std::nullopt
 * unless isSpecialOrthogonal holds: an improper matrix (det = -1) has a
 * full-rank associate matrix, and a non-orthogonal one (2 I, a shear) has an
 * associate matrix whose normalized rank-one part rebuilds a different matrix.
 */
template <std::floating_point T> std::optional<So4Pair<T>> isoclinicSplit(const Mat4<T> &m) {
  if (!isSpecialOrthogonal(m)) {
    return std::nullopt;
  }
  const std::array<Quat<T>, 4> units = {
      Quat<T>{.w = 1, .x = 0, .y = 0, .z = 0}, Quat<T>{.w = 0, .x = 1, .y = 0, .z = 0},
      Quat<T>{.w = 0, .x = 0, .y = 1, .z = 0}, Quat<T>{.w = 0, .x = 0, .y = 0, .z = 1}};
  Mat4<T> assoc{};
  for (std::size_t i = 0; i < 4; ++i) {
    for (std::size_t j = 0; j < 4; ++j) {
      const Mat4<T> k = so4FromPair(units.at(i), units.at(j));
      T inner{0};
      for (std::size_t r = 0; r < 4; ++r) {
        for (std::size_t c = 0; c < 4; ++c) {
          inner += m.at(r).at(c) * k.at(r).at(c);
        }
      }
      assoc.at(i).at(j) = inner / T{4};
    }
  }
  std::size_t bestRow = 0;
  T bestNorm2{-1};
  for (std::size_t i = 0; i < 4; ++i) {
    T n2{0};
    for (std::size_t j = 0; j < 4; ++j) {
      n2 += assoc.at(i).at(j) * assoc.at(i).at(j);
    }
    if (n2 > bestNorm2) {
      bestNorm2 = n2;
      bestRow = i;
    }
  }
  const T rowNorm = std::sqrt(bestNorm2);
  std::array<T, 4> b{};
  for (std::size_t j = 0; j < 4; ++j) {
    b.at(j) = assoc.at(bestRow).at(j) / rowNorm;
  }
  std::array<T, 4> a{};
  for (std::size_t i = 0; i < 4; ++i) {
    T sum{0};
    for (std::size_t j = 0; j < 4; ++j) {
      sum += assoc.at(i).at(j) * b.at(j);
    }
    a.at(i) = sum;
  }
  const Quat<T> qL = normalized(Quat<T>{.w = a.at(0), .x = a.at(1), .y = a.at(2), .z = a.at(3)});
  const Quat<T> qR = Quat<T>{.w = b.at(0), .x = b.at(1), .y = b.at(2), .z = b.at(3)};
  return So4Pair<T>{.left = qL, .right = qR};
}

} // namespace blackhole::tesseract

#endif // BLACKHOLE_RENDER_TESSERACT_SO4_H
