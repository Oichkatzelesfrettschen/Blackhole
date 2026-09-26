/**
 * @file tests/support/ricci_oracle.h
 * @brief Finite-difference Ricci tensor of a metric functor, for field-equation tests.
 *
 * The oracle takes any callable g(x) -> 4x4 covariant metric at coordinates
 * x = (t, r, theta, phi) and evaluates
 *
 *   Gamma^a_bc = (1/2) g^ad (d_b g_dc + d_c g_db - d_d g_bc)
 *   R_bc       = d_a Gamma^a_bc - d_c Gamma^a_ba + Gamma^a_ad Gamma^d_bc - Gamma^a_cd Gamma^d_ba
 *
 * with fourth-order central differences for the metric derivatives and again
 * for the Christoffel derivatives. It shares no code with the metric under
 * test, so a vacuum, Einstein-Lambda, or Einstein-Maxwell residual checks the
 * metric components against the field equations directly.
 *
 * Error budget at step h: truncation O(h^4) times fifth derivatives, and
 * rounding about eps |g| / h^2 from the nested difference. With h = 1e-3 in
 * units of M and |g| <= 1e2 both stay below 1e-8; the tests measure the
 * floor on exact vacuum Kerr and state their tolerance beside it.
 */

#ifndef BLACKHOLE_TESTS_SUPPORT_RICCI_ORACLE_H
#define BLACKHOLE_TESTS_SUPPORT_RICCI_ORACLE_H

#include <array>
#include <cmath>
#include <cstddef>
#include <utility>

namespace ricci_oracle {

using Vec4 = std::array<double, 4>;
using Mat4 = std::array<Vec4, 4>;
/** Gamma[a][b][c] = Gamma^a_bc. */
using Christoffel = std::array<Mat4, 4>;

inline Mat4 add(const Mat4 &lhs, const Mat4 &rhs, double scale) {
  Mat4 out = lhs;
  for (std::size_t i = 0; i < 4; ++i) {
    for (std::size_t j = 0; j < 4; ++j) {
      out[i][j] += scale * rhs[i][j];
    }
  }
  return out;
}

inline Christoffel add(const Christoffel &lhs, const Christoffel &rhs, double scale) {
  Christoffel out = lhs;
  for (std::size_t i = 0; i < 4; ++i) {
    out[i] = add(lhs[i], rhs[i], scale);
  }
  return out;
}

inline Vec4 add(const Vec4 &lhs, const Vec4 &rhs, double scale) {
  Vec4 out = lhs;
  for (std::size_t i = 0; i < 4; ++i) {
    out[i] += scale * rhs[i];
  }
  return out;
}

/** @brief Inverse of a 4x4 matrix by Gauss-Jordan elimination with partial pivoting. */
inline Mat4 inverse(const Mat4 &m) {
  Mat4 a = m;
  Mat4 inv{};
  for (std::size_t i = 0; i < 4; ++i) {
    inv[i][i] = 1.0;
  }
  for (std::size_t col = 0; col < 4; ++col) {
    std::size_t pivot = col;
    for (std::size_t row = col + 1; row < 4; ++row) {
      if (std::abs(a[row][col]) > std::abs(a[pivot][col])) {
        pivot = row;
      }
    }
    std::swap(a[col], a[pivot]);
    std::swap(inv[col], inv[pivot]);
    const double diag = a[col][col];
    for (std::size_t j = 0; j < 4; ++j) {
      a[col][j] /= diag;
      inv[col][j] /= diag;
    }
    for (std::size_t row = 0; row < 4; ++row) {
      if (row != col) {
        const double factor = a[row][col];
        for (std::size_t j = 0; j < 4; ++j) {
          a[row][j] -= factor * a[col][j];
          inv[row][j] -= factor * inv[col][j];
        }
      }
    }
  }
  return inv;
}

/**
 * @brief Fourth-order central difference of f along coordinate mu.
 *
 * f'(x) = (-f(x + 2h) + 8 f(x + h) - 8 f(x - h) + f(x - 2h)) / (12 h).
 */
template <typename F> auto derivative(const F &f, const Vec4 &x, std::size_t mu, double h) {
  auto shifted = [&](double offset) {
    Vec4 y = x;
    y[mu] += offset;
    return f(y);
  };
  const auto farMinus = shifted(-2.0 * h);
  auto out = add(farMinus, farMinus, -1.0); // zero of the result type
  out = add(out, shifted(2.0 * h), -1.0 / (12.0 * h));
  out = add(out, shifted(h), 8.0 / (12.0 * h));
  out = add(out, shifted(-h), -8.0 / (12.0 * h));
  return add(out, farMinus, 1.0 / (12.0 * h));
}

template <typename Metric> Christoffel christoffel(const Metric &g, const Vec4 &x, double h) {
  const Mat4 gInv = inverse(g(x));
  std::array<Mat4, 4> dg{};
  for (std::size_t mu = 0; mu < 4; ++mu) {
    dg[mu] = derivative(g, x, mu, h);
  }
  Christoffel gamma{};
  for (std::size_t a = 0; a < 4; ++a) {
    for (std::size_t b = 0; b < 4; ++b) {
      for (std::size_t c = 0; c < 4; ++c) {
        double sum = 0.0;
        for (std::size_t d = 0; d < 4; ++d) {
          sum += gInv[a][d] * (dg[b][d][c] + dg[c][d][b] - dg[d][b][c]);
        }
        gamma[a][b][c] = 0.5 * sum;
      }
    }
  }
  return gamma;
}

/** @brief Covariant Ricci tensor R_bc at x. */
template <typename Metric> Mat4 ricci(const Metric &g, const Vec4 &x, double h = 1.0e-3) {
  const Christoffel gamma = christoffel(g, x, h);
  auto gammaAt = [&](const Vec4 &y) { return christoffel(g, y, h); };
  std::array<Christoffel, 4> dGamma{};
  for (std::size_t e = 0; e < 4; ++e) {
    dGamma[e] = derivative(gammaAt, x, e, h);
  }
  Mat4 r{};
  for (std::size_t b = 0; b < 4; ++b) {
    for (std::size_t c = 0; c < 4; ++c) {
      double sum = 0.0;
      for (std::size_t a = 0; a < 4; ++a) {
        sum += dGamma[a][a][b][c] - dGamma[c][a][b][a];
        for (std::size_t d = 0; d < 4; ++d) {
          sum += gamma[a][a][d] * gamma[d][b][c] - gamma[a][c][d] * gamma[d][b][a];
        }
      }
      r[b][c] = sum;
    }
  }
  return r;
}

/** @brief Ricci scalar g^bc R_bc. */
inline double scalar(const Mat4 &gInv, const Mat4 &ricciTensor) {
  double sum = 0.0;
  for (std::size_t b = 0; b < 4; ++b) {
    for (std::size_t c = 0; c < 4; ++c) {
      sum += gInv[b][c] * ricciTensor[b][c];
    }
  }
  return sum;
}

/**
 * @brief Einstein-Maxwell source 2 (F_ma F_n^a - g_mn F_ab F^ab / 4) of a potential A_mu.
 *
 * Geometrized Gaussian units: G_mn = 8 pi T_mn with T_mn = (F_ma F_n^a -
 * g_mn F^2 / 4) / (4 pi). The source is traceless, so R = 0 and R_mn equals it.
 */
template <typename Potential>
Mat4 maxwellSource(const Potential &potential, const Mat4 &g, const Vec4 &x, double h = 1.0e-4) {
  std::array<Vec4, 4> dA{};
  for (std::size_t mu = 0; mu < 4; ++mu) {
    dA[mu] = derivative(potential, x, mu, h);
  }
  Mat4 f{};
  for (std::size_t m = 0; m < 4; ++m) {
    for (std::size_t n = 0; n < 4; ++n) {
      f[m][n] = dA[m][n] - dA[n][m];
    }
  }
  const Mat4 gInv = inverse(g);
  Mat4 fUp{}; // fUp[a][n] = g^ab F_bn
  for (std::size_t a = 0; a < 4; ++a) {
    for (std::size_t n = 0; n < 4; ++n) {
      double sum = 0.0;
      for (std::size_t b = 0; b < 4; ++b) {
        sum += gInv[a][b] * f[b][n];
      }
      fUp[a][n] = sum;
    }
  }
  double fSquared = 0.0; // F_ab F^ab
  for (std::size_t a = 0; a < 4; ++a) {
    for (std::size_t b = 0; b < 4; ++b) {
      double raised = 0.0; // F^ab = g^ac F_cn g^nb
      for (std::size_t n = 0; n < 4; ++n) {
        raised += fUp[a][n] * gInv[n][b];
      }
      fSquared += f[a][b] * raised;
    }
  }
  Mat4 source{};
  for (std::size_t m = 0; m < 4; ++m) {
    for (std::size_t n = 0; n < 4; ++n) {
      double contraction = 0.0; // F_ma F_n^a = F_ma g^ab F_nb = -F_ma fUp[a][n]
      for (std::size_t a = 0; a < 4; ++a) {
        contraction -= f[m][a] * fUp[a][n];
      }
      source[m][n] = 2.0 * (contraction - 0.25 * g[m][n] * fSquared);
    }
  }
  return source;
}

/** @brief Largest |lhs - scale * rhs| over all components. */
inline double maxAbsDifference(const Mat4 &lhs, const Mat4 &rhs, double scale) {
  double worst = 0.0;
  for (std::size_t i = 0; i < 4; ++i) {
    for (std::size_t j = 0; j < 4; ++j) {
      worst = std::fmax(worst, std::abs(lhs[i][j] - scale * rhs[i][j]));
    }
  }
  return worst;
}

} // namespace ricci_oracle

#endif // BLACKHOLE_TESTS_SUPPORT_RICCI_ORACLE_H
