/**
 * @file algebra_lattice.h
 * @brief The Z^4 lattice of the tesseract scene read as the basis of the
 *        4096-dimensional Cayley-Dickson algebra: Gray-Morton indexing, the
 *        zero-divisor (DMZ) mask of its single-bit links, and the
 *        Ammann-Beenker cut-and-project of the same lattice.
 *
 * Index. Lattice point n = (n0, n1, n2, n3) names basis unit e_i of the
 * level-TESSERACT_ALGEBRA_LEVEL algebra with i = grayMortonIndex(n): per axis
 * a, k = n_a mod 8 and its reflected Gray code g = k ^ (k >> 1); bit d of g is
 * bit 4 d + a of i. A unit step k -> k + 1 (including the wrap 7 -> 0) changes
 * one Gray digit, so every unit lattice step is a single-bit XOR of indices,
 * a candidate edge of the strutted emanation graph (emanation_table.h). Gray
 * codes map [0, 2^m) onto itself, so the subalgebra of dimension 2^L is a
 * sub-box of the 8^4 box.
 *
 * DMZ mask. For strut S (1 <= S < G = 2^(N-1), X = G + S) the assessors are
 * the lo labels in [1, G) other than S, with hi = lo ^ X. Index i names the
 * assessor lo(i) = i for i < G and i ^ X otherwise. The single-bit link
 * i -> i ^ 2^b with b < N - 1 joins lo(i) and lo(i) ^ 2^b; it is a DMZ edge
 * when both are assessors, they are not strut opposites (lo ^ lo' != S), and
 * dmzValueByClosedForm is nonzero, which is the emanation table's cell for
 * that pair (tests/algebra_lattice_test.cpp checks it against
 * createStruttedEt). Bit N - 1 is the assessor-chord direction and never a
 * DMZ edge. Each DMZ single-bit edge a -> a ^ 2^k also names one box-kite
 * octahedron {a, a ^ S, 2^k, 2^k ^ S, a ^ 2^k, a ^ 2^k ^ S}, present as a
 * whole (checked at N = 5..8 in the test), so the count of set bits of a
 * vertex is the number of local box-kites it anchors.
 *
 * Ammann-Beenker. With e_j projected to angle j pi/4 in the physical plane
 * and 3 j pi/4 in the perpendicular plane (orthonormal bases
 * AMMANN_BEENKER_PAR and AMMANN_BEENKER_PERP), lattice points whose
 * perpendicular projection minus the phason offset lies in the octagon
 * pi_perp([0, 1]^4) are the vertices of an Ammann-Beenker tiling (Boyle and
 * Mygdalas, Spacetime Quasicrystals, arXiv:2601.07769, section 2), and unit
 * steps between accepted points are its edges.
 */

#ifndef BLACKHOLE_RENDER_TESSERACT_ALGEBRA_LATTICE_H
#define BLACKHOLE_RENDER_TESSERACT_ALGEBRA_LATTICE_H

#include <array>
#include <bit>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "render/tesseract/emanation_table.h"

namespace blackhole::tesseract {

/// Level of the algebra the lattice carries: dimension 4096, 8 points per axis.
inline constexpr int TESSERACT_ALGEBRA_LEVEL = 12;
/// Lattice points per axis before the index repeats.
inline constexpr int ALGEBRA_LATTICE_SIDE = 8;
/// Largest strut of the level, 2^(N-1) - 1.
inline constexpr int ALGEBRA_MAX_STRUT = (1 << (TESSERACT_ALGEBRA_LEVEL - 1)) - 1;

/** @brief Reflected Gray code of @p k. */
constexpr int grayCode(int k) {
  return k ^ (k >> 1);
}

/** @brief Basis index of lattice point @p n (any integers; each axis taken mod 8). */
constexpr int grayMortonIndex(const std::array<int, 4> &n) {
  int index = 0;
  for (int a = 0; a < 4; ++a) {
    const int k = ((n[static_cast<std::size_t>(a)] % ALGEBRA_LATTICE_SIDE) + ALGEBRA_LATTICE_SIDE) %
                  ALGEBRA_LATTICE_SIDE;
    const int g = grayCode(k);
    for (int d = 0; d < 3; ++d) {
      index |= ((g >> d) & 1) << ((4 * d) + a);
    }
  }
  return index;
}

/**
 * @brief DMZ mask of strut @p strut at level @p level (5 <= level <= 12).
 *
 * present[i] bit b is set when the link i -> i ^ 2^b is a DMZ edge;
 * positive[i] bit b when its edge sign is +1. Indices at or above 2^level are
 * zero.
 */
struct AlgebraMask {
  int level = 0;
  int strut = 0;
  std::vector<std::uint16_t> present;
  std::vector<std::uint16_t> positive;
};

/** @brief Assessor label of index @p i for generator @p g and composite @p x. */
constexpr int assessorLabel(int i, int g, int x) {
  return i < g ? i : i ^ x;
}

inline AlgebraMask buildAlgebraMask(int level, int strut) {
  AlgebraMask mask;
  mask.level = level;
  mask.strut = strut;
  const int dim = 1 << level;
  const int g = dim >> 1;
  const int x = g + strut;
  const std::size_t entries = std::size_t{1} << TESSERACT_ALGEBRA_LEVEL;
  mask.present.assign(entries, 0);
  mask.positive.assign(entries, 0);
  for (int i = 0; i < dim; ++i) {
    const int a = assessorLabel(i, g, x);
    if (a == 0 || a == strut) {
      continue;
    }
    for (int b = 0; b < level - 1; ++b) {
      const int other = a ^ (1 << b);
      if (other == 0 || other == strut || (a ^ other) == strut) {
        continue;
      }
      const int value = dmzValueByClosedForm(dim, x, a, other);
      if (value == 0) {
        continue;
      }
      const auto bit = static_cast<std::uint16_t>(1U << static_cast<unsigned>(b));
      mask.present[static_cast<std::size_t>(i)] |= bit;
      if (value > 0) {
        mask.positive[static_cast<std::size_t>(i)] |= bit;
      }
    }
  }
  return mask;
}

/** @brief Box-kite octahedra anchored at index @p i: its DMZ single-bit edges. */
inline int localBoxKites(const AlgebraMask &mask, int i) {
  return std::popcount(static_cast<unsigned>(mask.present[static_cast<std::size_t>(i)]));
}

/// Orthonormal basis of the Ammann-Beenker physical plane (rows), e_j at angle j pi/4.
inline constexpr std::array<std::array<double, 4>, 2> AMMANN_BEENKER_PAR{{
    {0.70710678118654752, 0.5, 0.0, -0.5},
    {0.0, 0.5, 0.70710678118654752, 0.5},
}};
/// Orthonormal basis of the perpendicular plane, e_j at angle 3 j pi/4.
inline constexpr std::array<std::array<double, 4>, 2> AMMANN_BEENKER_PERP{{
    {0.70710678118654752, -0.5, 0.0, 0.5},
    {0.0, 0.5, -0.70710678118654752, 0.5},
}};

/** @brief Projection of @p v onto the plane with orthonormal rows @p basis. */
inline std::array<double, 2> projectPlane(const std::array<std::array<double, 4>, 2> &basis,
                                          const std::array<double, 4> &v) {
  std::array<double, 2> out{};
  for (std::size_t r = 0; r < 2; ++r) {
    for (std::size_t c = 0; c < 4; ++c) {
      out.at(r) += basis.at(r).at(c) * v.at(c);
    }
  }
  return out;
}

/**
 * @brief Whether perpendicular point @p perp lies in the octagon
 *        pi_perp([0, 1]^4): the zonotope of the four projected unit vectors,
 *        tested as four slabs.
 */
inline bool ammannBeenkerAccepts(const std::array<double, 2> &perp) {
  const std::array<double, 4> half{0.5, 0.5, 0.5, 0.5};
  const std::array<double, 2> center = projectPlane(AMMANN_BEENKER_PERP, half);
  const std::array<double, 2> d{perp[0] - center[0], perp[1] - center[1]};
  for (std::size_t k = 0; k < 4; ++k) {
    const double wx = AMMANN_BEENKER_PERP[0].at(k);
    const double wy = AMMANN_BEENKER_PERP[1].at(k);
    const double length = std::hypot(wx, wy);
    const double nx = -wy / length;
    const double ny = wx / length;
    double halfWidth = 0.0;
    for (std::size_t j = 0; j < 4; ++j) {
      halfWidth += 0.5 * std::abs((nx * AMMANN_BEENKER_PERP[0].at(j)) +
                                  (ny * AMMANN_BEENKER_PERP[1].at(j)));
    }
    if (std::abs((nx * d[0]) + (ny * d[1])) > halfWidth + 1e-12) {
      return false;
    }
  }
  return true;
}

} // namespace blackhole::tesseract

#endif // BLACKHOLE_RENDER_TESSERACT_ALGEBRA_LATTICE_H
