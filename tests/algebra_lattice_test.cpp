/**
 * @file algebra_lattice_test.cpp
 * @brief Checks of src/render/tesseract/algebra_lattice.h: the Gray-Morton
 *        index, the DMZ mask against the strutted emanation tables, the
 *        box-kite octahedra the mask anchors, and the Ammann-Beenker window.
 */

#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <numbers>
#include <vector>

#include <gtest/gtest.h>

#include "render/tesseract/algebra_lattice.h"
#include "render/tesseract/emanation_table.h"

namespace {

using blackhole::tesseract::AlgebraMask;
using blackhole::tesseract::AMMANN_BEENKER_PAR;
using blackhole::tesseract::AMMANN_BEENKER_PERP;
using blackhole::tesseract::ammannBeenkerAccepts;
using blackhole::tesseract::buildAlgebraMask;
using blackhole::tesseract::createStruttedEt;
using blackhole::tesseract::EmanationTable;
using blackhole::tesseract::grayMortonIndex;
using blackhole::tesseract::projectPlane;
using blackhole::tesseract::TESSERACT_ALGEBRA_LEVEL;

constexpr int SIDE = 8;
constexpr int BOX_KITE_EDGES = 12;

// Signed table value of assessors @p a and @p b, 0 when either is no assessor
// of the table or the cell is blank.
int tableValue(const EmanationTable &table, const std::vector<int> &position, int a, int b) {
  const int pa = position.at(static_cast<std::size_t>(a));
  const int pb = position.at(static_cast<std::size_t>(b));
  if (pa < 0 || pb < 0) {
    return 0;
  }
  return table.at(pa, pb);
}

std::vector<int> tonePositions(const EmanationTable &table) {
  std::vector<int> position(static_cast<std::size_t>(table.tone.g), -1);
  for (int p = 0; p < table.tone.k; ++p) {
    position.at(static_cast<std::size_t>(table.tone.lo.at(static_cast<std::size_t>(p)))) = p;
  }
  return position;
}

bool maskBit(const std::vector<std::uint16_t> &bits, int i, int b) {
  return ((bits.at(static_cast<std::size_t>(i)) >> static_cast<unsigned>(b)) & 1U) != 0U;
}

// Every unit lattice step, including the wrap from 7 to 0, is a single-bit
// XOR of indices at bit 4 d + a for the flipped Gray digit d of axis a.
TEST(AlgebraLattice, EveryUnitStepFlipsOneIndexBit) {
  for (int a = 0; a < 4; ++a) {
    for (int k = 0; k < SIDE; ++k) {
      std::array<int, 4> n{3, 5, 1, 6};
      n.at(static_cast<std::size_t>(a)) = k;
      std::array<int, 4> next = n;
      next.at(static_cast<std::size_t>(a)) = k + 1;
      const int diff = grayMortonIndex(n) ^ grayMortonIndex(next);
      ASSERT_EQ(std::popcount(static_cast<unsigned>(diff)), 1) << "axis " << a << " k " << k;
      EXPECT_EQ(std::countr_zero(static_cast<unsigned>(diff)) % 4, a);
    }
  }
}

// The index is a bijection of the 8^4 box onto [0, 4096), and the subalgebra
// of dimension 2^L is a sub-box: its indices are the points whose Gray digits
// above level L vanish, a product of per-axis prefixes.
TEST(AlgebraLattice, IndexIsABijectionAndSubalgebrasAreSubBoxes) {
  std::vector<int> seen(std::size_t{1} << TESSERACT_ALGEBRA_LEVEL, 0);
  for (int x = 0; x < SIDE; ++x) {
    for (int y = 0; y < SIDE; ++y) {
      for (int z = 0; z < SIDE; ++z) {
        for (int w = 0; w < SIDE; ++w) {
          const std::array<int, 4> n{x, y, z, w};
          const int i = grayMortonIndex(n);
          ++seen.at(static_cast<std::size_t>(i));
          for (int level = 4; level <= TESSERACT_ALGEBRA_LEVEL; ++level) {
            bool inBox = true;
            for (int a = 0; a < 4; ++a) {
              // Axis a holds the index bits a, a + 4, a + 8 below `level`.
              const int bits = std::max(0, (level - a + 3) / 4);
              inBox = inBox && n.at(static_cast<std::size_t>(a)) < (1 << bits);
            }
            EXPECT_EQ(i < (1 << level), inBox) << "level " << level << " index " << i;
          }
        }
      }
    }
  }
  EXPECT_TRUE(std::ranges::all_of(seen, [](int c) { return c == 1; }));
}

// The mask bit for the link i -> i ^ 2^b is set exactly when the strutted
// emanation table (full magnitude test, independent of the closed form) has a
// filled cell for the two assessors, with the table's sign.
TEST(AlgebraLattice, MaskMatchesTheStruttedTable) {
  for (int level = 5; level <= 9; ++level) {
    const int g = 1 << (level - 1);
    for (const int strut : {1, 3, g / 2 + 1, g - 1}) {
      const EmanationTable table = createStruttedEt(level, strut);
      const std::vector<int> position = tonePositions(table);
      const AlgebraMask mask = buildAlgebraMask(level, strut);
      const int x = g + strut;
      for (int i = 0; i < (1 << level); ++i) {
        const int a = i < g ? i : i ^ x;
        for (int b = 0; b < level - 1; ++b) {
          const int value = tableValue(table, position, a, a ^ (1 << b));
          ASSERT_EQ(maskBit(mask.present, i, b), value != 0)
              << "N " << level << " S " << strut << " i " << i << " b " << b;
          if (value != 0) {
            EXPECT_EQ(maskBit(mask.positive, i, b), value > 0);
          }
        }
        EXPECT_FALSE(maskBit(mask.present, i, level - 1)) << "assessor chord marked";
      }
    }
  }
}

// A DMZ single-bit edge a -> a ^ 2^k anchors the box-kite octahedron of the
// projective line {a, 2^k, a ^ 2^k}: its three strut pairs span 12 table
// edges, all filled, 6 with sign +1 and 6 with sign -1.
TEST(AlgebraLattice, EachMaskEdgeAnchorsAWholeBoxKite) {
  for (int level = 5; level <= 8; ++level) {
    const int g = 1 << (level - 1);
    for (int strut = 1; strut < g; strut += (level < 7 ? 1 : 7)) {
      const EmanationTable table = createStruttedEt(level, strut);
      const std::vector<int> position = tonePositions(table);
      const AlgebraMask mask = buildAlgebraMask(level, strut);
      for (int a = 1; a < g; ++a) {
        for (int k = 0; k < level - 1; ++k) {
          if (!maskBit(mask.present, a, k)) {
            continue;
          }
          const std::array<int, 3> line{a, 1 << k, a ^ (1 << k)};
          int positive = 0;
          int negative = 0;
          for (std::size_t p = 0; p < 3; ++p) {
            for (std::size_t q = p + 1; q < 3; ++q) {
              for (const int u : {line.at(p), line.at(p) ^ strut}) {
                for (const int v : {line.at(q), line.at(q) ^ strut}) {
                  const int value = tableValue(table, position, u, v);
                  positive += value > 0 ? 1 : 0;
                  negative += value < 0 ? 1 : 0;
                }
              }
            }
          }
          ASSERT_EQ(positive + negative, BOX_KITE_EDGES)
              << "N " << level << " S " << strut << " a " << a << " k " << k;
          EXPECT_EQ(positive, BOX_KITE_EDGES / 2);
        }
      }
    }
  }
}

// The window is the regular octagon pi_perp([0, 1]^4): the projections of
// the 16 hypercube vertices fill it, its 8 extreme points lie on one circle,
// and points just outside the extremes are rejected.
TEST(AlgebraLattice, AmmannBeenkerWindowIsTheRegularOctagon) {
  const std::array<double, 2> center = projectPlane(AMMANN_BEENKER_PERP, {0.5, 0.5, 0.5, 0.5});
  std::vector<double> radii;
  for (int corner = 0; corner < 16; ++corner) {
    const std::array<double, 4> v{static_cast<double>(corner & 1), static_cast<double>((corner >> 1) & 1),
                                  static_cast<double>((corner >> 2) & 1),
                                  static_cast<double>((corner >> 3) & 1)};
    const std::array<double, 2> perp = projectPlane(AMMANN_BEENKER_PERP, v);
    EXPECT_TRUE(ammannBeenkerAccepts(perp)) << "corner " << corner;
    const double dx = perp[0] - center[0];
    const double dy = perp[1] - center[1];
    radii.push_back(std::hypot(dx, dy));
    // Every hypercube corner is inside or on the octagon; one pushed 1% past
    // an extreme corner is outside.
    if (radii.back() > 0.9) {
      EXPECT_FALSE(ammannBeenkerAccepts({center[0] + (1.01 * dx), center[1] + (1.01 * dy)}))
          << "corner " << corner;
    }
  }
  const double outer = *std::ranges::max_element(radii);
  // Circumradius of the octagon with edge 1/sqrt(2): (1/sqrt(2)) / (2 sin(pi/8)).
  EXPECT_NEAR(outer, (1.0 / std::numbers::sqrt2) / (2.0 * std::sin(std::numbers::pi / 8.0)), 1e-12);
  EXPECT_EQ(std::ranges::count_if(radii, [outer](double r) { return std::abs(r - outer) < 1e-9; }), 8);
}

// The physical and perpendicular bases are orthonormal and complementary, and
// e_j projects to angle j pi/4 (physical) and 3 j pi/4 (perpendicular).
TEST(AlgebraLattice, AmmannBeenkerBasesAreOrthonormalOctagonalProjections) {
  const std::array<std::array<double, 4>, 4> rows{AMMANN_BEENKER_PAR[0], AMMANN_BEENKER_PAR[1],
                                                 AMMANN_BEENKER_PERP[0], AMMANN_BEENKER_PERP[1]};
  for (std::size_t r = 0; r < 4; ++r) {
    for (std::size_t c = 0; c < 4; ++c) {
      double d = 0.0;
      for (std::size_t k = 0; k < 4; ++k) {
        d += rows.at(r).at(k) * rows.at(c).at(k);
      }
      EXPECT_NEAR(d, r == c ? 1.0 : 0.0, 1e-15);
    }
  }
  for (int j = 0; j < 4; ++j) {
    std::array<double, 4> e{};
    e.at(static_cast<std::size_t>(j)) = 1.0;
    const std::array<double, 2> par = projectPlane(AMMANN_BEENKER_PAR, e);
    const std::array<double, 2> perp = projectPlane(AMMANN_BEENKER_PERP, e);
    const double quarter = std::numbers::pi / 4.0;
    EXPECT_NEAR(std::atan2(par[1], par[0]), j * quarter, 1e-12);
    const double perpAngle = std::remainder(std::atan2(perp[1], perp[0]) - (3.0 * j * quarter),
                                            2.0 * std::numbers::pi);
    EXPECT_NEAR(perpAngle, 0.0, 1e-12);
  }
}

} // namespace
