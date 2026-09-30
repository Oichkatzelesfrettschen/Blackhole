/**
 * @file emanation_table_test.cpp
 * @brief Checks of src/render/tesseract/emanation_table.h against the
 *        strutted emanation tables of open_gororoba and de Marrais's
 *        theorems (arXiv:math/0603281, arXiv:0704.0026).
 *
 * The expected counts come from an independent run of open_gororoba's
 * create_strutted_et algorithm; every count is a multiple of 24, one
 * box-kite's directed DMZ cells. The full N = 10 table of a mandala strut
 * (S = 1 or 3) has Trip_8 = 255 * 254 / 6 = 10795 box-kites, 259080 cells.
 */

#include <algorithm>
#include <array>
#include <cstddef>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include "render/tesseract/emanation_table.h"

namespace {

using blackhole::tesseract::cdBasisMulSign;
using blackhole::tesseract::createStruttedEt;
using blackhole::tesseract::dmzValueByClosedForm;
using blackhole::tesseract::EmanationTable;
using blackhole::tesseract::expandToLevel;
using blackhole::tesseract::minLevelForStrut;
using blackhole::tesseract::primaryCopyPosition;
using blackhole::tesseract::regimeAddress;
using blackhole::tesseract::skyRegimeStruts;
using blackhole::tesseract::WalkCell;
using blackhole::tesseract::xorTripleWalk;

constexpr int RENDER_LEVEL = 10;
constexpr std::size_t BOX_KITE_CELLS = 24;

struct CountCase {
  int strut;
  std::size_t dmz;
};

// N = 10 (dim 1024): 510 x 510 table, 259080 addressable cells.
constexpr std::array<CountCase, 8> LEVEL10_COUNTS = {{{.strut = 1, .dmz = 259080},
                                                      {.strut = 3, .dmz = 259080},
                                                      {.strut = 9, .dmz = 160776},
                                                      {.strut = 17, .dmz = 87048},
                                                      {.strut = 33, .dmz = 44040},
                                                      {.strut = 65, .dmz = 21000},
                                                      {.strut = 129, .dmz = 9096},
                                                      {.strut = 257, .dmz = 3048}}};

TEST(EmanationTable, SignTableIsTheQuaternionAlgebraAtDimensionFour) {
  // e1 e2 = e3, e2 e3 = e1, e3 e1 = e2; imaginary units square to -1.
  EXPECT_EQ(cdBasisMulSign(4, 1, 2), 1);
  EXPECT_EQ(cdBasisMulSign(4, 2, 1), -1);
  EXPECT_EQ(cdBasisMulSign(4, 2, 3), 1);
  EXPECT_EQ(cdBasisMulSign(4, 3, 1), 1);
  for (int p = 1; p < 4; ++p) {
    EXPECT_EQ(cdBasisMulSign(4, p, p), -1);
  }
  // Doubling prefixes: an algebra's signs are the sub-algebra's on the lower half.
  for (int p = 0; p < 8; ++p) {
    for (int q = 0; q < 8; ++q) {
      EXPECT_EQ(cdBasisMulSign(16, p, q), cdBasisMulSign(8, p, q));
    }
  }
}

TEST(EmanationTable, DmzCountsAtDimension1024) {
  for (const CountCase &c : LEVEL10_COUNTS) {
    const EmanationTable table = createStruttedEt(RENDER_LEVEL, c.strut);
    EXPECT_EQ(table.tone.k, 510) << "S=" << c.strut;
    EXPECT_EQ(table.totalPossible, 259080U) << "S=" << c.strut;
    EXPECT_EQ(table.dmzCount, c.dmz) << "S=" << c.strut;
    EXPECT_EQ(table.dmzCount % BOX_KITE_CELLS, 0U) << "S=" << c.strut;
  }
  // The mandala tables hold Trip_8 box-kites.
  EXPECT_EQ(259080U / BOX_KITE_CELLS, 255U * 254U / 6U);
}

std::map<std::size_t, std::size_t> regimeCounts(int n) {
  std::map<std::size_t, std::size_t> counts;
  for (int s = 1; s < (1 << (n - 1)); ++s) {
    ++counts[createStruttedEt(n, s).dmzCount];
  }
  return counts;
}

TEST(EmanationTable, RegimeSetsOfPathionsAndChingons) {
  // dim 32: two regimes; dim 64: four (de Marrais's regime doubling).
  const std::map<std::size_t, std::size_t> pathions = {{72, 7}, {168, 8}};
  EXPECT_EQ(regimeCounts(5), pathions);
  const std::map<std::size_t, std::size_t> chingons = {{168, 8}, {456, 7}, {552, 7}, {840, 9}};
  EXPECT_EQ(regimeCounts(6), chingons);
  for (const auto &[count, struts] : regimeCounts(7)) {
    EXPECT_EQ(count % BOX_KITE_CELLS, 0U);
    EXPECT_GT(struts, 0U);
  }
}

TEST(EmanationTable, RegimeAddressPartitionsStrutsByDmzCount) {
  for (const int n : {7, 8}) {
    std::map<std::vector<int>, std::set<std::size_t>> countsByAddress;
    for (int s = 1; s < (1 << (n - 1)); ++s) {
      countsByAddress[regimeAddress(n, s)].insert(createStruttedEt(n, s).dmzCount);
    }
    // 2^(N-4) regimes, each with one DMZ count.
    EXPECT_EQ(countsByAddress.size(), std::size_t{1} << (n - 4)) << "N=" << n;
    for (const auto &entry : countsByAddress) {
      EXPECT_EQ(entry.second.size(), 1U) << "N=" << n;
    }
  }
}

TEST(EmanationTable, SkyRegimeStrutsAreSkyAndDistinctRegimes) {
  const std::vector<int> ride = skyRegimeStruts(RENDER_LEVEL);
  ASSERT_GT(ride.size(), 8U);
  std::set<std::vector<int>> addresses;
  for (const int s : ride) {
    EXPECT_GT(s, 8);
    EXPECT_NE(s & (s - 1), 0) << "S=" << s << " is a power of two";
    addresses.insert(regimeAddress(RENDER_LEVEL, s));
  }
  EXPECT_EQ(addresses.size(), ride.size());
  EXPECT_LE(ride.size(), std::size_t{1} << (RENDER_LEVEL - 4));
}

// Tone-row position of label @p lo in @p table, or -1.
int positionOf(const EmanationTable &table, int lo) {
  for (int i = 0; i < table.tone.k; ++i) {
    if (table.tone.lo[static_cast<std::size_t>(i)] == lo) {
      return i;
    }
  }
  return -1;
}

// Positions in @p newTable of every low label of @p oldTable, shifted by @p offset.
std::vector<int> embeddedPositions(const EmanationTable &oldTable, const EmanationTable &newTable,
                                   int offset) {
  std::vector<int> positions(oldTable.tone.lo.size());
  std::ranges::transform(oldTable.tone.lo, positions.begin(),
                         [&](int lo) { return positionOf(newTable, lo + offset); });
  return positions;
}

bool offDiagonal(int r, int c, int k) {
  return r != c && r + c != k - 1;
}

TEST(EmanationTable, Theorem11EmbedsTheLowerLevelAsTwoSubBlocks) {
  // The level-7 table of strut S reappears in the level-8 table with the same
  // strut, at the tone-row positions of lo (primary) and lo + 2^(n-1) (shifted).
  for (const int s : {3, 9, 17}) {
    const EmanationTable oldTable = createStruttedEt(7, s);
    const EmanationTable newTable = createStruttedEt(8, s);
    const std::vector<int> primary = embeddedPositions(oldTable, newTable, 0);
    const std::vector<int> shifted = embeddedPositions(oldTable, newTable, oldTable.tone.g);
    const int k = oldTable.tone.k;
    for (int r = 0; r < k; ++r) {
      ASSERT_GE(primary[static_cast<std::size_t>(r)], 0);
      ASSERT_GE(shifted[static_cast<std::size_t>(r)], 0);
    }
    for (int r = 0; r < k; ++r) {
      for (int c = 0; c < k; ++c) {
        if (!offDiagonal(r, c, k)) {
          continue;
        }
        const int expected = oldTable.at(r, c);
        const auto rr = static_cast<std::size_t>(r);
        const auto cc = static_cast<std::size_t>(c);
        ASSERT_EQ(newTable.at(primary[rr], primary[cc]), expected)
            << "primary S=" << s << " r=" << r << " c=" << c;
        // The shifted copy repeats the DMZ pattern; its values differ by the
        // shifted low indices.
        ASSERT_EQ(newTable.at(shifted[rr], shifted[cc]) != 0, expected != 0)
            << "shifted S=" << s << " r=" << r << " c=" << c;
      }
    }
  }
}

TEST(EmanationTable, MinLevelIsTheSmallestLevelHoldingTheStrut) {
  EXPECT_EQ(minLevelForStrut(1), 4);
  EXPECT_EQ(minLevelForStrut(7), 4);
  EXPECT_EQ(minLevelForStrut(9), 5);
  EXPECT_EQ(minLevelForStrut(17), 6);
  EXPECT_EQ(minLevelForStrut(129), 9);
  EXPECT_EQ(minLevelForStrut(257), 10);
  EXPECT_EQ(minLevelForStrut(511), 10);
}

// Zoom nesting: the level-n table is the level-(n+1) table with its central
// cross removed, i.e. its four corner blocks, cell for cell.
TEST(EmanationTable, LowerLevelTableIsTheFourCornersOfTheNextLevel) {
  for (const int s : {9, 17, 33, 129}) {
    for (int n = minLevelForStrut(s); n < RENDER_LEVEL; ++n) {
      const EmanationTable small = createStruttedEt(n, s);
      const EmanationTable large = createStruttedEt(n + 1, s);
      const int k = small.tone.k;
      ASSERT_EQ(large.tone.k, (2 * k) + 2);
      std::size_t compared = 0;
      for (int r = 0; r < k; ++r) {
        for (int c = 0; c < k; ++c) {
          ASSERT_EQ(large.at(primaryCopyPosition(n, r), primaryCopyPosition(n, c)), small.at(r, c))
              << "S=" << s << " level " << n << " r=" << r << " c=" << c;
          ++compared;
        }
      }
      EXPECT_EQ(compared, static_cast<std::size_t>(k) * static_cast<std::size_t>(k));
    }
  }
}

// The composite map the shader applies: every level's table sits inside the level-10 texture.
TEST(EmanationTable, EveryLevelEmbedsInTheRenderedLevel) {
  const int s = 17;
  const EmanationTable top = createStruttedEt(RENDER_LEVEL, s);
  for (int n = minLevelForStrut(s); n < RENDER_LEVEL; ++n) {
    const EmanationTable small = createStruttedEt(n, s);
    const int k = small.tone.k;
    for (int r = 0; r < k; ++r) {
      for (int c = 0; c < k; ++c) {
        ASSERT_EQ(top.at(expandToLevel(n, RENDER_LEVEL, r), expandToLevel(n, RENDER_LEVEL, c)),
                  small.at(r, c))
            << "level " << n << " r=" << r << " c=" << c;
      }
    }
  }
}

// The DMZ set is closed under xor triples: (a, b) filled makes (a, a ^ b) and
// (b, a ^ b) filled, so the walk's xor step never leaves the filled cells.
TEST(EmanationTable, FilledCellsAreClosedUnderXorTriples) {
  for (const int s : {9, 17, 129}) {
    const EmanationTable table = createStruttedEt(RENDER_LEVEL, s);
    const int k = table.tone.k;
    std::vector<int> position(static_cast<std::size_t>(table.tone.g), -1);
    for (int i = 0; i < k; ++i) {
      position[static_cast<std::size_t>(table.tone.lo[static_cast<std::size_t>(i)])] = i;
    }
    for (int r = 0; r < k; ++r) {
      for (int c = 0; c < k; ++c) {
        if (table.at(r, c) == 0) {
          continue;
        }
        const int a = table.tone.lo[static_cast<std::size_t>(r)];
        const int b = table.tone.lo[static_cast<std::size_t>(c)];
        const int third = position[static_cast<std::size_t>(a ^ b)];
        ASSERT_GE(third, 0) << "S=" << s;
        ASSERT_NE(table.at(r, third), 0) << "S=" << s << " r=" << r << " c=" << c;
        ASSERT_NE(table.at(c, third), 0) << "S=" << s << " r=" << r << " c=" << c;
      }
    }
  }
}

// Rules of the walk: even steps follow (a, b) -> (a, a ^ b) within the row, odd
// steps stay in the column. Returns the number of distinct cells visited.
std::size_t checkWalkRules(const EmanationTable &table, const std::vector<WalkCell> &walk, int s) {
  std::set<std::pair<int, int>> distinct;
  for (std::size_t i = 0; i < walk.size(); ++i) {
    EXPECT_NE(table.at(walk[i].row, walk[i].col), 0) << "S=" << s << " step " << i;
    distinct.insert({walk[i].row, walk[i].col});
    if (i + 1 == walk.size()) {
      break;
    }
    if (i % 2 == 1) {
      EXPECT_EQ(walk[i + 1].col, walk[i].col) << "S=" << s << " step " << i;
      continue;
    }
    EXPECT_EQ(walk[i + 1].row, walk[i].row) << "S=" << s << " step " << i;
    const int label = table.tone.lo[static_cast<std::size_t>(walk[i].row)] ^
                      table.tone.lo[static_cast<std::size_t>(walk[i].col)];
    EXPECT_EQ(table.tone.lo[static_cast<std::size_t>(walk[i + 1].col)], label)
        << "S=" << s << " step " << i;
  }
  return distinct.size();
}

// The walk the renderer uploads: every step lands on a filled cell, and the
// walk visits more cells than one xor-triple orbit holds (sparse tables close
// into shorter cycles).
TEST(EmanationTable, XorTripleWalkOnlyVisitsFilledCells) {
  for (const int s : {9, 17, 65, 129, 257}) {
    const EmanationTable table = createStruttedEt(RENDER_LEVEL, s);
    const std::vector<WalkCell> walk =
        xorTripleWalk(table, blackhole::tesseract::EMANATION_WALK_LENGTH);
    ASSERT_EQ(walk.size(), static_cast<std::size_t>(blackhole::tesseract::EMANATION_WALK_LENGTH));
    EXPECT_GE(checkWalkRules(table, walk, s), 16U) << "S=" << s;
  }
}

TEST(EmanationTable, ClosedFormPredicateMatchesTheBuilderOnEveryCell) {
  for (const int s : {17, 129}) {
    const EmanationTable table = createStruttedEt(RENDER_LEVEL, s);
    const int dim = 1 << RENDER_LEVEL;
    const int k = table.tone.k;
    for (int r = 0; r < k; ++r) {
      for (int c = 0; c < k; ++c) {
        int expected = 0;
        if (c != r && r + c != k - 1) {
          expected =
              dmzValueByClosedForm(dim, table.tone.x, table.tone.lo[static_cast<std::size_t>(r)],
                                   table.tone.lo[static_cast<std::size_t>(c)]);
        }
        ASSERT_EQ(table.at(r, c), expected) << "S=" << s << " r=" << r << " c=" << c;
      }
    }
  }
}

TEST(EmanationTable, TableIsSymmetricAndMirrorSymmetric) {
  // value(r, c) = value(c, r), and the mirror pairing of the tone row makes
  // the DMZ pattern equal under r -> K - 1 - r.
  for (const int s : {9, 17, 129}) {
    const EmanationTable table = createStruttedEt(RENDER_LEVEL, s);
    const int k = table.tone.k;
    for (int r = 0; r < k; ++r) {
      for (int c = 0; c < k; ++c) {
        ASSERT_EQ(table.at(r, c), table.at(c, r)) << "S=" << s;
        ASSERT_EQ(table.at(r, c) != 0, table.at(k - 1 - r, c) != 0) << "S=" << s;
      }
    }
  }
}

TEST(EmanationTable, ValuesAreXorOfToneLabelsAndNeverZeroWhenFilled) {
  const EmanationTable table = createStruttedEt(RENDER_LEVEL, 33);
  const int k = table.tone.k;
  std::size_t filled = 0;
  for (int r = 0; r < k; ++r) {
    for (int c = 0; c < k; ++c) {
      const int v = table.at(r, c);
      if (v == 0) {
        continue;
      }
      ++filled;
      const int magnitude = v < 0 ? -v : v;
      EXPECT_EQ(magnitude, table.tone.lo[static_cast<std::size_t>(r)] ^
                               table.tone.lo[static_cast<std::size_t>(c)]);
    }
  }
  EXPECT_EQ(filled, table.dmzCount);
}

} // namespace
