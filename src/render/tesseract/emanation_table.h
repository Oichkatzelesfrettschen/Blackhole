/**
 * @file emanation_table.h
 * @brief Strutted emanation tables of the 2^N-dimensional Cayley-Dickson
 *        algebras, in integer arithmetic.
 *
 * Ports, for render-only use, the construction in open_gororoba
 * (crates/cd_kernel/src/cayley_dickson/signs.rs `cd_basis_mul_sign_iter`,
 * crates/algebra_experimental/src/emanation/strutted_et.rs
 * `generate_tone_row` and `create_strutted_et`, regime_address.rs
 * `regime_address`), which implements de Marrais's "Create Emanation Table"
 * algorithm (R. P. C. de Marrais, "Presto! Digitization I", arXiv:math/0603281,
 * appendix) on the box-kite zero-divisor structure of arXiv:math/0011260.
 *
 * Definitions. The basis product of the doubling (a, b)(c, d) =
 * (ac - conj(d) b, da + b conj(c)) is e_p e_q = s(p, q) e_(p^q) with s = +-1.
 * For level N (dim = 2^N), strut constant S in [1, G) with G = 2^(N-1), and
 * X = G + S, the tone row lists K = G - 2 assessors (lo, hi = lo ^ X), lo != S,
 * mirror-paired by the strut-opposite lo ^ S. A cell (r, c) off the diagonal
 * and off the strut-opposite anti-diagonal is a DMZ (mutual zero-divisor) cell
 * when the X-pattern products UL = hi_r lo_c, UR = hi_r hi_c, LL = lo_r lo_c,
 * LR = lo_r hi_c satisfy |UL| = |LR|, |UR| = |LL|, and sgn(UL) = sgn(LR) holds
 * exactly when sgn(UR) = sgn(LL). Its value is edge * (lo_r ^ lo_c) with
 * edge = +1 when sgn(UL) = sgn(LR) and -1 otherwise.
 *
 * Every operation is an integer, so the table is identical on every host and
 * driver. The magnitude conditions always hold because hi = lo ^ X, so the
 * DMZ test reduces to the four signs (dmzByClosedForm), which is what a
 * shader could evaluate cell by cell; the renderer bakes the table instead.
 */

#ifndef BLACKHOLE_RENDER_TESSERACT_EMANATION_TABLE_H
#define BLACKHOLE_RENDER_TESSERACT_EMANATION_TABLE_H

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <map>
#include <vector>

namespace blackhole::tesseract {

/// Smallest level whose tone row exists (sedenions).
inline constexpr int EMANATION_MIN_LEVEL = 4;
/// Level the renderer draws: dim 1024, a 510 x 510 table.
inline constexpr int EMANATION_RENDER_LEVEL = 10;

/**
 * @brief Sign s(p, q) of e_p e_q = s e_(p^q) in the Cayley-Dickson algebra of
 *        dimension @p dim (a power of two), for p, q in [0, dim).
 *
 * log2(dim) iterations of the doubling reduction (signs.rs cd_basis_mul_sign_iter):
 * a swap when only q is in the upper half, a negation when only p is, and a
 * halving of both indices when both are.
 */
constexpr int cdBasisMulSign(int dim, int p, int q) {
  int sign = 1;
  for (int half = dim >> 1; half > 0; half >>= 1) {
    const bool pHigh = p >= half;
    const bool qHigh = q >= half;
    if (!pHigh && qHigh) {
      const int qLow = q - half;
      q = p;
      p = qLow;
    } else if (pHigh && !qHigh) {
      p -= half;
      if (q != 0) {
        sign = -sign;
      }
    } else if (pHigh && qHigh) {
      const int qLow = q - half;
      const int pLow = p - half;
      if (qLow == 0) {
        return -sign;
      }
      p = qLow;
      q = pLow;
    }
  }
  return sign;
}

/** @brief Tone row of level @p n and strut @p s: K assessor low indices, mirror-paired. */
struct ToneRow {
  int n = 0;
  int s = 0;
  int g = 0; ///< Generator 2^(n-1).
  int x = 0; ///< Composite g + s, equal to g ^ s.
  int k = 0; ///< Labels per row and column, g - 2.
  std::vector<int> lo;
};

/** @brief Tone row for 4 <= @p n and 1 <= @p s < 2^(n-1) (strutted_et.rs generate_tone_row). */
inline ToneRow generateToneRow(int n, int s) {
  ToneRow row;
  row.n = n;
  row.s = s;
  row.g = 1 << (n - 1);
  row.x = row.g + s;
  row.k = row.g - 2;
  row.lo.assign(static_cast<std::size_t>(row.k), 0);
  int front = 0;
  int back = row.k - 1;
  for (int candidate = 1; candidate < row.g; ++candidate) {
    if (candidate == s) {
      continue;
    }
    const int partner = candidate ^ s;
    if (candidate < partner) {
      row.lo[static_cast<std::size_t>(front)] = candidate;
      row.lo[static_cast<std::size_t>(back)] = partner;
      if (2 * (front + 1) == row.k) {
        break;
      }
      ++front;
      --back;
    }
  }
  return row;
}

/**
 * @brief DMZ decision of the assessors (a, a ^ x) and (b, b ^ x) from the four
 *        signs alone; the value is edge * (a ^ b), zero when not a DMZ.
 */
constexpr int dmzValueByClosedForm(int dim, int x, int a, int b) {
  const int ul = cdBasisMulSign(dim, a ^ x, b);
  const int ur = cdBasisMulSign(dim, a ^ x, b ^ x);
  const int ll = cdBasisMulSign(dim, a, b);
  const int lr = cdBasisMulSign(dim, a, b ^ x);
  const bool edgeOne = ul == lr;
  const bool edgeTwo = ur == ll;
  if (edgeOne != edgeTwo) {
    return 0;
  }
  return (edgeOne ? 1 : -1) * (a ^ b);
}

/** @brief K x K table of signed DMZ values in tone-row order; zero marks no DMZ. */
struct EmanationTable {
  ToneRow tone;
  std::vector<std::int16_t> value; ///< Row-major, value[r * k + c].
  std::size_t dmzCount = 0;        ///< Nonzero cells.
  std::size_t totalPossible = 0;   ///< Cells off the diagonal and the strut-opposite anti-diagonal.

  [[nodiscard]] int at(int r, int c) const {
    return value[(static_cast<std::size_t>(r) * static_cast<std::size_t>(tone.k)) +
                 static_cast<std::size_t>(c)];
  }
};

/**
 * @brief Strutted emanation table (strutted_et.rs create_strutted_et).
 *
 * Runs the X-pattern test with the full magnitude check on the products' XOR
 * indices, independent of dmzValueByClosedForm, so the two can be compared.
 */
inline EmanationTable createStruttedEt(int n, int s) {
  EmanationTable table;
  table.tone = generateToneRow(n, s);
  const int dim = 1 << n;
  const int k = table.tone.k;
  const int x = table.tone.x;
  table.value.assign(static_cast<std::size_t>(k) * static_cast<std::size_t>(k), 0);
  for (int r = 0; r < k; ++r) {
    const int loRow = table.tone.lo[static_cast<std::size_t>(r)];
    const int hiRow = loRow ^ x;
    for (int c = 0; c < k; ++c) {
      if (c == r || r + c == k - 1) {
        continue;
      }
      ++table.totalPossible;
      const int loCol = table.tone.lo[static_cast<std::size_t>(c)];
      const int hiCol = loCol ^ x;
      const int ulIndex = hiRow ^ loCol;
      const int urIndex = hiRow ^ hiCol;
      const int llIndex = loRow ^ loCol;
      const int lrIndex = loRow ^ hiCol;
      if (ulIndex != lrIndex || urIndex != llIndex) {
        continue;
      }
      const int ulSign = cdBasisMulSign(dim, hiRow, loCol);
      const int urSign = cdBasisMulSign(dim, hiRow, hiCol);
      const int llSign = cdBasisMulSign(dim, loRow, loCol);
      const int lrSign = cdBasisMulSign(dim, loRow, hiCol);
      const int edge = ulSign == lrSign ? 1 : -1;
      const int edgeTwo = urSign == llSign ? 1 : -1;
      if (edge != edgeTwo) {
        continue;
      }
      table.value[(static_cast<std::size_t>(r) * static_cast<std::size_t>(k)) +
                  static_cast<std::size_t>(c)] = static_cast<std::int16_t>(edge * llIndex);
      ++table.dmzCount;
    }
  }
  return table;
}

/**
 * @brief Regime address of strut @p s at level @p n (regime_address.rs):
 *        n - 4 bits; struts sharing an address share a DMZ count.
 */
inline std::vector<int> regimeAddress(int n, int s) {
  std::vector<int> address;
  for (; n > EMANATION_MIN_LEVEL; --n) {
    // A generator (a power of two, 8 or more) is a mandala strut at every level.
    if (s >= 8 && (s & (s - 1)) == 0) {
      s = 3;
    }
    const int half = 1 << (n - 2);
    if (s <= half) {
      address.push_back(0);
    } else {
      address.push_back(1);
      s -= half;
    }
  }
  return address;
}

/** @brief Sky strut (de Marrais 2007, arXiv:0704.0112): s > 8 and not a power of two. */
constexpr bool isSkyStrut(int s) {
  return s > 8 && (s & (s - 1)) != 0;
}

/**
 * @brief One representative sky strut per regime of level @p n, ascending.
 *
 * The smallest sky strut of each regime address, so a sequence through the
 * list visits every sky regime once. The balloon ride steps through it.
 */
inline std::vector<int> skyRegimeStruts(int n) {
  std::map<std::vector<int>, int> smallest;
  const int g = 1 << (n - 1);
  for (int s = 9; s < g; ++s) {
    if (!isSkyStrut(s)) {
      continue;
    }
    smallest.try_emplace(regimeAddress(n, s), s);
  }
  std::vector<int> struts;
  struts.reserve(smallest.size());
  for (const auto &entry : smallest) {
    struts.push_back(entry.second);
  }
  std::ranges::sort(struts);
  return struts;
}

} // namespace blackhole::tesseract

#endif // BLACKHOLE_RENDER_TESSERACT_EMANATION_TABLE_H
