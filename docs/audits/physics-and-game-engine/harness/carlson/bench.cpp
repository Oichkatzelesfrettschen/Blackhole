// Carlson R_F/R_D/R_J accuracy and cost: Blackhole elliptic_integrals.h vs
// Carlson-1995 stopping rule vs Boost.Math, referee = mpmath (ref.csv).
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <boost/math/special_functions/ellint_rf.hpp>
#include <boost/math/special_functions/ellint_rd.hpp>
#include <boost/math/special_functions/ellint_rj.hpp>
#include "physics/elliptic_integrals.h"

namespace c95 {
static int itRf = 0, itRd = 0, itRj = 0;
inline double rc(double x, double y) {
  if (x == y) return 1.0 / std::sqrt(x);
  if (x < y) return std::atan(std::sqrt((y - x) / x)) / std::sqrt(y - x);
  return std::asinh(std::sqrt((x - y) / y)) / std::sqrt(x - y);
}
inline double rf(double x, double y, double z) {
  constexpr double tol = 0.0025;
  double a, dx, dy, dz;
  for (;;) {
    a = (x + y + z) / 3.0;
    dx = (a - x) / a; dy = (a - y) / a; dz = (a - z) / a;
    if (std::max({std::abs(dx), std::abs(dy), std::abs(dz)}) < tol) break;
    ++itRf;
    const double sx = std::sqrt(x), sy = std::sqrt(y), sz = std::sqrt(z);
    const double l = sx * (sy + sz) + sy * sz;
    x = 0.25 * (x + l); y = 0.25 * (y + l); z = 0.25 * (z + l);
  }
  const double e2 = dx * dy - dz * dz, e3 = dx * dy * dz;
  return (1.0 + (e2 / 24.0 - 0.1 - 3.0 / 44.0 * e3) * e2 + e3 / 14.0) / std::sqrt(a);
}
inline double rd(double x, double y, double z) {
  constexpr double tol = 0.0015;
  double sum = 0.0, fac = 1.0, a, dx, dy, dz;
  for (;;) {
    a = 0.2 * (x + y + 3.0 * z);
    dx = (a - x) / a; dy = (a - y) / a; dz = (a - z) / a;
    if (std::max({std::abs(dx), std::abs(dy), std::abs(dz)}) < tol) break;
    ++itRd;
    const double sx = std::sqrt(x), sy = std::sqrt(y), sz = std::sqrt(z);
    const double l = sx * (sy + sz) + sy * sz;
    sum += fac / (sz * (z + l)); fac *= 0.25;
    x = 0.25 * (x + l); y = 0.25 * (y + l); z = 0.25 * (z + l);
  }
  constexpr double C1 = 3.0 / 14.0, C2 = 1.0 / 6.0, C3 = 9.0 / 22.0, C4 = 3.0 / 26.0,
                   C5 = 0.25 * C3, C6 = 1.5 * C4;
  const double ea = dx * dy, eb = dz * dz, ec = ea - eb, ed = ea - 6.0 * eb, ee = ed + ec + ec;
  return 3.0 * sum + fac * (1.0 + ed * (-C1 + C5 * ed - C6 * dz * ee) +
                            dz * (C2 * ee + dz * (-C3 * ec + dz * C4 * ea))) / (a * std::sqrt(a));
}
inline double rj(double x, double y, double z, double p) {
  constexpr double tol = 0.0015;
  double sum = 0.0, fac = 1.0, a, dx, dy, dz, dp;
  for (;;) {
    a = 0.2 * (x + y + z + p + p);
    dx = (a - x) / a; dy = (a - y) / a; dz = (a - z) / a; dp = (a - p) / a;
    if (std::max({std::abs(dx), std::abs(dy), std::abs(dz), std::abs(dp)}) < tol) break;
    ++itRj;
    const double sx = std::sqrt(x), sy = std::sqrt(y), sz = std::sqrt(z);
    const double l = sx * (sy + sz) + sy * sz;
    const double al = p * (sx + sy + sz) + sx * sy * sz;
    const double be = p * (p + l) * (p + l);
    sum += fac * rc(al * al, be); fac *= 0.25;
    x = 0.25 * (x + l); y = 0.25 * (y + l); z = 0.25 * (z + l); p = 0.25 * (p + l);
  }
  constexpr double C1 = 3.0 / 14.0, C2 = 1.0 / 3.0, C3 = 3.0 / 22.0, C4 = 3.0 / 26.0,
                   C5 = 0.75 * C3, C6 = 1.5 * C4, C7 = 0.5 * C2, C8 = C3 + C3;
  const double ea = dx * (dy + dz) + dy * dz, eb = dx * dy * dz, ec = dp * dp, ed = ea - 3.0 * ec,
               ee = eb + 2.0 * dp * (ea - ec);
  return 3.0 * sum + fac * (1.0 + ed * (-C1 + C5 * ed - C6 * ee) + eb * (C7 + dp * (-C8 + dp * C4)) +
                            dp * ea * (C2 - dp * C3) - C2 * dp * ec) / (a * std::sqrt(a));
}
}  // namespace c95

struct Row { std::string tag; double x, y, z, p, rf, rd, rj; };

template <class F> double timeNs(const std::vector<Row>& rows, F f, int reps) {
  volatile double sink = 0.0;
  auto t0 = std::chrono::steady_clock::now();
  for (int r = 0; r < reps; ++r)
    for (const auto& w : rows) sink = sink + f(w);
  auto t1 = std::chrono::steady_clock::now();
  (void)sink;
  return std::chrono::duration<double, std::nano>(t1 - t0).count() / (double(reps) * rows.size());
}
template <class F> void acc(const char* name, const std::vector<Row>& rows, F f, double Row::*ref) {
  double mx = 0.0; std::vector<double> e;
  for (const auto& w : rows) {
    const double v = f(w), r = w.*ref;
    const double re = std::abs(v - r) / std::abs(r);
    e.push_back(re); mx = std::max(mx, re);
  }
  std::sort(e.begin(), e.end());
  std::printf("  %-34s max_rel=%.3e  median_rel=%.3e\n", name, mx, e[e.size() / 2]);
}

int main() {
  std::vector<Row> rows; std::ifstream in("ref.csv"); std::string line;
  while (std::getline(in, line)) {
    std::stringstream ss(line); std::string c; std::vector<std::string> f;
    while (std::getline(ss, c, ',')) f.push_back(c);
    rows.push_back({f[0], std::stod(f[1]), std::stod(f[2]), std::stod(f[3]), std::stod(f[4]),
                    std::stod(f[5]), std::stod(f[6]), std::stod(f[7])});
  }
  // R_D requires z>0 (always true here); R_F, R_J at most one zero among x,y,z.
  std::printf("rows=%zu\n", rows.size());
  auto bhRf = [](const Row& w) { return physics::carlsonRf(w.x, w.y, w.z); };
  auto bhRfLoose = [](const Row& w) { return physics::carlsonRf(w.x, w.y, w.z, 2.5e-3); };
  auto bhRd = [](const Row& w) { return physics::carlsonRd(w.x, w.y, w.z); };
  auto bhRdLoose = [](const Row& w) { return physics::carlsonRd(w.x, w.y, w.z, 1.5e-3); };
  auto bhRj = [](const Row& w) { return physics::carlsonRj(w.x, w.y, w.z, w.p); };
  auto bhRjLoose = [](const Row& w) { return physics::carlsonRj(w.x, w.y, w.z, w.p, 1.5e-3); };
  auto cRf = [](const Row& w) { return c95::rf(w.x, w.y, w.z); };
  auto cRd = [](const Row& w) { return c95::rd(w.x, w.y, w.z); };
  auto cRj = [](const Row& w) { return c95::rj(w.x, w.y, w.z, w.p); };
  auto bRf = [](const Row& w) { return boost::math::ellint_rf(w.x, w.y, w.z); };
  auto bRd = [](const Row& w) { return boost::math::ellint_rd(w.x, w.y, w.z); };
  auto bRj = [](const Row& w) { return boost::math::ellint_rj(w.x, w.y, w.z, w.p); };
  std::puts("ACCURACY vs mpmath (dps=40)");
  acc("RF blackhole tol=1e-10", rows, bhRf, &Row::rf);
  acc("RF blackhole tol=2.5e-3 (series test)", rows, bhRfLoose, &Row::rf);
  acc("RF carlson95 r=2.5e-3", rows, cRf, &Row::rf);
  acc("RF boost", rows, bRf, &Row::rf);
  acc("RD blackhole tol=1e-10", rows, bhRd, &Row::rd);
  acc("RD blackhole tol=1.5e-3 (series test)", rows, bhRdLoose, &Row::rd);
  acc("RD carlson95 r=1.5e-3", rows, cRd, &Row::rd);
  acc("RD boost", rows, bRd, &Row::rd);
  acc("RJ blackhole tol=1e-10", rows, bhRj, &Row::rj);
  acc("RJ blackhole tol=1.5e-3 (series test)", rows, bhRjLoose, &Row::rj);
  acc("RJ carlson95 r=1.5e-3", rows, cRj, &Row::rj);
  acc("RJ boost", rows, bRj, &Row::rj);
  c95::itRf = c95::itRd = c95::itRj = 0;
  for (const auto& w : rows) { c95::rf(w.x, w.y, w.z); c95::rd(w.x, w.y, w.z); c95::rj(w.x, w.y, w.z, w.p); }
  std::printf("carlson95 mean duplication steps: RF %.2f RD %.2f RJ %.2f\n",
              double(c95::itRf) / rows.size(), double(c95::itRd) / rows.size(), double(c95::itRj) / rows.size());
  const int reps = 2000;
  std::puts("COST ns/call (median of 5 runs)");
  auto med = [&](auto f) { double t[5]; for (double& v : t) v = timeNs(rows, f, reps); std::sort(t, t + 5); return t[2]; };
  std::printf("  RF blackhole %.1f | carlson95 %.1f | boost %.1f\n", med(bhRf), med(cRf), med(bRf));
  std::printf("  RD blackhole %.1f | carlson95 %.1f | boost %.1f\n", med(bhRd), med(cRd), med(bRd));
  std::printf("  RJ blackhole %.1f | carlson95 %.1f | boost %.1f\n", med(bhRj), med(cRj), med(bRj));
}
