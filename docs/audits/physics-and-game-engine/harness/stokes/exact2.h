// Exact constant-coefficient polarized transfer step, direct-integral form (no K^{-1} split):
//   S(s) = e^{-Ks} S0 + (int_0^s e^{-Kt} dt) J,  K = aI*1 + K',  K' in so(1,3).
// e^{-K't} = a0(t) - b1(t) K' + a2(t) K'^2 - b3(t) K'^3 from the minimal polynomial
// (x^2 - L1^2)(x^2 + L2^2), (L1 + i L2)^2 = (eta + i rho).(eta + i rho).
#pragma once
#include <cmath>
#include <algorithm>
namespace ex2 {
struct Kp { double aQ, aV, rV, rQ; };
inline void applyKp(const Kp& k, const double v[4], double o[4]) {
  o[0] = k.aQ * v[1] + k.aV * v[3];
  o[1] = k.aQ * v[0] + k.rV * v[2];
  o[2] = -k.rV * v[1] + k.rQ * v[3];
  o[3] = k.aV * v[0] - k.rQ * v[2];
}
inline double shcm1(double x) { const double x2 = x * x; return std::abs(x) < 0.1 ? x2 / 6.0 * (1.0 + x2 / 20.0 * (1.0 + x2 / 42.0)) : std::sinh(x) / x - 1.0; }
inline double sincm1(double x) { const double x2 = x * x; return std::abs(x) < 0.1 ? -x2 / 6.0 * (1.0 - x2 / 20.0 * (1.0 - x2 / 42.0)) : std::sin(x) / x - 1.0; }
inline double ex1(double y) { return std::abs(y) < 1e-12 ? 1.0 - 0.5 * y : -std::expm1(-y) / y; }  // (1-e^{-y})/y
// M[n] = int_0^s t^n e^{-a t} dt, n = 0..7.
struct RecipTable { double r[41]; constexpr RecipTable() : r{} { for (int n = 1; n <= 40; ++n) r[n] = 1.0 / n; } };
inline constexpr RecipTable kRecip{};
inline void moments(double a, double s, double M[8]) {
  const double x = a * s;
  if (x > 8.0) {  // upward recurrence is stable for x > n
    const double e = std::exp(-x); double sn = 1.0;
    M[0] = -std::expm1(-x) / a;
    for (int n = 1; n < 8; ++n) { sn *= s; M[n] = (n * M[n - 1] - sn * e) / a; }
    return;
  }
  // Downward recurrence m_{n-1} = (x m_n + e^{-x}) / n on m_n = int_0^1 u^n e^{-xu} du, stable for x <= 8.
  const double e = std::exp(-x);
  double m = e / (41.0 + x);
  for (int n = 40; n >= 8; --n) m = (x * m + e) * kRecip.r[n];  // m now holds m_7
  double sp = std::pow(s, 8);
  M[7] = sp * m;
  const double is = 1.0 / s;
  for (int n = 7; n >= 1; --n) { m = (x * m + e) * kRecip.r[n]; sp *= is; M[n - 1] = sp * m; }
}
struct Out { double i, q, u, v; };
inline Out step(const double S0[4], const double J[4], double aI, double aQ, double aV, double rV, double rQ, double s) {
  const Kp k{aQ, aV, rV, rQ};
  const double e2 = aQ * aQ + aV * aV, r2 = rV * rV + rQ * rQ, er = aQ * rQ + aV * rV;
  const double h = 0.5 * (e2 - r2), root = std::sqrt(h * h + er * er);
  const double L1s = std::max(0.0, h + root), L2s = std::max(0.0, root - h);
  const double L1 = std::sqrt(L1s), L2 = std::sqrt(L2s), D = L1s + L2s;
  const double x1 = L1 * s, x2 = L2 * s;
  // Homogeneous coefficients at t = s.
  double a0 = 1, a2 = 0.5 * s * s, b1 = s, b3 = s * s * s / 6.0;
  if (D > 0) {
    const double sh = s * (1.0 + shcm1(x1)), sn = s * (1.0 + sincm1(x2));
    const double chm1 = 2.0 * std::sinh(0.5 * x1) * std::sinh(0.5 * x1), omc = 2.0 * std::sin(0.5 * x2) * std::sin(0.5 * x2);
    a0 = 1.0 + (L2s * chm1 - L1s * omc) / D;
    a2 = (chm1 + omc) / D;
    b1 = (L2s * sh + L1s * sn) / D;
    b3 = s * (shcm1(x1) - sincm1(x2)) / D;
  }
  // Integrated coefficients int_0^s e^{-aI t} {a0,a2,b1,b3}(t) dt.
  double M[8]; bool haveM = false;
  auto needM = [&]() { if (!haveM) { moments(aI, s, M); haveM = true; } };
  auto phi = [&](double x) { return s * ex1(x * s); };
  const double Ich = 0.5 * (phi(aI - L1) + phi(aI + L1));
  const double Ish = (x1 >= 0.1) ? (phi(aI - L1) - phi(aI + L1)) / (2.0 * L1)
                                 : (needM(), M[1]) + L1s * M[3] / 6.0 + L1s * L1s * M[5] / 120.0 + L1s * L1s * L1s * M[7] / 5040.0;
  const double E = std::exp(-aI * s), C = std::cos(x2), Sn = std::sin(x2);
  const double omEC = -std::expm1(-aI * s) * C + 2.0 * std::sin(0.5 * x2) * std::sin(0.5 * x2);  // 1 - E*C
  double Ic, Is;
  if (x2 >= 0.1) {
    const double den = aI * aI + L2s;
    Ic = (aI * omEC + L2 * E * Sn) / den;
    Is = (omEC - aI * E * s * (1.0 + sincm1(x2))) / den;
  } else {
    needM();
    Ic = M[0] - L2s * M[2] / 2.0 + L2s * L2s * M[4] / 24.0 - L2s * L2s * L2s * M[6] / 720.0;
    Is = M[1] - L2s * M[3] / 6.0 + L2s * L2s * M[5] / 120.0 - L2s * L2s * L2s * M[7] / 5040.0;
  }
  double A0, A2, B1, B3;
  if (D <= 0) { needM(); A0 = M[0]; A2 = M[2] / 2.0; B1 = M[1]; B3 = M[3] / 6.0; }
  else {
    A0 = (L2s * Ich + L1s * Ic) / D;
    B1 = (L2s * Ish + L1s * Is) / D;
    if (std::max(x1, x2) < 0.1) {
      needM();
      const double q4 = L1s * L1s - L1s * L2s + L2s * L2s;
      A2 = M[2] / 2.0 + (L1s - L2s) * M[4] / 24.0 + q4 * M[6] / 720.0;
      B3 = M[3] / 6.0 + (L1s - L2s) * M[5] / 120.0 + q4 * M[7] / 5040.0;
    } else {
      A2 = (Ich - Ic) / D;
      B3 = (Ish - Is) / D;
    }
  }
  double v1[4], v2[4], v3[4], j1[4], j2[4], j3[4];
  applyKp(k, S0, v1); applyKp(k, v1, v2); applyKp(k, v2, v3);
  applyKp(k, J, j1); applyKp(k, j1, j2); applyKp(k, j2, j3);
  double o[4];
  for (int i = 0; i < 4; ++i)
    o[i] = E * (a0 * S0[i] - b1 * v1[i] + a2 * v2[i] - b3 * v3[i]) + (A0 * J[i] - B1 * j1[i] + A2 * j2[i] - B3 * j3[i]);
  return {o[0], o[1], o[2], o[3]};
}
}  // namespace ex2
