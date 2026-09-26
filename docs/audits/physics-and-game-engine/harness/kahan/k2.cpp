// FP32 RK4 photon orbit in Schwarzschild (r_s = 1, geodesic acceleration a = -1.5 L^2 x / r^5)
// with plain vs Kahan-compensated state accumulation; reference = same scheme in long double.
#include <cmath>
#include <cstdio>
#include <array>
#include <chrono>
// State (x, y, vx, vy) as a real array, so the compensated loop indexes elements of one object.
template <class T> using S = std::array<T, 4>;
enum { X_, Y_, VX_, VY_ };
template <class T> static S<T> f(const S<T>& s, T L2) {
  const T r2 = s[X_] * s[X_] + s[Y_] * s[Y_], r = std::sqrt(r2), r5 = r2 * r2 * r;
  const T k = T(-1.5) * L2 / r5;
  return {s[VX_], s[VY_], k * s[X_], k * s[Y_]};
}
template <class T> static S<T> axpy(const S<T>& a, const S<T>& b, T h) {
  S<T> out{};
  for (int j = 0; j < 4; ++j) out[j] = a[j] + h * b[j];
  return out;
}
template <class T, bool Kahan> static S<T> run(S<T> s, T h, int n, T L2) {
  S<T> c{};
  for (int i = 0; i < n; ++i) {
    const S<T> k1 = f(s, L2), k2 = f(axpy(s, k1, h / 2), L2), k3 = f(axpy(s, k2, h / 2), L2), k4 = f(axpy(s, k3, h), L2);
    const T w = h / 6;
    S<T> d{};
    for (int j = 0; j < 4; ++j) d[j] = w * (k1[j] + 2 * k2[j] + 2 * k3[j] + k4[j]);
    if constexpr (Kahan) {
      for (int j = 0; j < 4; ++j) { const T yv = d[j] - c[j]; const T t = s[j] + yv; c[j] = (t - s[j]) - yv; s[j] = t; }
    } else {
      for (int j = 0; j < 4; ++j) s[j] = s[j] + d[j];
    }
  }
  return s;
}
int main() {
  // Photon from x=30 heading -x with impact parameter b (b_c = 2.598 for r_s = 1).
  for (double b : {3.5, 2.7}) for (double h : {0.05, 0.01, 0.002}) {
    const double X = 30, Y = b, L = b;  // |v| = 1, L = x*vy - y*vx = b
    const int n = int(std::lround(60.0 / h));
    auto ref = run<long double, false>({X, Y, -1, 0}, h, n, (long double)(L * L));
    auto truth = run<long double, false>({X, Y, -1, 0}, h / 64, n * 64, (long double)(L * L));
    auto p = run<float, false>({float(X), float(Y), -1.f, 0.f}, float(h), n, float(L * L));
    auto q = run<float, true>({float(X), float(Y), -1.f, 0.f}, float(h), n, float(L * L));
    auto e = [&](auto s) { return std::hypot(double(s[X_] - ref[X_]), double(s[Y_] - ref[Y_])) / std::hypot(double(ref[X_]), double(ref[Y_])); };
    auto t0 = std::chrono::steady_clock::now(); volatile float sink = 0;
    for (int r = 0; r < 200; ++r) sink = sink + run<float, false>({float(X) + 1e-3f * float(r), float(Y), -1.f, 0.f}, float(h), n, float(L * L))[X_];
    auto t1 = std::chrono::steady_clock::now();
    for (int r = 0; r < 200; ++r) sink = sink + run<float, true>({float(X) + 1e-3f * float(r), float(Y), -1.f, 0.f}, float(h), n, float(L * L))[X_];
    auto t2 = std::chrono::steady_clock::now();
    const double tp = std::chrono::duration<double>(t1 - t0).count(), tk = std::chrono::duration<double>(t2 - t1).count();
    auto et = [&](auto s) { return std::hypot(double(s[X_] - truth[X_]), double(s[Y_] - truth[Y_])) / std::hypot(double(truth[X_]), double(truth[Y_])); };
    std::printf("b=%.1f h=%-5g steps=%-6d roundoff: plain %.2e kahan %.2e | total vs truth(h/64): truncation-only %.2e plain %.2e kahan %.2e | cost %.2f\n", b, h, n, e(p), e(q), et(ref), et(p), et(q), tk / tp);
  }
}
