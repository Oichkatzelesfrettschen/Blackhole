// FP32 RK4 photon orbit in Schwarzschild (r_s = 1, geodesic acceleration a = -1.5 L^2 x / r^5)
// with plain vs Kahan-compensated state accumulation; reference = same scheme in long double.
#include <cmath>
#include <cstdio>
#include <chrono>
template <class T> struct S { T x, y, vx, vy; };
template <class T> static S<T> f(const S<T>& s, T L2) {
  const T r2 = s.x * s.x + s.y * s.y, r = std::sqrt(r2), r5 = r2 * r2 * r;
  const T k = T(-1.5) * L2 / r5;
  return {s.vx, s.vy, k * s.x, k * s.y};
}
template <class T> static S<T> axpy(const S<T>& a, const S<T>& b, T h) {
  return {a.x + h * b.x, a.y + h * b.y, a.vx + h * b.vx, a.vy + h * b.vy};
}
template <class T, bool Kahan> static S<T> run(S<T> s, T h, int n, T L2) {
  S<T> c{0, 0, 0, 0};
  for (int i = 0; i < n; ++i) {
    const S<T> k1 = f(s, L2), k2 = f(axpy(s, k1, h / 2), L2), k3 = f(axpy(s, k2, h / 2), L2), k4 = f(axpy(s, k3, h), L2);
    const T w = h / 6;
    S<T> d{w * (k1.x + 2 * k2.x + 2 * k3.x + k4.x), w * (k1.y + 2 * k2.y + 2 * k3.y + k4.y),
           w * (k1.vx + 2 * k2.vx + 2 * k3.vx + k4.vx), w * (k1.vy + 2 * k2.vy + 2 * k3.vy + k4.vy)};
    if constexpr (Kahan) {
      T* sp = &s.x; T* dp = &d.x; T* cp = &c.x;
      for (int j = 0; j < 4; ++j) { const T yv = dp[j] - cp[j]; const T t = sp[j] + yv; cp[j] = (t - sp[j]) - yv; sp[j] = t; }
    } else {
      s = {s.x + d.x, s.y + d.y, s.vx + d.vx, s.vy + d.vy};
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
    auto p = run<float, false>({float(X), float(Y), -1.f, 0.f}, float(h), n, float(L * L));
    auto q = run<float, true>({float(X), float(Y), -1.f, 0.f}, float(h), n, float(L * L));
    auto e = [&](auto s) { return std::hypot(double(s.x - ref.x), double(s.y - ref.y)) / std::hypot(double(ref.x), double(ref.y)); };
    auto t0 = std::chrono::steady_clock::now(); volatile float sink = 0;
    for (int r = 0; r < 200; ++r) sink = sink + run<float, false>({float(X) + 1e-3f * float(r), float(Y), -1.f, 0.f}, float(h), n, float(L * L)).x;
    auto t1 = std::chrono::steady_clock::now();
    for (int r = 0; r < 200; ++r) sink = sink + run<float, true>({float(X) + 1e-3f * float(r), float(Y), -1.f, 0.f}, float(h), n, float(L * L)).x;
    auto t2 = std::chrono::steady_clock::now();
    const double tp = std::chrono::duration<double>(t1 - t0).count(), tk = std::chrono::duration<double>(t2 - t1).count();
    std::printf("b=%.1f h=%-5g steps=%-6d FP32 plain rel err %.2e | FP32 Kahan %.2e | cost ratio kahan/plain %.2f\n", b, h, n, e(p), e(q), tk / tp);
  }
}
