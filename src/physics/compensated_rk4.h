/**
 * @file compensated_rk4.h
 * @brief Classical RK4 with an optional Kahan-compensated state update.
 *
 * An RK4 run of N steps adds N increments to the state. In single precision
 * the rounding of each addition accumulates as roughly N u (u = 2^-24), which
 * for the step counts a GPU ray integrator runs (10^3 to 10^4) outweighs the
 * RK4 truncation error of a smooth photon orbit. Rk4Accumulation::Compensated
 * carries the rounding error of every `state += increment` in a second array
 * and feeds it back into the next increment (Kahan 1965), which holds the
 * accumulated rounding near 2u independent of N, for 4 extra additions per
 * state component per step.
 *
 * The compensation (t - y) - increment is algebraically zero, so it survives
 * only under value-safe floating point: a translation unit compiled with
 * -fassociative-math (part of -ffast-math) folds it away and silently runs the
 * plain update. Blackhole compiles IEEE by default; tests and benches of this
 * header add -fno-fast-math under ENABLE_FAST_MATH, and a GLSL port declares
 * the compensation variables `precise`.
 *
 * schwarzschildPhotonRhs is the Cartesian Binet form of the null geodesic in
 * Schwarzschild, the right-hand side shader/include/geodesics.glsl integrates:
 * x'' = -1.5 r_s h^2 x / r^5 with h = |x cross x'| conserved.
 *
 * Reference: Kahan (1965), Comm. ACM 8, 40 ("Further remarks on reducing
 * truncation errors").
 */

#ifndef PHYSICS_COMPENSATED_RK4_H
#define PHYSICS_COMPENSATED_RK4_H

#include <array>
#include <cmath>
#include <cstddef>

namespace physics {

/// State accumulation of an RK4 step.
enum class Rk4Accumulation {
  Plain,      ///< state += increment
  Compensated ///< Kahan-compensated state += increment
};

/**
 * @brief Fixed-step classical RK4 over an N-component state of type T.
 *
 * @tparam T    float or double
 * @tparam N    state dimension
 * @tparam Mode Plain or Compensated accumulation
 */
template <typename T, std::size_t N, Rk4Accumulation Mode> class Rk4Integrator {
public:
  using State = std::array<T, N>;

  explicit Rk4Integrator(const State &y0) noexcept : y_(y0) {}

  /// Advance by h with dy/dt = f(y) (autonomous right-hand side).
  template <typename Rhs> void step(const Rhs &f, T h) noexcept {
    const T half = h / T(2);
    const State k1 = f(y_);
    const State k2 = f(axpy(y_, k1, half));
    const State k3 = f(axpy(y_, k2, half));
    const State k4 = f(axpy(y_, k3, h));
    const T w = h / T(6);
    for (std::size_t i = 0; i < N; ++i) {
      const T inc = w * (k1[i] + (T(2) * k2[i]) + (T(2) * k3[i]) + k4[i]);
      if constexpr (Mode == Rk4Accumulation::Compensated) {
        const T corrected = inc - c_[i];
        const T sum = y_[i] + corrected;
        c_[i] = (sum - y_[i]) - corrected;
        y_[i] = sum;
      } else {
        y_[i] = y_[i] + inc;
      }
    }
  }

  [[nodiscard]] const State &state() const noexcept { return y_; }

private:
  static State axpy(const State &y, const State &k, T h) noexcept {
    State out{};
    for (std::size_t i = 0; i < N; ++i) {
      out[i] = y[i] + (h * k[i]);
    }
    return out;
  }

  State y_{};
  State c_{}; ///< Kahan compensation, the negated low part of each state component
};

/**
 * @brief Schwarzschild photon in Cartesian Binet form, state (x, y, z, vx, vy, vz).
 *
 * @param s  State
 * @param rs Schwarzschild radius
 * @param h2 Squared specific angular momentum |x cross v|^2 of the ray
 * @return d(state)/d(lambda)
 */
template <typename T>
[[nodiscard]] std::array<T, 6> schwarzschildPhotonRhs(const std::array<T, 6> &s, T rs,
                                                      T h2) noexcept {
  const T r2 = (s[0] * s[0]) + (s[1] * s[1]) + (s[2] * s[2]);
  const T r = std::sqrt(r2);
  const T k = T(-1.5) * rs * h2 / (r2 * r2 * r);
  return {s[3], s[4], s[5], k * s[0], k * s[1], k * s[2]};
}

} // namespace physics

#endif // PHYSICS_COMPENSATED_RK4_H
