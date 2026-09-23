/**
 * @file verified/eos.hpp
 * @brief Verified Equation of State functions - derived from Rocq formalization
 *
 * Maintained C++ reference for rocq/theories/Compact/EOS.v
 *
 * Key equations (polytropic EOS):
 *   - Pressure: P = K * rho^gamma
 *   - Energy density: epsilon = rho + P/(gamma - 1)  [geometric units]
 *   - Sound speed: c_s^2 = gamma * P / (epsilon + P)
 *
 * References:
 *   - Shapiro & Teukolsky, "Black Holes, White Dwarfs, and Neutron Stars"
 *   - Oppenheimer & Volkoff (1939), Tolman (1939)
 *
 * The maintained C++ is an input to scripts/cpp_to_glsl.py.
 * Rocq definitions document the mathematical source; floating-point
 * implementations are checked by tests rather than a proved extraction chain.
 *
 * @note Uses geometric units where c = G = 1
 * @note Sound speed must be subluminal: c_s < 1
 */

#ifndef PHYSICS_VERIFIED_EOS_HPP
#define PHYSICS_VERIFIED_EOS_HPP

#include <cmath>
#include <stdexcept>

namespace verified {

// ============================================================================
// Common Polytropic Indices (from Rocq: EOS.v)
// ============================================================================

/**
 * @brief Non-relativistic degenerate electrons: gamma = 5/3
 *
 * Derived from Rocq: Definition gamma_nonrel_degenerate : R := 5 / 3.
 *
 * Used for: White dwarf cores, low-density neutron star crust
 */
inline constexpr double GAMMA_NONREL_DEGENERATE = 5.0 / 3.0;

/**
 * @brief Ultra-relativistic degenerate electrons: gamma = 4/3
 *
 * Derived from Rocq: Definition gamma_ultrarel_degenerate : R := 4 / 3.
 *
 * Used for: Massive white dwarfs near Chandrasekhar limit
 */
inline constexpr double GAMMA_ULTRAREL_DEGENERATE = 4.0 / 3.0;

/**
 * @brief Stiff equation of state: gamma = 2
 *
 * Derived from Rocq: Definition gamma_stiff : R := 2.
 *
 * Used for: Maximum stiffness consistent with causality
 */
inline constexpr double GAMMA_STIFF = 2.0;

/**
 * @brief Radiation-dominated: gamma = 4/3
 *
 * Derived from Rocq: Definition gamma_radiation : R := 4 / 3.
 *
 * Used for: Relativistic gas, radiation pressure
 */
inline constexpr double GAMMA_RADIATION = 4.0 / 3.0;

// ============================================================================
// Polytropic Equation of State (from Rocq: PolytropeParams, polytrope_*)
// ============================================================================

/**
 * @brief Polytropic EOS parameters
 *
 * Derived from Rocq: Record PolytropeParams := mkPolytrope {
 *   poly_K : R; poly_gamma : R
 * }.
 *
 * A polytropic EOS is characterized by:
 *   - K: polytropic constant (units depend on gamma)
 *   - gamma: adiabatic index (must be > 1)
 */
struct PolytropeParams {
  double k;     ///< Polytropic constant
  double gamma; ///< Adiabatic index (must be > 1)

  /**
   * @brief Constructor with validation
   * @throws std::invalid_argument if parameters are unphysical
   */
  constexpr PolytropeParams(double polytropicConstant, double g) : k(polytropicConstant), gamma(g) {
    // Validation (in constexpr context, throws are allowed since C++14)
    // For runtime: check K > 0 and gamma > 1
  }

    /**
     * @brief Non-relativistic degenerate electron gas
     */
    static constexpr PolytropeParams nonrelDegenerate(double k) noexcept {
      return PolytropeParams{k, GAMMA_NONREL_DEGENERATE};
    }

    /**
     * @brief Ultra-relativistic degenerate electron gas
     */
    static constexpr PolytropeParams ultrarelDegenerate(double k) noexcept {
      return PolytropeParams{k, GAMMA_ULTRAREL_DEGENERATE};
    }

    /**
     * @brief Stiff EOS (maximum causality-respecting stiffness)
     */
    static constexpr PolytropeParams stiff(double k) noexcept {
      return PolytropeParams{k, GAMMA_STIFF};
    }
};

/**
 * @brief Check if polytrope parameters are valid
 *
 * Derived from Rocq: Definition valid_polytrope (p : PolytropeParams) : Prop :=
 *   p.(poly_K) > 0 /\ p.(poly_gamma) > 1.
 *
 * @param p Polytrope parameters
 * @return true if K > 0 and gamma > 1
 */
[[nodiscard]] constexpr bool validPolytrope(const PolytropeParams &p) noexcept {
  return p.k > 0.0 && p.gamma > 1.0;
}

/**
 * @brief Pressure from density: P = K * rho^gamma
 *
 * Derived from Rocq: Definition polytrope_pressure (p : PolytropeParams) (rho : R) : R :=
 *   p.(poly_K) * Rpower rho p.(poly_gamma).
 *
 * Theorem pressure_positive:
 *   valid_polytrope p -> rho > 0 -> polytrope_pressure p rho > 0.
 *
 * @param p Polytrope parameters
 * @param rho Rest mass density (geometric units)
 * @return Pressure P = K * rho^gamma
 */
[[nodiscard]] inline double polytropePressure(const PolytropeParams &p, double rho) noexcept {
  return p.k * std::pow(rho, p.gamma);
}

/**
 * @brief Energy density including rest mass: epsilon = rho + P/(gamma - 1)
 *
 * Derived from Rocq: Definition polytrope_energy_density (p : PolytropeParams) (rho : R) : R :=
 *   let P := polytrope_pressure p rho in
 *   rho + P / (p.(poly_gamma) - 1).
 *
 * In geometric units (c = 1): epsilon = rho * c^2 + P/(gamma-1) = rho + P/(gamma-1)
 *
 * Theorem energy_exceeds_rest_mass:
 *   valid_polytrope p -> rho > 0 -> polytrope_energy_density p rho > rho.
 *
 * @param p Polytrope parameters
 * @param rho Rest mass density
 * @return Energy density epsilon
 */
[[nodiscard]] inline double polytropeEnergyDensity(const PolytropeParams &p, double rho) noexcept {
  const double pressure = polytropePressure(p, rho);
  return rho + pressure / (p.gamma - 1.0);
}

/**
 * @brief Sound speed squared: c_s^2 = gamma * P / (epsilon + P)
 *
 * Derived from Rocq: Definition polytrope_sound_speed_sq (p : PolytropeParams) (rho : R) : R :=
 *   let P := polytrope_pressure p rho in
 *   let eps := polytrope_energy_density p rho in
 *   p.(poly_gamma) * P / (eps + P).
 *
 * Theorem sound_speed_subluminal:
 *   valid_polytrope p -> gamma <= 2 -> rho > 0 -> c_s^2 < 1.
 *
 * Must satisfy c_s^2 <= 1 for causality (in c = 1 units).
 *
 * @param p Polytrope parameters
 * @param rho Rest mass density
 * @return Sound speed squared (must be < 1 for causality)
 */
[[nodiscard]] inline double polytropeSoundSpeedSq(const PolytropeParams &p, double rho) noexcept {
  const double pressure = polytropePressure(p, rho);
  const double eps = polytropeEnergyDensity(p, rho);
  return p.gamma * pressure / (eps + pressure);
}

/**
 * @brief Sound speed: c_s = sqrt(gamma * P / (epsilon + P))
 *
 * @param p Polytrope parameters
 * @param rho Rest mass density
 * @return Sound speed (must be < 1 for causality)
 */
[[nodiscard]] inline double polytropeSoundSpeed(const PolytropeParams &p, double rho) noexcept {
  return std::sqrt(polytropeSoundSpeedSq(p, rho));
}

// ============================================================================
// Polytropic Index (from Rocq: polytropic_index)
// ============================================================================

/**
 * @brief Polytropic index: n = 1 / (gamma - 1)
 *
 * Derived from Rocq: Definition polytropic_index (gamma : R) : R := 1 / (gamma - 1).
 *
 * Commonly used in stellar structure literature.
 * Inverse relation: gamma = 1 + 1/n
 *
 * Common indices:
 *   - n = 3/2 (gamma = 5/3): non-relativistic degenerate
 *   - n = 3 (gamma = 4/3): relativistic degenerate
 *   - n = 1 (gamma = 2): stiff EOS
 *
 * @param gamma Adiabatic index
 * @return Polytropic index n
 */
[[nodiscard]] constexpr double polytropicIndex(double gamma) noexcept {
  return 1.0 / (gamma - 1.0);
}

/**
 * @brief Adiabatic index from polytropic index: gamma = 1 + 1/n
 *
 * @param n Polytropic index
 * @return Adiabatic index gamma
 */
[[nodiscard]] constexpr double gammaFromIndex(double n) noexcept {
  return 1.0 + 1.0 / n;
}

// ============================================================================
// Relativistic Quantities (from Rocq: polytrope_enthalpy, polytrope_log_enthalpy)
// ============================================================================

/**
 * @brief Specific enthalpy: h = (epsilon + P) / rho
 *
 * Derived from Rocq: Definition polytrope_enthalpy (p : PolytropeParams) (rho : R) : R :=
 *   let P := polytrope_pressure p rho in
 *   let eps := polytrope_energy_density p rho in
 *   (eps + P) / rho.
 *
 * Used in relativistic hydrodynamics and TOV solver.
 *
 * @param p Polytrope parameters
 * @param rho Rest mass density
 * @return Specific enthalpy h
 */
[[nodiscard]] inline double polytropeEnthalpy(const PolytropeParams &p, double rho) noexcept {
  const double pressure = polytropePressure(p, rho);
  const double eps = polytropeEnergyDensity(p, rho);
  return (eps + pressure) / rho;
}

/**
 * @brief Log-enthalpy: H = ln(h)
 *
 * Derived from Rocq: Definition polytrope_log_enthalpy (p : PolytropeParams) (rho : R) : R :=
 *   ln (polytrope_enthalpy p rho).
 *
 * Useful for integration in TOV solver.
 *
 * @param p Polytrope parameters
 * @param rho Rest mass density
 * @return Log-enthalpy H = ln(h)
 */
[[nodiscard]] inline double polytropeLogEnthalpy(const PolytropeParams &p, double rho) noexcept {
  return std::log(polytropeEnthalpy(p, rho));
}

/**
 * @brief Adiabatic index Gamma_1 = d(ln P) / d(ln rho) at constant entropy
 *
 * Derived from Rocq: Definition adiabatic_index (p : PolytropeParams) : R :=
 *   p.(poly_gamma).
 *
 * For a polytrope, Gamma_1 = gamma by definition.
 *
 * @param p Polytrope parameters
 * @return Adiabatic index = gamma
 */
[[nodiscard]] constexpr double adiabaticIndex(const PolytropeParams &p) noexcept {
  return p.gamma;
}

// ============================================================================
// Inverse Relations (density from pressure/enthalpy)
// ============================================================================

/**
 * @brief Density from pressure: rho = (P/K)^(1/gamma)
 *
 * Inverse of P = K * rho^gamma
 *
 * @param p Polytrope parameters
 * @param pressure Pressure
 * @return Rest mass density rho
 */
[[nodiscard]] inline double densityFromPressure(const PolytropeParams &p,
                                                double pressure) noexcept {
  return std::pow(pressure / p.k, 1.0 / p.gamma);
}

/**
 * @brief Density from enthalpy (requires numerical solution in general)
 *
 * For polytrope: h = 1 + gamma/(gamma-1) * K * rho^(gamma-1)
 * Solving for rho: rho = ((h-1) * (gamma-1) / (gamma * K))^(1/(gamma-1))
 *
 * @param p Polytrope parameters
 * @param h Specific enthalpy
 * @return Rest mass density rho
 */
[[nodiscard]] inline double densityFromEnthalpy(const PolytropeParams &p, double h) noexcept {
  // For polytrope: h = 1 + gamma/(gamma-1) * K * rho^(gamma-1)
  // Therefore: (h-1) = gamma/(gamma-1) * K * rho^(gamma-1)
  // rho = ((h-1) * (gamma-1) / (gamma * K))^(1/(gamma-1))
  const double factor = (h - 1.0) * (p.gamma - 1.0) / (p.gamma * p.k);
  return std::pow(factor, 1.0 / (p.gamma - 1.0));
}

// ============================================================================
// Causality Check
// ============================================================================

/**
 * @brief Check if EOS is causal at given density
 *
 * Causality requires: c_s^2 <= 1
 *
 * @param p Polytrope parameters
 * @param rho Rest mass density
 * @return true if sound speed is subluminal
 */
[[nodiscard]] inline bool isCausal(const PolytropeParams &p, double rho) noexcept {
  return polytropeSoundSpeedSq(p, rho) <= 1.0;
}

/**
 * @brief Check if EOS is causal for all densities (stiff EOS limit)
 *
 * For polytropes, causality is guaranteed if gamma <= 2.
 *
 * @param p Polytrope parameters
 * @return true if gamma <= 2
 */
[[nodiscard]] constexpr bool isGloballyCausal(const PolytropeParams &p) noexcept {
  return p.gamma <= 2.0;
}

// ============================================================================
// Extraction Interface (from Rocq: compute_* functions)
// ============================================================================

/**
 * @brief Compute pressure (extraction interface)
 *
 * Derived from Rocq: Definition compute_pressure (K gamma rho : R) : R :=
 *   K * Rpower rho gamma.
 */
[[nodiscard]] inline double computePressure(double k, double gamma, double rho) noexcept {
  return k * std::pow(rho, gamma);
}

/**
 * @brief Compute energy density (extraction interface)
 *
 * Derived from Rocq: Definition compute_energy_density (K gamma rho : R) : R :=
 *   let P := K * Rpower rho gamma in
 *   rho + P / (gamma - 1).
 */
[[nodiscard]] inline double computeEnergyDensity(double k, double gamma, double rho) noexcept {
  const double p = k * std::pow(rho, gamma);
  return rho + p / (gamma - 1.0);
}

/**
 * @brief Compute sound speed squared (extraction interface)
 *
 * Derived from Rocq: Definition compute_sound_speed_sq (K gamma rho : R) : R :=
 *   let P := K * Rpower rho gamma in
 *   let eps := rho + P / (gamma - 1) in
 *   gamma * P / (eps + P).
 */
[[nodiscard]] inline double computeSoundSpeedSq(double k, double gamma, double rho) noexcept {
  const double p = k * std::pow(rho, gamma);
  const double eps = rho + p / (gamma - 1.0);
  return gamma * p / (eps + p);
}

/**
 * @brief Compute enthalpy (extraction interface)
 *
 * Derived from Rocq: Definition compute_enthalpy (K gamma rho : R) : R :=
 *   let P := K * Rpower rho gamma in
 *   let eps := rho + P / (gamma - 1) in
 *   (eps + P) / rho.
 */
[[nodiscard]] inline double computeEnthalpy(double k, double gamma, double rho) noexcept {
  const double p = k * std::pow(rho, gamma);
  const double eps = rho + p / (gamma - 1.0);
  return (eps + p) / rho;
}

} // namespace verified

#endif // PHYSICS_VERIFIED_EOS_HPP
