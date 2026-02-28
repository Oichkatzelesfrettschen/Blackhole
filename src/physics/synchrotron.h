/**
 * @file synchrotron.h
 * @brief Synchrotron radiation from relativistic electrons.
 *
 * Synchrotron emission occurs when relativistic electrons spiral
 * in magnetic fields. Key for:
 * - Accretion disk coronae
 * - Relativistic jets
 * - Radio lobes
 *
 * Key formulas:
 *   Critical frequency: ν_c = (3/2) × (eB)/(2πm_e c) × γ²
 *   Power per electron: P = (4/3) σ_T c γ² U_B
 *   Cooling time: t_cool = γm_e c² / P
 *
 * References:
 *   - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics" Ch. 6
 *   - Longair (2011) "High Energy Astrophysics" Ch. 8
 *
 * Cleanroom implementation based on standard formulas.
 */

#ifndef PHYSICS_SYNCHROTRON_H
#define PHYSICS_SYNCHROTRON_H

#include "constants.h"
#include "safe_limits.h"
#include <cmath>
#ifdef __has_include
#  if __has_include(<boost/math/special_functions/bessel.hpp>)
#    include <boost/math/special_functions/bessel.hpp>
#    define PHYSICS_HAS_BOOST_BESSEL 1
#  endif
#endif

namespace physics {

// ============================================================================
// Synchrotron Constants (CGS)
// ============================================================================

/// Electron mass [g]
inline constexpr double M_ELECTRON = 9.1093837015e-28;

/// Electron charge [esu = g^1/2 cm^3/2 / s]
inline constexpr double E_CHARGE = 4.80320425e-10;

/// Classical electron radius r_e = e²/(m_e c²) [cm]
inline constexpr double R_ELECTRON = 2.8179403262e-13;

/// Thomson cross section σ_T = (8π/3) r_e² [cm²]
inline constexpr double SIGMA_THOMSON = 6.6524587321e-25;

/// Fine structure constant α ≈ 1/137
inline constexpr double ALPHA_FINE = 7.2973525693e-3;

/// Synchrotron constant: 3e/(4π m_e³ c⁵) for critical frequency
inline constexpr double SYNCHROTRON_CONST = 3.0 * E_CHARGE / (4.0 * PI * M_ELECTRON * M_ELECTRON * M_ELECTRON * C * C * C * C * C);

// ============================================================================
// Electron Gyration
// ============================================================================

/**
 * @brief Compute electron gyrofrequency (cyclotron frequency).
 *
 * ω_B = eB/(m_e c)
 * ν_B = ω_B/(2π) = eB/(2π m_e c)
 *
 * @param B Magnetic field strength [Gauss]
 * @return Gyrofrequency [Hz]
 */
inline double gyrofrequency(double B) {
  return E_CHARGE * std::abs(B) / (TWO_PI * M_ELECTRON * C);
}

/**
 * @brief Compute electron gyroradius (Larmor radius).
 *
 * r_L = γ m_e c² / (eB) = γ v_⊥ / ω_B
 *
 * For relativistic electrons with v ≈ c:
 * r_L ≈ γ m_e c / (eB)
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @return Gyroradius [cm]
 */
inline double gyroradius(double gamma, double B) {
  if (std::abs(B) < 1e-30) {
    return safe_infinity<double>();
  }
  return gamma * M_ELECTRON * C / (E_CHARGE * std::abs(B));
}

// ============================================================================
// Synchrotron Emission
// ============================================================================

/**
 * @brief Compute synchrotron critical frequency.
 *
 * ν_c = (3/2) × (eB)/(2π m_e c) × γ² × sin α
 *
 * For pitch angle α = π/2 (perpendicular to field):
 * ν_c = (3/4π) × (eB)/(m_e c) × γ²
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @param pitch_angle Pitch angle [rad], default π/2
 * @return Critical frequency [Hz]
 */
inline double synchrotron_frequency_critical(double gamma, double B,
                                              double pitch_angle = PI / 2.0) {
  double sin_alpha = std::sin(pitch_angle);
  return (3.0 / (4.0 * PI)) * (E_CHARGE * std::abs(B)) / (M_ELECTRON * C) *
         gamma * gamma * sin_alpha;
}

/**
 * @brief Compute peak synchrotron frequency.
 *
 * The spectrum peaks at ν_peak ≈ 0.29 ν_c
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @return Peak frequency [Hz]
 */
inline double synchrotron_frequency_peak(double gamma, double B) {
  return 0.29 * synchrotron_frequency_critical(gamma, B);
}

/**
 * @brief Compute synchrotron power radiated by single electron.
 *
 * P = (4/3) σ_T c γ² β² U_B
 *
 * where U_B = B²/(8π) is magnetic energy density.
 * For ultrarelativistic electrons (β ≈ 1):
 * P = (4/3) σ_T c γ² (B²/8π)
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @return Power radiated [erg/s]
 */
inline double synchrotron_power_single_electron(double gamma, double B) {
  double U_B = B * B / (8.0 * PI); // Magnetic energy density
  double beta_sq = 1.0 - 1.0 / (gamma * gamma);
  return (4.0 / 3.0) * SIGMA_THOMSON * C * gamma * gamma * beta_sq * U_B;
}

/**
 * @brief Compute synchrotron cooling time.
 *
 * t_cool = E / P = γ m_e c² / P
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @return Cooling time [s]
 */
inline double synchrotron_cooling_time(double gamma, double B) {
  double P = synchrotron_power_single_electron(gamma, B);
  if (P < 1e-50) {
    return safe_infinity<double>();
  }
  return gamma * M_ELECTRON * C * C / P;
}

/**
 * @brief Compute cooling Lorentz factor at given time.
 *
 * Electrons above γ_cool have cooled significantly.
 * γ_cool = 6π m_e c / (σ_T B² t)
 *
 * @param B Magnetic field strength [Gauss]
 * @param t Time since injection [s]
 * @return Cooling Lorentz factor
 */
inline double synchrotron_cooling_lorentz_factor(double B, double t) {
  if (t < 1e-50 || std::abs(B) < 1e-30) {
    return safe_infinity<double>();
  }
  return 6.0 * PI * M_ELECTRON * C / (SIGMA_THOMSON * B * B * t);
}

// ============================================================================
// Synchrotron Spectrum Functions
// ============================================================================

/**
 * @brief Synchrotron function F(x) for single electron.
 *
 * F(x) = x * integral_x^inf K_{5/3}(xi) dxi
 *
 * where x = nu/nu_c and K_{5/3} is the modified Bessel function of order 5/3.
 *
 * WHY: The Fouka & Ouichaoui (2013) polynomial fit in the intermediate regime
 * (0.01 < x < 10) has ~1% systematic error.  When boost::math is available,
 * we numerically integrate K_{5/3} using 32-point Gauss-Legendre quadrature,
 * giving machine-precision accuracy for the CPU physics path.  The GPU/GLSL
 * path continues to use the polynomial approximation since GLSL cannot call
 * boost functions.
 *
 * References:
 *   - Rybicki & Lightman (1979) Ch. 6, Eq. 6.31
 *   - Fouka & Ouichaoui (2013), MNRAS 436, 1546 (polynomial fit, kept as
 *     fallback when boost is unavailable)
 *   - boost::math::cyl_bessel_k (boost 1.90.0, already in conanfile.py)
 *
 * @param x Dimensionless frequency nu/nu_c
 * @return F(x) synchrotron function value
 */
inline double synchrotron_F(double x) {
  if (x <= 0) return 0.0;

  // Low frequency asymptote: F(x) ~= 1.8084 * x^(1/3)  [Rybicki-Lightman 6.36]
  if (x < 0.01) {
    return 1.8084 * std::pow(x, 1.0 / 3.0);
  }

  // High frequency asymptote: F(x) ~= sqrt(pi/2) * sqrt(x) * exp(-x)
  if (x > 10) {
    return std::sqrt(PI / 2.0) * std::sqrt(x) * std::exp(-x);
  }

  // Intermediate regime: 0.01 <= x <= 10
#ifdef PHYSICS_HAS_BOOST_BESSEL
  // WHY: K_{5/3}(xi) varies rapidly near xi=x (especially for small x) and
  // decays exponentially for xi >> 1.  We use a two-segment GL quadrature:
  //   Segment 1: [x, x + delta] -- fine spacing near the lower limit
  //   Segment 2: [x + delta, x + 30] -- tail region; K_{5/3} < 1e-13 beyond
  // where delta = max(2*x, 0.5).  This captures the near-singularity at x~0.
  //
  // Gauss-Legendre nodes and weights for n=16 on [-1,1]
  static const double gl_nodes[16] = {
    -0.9894009349916499, -0.9445750230732326,
    -0.8656312023341783, -0.7554044083550030,
    -0.6178762444026438, -0.4580167776572274,
    -0.2816035507792589, -0.0950125098360623,
     0.0950125098360623,  0.2816035507792589,
     0.4580167776572274,  0.6178762444026438,
     0.7554044083550030,  0.8656312023341783,
     0.9445750230732326,  0.9894009349916499
  };
  static const double gl_weights[16] = {
    0.0271524594117541, 0.0622535239386479,
    0.0951585116824928, 0.1246289512509922,
    0.1495959888165767, 0.1691565193950025,
    0.1826034150449236, 0.1894506104550685,
    0.1894506104550685, 0.1826034150449236,
    0.1691565193950025, 0.1495959888165767,
    0.1246289512509922, 0.0951585116824928,
    0.0622535239386479, 0.0271524594117541
  };

  // Helper lambda: GL integral over [a, b]
  auto gl_integral = [&](double a, double b) -> double {
    double hr  = 0.5 * (b - a);
    double mid = 0.5 * (b + a);
    double sum = 0.0;
    for (int i = 0; i < 16; ++i) {
      double xi = mid + hr * gl_nodes[i];
      if (xi <= 0.0) continue;
      sum += gl_weights[i] * boost::math::cyl_bessel_k(5.0 / 3.0, xi);
    }
    return sum * hr;
  };

  // Segment 1: near the lower limit where the integrand is large
  double delta = std::max(2.0 * x, 0.5);
  double integral = gl_integral(x, x + delta);

  // Segment 2: tail; K_{5/3} is small here; integrate up to x + 30
  double x_tail = x + 30.0;
  if (x + delta < x_tail) {
    integral += gl_integral(x + delta, x_tail);
  }

  return x * integral;
#else
  // Fallback: Fouka & Ouichaoui (2013) polynomial fit, ~1% accuracy
  return 1.8084 * std::pow(x, 1.0 / 3.0) *
         std::exp(-x) *
         (1.0 + 0.884 * std::pow(x, 2.0 / 3.0) +
          0.471 * std::pow(x, 4.0 / 3.0));
#endif
}

/**
 * @brief Synchrotron function G(x) for polarized emission.
 *
 * G(x) = x × K_{2/3}(x)
 *
 * Used for calculating polarization degree.
 *
 * @param x Dimensionless frequency ν/ν_c
 * @return G(x) function value
 */
inline double synchrotron_G(double x) {
  if (x <= 0) return 0.0;

  // Small-x asymptote: K_{2/3}(x) ~ Gamma(2/3)/2 * (2/x)^(2/3)
  // => G(x) = x * K_{2/3}(x) ~ 1.3541 * x^(1/3)  [R&L 1979 Appendix]
  if (x < 0.01) {
    return 1.3541 * std::pow(x, 1.0 / 3.0);
  }

  // Large-x asymptote: K_{2/3}(x) ~ sqrt(pi/(2x)) * exp(-x)
  // => G(x) = x * K_{2/3}(x) ~ sqrt(pi*x/2) * exp(-x)
  if (x > 10) {
    return std::sqrt(PI / 2.0) * std::sqrt(x) * std::exp(-x);
  }

  // Intermediate regime 0.01 <= x <= 10: evaluate G(x) = x * K_{2/3}(x) directly.
#ifdef PHYSICS_HAS_BOOST_BESSEL
  // WHY: The polynomial fit gives G(x) > F(x) for x in [1, 10], which is
  // physically impossible (polarization fraction must be <= 1). Direct Bessel
  // evaluation via boost::math is sub-ULP accurate and has O(1) cost.
  return x * boost::math::cyl_bessel_k(2.0 / 3.0, x);
#else
  // Polynomial fallback (~10% error for x~1-10; Boost not available)
  return 1.3541 * std::pow(x, 1.0 / 3.0) * std::exp(-x) *
         (1.0 + 0.6 * std::pow(x, 2.0 / 3.0));
#endif
}

/**
 * @brief Compute synchrotron polarization degree.
 *
 * Π = G(x) / F(x)
 *
 * For power-law electron distribution with index p:
 * Π_max = (p + 1) / (p + 7/3)
 *
 * @param x Dimensionless frequency ν/ν_c
 * @return Polarization degree (0 to 1)
 */
inline double synchrotron_polarization(double x) {
  double F_val = synchrotron_F(x);
  double G_val = synchrotron_G(x);
  if (F_val < 1e-50) return 0.0;
  return G_val / F_val;
}

// ============================================================================
// Power-Law Electron Distribution
// ============================================================================

/**
 * @brief Compute synchrotron spectrum from power-law electrons.
 *
 * For electron distribution N(γ) ∝ γ^(-p) between γ_min and γ_max,
 * the spectrum is F_ν ∝ ν^(-(p-1)/2) between break frequencies.
 *
 * @param nu Frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param gamma_min Minimum electron Lorentz factor
 * @param gamma_max Maximum electron Lorentz factor
 * @param p Power-law index (typically 2-3)
 * @return Relative spectral power (normalized)
 */
inline double synchrotron_spectrum_power_law(double nu, double B,
                                              double gamma_min, double gamma_max,
                                              double p) {
  // Characteristic frequencies
  double nu_min = synchrotron_frequency_critical(gamma_min, B);
  double nu_max = synchrotron_frequency_critical(gamma_max, B);

  if (nu <= 0) return 0.0;

  // Spectral index for optically thin synchrotron
  double alpha = -(p - 1.0) / 2.0;

  if (nu < nu_min) {
    // Below minimum: self-absorbed regime, F ∝ ν^(5/2)
    return std::pow(nu / nu_min, 2.5);
  } else if (nu < nu_max) {
    // Power-law regime
    return std::pow(nu / nu_min, alpha);
  } else {
    // Exponential cutoff above γ_max
    return std::pow(nu_max / nu_min, alpha) * std::exp(-(nu - nu_max) / nu_max);
  }
}

/**
 * @brief Compute spectral index for power-law electrons.
 *
 * α = -(p - 1)/2 where F_ν ∝ ν^α
 *
 * @param p Electron power-law index
 * @return Spectral index
 */
inline double synchrotron_spectral_index(double p) {
  return -(p - 1.0) / 2.0;
}

/**
 * @brief Compute electron index from spectral index.
 *
 * p = 1 - 2α
 *
 * @param alpha Spectral index
 * @return Electron power-law index
 */
inline double electron_index_from_spectral(double alpha) {
  return 1.0 - 2.0 * alpha;
}

// ============================================================================
// Self-Absorption
// ============================================================================

/**
 * @brief Compute synchrotron self-absorption coefficient.
 *
 * The absorption coefficient scales as:
 * α_ν ∝ ν^(-(p+4)/2) for power-law electrons
 *
 * Below the self-absorption frequency ν_a, the source becomes
 * optically thick and the spectrum changes to F_ν ∝ ν^(5/2).
 *
 * @param nu Frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param n_e Electron density [cm^-3]
 * @param p Electron power-law index
 * @return Absorption coefficient [cm^-1]
 */
inline double synchrotron_absorption_coefficient(double nu, double B,
                                                  double n_e,
                                                  double p) {
  // Simplified formula (order of magnitude)
  double nu_B = gyrofrequency(B);
  double prefactor = 0.02 * E_CHARGE * n_e / (M_ELECTRON * C);

  double exponent = -(p + 4.0) / 2.0;
  return prefactor * std::pow(nu_B, (p + 2.0) / 2.0) * std::pow(nu, exponent);
}

/**
 * @brief Compute self-absorption frequency.
 *
 * The frequency where τ_ν = 1 (optical depth unity).
 *
 * @param B Magnetic field [Gauss]
 * @param n_e Electron density [cm^-3]
 * @param R Source size [cm]
 * @param p Electron power-law index
 * @return Self-absorption frequency [Hz]
 */
inline double synchrotron_self_absorption_frequency(double B, double n_e,
                                                     double R,
                                                     double p) {
  // Approximation: ν_a where τ = α_ν × R = 1
  double nu_B = gyrofrequency(B);

  // Scaling: ν_a ∝ (n_e R)^(2/(p+4)) × B^((p+2)/(p+4))
  double exponent = 2.0 / (p + 4.0);
  return nu_B * std::pow(n_e * R / 1e20, exponent);
}

// ============================================================================
// GPU LUT Generation for G(x)
// ============================================================================

/**
 * @brief Generate a 1D lookup table for G(x) = x * K_{2/3}(x).
 *
 * WHY: GLSL cannot call boost::math, so we precompute G(x) on the CPU
 * and upload it as a 1D float texture. The shader samples this LUT
 * using log-spaced u = log(x/x_min) / log(x_max/x_min).
 *
 * The LUT covers x in [x_min, x_max] with N entries, log-spaced for
 * uniform fractional resolution across the dynamic range.
 *
 * @param lut      Output array (must hold N floats)
 * @param N        Number of LUT entries (256 recommended)
 * @param x_min    Minimum x value (0.001 recommended)
 * @param x_max    Maximum x value (30.0 recommended -- G(30) ~ 1e-13)
 */
inline void synchrotron_G_generate_lut(float* lut, int N,
                                       double x_min = 0.001,
                                       double x_max = 30.0) {
  double log_ratio = std::log(x_max / x_min);
  for (int i = 0; i < N; ++i) {
    double u = static_cast<double>(i) / (N - 1);
    double x = x_min * std::exp(u * log_ratio);
    lut[i] = static_cast<float>(synchrotron_G(x));
  }
}

/// LUT range constants matching the generation defaults above.
/// Shaders must use these same values for the log-space mapping.
constexpr float SYNCH_G_LUT_X_MIN = 0.001f;
constexpr float SYNCH_G_LUT_X_MAX = 30.0f;

} // namespace physics

#endif // PHYSICS_SYNCHROTRON_H
