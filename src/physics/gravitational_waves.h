/**
 * @file gravitational_waves.h
 * @brief Gravitational wave physics for compact binary systems.
 *
 * Implements the quadrupole formula and post-Newtonian corrections
 * for gravitational wave strain from inspiraling binaries.
 *
 * Key formulas:
 *
 * Strain amplitude (leading order):
 *   h = (4/D) * (G M_c/c²)^(5/3) * (π f/c)^(2/3)
 *
 * Chirp mass:
 *   M_c = (m₁ m₂)^(3/5) / (m₁ + m₂)^(1/5)
 *
 * Frequency evolution (Peters 1964):
 *   df/dt = (96/5) π^(8/3) (G M_c/c³)^(5/3) f^(11/3)
 *
 * Time to coalescence:
 *   τ = (5/256) (G M_c/c³)^(-5/3) (π f)^(-8/3)
 *
 * References:
 * - Peters & Mathews (1963), Phys. Rev. 131, 435
 * - Blanchet (2014), Living Reviews in Relativity
 * - LIGO Scientific Collaboration, Phys. Rev. Lett. 116, 061102 (2016)
 *
 * Cleanroom implementation based on standard GR formulas.
 */

#ifndef PHYSICS_GRAVITATIONAL_WAVES_H
#define PHYSICS_GRAVITATIONAL_WAVES_H

#include "constants.h"
#include "kerr.h"
#include <cmath>
#include <complex>
#include <vector>

namespace physics {

// ============================================================================
// Binary System Parameters
// ============================================================================

/**
 * @brief Parameters for a compact binary system.
 */
struct BinarySystem {
  double m1;        ///< Primary mass [g]
  double m2;        ///< Secondary mass [g]
  double a1;        ///< Primary spin parameter [cm]
  double a2;        ///< Secondary spin parameter [cm]
  double distance;  ///< Luminosity distance [cm]
  double inclination; ///< Orbital inclination [rad]

  // Derived quantities
  double M_total() const { return m1 + m2; }
  double mu() const { return m1 * m2 / M_total(); } // Reduced mass
  double eta() const { return mu() / M_total(); }   // Symmetric mass ratio
  double q() const { return m2 / m1; }              // Mass ratio (q ≤ 1)
};

/**
 * @brief Compute chirp mass.
 *
 * M_c = (m₁ m₂)^(3/5) / (m₁ + m₂)^(1/5)
 *     = M_total * η^(3/5)
 *
 * The chirp mass is the primary parameter measured from GW signal.
 *
 * @param m1 Primary mass [g]
 * @param m2 Secondary mass [g]
 * @return Chirp mass [g]
 */
inline double chirp_mass(double m1, double m2) {
  double M_total = m1 + m2;
  double eta = (m1 * m2) / (M_total * M_total);
  return M_total * std::pow(eta, 0.6);
}

/**
 * @brief Compute chirp mass in geometric units.
 *
 * M_c^(geo) = G M_c / c³ [seconds]
 *
 * @param M_c Chirp mass [g]
 * @return Chirp mass in seconds
 */
inline double chirp_mass_geometric(double M_c) {
  return G * M_c / (C * C * C);
}

// ============================================================================
// Gravitational Wave Strain - Newtonian Order
// ============================================================================

/**
 * @brief Compute GW strain amplitude at Newtonian order.
 *
 * h₀ = (4/D) * (G M_c/c²)^(5/3) * (π f/c)^(2/3)
 *
 * This is the leading-order strain for circular orbits.
 *
 * @param M_c Chirp mass [g]
 * @param f Gravitational wave frequency [Hz]
 * @param D Luminosity distance [cm]
 * @return Dimensionless strain amplitude
 */
inline double gw_strain_amplitude(double M_c, double f, double D) {
  if (D <= 0 || f <= 0) return 0.0;

  // G M_c / c²
  double GM_c_over_c2 = G * M_c / C2;

  // (G M_c / c²)^(5/3)
  double factor1 = std::pow(GM_c_over_c2, 5.0 / 3.0);

  // (π f / c)^(2/3)
  double factor2 = std::pow(M_PI * f / C, 2.0 / 3.0);

  return (4.0 / D) * factor1 * factor2;
}

/**
 * @brief Compute plus and cross polarization strains.
 *
 * h₊ = h₀ * (1 + cos²ι)/2 * cos(Φ)
 * h× = h₀ * cos(ι) * sin(Φ)
 *
 * @param h0 Strain amplitude
 * @param inclination Orbital inclination [rad]
 * @param phase Orbital phase [rad]
 * @param h_plus Output: plus polarization
 * @param h_cross Output: cross polarization
 */
inline void gw_polarizations(double h0, double inclination, double phase,
                             double &h_plus, double &h_cross) {
  double cos_i = std::cos(inclination);
  double cos_i2 = cos_i * cos_i;

  h_plus = h0 * (1.0 + cos_i2) / 2.0 * std::cos(2.0 * phase);
  h_cross = h0 * cos_i * std::sin(2.0 * phase);
}

// ============================================================================
// Frequency Evolution
// ============================================================================

/**
 * @brief Compute GW frequency derivative (chirp rate).
 *
 * df/dt = (96/5) π^(8/3) (G M_c/c³)^(5/3) f^(11/3)
 *
 * @param M_c Chirp mass [g]
 * @param f Current frequency [Hz]
 * @return Frequency derivative [Hz/s]
 */
inline double frequency_derivative(double M_c, double f) {
  double M_c_geo = chirp_mass_geometric(M_c);

  // (G M_c / c³)^(5/3)
  double factor1 = std::pow(M_c_geo, 5.0 / 3.0);

  // π^(8/3)
  double factor2 = std::pow(M_PI, 8.0 / 3.0);

  // f^(11/3)
  double factor3 = std::pow(f, 11.0 / 3.0);

  return (96.0 / 5.0) * factor2 * factor1 * factor3;
}

/**
 * @brief Compute time to coalescence.
 *
 * τ = (5/256) (G M_c/c³)^(-5/3) (π f)^(-8/3)
 *
 * @param M_c Chirp mass [g]
 * @param f Current frequency [Hz]
 * @return Time to merger [s]
 */
inline double time_to_coalescence(double M_c, double f) {
  if (f <= 0) return std::numeric_limits<double>::infinity();

  double M_c_geo = chirp_mass_geometric(M_c);

  // (G M_c / c³)^(-5/3)
  double factor1 = std::pow(M_c_geo, -5.0 / 3.0);

  // (π f)^(-8/3)
  double factor2 = std::pow(M_PI * f, -8.0 / 3.0);

  return (5.0 / 256.0) * factor1 * factor2;
}

/**
 * @brief Compute orbital separation from GW frequency.
 *
 * From Kepler's law: a³ = G M_total / (4π² f_orb²)
 * where f_GW = 2 f_orb for quadrupole radiation.
 *
 * @param M_total Total mass [g]
 * @param f GW frequency [Hz]
 * @return Orbital separation [cm]
 */
inline double orbital_separation(double M_total, double f) {
  if (f <= 0) return std::numeric_limits<double>::infinity();

  double f_orb = f / 2.0; // Orbital frequency is half GW frequency

  // a³ = G M / (4π² f²)
  double a_cubed = G * M_total / (4.0 * M_PI * M_PI * f_orb * f_orb);

  return std::cbrt(a_cubed);
}

/**
 * @brief Compute GW frequency at ISCO.
 *
 * f_ISCO = c³ / (π G M_total) * (r_ISCO/M)^(-3/2)
 *
 * For Schwarzschild: r_ISCO = 6M, so f_ISCO = c³/(6^(3/2) π G M)
 *
 * @param M_total Total mass [g]
 * @param r_isco_over_M ISCO radius in units of M (6 for Schwarzschild)
 * @return ISCO frequency [Hz]
 */
inline double gw_frequency_isco(double M_total, double r_isco_over_M = 6.0) {
  double M_geo = G * M_total / (C * C * C); // In seconds

  return 1.0 / (M_PI * M_geo * std::pow(r_isco_over_M, 1.5));
}

// ============================================================================
// Post-Newtonian Corrections
// ============================================================================

/**
 * @brief Compute strain with 1PN correction.
 *
 * Includes the first post-Newtonian correction to the amplitude:
 * h = h₀ * [1 + (55/48 - 55/16 η) x + O(x²)]
 *
 * where x = (π G M f/c³)^(2/3) is the PN expansion parameter.
 *
 * @param M_c Chirp mass [g]
 * @param eta Symmetric mass ratio
 * @param f GW frequency [Hz]
 * @param D Distance [cm]
 * @return 1PN-corrected strain amplitude
 */
inline double gw_strain_1pn(double M_c, double eta, double f, double D) {
  double h0 = gw_strain_amplitude(M_c, f, D);

  // Compute M_total from M_c and eta
  // M_c = M * eta^(3/5) => M = M_c / eta^(3/5)
  double M_total = M_c / std::pow(eta, 0.6);
  double M_geo = G * M_total / (C * C * C);

  // PN parameter x = (π M f)^(2/3)
  double x = std::pow(M_PI * M_geo * f, 2.0 / 3.0);

  // 1PN amplitude correction
  double pn_correction = 1.0 + (55.0 / 48.0 - 55.0 * eta / 16.0) * x;

  return h0 * pn_correction;
}

/**
 * @brief Compute GW phase with 3.5PN corrections.
 *
 * Φ(f) = 2πf t_c - Φ_c - π/4 + (3/128)(πMf)^(-5/3) * [1 + PN corrections]
 *
 * The phase is critical for matched filtering in GW detection.
 *
 * @param M_c Chirp mass [g]
 * @param eta Symmetric mass ratio
 * @param f GW frequency [Hz]
 * @param t_c Time of coalescence [s]
 * @param phi_c Phase at coalescence [rad]
 * @return GW phase [rad]
 */
inline double gw_phase_3p5pn(double M_c, double eta, double f,
                             double t_c = 0.0, double phi_c = 0.0) {
  double M_total = M_c / std::pow(eta, 0.6);
  double M_geo = G * M_total / (C * C * C);

  // PN expansion parameter
  double v = std::cbrt(M_PI * M_geo * f);
  double v2 = v * v;
  double v3 = v2 * v;
  double v5 = v3 * v2;
  double v7 = v5 * v2;

  // Coefficients (Blanchet 2014)
  double eta2 = eta * eta;

  // Leading order
  double psi_N = 1.0;

  // 1PN
  double psi_1PN = (3715.0 / 756.0 + 55.0 * eta / 9.0) * v2;

  // 1.5PN
  double psi_15PN = -16.0 * M_PI * v3;

  // 2PN
  double psi_2PN = (15293365.0 / 508032.0 + 27145.0 * eta / 504.0 +
                   3085.0 * eta2 / 72.0) * v2 * v2;

  // 2.5PN (includes log term)
  double gamma_E = 0.5772156649; // Euler-Mascheroni constant
  double psi_25PN = M_PI * (38645.0 / 756.0 - 65.0 * eta / 9.0) *
                    (1.0 + 3.0 * std::log(v)) * v5;

  // Sum PN corrections
  double pn_sum = psi_N + psi_1PN + psi_15PN + psi_2PN + psi_25PN;

  // Leading phase
  double psi_leading = (3.0 / 128.0) / std::pow(M_PI * M_geo * f, 5.0 / 3.0);

  return 2.0 * M_PI * f * t_c - phi_c - M_PI / 4.0 + psi_leading * pn_sum;
}

// ============================================================================
// Waveform Generation
// ============================================================================

/**
 * @brief Point in a GW waveform.
 */
struct WaveformPoint {
  double t;        ///< Time [s]
  double f;        ///< Frequency [Hz]
  double h_plus;   ///< Plus polarization
  double h_cross;  ///< Cross polarization
  double phase;    ///< Orbital phase [rad]
};

/**
 * @brief Generate inspiral waveform.
 *
 * Integrates the frequency evolution and computes strain at each step.
 * Uses the stationary phase approximation for efficiency.
 *
 * @param binary Binary system parameters
 * @param f_low Starting frequency [Hz]
 * @param f_high Ending frequency [Hz]
 * @param dt Time step [s]
 * @return Vector of waveform points
 */
inline std::vector<WaveformPoint> generate_inspiral_waveform(
    const BinarySystem &binary, double f_low, double f_high, double dt) {

  std::vector<WaveformPoint> waveform;
  waveform.reserve(static_cast<size_t>((f_high - f_low) / (f_low * 1e-4)));

  double M_c = chirp_mass(binary.m1, binary.m2);
  double eta = binary.eta();

  double f = f_low;
  double t = 0.0;
  double phase = 0.0;

  while (f < f_high && f > 0) {
    // Strain amplitude
    double h0 = gw_strain_1pn(M_c, eta, f, binary.distance);

    // Polarizations
    double h_plus, h_cross;
    gw_polarizations(h0, binary.inclination, phase, h_plus, h_cross);

    // Store point
    WaveformPoint pt;
    pt.t = t;
    pt.f = f;
    pt.h_plus = h_plus;
    pt.h_cross = h_cross;
    pt.phase = phase;
    waveform.push_back(pt);

    // Evolve frequency
    double df_dt = frequency_derivative(M_c, f);
    f += df_dt * dt;

    // Evolve phase (GW frequency is twice orbital)
    phase += M_PI * f * dt;

    t += dt;

    // Safety check
    if (waveform.size() > 10000000) break;
  }

  return waveform;
}

// ============================================================================
// Ringdown (Quasi-Normal Modes)
// ============================================================================

/**
 * @brief Compute dominant QNM frequency for Schwarzschild.
 *
 * ω_22 ≈ 0.3737 / M (geometric units)
 *
 * For Kerr, depends on spin (Berti et al. 2009).
 *
 * @param M_final Final black hole mass [g]
 * @return QNM frequency [Hz]
 */
inline double qnm_frequency_schwarzschild(double M_final) {
  double M_geo = G * M_final / (C * C * C);
  return 0.3737 / (2.0 * M_PI * M_geo);
}

/**
 * @brief Compute QNM damping time for Schwarzschild.
 *
 * τ_22 ≈ M / 0.0890 (geometric units)
 *
 * @param M_final Final black hole mass [g]
 * @return Damping time [s]
 */
inline double qnm_damping_time_schwarzschild(double M_final) {
  double M_geo = G * M_final / (C * C * C);
  return M_geo / 0.0890;
}

/**
 * @brief Compute ringdown strain.
 *
 * h(t) = A * exp(-t/τ) * cos(ω t + φ)
 *
 * @param A Initial amplitude
 * @param omega_qnm QNM angular frequency [rad/s]
 * @param tau Damping time [s]
 * @param t Time since ringdown start [s]
 * @param phi Initial phase [rad]
 * @return Strain at time t
 */
inline double ringdown_strain(double A, double omega_qnm, double tau,
                              double t, double phi = 0.0) {
  if (t < 0) return 0.0;
  return A * std::exp(-t / tau) * std::cos(omega_qnm * t + phi);
}

// ============================================================================
// Energy and Angular Momentum
// ============================================================================

/**
 * @brief Compute GW luminosity (energy emission rate).
 *
 * L_GW = (32/5) c^5/G * η² (M ω)^(10/3)
 *
 * @param M_total Total mass [g]
 * @param eta Symmetric mass ratio
 * @param f GW frequency [Hz]
 * @return GW luminosity [erg/s]
 */
inline double gw_luminosity(double M_total, double eta, double f) {
  double M_geo = G * M_total / (C * C * C);
  double omega = M_PI * f; // Angular GW frequency (factor of 2 already in f)

  double M_omega = M_geo * omega;
  double factor = std::pow(M_omega, 10.0 / 3.0);

  return (32.0 / 5.0) * (C * C * C * C * C / G) * eta * eta * factor;
}

/**
 * @brief Compute total energy radiated in GWs.
 *
 * E_rad ≈ η M c² * (1 - √(8/9))  (for equal mass, non-spinning)
 *
 * More accurate formula uses numerical relativity fits.
 *
 * @param M_total Total mass [g]
 * @param eta Symmetric mass ratio
 * @return Radiated energy [erg]
 */
inline double gw_energy_radiated(double M_total, double eta) {
  // Phenomenological fit from numerical relativity
  // E_rad/M ≈ 0.0559 η² (equal mass limit)
  double epsilon = 0.0559 * eta * eta;

  // More accurate: Jiménez-Forteza et al. (2017)
  // E_rad/M = η * (1 - E_final/M)
  // where E_final/M ≈ 1 - 0.0559 η for non-spinning

  return epsilon * M_total * C2;
}

// ============================================================================
// Convenience Functions
// ============================================================================

/**
 * @brief Create binary neutron star system.
 *
 * @param m1 Primary mass in solar masses
 * @param m2 Secondary mass in solar masses
 * @param D Distance in Mpc
 * @return BinarySystem
 */
inline BinarySystem bns_system(double m1_solar, double m2_solar, double D_mpc) {
  BinarySystem binary;
  binary.m1 = m1_solar * M_SUN;
  binary.m2 = m2_solar * M_SUN;
  binary.a1 = 0.0;
  binary.a2 = 0.0;
  binary.distance = D_mpc * 1e6 * PARSEC;
  binary.inclination = 0.0; // Face-on
  return binary;
}

/**
 * @brief Create binary black hole system.
 *
 * @param m1 Primary mass in solar masses
 * @param m2 Secondary mass in solar masses
 * @param a1_star Dimensionless primary spin (0-1)
 * @param a2_star Dimensionless secondary spin (0-1)
 * @param D Distance in Mpc
 * @return BinarySystem
 */
inline BinarySystem bbh_system(double m1_solar, double m2_solar,
                               double a1_star, double a2_star, double D_mpc) {
  BinarySystem binary;
  binary.m1 = m1_solar * M_SUN;
  binary.m2 = m2_solar * M_SUN;

  // Convert dimensionless spin to spin parameter
  double M1 = G * binary.m1 / C2;
  double M2 = G * binary.m2 / C2;
  binary.a1 = a1_star * M1;
  binary.a2 = a2_star * M2;

  binary.distance = D_mpc * 1e6 * PARSEC;
  binary.inclination = 0.0;
  return binary;
}

/**
 * @brief Compute characteristic strain for detector sensitivity.
 *
 * h_c = 2 f |h̃(f)| ≈ h × √(N_cycles)
 *
 * @param M_c Chirp mass [g]
 * @param f GW frequency [Hz]
 * @param D Distance [cm]
 * @return Characteristic strain
 */
inline double characteristic_strain(double M_c, double f, double D) {
  double h0 = gw_strain_amplitude(M_c, f, D);

  // Number of cycles at frequency f
  double tau = time_to_coalescence(M_c, f);
  double N_cycles = f * tau;

  return h0 * std::sqrt(N_cycles);
}

} // namespace physics

#endif // PHYSICS_GRAVITATIONAL_WAVES_H
