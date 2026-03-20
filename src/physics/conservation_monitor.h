/**
 * @file conservation_monitor.h
 * @brief Track conserved quantities along Kerr geodesics.
 *
 * WHY: Numerical geodesic integration introduces drift in the conserved
 * quantities E (energy), L_z (angular momentum), and Q (Carter constant).
 * Monitoring this drift provides:
 *   - Error estimation for the integrator
 *   - Early termination for badly diverged rays
 *   - Convergence testing infrastructure
 *
 * WHAT: Computes E, L_z, Q from the 8D state vector and Kerr metric
 * parameters, and tracks their relative drift during integration.
 *
 * HOW: At each step, compute the conserved quantities from the current
 * state and compare to their initial values. Flag violations above
 * a configurable threshold.
 *
 * References:
 *   - Carter (1968) -- separability and fourth constant
 *   - Chandrasekhar "Mathematical Theory of Black Holes" Ch. 7
 */

#ifndef PHYSICS_CONSERVATION_MONITOR_H
#define PHYSICS_CONSERVATION_MONITOR_H

#include "constants.h"
#include <cmath>
#include <algorithm>

namespace physics {

/**
 * @brief Conserved quantities for Kerr geodesics.
 *
 * For a geodesic with 4-velocity u^mu in the Kerr metric:
 *   E = -g_tt u^t - g_tphi u^phi   (energy per unit mass)
 *   L = g_tphi u^t + g_phiphi u^phi (angular momentum per unit mass)
 *   Q = u_theta^2 + cos^2(theta) [a^2 (mu^2 - E^2) + L^2/sin^2(theta)]
 *       (Carter constant, where mu^2 = -g_mu_nu u^mu u^nu = 0 for photons)
 */
struct ConservedQuantities {
  double E = 0.0;    // Energy
  double Lz = 0.0;   // Angular momentum (z-component)
  double Q = 0.0;    // Carter constant
  double mu2 = 0.0;  // Rest mass invariant (0 for photons, -1 for massive)
};

/**
 * @brief Compute conserved quantities from state vector.
 *
 * Given the 4-velocity components and Kerr metric parameters,
 * compute E, L_z, Q, and the mass invariant mu^2.
 *
 * @param r Radial coordinate [geometric units]
 * @param theta Polar angle
 * @param ut Contravariant time velocity u^t
 * @param ur Contravariant radial velocity u^r
 * @param utheta Contravariant theta velocity u^theta
 * @param uphi Contravariant phi velocity u^phi
 * @param M Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return ConservedQuantities
 */
inline ConservedQuantities compute_conserved(
    double r, double theta,
    double ut, double ur, double utheta, double uphi,
    double M, double a) {

  double cos_th = std::cos(theta);
  double sin_th = std::sin(theta);
  double sin2 = sin_th * sin_th;
  double cos2 = cos_th * cos_th;
  double r_s = 2.0 * M;

  double sigma = r * r + a * a * cos2;
  double delta = r * r - r_s * r + a * a;

  // BL metric components
  double g_tt = -(1.0 - r_s * r / sigma);
  double g_tph = -r_s * r * a * sin2 / sigma;
  double g_phph = (r * r + a * a + r_s * r * a * a * sin2 / sigma) * sin2;
  double g_rr = sigma / delta;
  double g_thth = sigma;

  ConservedQuantities cq;

  // E = -u_t = -(g_tt u^t + g_tphi u^phi)
  cq.E = -(g_tt * ut + g_tph * uphi);

  // L_z = u_phi = g_tphi u^t + g_phiphi u^phi
  cq.Lz = g_tph * ut + g_phph * uphi;

  // mu^2 = -g_mu_nu u^mu u^nu (should be 0 for photons)
  cq.mu2 = -(g_tt * ut * ut + 2.0 * g_tph * ut * uphi
           + g_rr * ur * ur + g_thth * utheta * utheta
           + g_phph * uphi * uphi);

  // Carter constant Q
  double u_theta = g_thth * utheta; // covariant theta component
  cq.Q = u_theta * u_theta + cos2 * (a * a * (cq.mu2 - cq.E * cq.E)
         + cq.Lz * cq.Lz / sin2);

  return cq;
}

/**
 * @brief Conservation monitor for a single geodesic.
 *
 * Tracks the initial values of E, L, Q and reports relative drift.
 */
struct GeodesicConservationMonitor {
  ConservedQuantities initial;
  bool initialized = false;
  double max_E_drift = 0.0;
  double max_Lz_drift = 0.0;
  double max_Q_drift = 0.0;
  double max_mu2_drift = 0.0;
  int step_count = 0;

  /**
   * @brief Initialize with the first state.
   */
  void init(const ConservedQuantities& cq) {
    initial = cq;
    initialized = true;
    max_E_drift = 0.0;
    max_Lz_drift = 0.0;
    max_Q_drift = 0.0;
    max_mu2_drift = 0.0;
    step_count = 0;
  }

  /**
   * @brief Update with a new state and track drift.
   *
   * @param current Current conserved quantities
   * @return Maximum relative drift across all quantities
   */
  double update(const ConservedQuantities& current) {
    if (!initialized) {
      init(current);
      return 0.0;
    }

    ++step_count;

    auto rel_drift = [](double v0, double v1) -> double {
      double scale = std::max(std::abs(v0), 1e-30);
      return std::abs(v1 - v0) / scale;
    };

    double dE = rel_drift(initial.E, current.E);
    double dLz = rel_drift(initial.Lz, current.Lz);
    double dQ = rel_drift(initial.Q, current.Q);
    double dmu2 = std::abs(current.mu2 - initial.mu2);

    max_E_drift = std::max(max_E_drift, dE);
    max_Lz_drift = std::max(max_Lz_drift, dLz);
    max_Q_drift = std::max(max_Q_drift, dQ);
    max_mu2_drift = std::max(max_mu2_drift, dmu2);

    return std::max({dE, dLz, dQ, dmu2});
  }

  /**
   * @brief Check if any conserved quantity has drifted beyond threshold.
   *
   * @param threshold Relative drift tolerance (1e-8 typical for RK4)
   * @return true if any quantity exceeds threshold
   */
  [[nodiscard]] bool violated(double threshold = 1e-8) const {
    return max_E_drift > threshold ||
           max_Lz_drift > threshold ||
           max_Q_drift > threshold ||
           max_mu2_drift > threshold;
  }

  /**
   * @brief Maximum relative drift across all conserved quantities.
   */
  [[nodiscard]] double max_drift() const {
    return std::max({max_E_drift, max_Lz_drift, max_Q_drift, max_mu2_drift});
  }
};

} // namespace physics

#endif // PHYSICS_CONSERVATION_MONITOR_H
