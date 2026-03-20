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

#include <algorithm>
#include <cmath>

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
  double e = 0.0;    // Energy
  double lz = 0.0;   // Angular momentum (z-component)
  double q = 0.0;    // Carter constant
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
 * @param mGeom Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return ConservedQuantities
 */
[[nodiscard]] inline ConservedQuantities computeConserved(
    double r, double theta,
    double ut, double ur, double utheta, double uphi,
    double mGeom, double a) {

  const double cosTh = std::cos(theta);
  const double sinTh = std::sin(theta);
  const double sin2 = sinTh * sinTh;
  const double cos2 = cosTh * cosTh;
  const double rS = 2.0 * mGeom;

  const double sigma = (r * r) + (a * a * cos2);
  const double delta = ((r * r) - (rS * r)) + (a * a);

  // BL metric components
  const double gTt  = -(1.0 - ((rS * r) / sigma));
  const double gTph = -((rS * r * a * sin2) / sigma);
  const double gPhph = ((r * r) + (a * a) + ((rS * r * a * a * sin2) / sigma)) * sin2;
  const double gRr   = sigma / delta;
  const double gThth = sigma;

  ConservedQuantities cq;

  // E = -u_t = -(g_tt u^t + g_tphi u^phi)
  cq.e = -((gTt * ut) + (gTph * uphi));

  // L_z = u_phi = g_tphi u^t + g_phiphi u^phi
  cq.lz = (gTph * ut) + (gPhph * uphi);

  // mu^2 = -g_mu_nu u^mu u^nu (should be 0 for photons)
  cq.mu2 = -((gTt * ut * ut) + (2.0 * gTph * ut * uphi)
           + (gRr * ur * ur) + (gThth * utheta * utheta)
           + (gPhph * uphi * uphi));

  // Carter constant Q
  const double uTheta = gThth * utheta; // covariant theta component
  cq.q = (uTheta * uTheta) + (cos2 * ((a * a * (cq.mu2 - (cq.e * cq.e)))
         + (cq.lz * cq.lz / sin2)));

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
  double maxEDrift = 0.0;
  double maxLzDrift = 0.0;
  double maxQDrift = 0.0;
  double maxMu2Drift = 0.0;
  int stepCount = 0;

  /**
   * @brief Initialize with the first state.
   */
  void init(const ConservedQuantities& cq) {
    initial = cq;
    initialized = true;
    maxEDrift = 0.0;
    maxLzDrift = 0.0;
    maxQDrift = 0.0;
    maxMu2Drift = 0.0;
    stepCount = 0;
  }

  /**
   * @brief Update with a new state and track drift.
   *
   * @param current Current conserved quantities
   * @return Maximum relative drift across all quantities
   */
  [[nodiscard]] double update(const ConservedQuantities& current) {
    if (!initialized) {
      init(current);
      return 0.0;
    }

    ++stepCount;

    auto relDrift = [](double v0, double v1) -> double {
      const double scale = std::max(std::abs(v0), 1e-30);
      return std::abs(v1 - v0) / scale;
    };

    const double dE   = relDrift(initial.e,  current.e);
    const double dLz  = relDrift(initial.lz, current.lz);
    const double dQ   = relDrift(initial.q,  current.q);
    const double dmu2 = std::abs(current.mu2 - initial.mu2);

    maxEDrift   = std::max(maxEDrift,   dE);
    maxLzDrift  = std::max(maxLzDrift,  dLz);
    maxQDrift   = std::max(maxQDrift,   dQ);
    maxMu2Drift = std::max(maxMu2Drift, dmu2);

    return std::max({dE, dLz, dQ, dmu2});
  }

  /**
   * @brief Check if any conserved quantity has drifted beyond threshold.
   *
   * @param threshold Relative drift tolerance (1e-8 typical for RK4)
   * @return true if any quantity exceeds threshold
   */
  [[nodiscard]] bool violated(double threshold = 1e-8) const {
    return maxEDrift > threshold ||
           maxLzDrift > threshold ||
           maxQDrift > threshold ||
           maxMu2Drift > threshold;
  }

  /**
   * @brief Maximum relative drift across all conserved quantities.
   */
  [[nodiscard]] double maxDrift() const {
    return std::max({maxEDrift, maxLzDrift, maxQDrift, maxMu2Drift});
  }
};

} // namespace physics

#endif // PHYSICS_CONSERVATION_MONITOR_H
