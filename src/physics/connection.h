/**
 * @file connection.h
 * @brief Connection coefficients (Christoffel symbols) for spacetime metrics.
 *
 * Provides metric tensor and Christoffel symbol calculations for:
 * - Schwarzschild metric
 * - Kerr metric (Boyer-Lindquist coordinates)
 *
 * The Christoffel symbols of the second kind are:
 *   Gamma^alpha_mu_nu = (1/2) g^alpha_beta (d_mu g_beta_nu + d_nu g_beta_mu - d_beta g_mu_nu)
 *
 * Used in the geodesic equation:
 *   d^2 x^alpha / dlambda^2 + Gamma^alpha_mu_nu (dx^mu/dlambda)(dx^nu/dlambda) = 0
 *
 * References:
 *   - Misner, Thorne, Wheeler (1973) - Gravitation
 *   - Chandrasekhar (1983) - Mathematical Theory of Black Holes
 *
 * Cleanroom implementation based on standard GR textbook formulas.
 */

#ifndef PHYSICS_CONNECTION_H
#define PHYSICS_CONNECTION_H

#include <array>
#include <cmath>
#include <cstddef>

namespace physics {

// ============================================================================
// Type Definitions
// ============================================================================

/**
 * @brief 4x4 metric tensor (symmetric).
 *
 * Indices: [0]=t, [1]=r, [2]=theta, [3]=phi
 */
using Metric4 = std::array<std::array<double, 4>, 4>;

/**
 * @brief 4x4x4 connection coefficients.
 *
 * conn[alpha][mu][nu] = Gamma^alpha_mu_nu
 */
using Connection4 = std::array<std::array<std::array<double, 4>, 4>, 4>;

// ============================================================================
// Kerr Metric Tensor (Boyer-Lindquist Coordinates)
// ============================================================================

/**
 * @brief Compute covariant Kerr metric tensor g_mu_nu.
 *
 * In Boyer-Lindquist coordinates (t, r, theta, phi):
 *
 *   g_tt = -(1 - r_s r/Sigma)
 *   g_tphi = g_phit = -r_s r a sin^2(theta) / Sigma
 *   g_rr = Sigma/Delta
 *   g_thth = Sigma
 *   g_phiphi = (r^2 + a^2 + r_s r a^2 sin^2(theta) / Sigma) sin^2(theta)
 *
 * where Sigma = r^2 + a^2 cos^2(theta), Delta = r^2 - r_s r + a^2
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param rS Schwarzschild radius
 * @return Covariant metric tensor
 */
[[nodiscard]] inline Metric4 kerrGcov(double r, double theta, double a, double rS) {
  Metric4 g{};

  const double cosTheta = std::cos(theta);
  const double sinTheta = std::sin(theta);
  const double sin2 = sinTheta * sinTheta;
  const double cos2 = cosTheta * cosTheta;
  const double a2 = a * a;
  const double r2 = r * r;

  // Sigma = r^2 + a^2 cos^2(theta)
  double sigma = r2 + (a2 * cos2);

  // Delta = r^2 - r_s r + a^2
  double delta = r2 - (rS * r) + a2;

  // Avoid division by zero
  if (std::abs(sigma) < 1e-30) {
    sigma = 1e-30;
  }
  if (std::abs(delta) < 1e-30) {
    delta = (delta >= 0) ? 1e-30 : -1e-30;
  }

  // Metric components (in c=G=1 units, geometric)
  // g_tt
  g.at(0).at(0) = -(1.0 - ((rS * r) / sigma));

  // g_tphi = g_phit
  g.at(0).at(3) = -((rS * r * a * sin2) / sigma);
  g.at(3).at(0) = g.at(0).at(3);

  // g_rr
  g.at(1).at(1) = sigma / delta;

  // g_thth
  g.at(2).at(2) = sigma;

  // g_phiphi
  g.at(3).at(3) = (r2 + a2 + ((rS * r * a2 * sin2) / sigma)) * sin2;

  return g;
}

/**
 * @brief Compute contravariant Kerr metric tensor g^mu_nu.
 *
 * The inverse metric for Kerr in Boyer-Lindquist coordinates.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param rS Schwarzschild radius
 * @return Contravariant metric tensor
 */
[[nodiscard]] inline Metric4 kerrGcon(double r, double theta, double a, double rS) {
  Metric4 g{};

  const double cosTheta = std::cos(theta);
  const double sinTheta = std::sin(theta);
  const double sin2 = sinTheta * sinTheta;
  const double cos2 = cosTheta * cosTheta;
  const double a2 = a * a;
  const double r2 = r * r;

  // Sigma = r^2 + a^2 cos^2(theta)
  double sigma = r2 + (a2 * cos2);

  // Delta = r^2 - r_s r + a^2
  double delta = r2 - (rS * r) + a2;

  // bigA = (r^2 + a^2)^2 - a^2 Delta sin^2(theta)
  const double r2PlusA2 = r2 + a2;
  double bigA = (r2PlusA2 * r2PlusA2) - (a2 * delta * sin2);

  // Avoid singularities
  if (std::abs(sigma) < 1e-30) {
    sigma = 1e-30;
  }
  if (std::abs(delta) < 1e-30) {
    delta = (delta >= 0) ? 1e-30 : -1e-30;
  }
  if (std::abs(bigA) < 1e-30) {
    bigA = 1e-30;
  }

  // Inverse metric components
  // g^tt = -bigA / (Delta Sigma)
  g.at(0).at(0) = -(bigA / (delta * sigma));

  // g^tphi = g^phit = -r_s r a / (Delta Sigma)
  g.at(0).at(3) = -((rS * r * a) / (delta * sigma));
  g.at(3).at(0) = g.at(0).at(3);

  // g^rr = Delta / Sigma
  g.at(1).at(1) = delta / sigma;

  // g^thth = 1 / Sigma
  g.at(2).at(2) = 1.0 / sigma;

  // g^phiphi = (Delta - a^2 sin^2(theta)) / (Delta Sigma sin^2(theta))
  if (std::abs(sin2) > 1e-30) {
    g.at(3).at(3) = (delta - (a2 * sin2)) / (delta * sigma * sin2);
  } else {
    g.at(3).at(3) = 0.0; // At poles
  }

  return g;
}

// ============================================================================
// Kerr Christoffel Symbols
// ============================================================================

/**
 * @brief Compute Christoffel symbols for Kerr metric.
 *
 * Returns Gamma^alpha_mu_nu for the Kerr metric in Boyer-Lindquist coordinates.
 * Uses analytic expressions from Chandrasekhar (1983).
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param rS Schwarzschild radius
 * @return Connection coefficients conn[alpha][mu][nu] = Gamma^alpha_mu_nu
 */
[[nodiscard]] inline Connection4 kerrConnection(double r, double theta, double a, double rS) {
  Connection4 conn{};

  const double cosTheta = std::cos(theta);
  const double sinTheta = std::sin(theta);
  const double sin2 = sinTheta * sinTheta;
  const double cos2 = cosTheta * cosTheta;
  const double a2 = a * a;
  const double r2 = r * r;

  // Sigma = r^2 + a^2 cos^2(theta)
  const double sigma = r2 + (a2 * cos2);

  // Delta = r^2 - r_s r + a^2
  double delta = r2 - (rS * r) + a2;

  // Avoid singularities
  const double sigma2 = sigma * sigma;
  const double sigma3 = sigma2 * sigma;
  if (std::abs(sigma) < 1e-30) {
    return conn; // Return zeros near singularity
  }
  if (std::abs(delta) < 1e-30) {
    delta = (delta >= 0) ? 1e-30 : -1e-30;
  }

  // Useful combinations
  const double r2PlusA2 = r2 + a2;
  const double rsR = rS * r;

  // ============================================================
  // Gamma^t components
  // ============================================================

  // Gamma^t_tr = Gamma^t_rt
  const double gammaTTr = (rsR * (r2 - (a2 * cos2))) / (sigma2 * delta);
  conn.at(0).at(0).at(1) = gammaTTr;
  conn.at(0).at(1).at(0) = gammaTTr;

  // Gamma^t_ttheta = Gamma^t_thetat
  const double gammaTTtheta = -((rsR * a2 * sinTheta * cosTheta) / sigma2);
  conn.at(0).at(0).at(2) = gammaTTtheta;
  conn.at(0).at(2).at(0) = gammaTTtheta;

  // Gamma^t_rphi = Gamma^t_phir
  const double gammaTRphi =
      -((a * rsR * sin2 * (r2 - (a2 * cos2))) / (sigma2 * delta)) - ((a * rS * sin2) / sigma);
  conn.at(0).at(1).at(3) = gammaTRphi;
  conn.at(0).at(3).at(1) = gammaTRphi;

  // Gamma^t_thetaphi = Gamma^t_phitheta
  const double gammaTThetaphi = (2.0 * a * rsR * (r2 + a2) * sinTheta * cosTheta) / sigma2;
  conn.at(0).at(2).at(3) = gammaTThetaphi;
  conn.at(0).at(3).at(2) = gammaTThetaphi;

  // ============================================================
  // Gamma^r components
  // ============================================================

  // Gamma^r_tt
  conn.at(1).at(0).at(0) = (delta * rsR * (r2 - (a2 * cos2))) / sigma3;

  // Gamma^r_tphi = Gamma^r_phit
  const double gammaRTphi = -((a * delta * rsR * sin2 * (r2 - (a2 * cos2))) / sigma3);
  conn.at(1).at(0).at(3) = gammaRTphi;
  conn.at(1).at(3).at(0) = gammaRTphi;

  // Gamma^r_rr
  conn.at(1).at(1).at(1) = ((r * delta) - (sigma * (r - (rS / 2.0)))) / (sigma * delta);

  // Gamma^r_rtheta = Gamma^r_thetar
  const double gammaRRtheta = -((a2 * sinTheta * cosTheta) / sigma);
  conn.at(1).at(1).at(2) = gammaRRtheta;
  conn.at(1).at(2).at(1) = gammaRRtheta;

  // Gamma^r_thth
  conn.at(1).at(2).at(2) = -((r * delta) / sigma);

  // Gamma^r_phiphi
  conn.at(1).at(3).at(3) =
      ((-delta * r * sin2) - ((delta * a2 * sin2 * sin2 * rsR * (r2 - (a2 * cos2))) / sigma2)) /
      sigma;

  // ============================================================
  // Gamma^theta components
  // ============================================================

  // Gamma^theta_tt
  conn.at(2).at(0).at(0) = -((rsR * a2 * sinTheta * cosTheta) / sigma3);

  // Gamma^theta_tphi = Gamma^theta_phit
  const double gammaThetaTphi = (a * rsR * (r2 + a2) * sinTheta * cosTheta) / sigma3;
  conn.at(2).at(0).at(3) = gammaThetaTphi;
  conn.at(2).at(3).at(0) = gammaThetaTphi;

  // Gamma^theta_rr
  conn.at(2).at(1).at(1) = (a2 * sinTheta * cosTheta) / (sigma * delta);

  // Gamma^theta_rtheta = Gamma^theta_thetar
  const double gammaThetaRtheta = r / sigma;
  conn.at(2).at(1).at(2) = gammaThetaRtheta;
  conn.at(2).at(2).at(1) = gammaThetaRtheta;

  // Gamma^theta_thth
  conn.at(2).at(2).at(2) = -((a2 * sinTheta * cosTheta) / sigma);

  // Gamma^theta_phiphi
  const double sinCos = sinTheta * cosTheta;
  const double aTerm = (r2PlusA2 * r2PlusA2) + (a2 * delta * sin2);
  conn.at(2).at(3).at(3) =
      -(sinCos * ((aTerm / sigma) + ((2.0 * a2 * rsR * sin2) / sigma2))) / sigma;

  // ============================================================
  // Gamma^phi components
  // ============================================================

  // Gamma^phi_tr = Gamma^phi_rt
  const double gammaPhiTr = (a * rsR * (r2 - (a2 * cos2))) / (sigma2 * delta);
  conn.at(3).at(0).at(1) = gammaPhiTr;
  conn.at(3).at(1).at(0) = gammaPhiTr;

  // Gamma^phi_ttheta = Gamma^phi_thetat
  const double gammaPhiTtheta = -((a * rsR * cosTheta) / (sigma2 * sinTheta));
  if (std::abs(sinTheta) > 1e-10) {
    conn.at(3).at(0).at(2) = gammaPhiTtheta;
    conn.at(3).at(2).at(0) = gammaPhiTtheta;
  }

  // Gamma^phi_rphi = Gamma^phi_phir
  const double gammaPhiRphi =
      (r / sigma) - ((a2 * sin2 * rsR * (r2 - (a2 * cos2))) / (sigma2 * delta));
  conn.at(3).at(1).at(3) = gammaPhiRphi;
  conn.at(3).at(3).at(1) = gammaPhiRphi;

  // Gamma^phi_thetaphi = Gamma^phi_phitheta
  const double gammaPhiThetaphi =
      (cosTheta / sinTheta) + ((a2 * rsR * sinTheta * cosTheta) / sigma2);
  if (std::abs(sinTheta) > 1e-10) {
    conn.at(3).at(2).at(3) = gammaPhiThetaphi;
    conn.at(3).at(3).at(2) = gammaPhiThetaphi;
  }

  return conn;
}

// ============================================================================
// Schwarzschild Connection (Special Case of Kerr with a=0)
// ============================================================================

/**
 * @brief Compute covariant Schwarzschild metric tensor.
 *
 * Special case of Kerr with a=0.
 *
 * @param r Radial coordinate
 * @param theta Polar angle (only needed for phi-phi component)
 * @param rS Schwarzschild radius
 * @return Covariant metric tensor
 */
[[nodiscard]] inline Metric4 schwarzschildGcov(double r, double theta, double rS) {
  return kerrGcov(r, theta, 0.0, rS);
}

/**
 * @brief Compute contravariant Schwarzschild metric tensor.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param rS Schwarzschild radius
 * @return Contravariant metric tensor
 */
[[nodiscard]] inline Metric4 schwarzschildGcon(double r, double theta, double rS) {
  return kerrGcon(r, theta, 0.0, rS);
}

/**
 * @brief Compute Christoffel symbols for Schwarzschild metric.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param rS Schwarzschild radius
 * @return Connection coefficients
 */
[[nodiscard]] inline Connection4 schwarzschildConnection(double r, double theta, double rS) {
  return kerrConnection(r, theta, 0.0, rS);
}

// ============================================================================
// Index Raising/Lowering
// ============================================================================

/**
 * @brief Lower index on a 4-vector.
 *
 * u_mu = g_mu_nu u^nu
 *
 * @param ucon Contravariant 4-vector u^mu
 * @param gcov Covariant metric tensor
 * @return Covariant 4-vector u_mu
 */
[[nodiscard]] inline std::array<double, 4> lowerIndex(const std::array<double, 4> &ucon,
                                                      const Metric4 &gcov) {
  std::array<double, 4> ucov{};
  for (size_t mu = 0; mu < 4; ++mu) {
    for (size_t nu = 0; nu < 4; ++nu) {
      ucov.at(mu) += gcov.at(mu).at(nu) * ucon.at(nu);
    }
  }
  return ucov;
}

/**
 * @brief Raise index on a 4-vector.
 *
 * u^mu = g^mu_nu u_nu
 *
 * @param ucov Covariant 4-vector u_mu
 * @param gcon Contravariant metric tensor
 * @return Contravariant 4-vector u^mu
 */
[[nodiscard]] inline std::array<double, 4> raiseIndex(const std::array<double, 4> &ucov,
                                                      const Metric4 &gcon) {
  std::array<double, 4> ucon{};
  for (size_t mu = 0; mu < 4; ++mu) {
    for (size_t nu = 0; nu < 4; ++nu) {
      ucon.at(mu) += gcon.at(mu).at(nu) * ucov.at(nu);
    }
  }
  return ucon;
}

/**
 * @brief Compute geodesic acceleration from connection.
 *
 * a^alpha = -Gamma^alpha_mu_nu u^mu u^nu
 *
 * @param ucon 4-velocity u^mu
 * @param conn Connection coefficients
 * @return 4-acceleration a^alpha
 */
[[nodiscard]] inline std::array<double, 4> geodesicAcceleration(const std::array<double, 4> &ucon,
                                                                const Connection4 &conn) {
  std::array<double, 4> acc{};
  for (size_t alpha = 0; alpha < 4; ++alpha) {
    for (size_t mu = 0; mu < 4; ++mu) {
      for (size_t nu = 0; nu < 4; ++nu) {
        acc.at(alpha) -= conn.at(alpha).at(mu).at(nu) * ucon.at(mu) * ucon.at(nu);
      }
    }
  }
  return acc;
}

} // namespace physics

#endif // PHYSICS_CONNECTION_H
