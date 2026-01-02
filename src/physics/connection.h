/**
 * @file connection.h
 * @brief Connection coefficients (Christoffel symbols) for spacetime metrics.
 *
 * Provides metric tensor and Christoffel symbol calculations for:
 * - Schwarzschild metric
 * - Kerr metric (Boyer-Lindquist coordinates)
 *
 * The Christoffel symbols of the second kind are:
 *   Γ^α_μν = (1/2) g^αβ (∂_μ g_βν + ∂_ν g_βμ - ∂_β g_μν)
 *
 * Used in the geodesic equation:
 *   d²x^α/dλ² + Γ^α_μν (dx^μ/dλ)(dx^ν/dλ) = 0
 *
 * References:
 *   - Misner, Thorne, Wheeler (1973) - Gravitation
 *   - Chandrasekhar (1983) - Mathematical Theory of Black Holes
 *
 * Cleanroom implementation based on standard GR textbook formulas.
 */

#ifndef PHYSICS_CONNECTION_H
#define PHYSICS_CONNECTION_H

#include "constants.h"
#include "kerr.h"
#include <array>
#include <cmath>

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
 * conn[alpha][mu][nu] = Γ^α_μν
 */
using Connection4 = std::array<std::array<std::array<double, 4>, 4>, 4>;

// ============================================================================
// Kerr Metric Tensor (Boyer-Lindquist Coordinates)
// ============================================================================

/**
 * @brief Compute covariant Kerr metric tensor g_μν.
 *
 * In Boyer-Lindquist coordinates (t, r, θ, φ):
 *
 *   g_tt = -(1 - r_s r/Σ)
 *   g_tφ = g_φt = -r_s r a sin²θ / Σ
 *   g_rr = Σ/Δ
 *   g_θθ = Σ
 *   g_φφ = (r² + a² + r_s r a² sin²θ / Σ) sin²θ
 *
 * where Σ = r² + a² cos²θ, Δ = r² - r_s r + a²
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param r_s Schwarzschild radius
 * @return Covariant metric tensor
 */
inline Metric4 kerr_gcov(double r, double theta, double a, double r_s) {
  Metric4 g{};

  double cos_theta = std::cos(theta);
  double sin_theta = std::sin(theta);
  double sin2 = sin_theta * sin_theta;
  double cos2 = cos_theta * cos_theta;

  double a2 = a * a;
  double r2 = r * r;

  // Σ = r² + a² cos²θ
  double sigma = r2 + a2 * cos2;

  // Δ = r² - r_s r + a²
  double delta = r2 - r_s * r + a2;

  // Avoid division by zero
  if (std::abs(sigma) < 1e-30) {
    sigma = 1e-30;
  }
  if (std::abs(delta) < 1e-30) {
    delta = (delta >= 0) ? 1e-30 : -1e-30;
  }

  // Metric components (in c=G=1 units, geometric)
  // g_tt
  g[0][0] = -(1.0 - r_s * r / sigma);

  // g_tφ = g_φt
  g[0][3] = -r_s * r * a * sin2 / sigma;
  g[3][0] = g[0][3];

  // g_rr
  g[1][1] = sigma / delta;

  // g_θθ
  g[2][2] = sigma;

  // g_φφ
  g[3][3] = (r2 + a2 + r_s * r * a2 * sin2 / sigma) * sin2;

  return g;
}

/**
 * @brief Compute contravariant Kerr metric tensor g^μν.
 *
 * The inverse metric for Kerr in Boyer-Lindquist coordinates.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param r_s Schwarzschild radius
 * @return Contravariant metric tensor
 */
inline Metric4 kerr_gcon(double r, double theta, double a, double r_s) {
  Metric4 g{};

  double cos_theta = std::cos(theta);
  double sin_theta = std::sin(theta);
  double sin2 = sin_theta * sin_theta;
  double cos2 = cos_theta * cos_theta;

  double a2 = a * a;
  double r2 = r * r;

  // Σ = r² + a² cos²θ
  double sigma = r2 + a2 * cos2;

  // Δ = r² - r_s r + a²
  double delta = r2 - r_s * r + a2;

  // A = (r² + a²)² - a² Δ sin²θ
  double r2_plus_a2 = r2 + a2;
  double A = r2_plus_a2 * r2_plus_a2 - a2 * delta * sin2;

  // Avoid singularities
  if (std::abs(sigma) < 1e-30)
    sigma = 1e-30;
  if (std::abs(delta) < 1e-30)
    delta = (delta >= 0) ? 1e-30 : -1e-30;
  if (std::abs(A) < 1e-30)
    A = 1e-30;

  // Inverse metric components
  // g^tt = -A / (Δ Σ)
  g[0][0] = -A / (delta * sigma);

  // g^tφ = g^φt = -r_s r a / (Δ Σ)
  g[0][3] = -r_s * r * a / (delta * sigma);
  g[3][0] = g[0][3];

  // g^rr = Δ / Σ
  g[1][1] = delta / sigma;

  // g^θθ = 1 / Σ
  g[2][2] = 1.0 / sigma;

  // g^φφ = (Δ - a² sin²θ) / (Δ Σ sin²θ)
  if (std::abs(sin2) > 1e-30) {
    g[3][3] = (delta - a2 * sin2) / (delta * sigma * sin2);
  } else {
    g[3][3] = 0.0; // At poles
  }

  return g;
}

// ============================================================================
// Kerr Christoffel Symbols
// ============================================================================

/**
 * @brief Compute Christoffel symbols for Kerr metric.
 *
 * Returns Γ^α_μν for the Kerr metric in Boyer-Lindquist coordinates.
 * Uses analytic expressions from Chandrasekhar (1983).
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param r_s Schwarzschild radius
 * @return Connection coefficients conn[α][μ][ν] = Γ^α_μν
 */
inline Connection4 kerr_connection(double r, double theta, double a, double r_s) {
  Connection4 conn{};

  double cos_theta = std::cos(theta);
  double sin_theta = std::sin(theta);
  double sin2 = sin_theta * sin_theta;
  double cos2 = cos_theta * cos_theta;

  double a2 = a * a;
  double r2 = r * r;

  // Σ = r² + a² cos²θ
  double sigma = r2 + a2 * cos2;

  // Δ = r² - r_s r + a²
  double delta = r2 - r_s * r + a2;

  // Avoid singularities
  double sigma2 = sigma * sigma;
  double sigma3 = sigma2 * sigma;
  if (std::abs(sigma) < 1e-30) {
    return conn; // Return zeros near singularity
  }
  if (std::abs(delta) < 1e-30) {
    delta = (delta >= 0) ? 1e-30 : -1e-30;
  }

  // Useful combinations
  double r2_plus_a2 = r2 + a2;
  double rs_r = r_s * r;

  // ============================================================
  // Γ^t components
  // ============================================================

  // Γ^t_tr = Γ^t_rt
  double gamma_t_tr = rs_r * (r2 - a2 * cos2) / (sigma2 * delta);
  conn[0][0][1] = gamma_t_tr;
  conn[0][1][0] = gamma_t_tr;

  // Γ^t_tθ = Γ^t_θt
  double gamma_t_ttheta = -rs_r * a2 * sin_theta * cos_theta / sigma2;
  conn[0][0][2] = gamma_t_ttheta;
  conn[0][2][0] = gamma_t_ttheta;

  // Γ^t_rφ = Γ^t_φr
  double gamma_t_rphi =
      -a * rs_r * sin2 * (r2 - a2 * cos2) / (sigma2 * delta) -
      a * r_s * sin2 / sigma;
  conn[0][1][3] = gamma_t_rphi;
  conn[0][3][1] = gamma_t_rphi;

  // Γ^t_θφ = Γ^t_φθ
  double gamma_t_thetaphi =
      2.0 * a * rs_r * (r2 + a2) * sin_theta * cos_theta / sigma2;
  conn[0][2][3] = gamma_t_thetaphi;
  conn[0][3][2] = gamma_t_thetaphi;

  // ============================================================
  // Γ^r components
  // ============================================================

  // Γ^r_tt
  conn[1][0][0] = delta * rs_r * (r2 - a2 * cos2) / sigma3;

  // Γ^r_tφ = Γ^r_φt
  double gamma_r_tphi =
      -a * delta * rs_r * sin2 * (r2 - a2 * cos2) / sigma3;
  conn[1][0][3] = gamma_r_tphi;
  conn[1][3][0] = gamma_r_tphi;

  // Γ^r_rr
  conn[1][1][1] = (r * delta - sigma * (r - r_s / 2.0)) / (sigma * delta);

  // Γ^r_rθ = Γ^r_θr
  double gamma_r_rtheta = -a2 * sin_theta * cos_theta / sigma;
  conn[1][1][2] = gamma_r_rtheta;
  conn[1][2][1] = gamma_r_rtheta;

  // Γ^r_θθ
  conn[1][2][2] = -r * delta / sigma;

  // Γ^r_φφ
  conn[1][3][3] = (-delta * r * sin2 -
                   delta * a2 * sin2 * sin2 * rs_r * (r2 - a2 * cos2) / sigma2) /
                  sigma;

  // ============================================================
  // Γ^θ components
  // ============================================================

  // Γ^θ_tt
  conn[2][0][0] = -rs_r * a2 * sin_theta * cos_theta / sigma3;

  // Γ^θ_tφ = Γ^θ_φt
  double gamma_theta_tphi =
      a * rs_r * (r2 + a2) * sin_theta * cos_theta / sigma3;
  conn[2][0][3] = gamma_theta_tphi;
  conn[2][3][0] = gamma_theta_tphi;

  // Γ^θ_rr
  conn[2][1][1] = a2 * sin_theta * cos_theta / (sigma * delta);

  // Γ^θ_rθ = Γ^θ_θr
  double gamma_theta_rtheta = r / sigma;
  conn[2][1][2] = gamma_theta_rtheta;
  conn[2][2][1] = gamma_theta_rtheta;

  // Γ^θ_θθ
  conn[2][2][2] = -a2 * sin_theta * cos_theta / sigma;

  // Γ^θ_φφ
  double sin_cos = sin_theta * cos_theta;
  double A_term = r2_plus_a2 * r2_plus_a2 + a2 * delta * sin2;
  conn[2][3][3] = -sin_cos *
                  (A_term / sigma + 2.0 * a2 * rs_r * sin2 / sigma2) / sigma;

  // ============================================================
  // Γ^φ components
  // ============================================================

  // Γ^φ_tr = Γ^φ_rt
  double gamma_phi_tr = a * rs_r * (r2 - a2 * cos2) / (sigma2 * delta);
  conn[3][0][1] = gamma_phi_tr;
  conn[3][1][0] = gamma_phi_tr;

  // Γ^φ_tθ = Γ^φ_θt
  double gamma_phi_ttheta =
      -a * rs_r * cos_theta / (sigma2 * sin_theta);
  if (std::abs(sin_theta) > 1e-10) {
    conn[3][0][2] = gamma_phi_ttheta;
    conn[3][2][0] = gamma_phi_ttheta;
  }

  // Γ^φ_rφ = Γ^φ_φr
  double gamma_phi_rphi =
      r / sigma - a2 * sin2 * rs_r * (r2 - a2 * cos2) / (sigma2 * delta);
  conn[3][1][3] = gamma_phi_rphi;
  conn[3][3][1] = gamma_phi_rphi;

  // Γ^φ_θφ = Γ^φ_φθ
  double gamma_phi_thetaphi =
      cos_theta / sin_theta +
      a2 * rs_r * sin_theta * cos_theta / (sigma2);
  if (std::abs(sin_theta) > 1e-10) {
    conn[3][2][3] = gamma_phi_thetaphi;
    conn[3][3][2] = gamma_phi_thetaphi;
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
 * @param theta Polar angle (only needed for φφ component)
 * @param r_s Schwarzschild radius
 * @return Covariant metric tensor
 */
inline Metric4 schwarzschild_gcov(double r, double theta, double r_s) {
  return kerr_gcov(r, theta, 0.0, r_s);
}

/**
 * @brief Compute contravariant Schwarzschild metric tensor.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param r_s Schwarzschild radius
 * @return Contravariant metric tensor
 */
inline Metric4 schwarzschild_gcon(double r, double theta, double r_s) {
  return kerr_gcon(r, theta, 0.0, r_s);
}

/**
 * @brief Compute Christoffel symbols for Schwarzschild metric.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param r_s Schwarzschild radius
 * @return Connection coefficients
 */
inline Connection4 schwarzschild_connection(double r, double theta, double r_s) {
  return kerr_connection(r, theta, 0.0, r_s);
}

// ============================================================================
// Index Raising/Lowering
// ============================================================================

/**
 * @brief Lower index on a 4-vector.
 *
 * u_μ = g_μν u^ν
 *
 * @param ucon Contravariant 4-vector u^μ
 * @param gcov Covariant metric tensor
 * @return Covariant 4-vector u_μ
 */
inline std::array<double, 4> lower_index(const std::array<double, 4> &ucon,
                                         const Metric4 &gcov) {
  std::array<double, 4> ucov{};
  for (int mu = 0; mu < 4; ++mu) {
    for (int nu = 0; nu < 4; ++nu) {
      ucov[mu] += gcov[mu][nu] * ucon[nu];
    }
  }
  return ucov;
}

/**
 * @brief Raise index on a 4-vector.
 *
 * u^μ = g^μν u_ν
 *
 * @param ucov Covariant 4-vector u_μ
 * @param gcon Contravariant metric tensor
 * @return Contravariant 4-vector u^μ
 */
inline std::array<double, 4> raise_index(const std::array<double, 4> &ucov,
                                         const Metric4 &gcon) {
  std::array<double, 4> ucon{};
  for (int mu = 0; mu < 4; ++mu) {
    for (int nu = 0; nu < 4; ++nu) {
      ucon[mu] += gcon[mu][nu] * ucov[nu];
    }
  }
  return ucon;
}

/**
 * @brief Compute geodesic acceleration from connection.
 *
 * a^α = -Γ^α_μν u^μ u^ν
 *
 * @param ucon 4-velocity u^μ
 * @param conn Connection coefficients
 * @return 4-acceleration a^α
 */
inline std::array<double, 4> geodesic_acceleration(
    const std::array<double, 4> &ucon, const Connection4 &conn) {
  std::array<double, 4> acc{};
  for (int alpha = 0; alpha < 4; ++alpha) {
    for (int mu = 0; mu < 4; ++mu) {
      for (int nu = 0; nu < 4; ++nu) {
        acc[alpha] -= conn[alpha][mu][nu] * ucon[mu] * ucon[nu];
      }
    }
  }
  return acc;
}

} // namespace physics

#endif // PHYSICS_CONNECTION_H
