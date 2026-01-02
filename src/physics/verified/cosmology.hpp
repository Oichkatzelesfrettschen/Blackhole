/**
 * @file verified/cosmology.hpp
 * @brief Verified FLRW cosmology functions - derived from Rocq formalization
 *
 * This file is generated from proven Rocq theories:
 *   - rocq/theories/Cosmology/FLRW.v
 *   - rocq/theories/Cosmology/Distances.v
 *
 * Key equations (flat LambdaCDM cosmology):
 *   - Friedmann: H^2 = (8*pi*G/3) * rho - k/a^2 + Lambda/3
 *   - Dimensionless Hubble: E(z) = H(z)/H0 = sqrt(Omega_m*(1+z)^3 + Omega_Lambda)
 *   - Comoving distance: D_C(z) = (c/H0) * integral_0^z dz'/E(z')
 *   - Luminosity distance: D_L(z) = (1+z) * D_C(z)
 *   - Angular diameter distance: D_A(z) = D_C(z) / (1+z)
 *
 * References:
 *   - Planck 2018 Cosmological Parameters (arXiv:1807.06209)
 *   - Hogg, "Distance measures in cosmology" (arXiv:astro-ph/9905116)
 *   - Parnovsky 2025, Axiodilaton cosmology (arXiv:2512.13544)
 *
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * @note All functions use SI/cosmological units unless noted
 * @note Distances in Mpc, H0 in km/s/Mpc
 */

#ifndef PHYSICS_VERIFIED_COSMOLOGY_HPP
#define PHYSICS_VERIFIED_COSMOLOGY_HPP

#include <cmath>
#include <numbers>

namespace verified {

// ============================================================================
// Physical Constants (from Rocq: FLRW.v)
// ============================================================================

/**
 * @brief Speed of light in km/s
 *
 * Derived from Rocq: Definition c_km_s : R := 299792.458.
 */
inline constexpr double c_km_s = 299792.458;

/**
 * @brief Speed of light in m/s
 */
inline constexpr double c_m_s = 299792458.0;

// ============================================================================
// Planck 2018 Cosmological Parameters (from Rocq: FLRW.v)
// ============================================================================

/**
 * @brief Planck 2018 Hubble constant: H0 = 67.36 km/s/Mpc
 *
 * Derived from Rocq: Definition H0_Planck18 : R := 67.36.
 */
inline constexpr double H0_Planck18 = 67.36;

/**
 * @brief Planck 2018 total matter density parameter: Omega_m = 0.3153
 *
 * Derived from Rocq: Definition Omega_m_Planck18 : R := 0.3153.
 */
inline constexpr double Omega_m_Planck18 = 0.3153;

/**
 * @brief Planck 2018 baryon density parameter: Omega_b = 0.0493
 *
 * Derived from Rocq: Definition Omega_b_Planck18 : R := 0.0493.
 */
inline constexpr double Omega_b_Planck18 = 0.0493;

/**
 * @brief Planck 2018 CMB temperature: T_CMB = 2.7255 K
 *
 * Derived from Rocq: Definition T_CMB_Planck18 : R := 2.7255.
 */
inline constexpr double T_CMB_Planck18 = 2.7255;

/**
 * @brief Planck 2018 sound horizon at recombination: r_s = 147.09 Mpc
 *
 * Derived from Rocq: Definition sound_horizon_Planck18 : R := 147.09.
 */
inline constexpr double sound_horizon_Planck18 = 147.09;

// ============================================================================
// Flat LambdaCDM Cosmology (from Rocq: FlatLCDM record)
// ============================================================================

/**
 * @brief Flat LambdaCDM cosmology parameters
 *
 * Derived from Rocq: Record FlatLCDM := mkFlatLCDM {
 *   H0 : R; Omega_m : R; Omega_b : R; T_CMB : R
 * }.
 */
struct FlatLCDM {
    double H0;       ///< Hubble constant in km/s/Mpc
    double Omega_m;  ///< Matter density parameter (CDM + baryons)
    double Omega_b;  ///< Baryon density parameter
    double T_CMB;    ///< CMB temperature in Kelvin

    /**
     * @brief Default constructor: Planck 2018 cosmology
     */
    constexpr FlatLCDM() noexcept
        : H0(H0_Planck18), Omega_m(Omega_m_Planck18),
          Omega_b(Omega_b_Planck18), T_CMB(T_CMB_Planck18) {}

    /**
     * @brief Custom cosmology constructor
     */
    constexpr FlatLCDM(double h0, double om, double ob, double tcmb) noexcept
        : H0(h0), Omega_m(om), Omega_b(ob), T_CMB(tcmb) {}
};

/**
 * @brief Planck 2018 cosmology instance
 *
 * Derived from Rocq: Definition Planck18 : FlatLCDM :=
 *   mkFlatLCDM H0_Planck18 Omega_m_Planck18 Omega_b_Planck18 T_CMB_Planck18.
 */
inline constexpr FlatLCDM Planck18{};

// ============================================================================
// Derived Quantities (from Rocq: FLRW.v)
// ============================================================================

/**
 * @brief Dark energy density parameter for flat universe
 *
 * Derived from Rocq: Definition Omega_Lambda (cosmo : FlatLCDM) : R := 1 - cosmo.(Omega_m).
 *
 * @param Omega_m Matter density parameter
 * @return Omega_Lambda = 1 - Omega_m
 */
[[nodiscard]] constexpr double Omega_Lambda(double Omega_m) noexcept {
    return 1.0 - Omega_m;
}

/**
 * @brief Hubble time: t_H = 1/H0
 *
 * Derived from Rocq: Definition hubble_time (H0 : R) : R := 1 / H0.
 *
 * @param H0 Hubble constant in km/s/Mpc
 * @return Hubble time in Mpc/(km/s) units (~14.4 Gyr for H0=67.36)
 */
[[nodiscard]] constexpr double hubble_time(double H0) noexcept {
    return 1.0 / H0;
}

/**
 * @brief Hubble length: D_H = c/H0
 *
 * Derived from Rocq: Definition hubble_length (H0 : R) : R := c_km_s / H0.
 *
 * @param H0 Hubble constant in km/s/Mpc
 * @return Hubble length in Mpc (~4450 Mpc for H0=67.36)
 */
[[nodiscard]] constexpr double hubble_length(double H0) noexcept {
    return c_km_s / H0;
}

// ============================================================================
// Friedmann Equation (from Rocq: E_z, hubble_parameter)
// ============================================================================

/**
 * @brief Dimensionless Hubble parameter: E(z) = H(z)/H0
 *
 * Derived from Rocq: Definition E_z (cosmo : FlatLCDM) (z : R) : R :=
 *   sqrt (cosmo.(Omega_m) * (1 + z)^3 + Omega_Lambda cosmo).
 *
 * For flat LambdaCDM: E(z) = sqrt(Omega_m * (1+z)^3 + Omega_Lambda)
 *
 * Theorem E_at_z0: E(0) = 1 for properly normalized cosmology.
 *
 * @param Omega_m Matter density parameter
 * @param z Redshift
 * @return E(z) = H(z)/H0
 */
[[nodiscard]] inline double E_z(double Omega_m, double z) noexcept {
    const double one_plus_z = 1.0 + z;
    const double one_plus_z_cubed = one_plus_z * one_plus_z * one_plus_z;
    const double OL = Omega_Lambda(Omega_m);
    return std::sqrt(Omega_m * one_plus_z_cubed + OL);
}

/**
 * @brief E(z) with cosmology struct
 */
[[nodiscard]] inline double E_z(const FlatLCDM& cosmo, double z) noexcept {
    return E_z(cosmo.Omega_m, z);
}

/**
 * @brief Hubble parameter at redshift z: H(z) = H0 * E(z)
 *
 * Derived from Rocq: Definition hubble_parameter (cosmo : FlatLCDM) (z : R) : R :=
 *   cosmo.(H0) * E_z cosmo z.
 *
 * @param H0 Hubble constant in km/s/Mpc
 * @param Omega_m Matter density parameter
 * @param z Redshift
 * @return H(z) in km/s/Mpc
 */
[[nodiscard]] inline double hubble_parameter(double H0, double Omega_m, double z) noexcept {
    return H0 * E_z(Omega_m, z);
}

/**
 * @brief H(z) with cosmology struct
 */
[[nodiscard]] inline double hubble_parameter(const FlatLCDM& cosmo, double z) noexcept {
    return cosmo.H0 * E_z(cosmo, z);
}

// ============================================================================
// Deceleration Parameter (from Rocq: deceleration_q)
// ============================================================================

/**
 * @brief Deceleration parameter: q(z) = -1 + (1+z) * (dE/dz) / E(z)
 *
 * Derived from Rocq: Definition deceleration_q (cosmo : FlatLCDM) (z : R) : R :=
 *   let E := E_z cosmo z in
 *   let dEdz := (3/2) * cosmo.(Omega_m) * (1 + z)^2 / (2 * E) in
 *   -1 + (1 + z) * dEdz / E.
 *
 * q < 0 indicates accelerating expansion
 * For Planck18: z_acc ~ 0.67 (transition redshift)
 *
 * @param Omega_m Matter density parameter
 * @param z Redshift
 * @return q(z), negative for acceleration
 */
[[nodiscard]] inline double deceleration_parameter(double Omega_m, double z) noexcept {
    const double one_plus_z = 1.0 + z;
    const double E = E_z(Omega_m, z);

    // dE/dz = (3/2) * Omega_m * (1+z)^2 / (2*E)
    const double dEdz = 1.5 * Omega_m * one_plus_z * one_plus_z / (2.0 * E);

    return -1.0 + one_plus_z * dEdz / E;
}

// ============================================================================
// Matter-Radiation Equality (from Rocq: z_equality)
// ============================================================================

/**
 * @brief Redshift of matter-radiation equality
 *
 * Derived from Rocq: Definition z_equality (Omega_m Omega_r : R) : R :=
 *   Omega_m / Omega_r - 1.
 *
 * For Planck18: z_eq ~ 3400
 *
 * @param Omega_m Matter density parameter
 * @param Omega_r Radiation density parameter
 * @return z_eq
 */
[[nodiscard]] constexpr double z_equality(double Omega_m, double Omega_r) noexcept {
    return Omega_m / Omega_r - 1.0;
}

// ============================================================================
// Cosmological Distances (from Rocq: Distances.v)
// ============================================================================

/**
 * @brief Linear approximation for comoving distance (small z)
 *
 * Derived from Rocq: Definition comoving_distance_linear (cosmo : FlatLCDM) (z : R) : R :=
 *   hubble_length cosmo.(H0) * z.
 *
 * For z << 1: D_C(z) ~ (c/H0) * z
 *
 * @param H0 Hubble constant
 * @param z Redshift (should be << 1)
 * @return Approximate comoving distance in Mpc
 */
[[nodiscard]] constexpr double comoving_distance_linear(double H0, double z) noexcept {
    return hubble_length(H0) * z;
}

/**
 * @brief Comoving distance via trapezoidal integration
 *
 * D_C(z) = (c/H0) * integral_0^z dz'/E(z')
 *
 * Uses trapezoidal rule with n subdivisions.
 *
 * @param cosmo Cosmology parameters
 * @param z Redshift
 * @param n Number of integration steps (default 1000)
 * @return Comoving distance in Mpc
 */
[[nodiscard]] inline double comoving_distance(
    const FlatLCDM& cosmo, double z, std::size_t n = 1000) noexcept
{
    if (z <= 0.0) return 0.0;

    const double D_H = hubble_length(cosmo.H0);
    const double dz = z / static_cast<double>(n);

    // Trapezoidal rule: sum of 1/E(z') from z'=0 to z'=z
    double sum = 0.5 / E_z(cosmo, 0.0);  // First endpoint
    for (std::size_t i = 1; i < n; ++i) {
        const double z_i = static_cast<double>(i) * dz;
        sum += 1.0 / E_z(cosmo, z_i);
    }
    sum += 0.5 / E_z(cosmo, z);  // Last endpoint

    return D_H * sum * dz;
}

/**
 * @brief Luminosity distance: D_L(z) = (1+z) * D_C(z)
 *
 * Derived from Rocq: Definition luminosity_distance (cosmo : FlatLCDM) (z : R) : R :=
 *   (1 + z) * comoving_distance cosmo z.
 *
 * Theorem luminosity_distance_at_z0: D_L(0) = 0.
 *
 * @param cosmo Cosmology parameters
 * @param z Redshift
 * @param n Integration steps
 * @return Luminosity distance in Mpc
 */
[[nodiscard]] inline double luminosity_distance(
    const FlatLCDM& cosmo, double z, std::size_t n = 1000) noexcept
{
    return (1.0 + z) * comoving_distance(cosmo, z, n);
}

/**
 * @brief Angular diameter distance: D_A(z) = D_C(z) / (1+z)
 *
 * Derived from Rocq: Definition angular_diameter_distance (cosmo : FlatLCDM) (z : R) : R :=
 *   comoving_distance cosmo z / (1 + z).
 *
 * Note: D_A has maximum at z ~ 1-2 for typical cosmologies.
 *
 * @param cosmo Cosmology parameters
 * @param z Redshift
 * @param n Integration steps
 * @return Angular diameter distance in Mpc
 */
[[nodiscard]] inline double angular_diameter_distance(
    const FlatLCDM& cosmo, double z, std::size_t n = 1000) noexcept
{
    return comoving_distance(cosmo, z, n) / (1.0 + z);
}

/**
 * @brief Distance duality: D_L = (1+z)^2 * D_A
 *
 * Derived from Rocq: Theorem distance_duality:
 *   z > 0 -> luminosity_distance cosmo z = (1 + z)^2 * angular_diameter_distance cosmo z.
 *
 * Also known as Etherington reciprocity theorem.
 *
 * @param D_L Luminosity distance
 * @param D_A Angular diameter distance
 * @param z Redshift
 * @param tol Tolerance for verification
 * @return true if duality holds within tolerance
 */
[[nodiscard]] inline bool verify_distance_duality(
    double D_L, double D_A, double z, double tol = 1e-6) noexcept
{
    if (z <= 0.0) return true;
    const double one_plus_z = 1.0 + z;
    const double ratio = D_L / (one_plus_z * one_plus_z * D_A);
    return std::abs(ratio - 1.0) < tol;
}

/**
 * @brief Distance modulus: mu = 5 * log10(D_L/10pc) = 5 * log10(D_L) + 25
 *
 * Derived from Rocq: Definition distance_modulus (D_L_Mpc : R) : R :=
 *   5 * ln D_L_Mpc / ln 10 + 25.
 *
 * Used for comparing apparent and absolute magnitudes: m - M = mu
 *
 * @param D_L_Mpc Luminosity distance in Mpc
 * @return Distance modulus in magnitudes
 */
[[nodiscard]] inline double distance_modulus(double D_L_Mpc) noexcept {
    return 5.0 * std::log10(D_L_Mpc) + 25.0;
}

/**
 * @brief Comoving volume: V_C(z) = (4*pi/3) * D_C(z)^3
 *
 * Derived from Rocq: Definition comoving_volume (cosmo : FlatLCDM) (z : R) : R :=
 *   (4 * PI / 3) * (comoving_distance cosmo z)^3.
 *
 * @param cosmo Cosmology parameters
 * @param z Redshift
 * @param n Integration steps
 * @return Comoving volume in Mpc^3
 */
[[nodiscard]] inline double comoving_volume(
    const FlatLCDM& cosmo, double z, std::size_t n = 1000) noexcept
{
    const double D_C = comoving_distance(cosmo, z, n);
    return (4.0 * std::numbers::pi / 3.0) * D_C * D_C * D_C;
}

// ============================================================================
// Axiodilaton Extension (from Rocq: 2025 Research Integration)
// ============================================================================

/**
 * @brief Axiodilaton cosmology parameters
 *
 * Derived from Rocq: Record AxiodilatonParams := mkAxiodilaton {
 *   ad_Omega_m : R; ad_Omega_ad : R; ad_coupling : R
 * }.
 *
 * From arXiv:2512.13544:
 *   - Raises H0 to ~69.2 km/s/Mpc
 *   - Reduces Hubble tension to < 3 sigma
 *   - Requires coupling |g| ~ 10^-2 to 10^-1
 */
struct AxiodilatonParams {
    double Omega_m;    ///< Matter density parameter
    double Omega_ad;   ///< Axiodilaton contribution
    double coupling;   ///< Dilaton-matter coupling |g|

    constexpr AxiodilatonParams(double om, double oad, double g) noexcept
        : Omega_m(om), Omega_ad(oad), coupling(g) {}
};

/**
 * @brief Axiodilaton contribution function
 *
 * Derived from Rocq: Definition f_axiodilaton (z : R) (ad : AxiodilatonParams) : R :=
 *   ad.(ad_Omega_ad) * (1 + z)^2.
 *
 * Simplified model: axiodilaton acts like early dark energy.
 * Full model requires solving Klein-Gordon equation.
 *
 * @param z Redshift
 * @param ad Axiodilaton parameters
 * @return Axiodilaton contribution to E(z)^2
 */
[[nodiscard]] inline double f_axiodilaton(double z, const AxiodilatonParams& ad) noexcept {
    const double one_plus_z = 1.0 + z;
    return ad.Omega_ad * one_plus_z * one_plus_z;
}

/**
 * @brief Modified Hubble parameter with axiodilaton
 *
 * Derived from Rocq: Definition hubble_axiodilaton (H0 : R) (ad : AxiodilatonParams) (z : R) : R :=
 *   let Omega_Lambda := 1 - ad.(ad_Omega_m) - ad.(ad_Omega_ad) in
 *   H0 * sqrt (ad.(ad_Omega_m) * (1 + z)^3 + f_axiodilaton z ad + Omega_Lambda).
 *
 * Predicted: H0 = 69.22 +/- 0.28 km/s/Mpc (resolves Hubble tension)
 *
 * @param H0 Base Hubble constant
 * @param ad Axiodilaton parameters
 * @param z Redshift
 * @return H(z) in km/s/Mpc
 */
[[nodiscard]] inline double hubble_axiodilaton(
    double H0, const AxiodilatonParams& ad, double z) noexcept
{
    const double one_plus_z = 1.0 + z;
    const double one_plus_z_cubed = one_plus_z * one_plus_z * one_plus_z;
    const double OL = 1.0 - ad.Omega_m - ad.Omega_ad;

    return H0 * std::sqrt(
        ad.Omega_m * one_plus_z_cubed +
        f_axiodilaton(z, ad) +
        OL
    );
}

// ============================================================================
// Extraction Interface (from Rocq: compute_* functions)
// ============================================================================

/**
 * @brief Compute E(z) (extraction interface)
 *
 * Derived from Rocq: Definition compute_E_z (Omega_m z : R) : R :=
 *   sqrt (Omega_m * (1 + z)^3 + (1 - Omega_m)).
 */
[[nodiscard]] inline double compute_E_z(double Omega_m, double z) noexcept {
    return E_z(Omega_m, z);
}

/**
 * @brief Compute Hubble parameter (extraction interface)
 *
 * Derived from Rocq: Definition compute_hubble (H0 Omega_m z : R) : R :=
 *   H0 * compute_E_z Omega_m z.
 */
[[nodiscard]] inline double compute_hubble(double H0, double Omega_m, double z) noexcept {
    return hubble_parameter(H0, Omega_m, z);
}

/**
 * @brief Compute Hubble length (extraction interface)
 *
 * Derived from Rocq: Definition compute_hubble_length (H0 : R) : R := c_km_s / H0.
 */
[[nodiscard]] constexpr double compute_hubble_length(double H0) noexcept {
    return hubble_length(H0);
}

/**
 * @brief Compute Omega_Lambda (extraction interface)
 *
 * Derived from Rocq: Definition compute_Omega_Lambda (Omega_m : R) : R := 1 - Omega_m.
 */
[[nodiscard]] constexpr double compute_Omega_Lambda(double Omega_m) noexcept {
    return Omega_Lambda(Omega_m);
}

/**
 * @brief Compute luminosity distance (extraction interface)
 */
[[nodiscard]] inline double compute_luminosity_distance(
    double H0, double Omega_m, double z, std::size_t n = 1000) noexcept
{
    FlatLCDM cosmo{H0, Omega_m, 0.0, 0.0};
    return luminosity_distance(cosmo, z, n);
}

/**
 * @brief Compute angular diameter distance (extraction interface)
 */
[[nodiscard]] inline double compute_angular_diameter_distance(
    double H0, double Omega_m, double z, std::size_t n = 1000) noexcept
{
    FlatLCDM cosmo{H0, Omega_m, 0.0, 0.0};
    return angular_diameter_distance(cosmo, z, n);
}

/**
 * @brief Compute distance modulus (extraction interface)
 */
[[nodiscard]] inline double compute_distance_modulus(double D_L_Mpc) noexcept {
    return distance_modulus(D_L_Mpc);
}

/**
 * @brief Compute comoving volume (extraction interface)
 */
[[nodiscard]] inline double compute_comoving_volume(
    double H0, double Omega_m, double z, std::size_t n = 1000) noexcept
{
    FlatLCDM cosmo{H0, Omega_m, 0.0, 0.0};
    return comoving_volume(cosmo, z, n);
}

/**
 * @brief Linear comoving distance approximation (extraction interface)
 */
[[nodiscard]] constexpr double compute_comoving_distance_linear(double H0, double z) noexcept {
    return comoving_distance_linear(H0, z);
}

} // namespace verified

#endif // PHYSICS_VERIFIED_COSMOLOGY_HPP
