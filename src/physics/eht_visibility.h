/**
 * @file eht_visibility.h
 * @brief Synthetic EHT visibility pipeline: UV coverage, DFT visibilities,
 *        closure phases, and closure amplitudes.
 *
 * WHY: The Event Horizon Telescope measures complex visibilities V(u,v) -- the
 * Fourier transform of the sky brightness distribution -- sampled at discrete
 * baseline coordinates (u,v) set by the Earth-baseline geometry and the
 * observing wavelength.  Individual visibilities are corrupted by station-based
 * phase and amplitude errors (atmospheric phase, gain variations).  Closure
 * phases and closure amplitudes are combinations that are exactly invariant to
 * these station-based errors and therefore provide robust calibration-free
 * observables for black hole shadow imaging.
 *
 * WHAT: This header provides:
 *   1. (u,v,w) coordinate calculation from geocentric station positions
 *      (Thompson, Moran & Swenson 2017, standard VLBI baseline formula).
 *   2. Complex visibility by direct DFT of a 2D intensity image.
 *   3. Closure phase: arg(V_12 * V_23 * V_31) -- three-station triangle invariant.
 *   4. Closure amplitude: |V_12 V_34| / |V_13 V_24| -- four-station invariant.
 *   5. EHT 2017 station positions and standard observing parameters.
 *   6. Analytical ring visibility (J_0 formula) for testing and shadow diameter
 *      estimation via the first null of V(q).
 *
 * SCOPE: This is a reference/validation implementation.  For production imaging
 * of large arrays use a fast FFT backend; the direct DFT here runs in O(N^2 * P)
 * where N^2 is the number of image pixels and P the number of (u,v) samples.
 *
 * References:
 *   - Thompson, Moran & Swenson (2017). Interferometry and Synthesis in Radio
 *     Astronomy, 3rd ed. (Springer). Chapters 4-10.
 *   - Jennison (1958), MNRAS 118, 276 -- closure phase original
 *   - EHT Collaboration (2019), ApJ 875, L3 -- M87* EHT array parameters
 *   - EHT Collaboration (2022), ApJ 930, L12 -- Sgr A* first image
 *   - Akiyama et al. (2017), AJ 153, 159 -- VLBI imaging pipeline
 */

#ifndef PHYSICS_EHT_VISIBILITY_H
#define PHYSICS_EHT_VISIBILITY_H

#include <array>
#include <cmath>
#include <cstddef>
#include <limits>
#include <numbers>
#include <utility>
#include <vector>

namespace physics {

// ============================================================================
// Complex visibility type
// ============================================================================

/**
 * @brief Complex visibility V(u,v) = Re + i Im.
 *
 * The visibility is the 2D Fourier transform of the sky brightness distribution
 * at spatial frequency (u,v) measured in wavelengths (lambda = c/nu_obs).
 * By the van Cittert-Zernike theorem, V(u,v) is directly observable with an
 * interferometer whose baseline vector has projected length (u,v).
 */
struct ComplexVis {
    double re = 0.0;  ///< Real part
    double im = 0.0;  ///< Imaginary part

    /// Visibility amplitude |V|.
    [[nodiscard]] double amplitude() const noexcept { return std::hypot(re, im); }

    /// Visibility phase arg(V) in (-pi, pi].
    [[nodiscard]] double phase() const noexcept { return std::atan2(im, re); }

    /// Complex conjugate: V* = Re - i Im.  Flipping the baseline sign gives V*.
    [[nodiscard]] ComplexVis conjugate() const noexcept { return {re, -im}; }

    /// Complex multiplication (used for bispectrum products).
    [[nodiscard]] ComplexVis operator*(const ComplexVis& o) const noexcept {
        return {re * o.re - im * o.im, re * o.im + im * o.re};
    }

    /// Complex addition (used for superposition).
    [[nodiscard]] ComplexVis operator+(const ComplexVis& o) const noexcept {
        return {re + o.re, im + o.im};
    }
};

// ============================================================================
// Telescope station
// ============================================================================

/**
 * @brief VLBI telescope station with geocentric position and aperture size.
 *
 * Coordinates are in the ECEF (Earth-Centred, Earth-Fixed) frame, also called
 * the geocentric equatorial frame: X toward (0 lon, 0 lat), Z toward the North
 * pole, Y completing the right-handed system.
 */
struct TelescopeStation {
    const char* name;   ///< Abbreviated station name (e.g., "ALMA")
    double X;           ///< ECEF X [m]
    double Y;           ///< ECEF Y [m]
    double Z;           ///< ECEF Z [m] (rotational axis, positive North)
    double diameter;    ///< Effective aperture diameter [m]
};

// ============================================================================
// UV coordinate calculation
// ============================================================================

/**
 * @brief (u, v, w) baseline coordinates (all in wavelengths).
 *
 * The w coordinate is the delay (line-of-sight component); it is needed for
 * wide-field imaging but not for narrow-field visibility evaluation.
 */
struct UVW {
    double u;   ///< East-West spatial frequency [wavelengths]
    double v;   ///< North-South spatial frequency [wavelengths]
    double w;   ///< Line-of-sight delay [wavelengths]
};

/**
 * @brief Compute (u,v,w) coordinates for a baseline at a given hour angle.
 *
 * WHY: The projected baseline (u,v) that an interferometer samples depends on
 * the baseline orientation, the source direction, and Earth's rotation.  As the
 * Earth rotates, the hour angle H increases and (u,v) traces an ellipse
 * (the "UV track") that provides different spatial frequencies for imaging.
 *
 * WHAT: Standard VLBI baseline-to-UV transform (TMS 2017, Eq. 4.1):
 *
 *   u = (dX sin H + dY cos H) / lambda
 *   v = (-dX sin d cos H + dY sin d sin H + dZ cos d) / lambda
 *   w = ( dX cos d cos H - dY cos d sin H + dZ sin d) / lambda
 *
 * where d = source declination, H = hour angle (negative = East of meridian),
 * (dX, dY, dZ) = station_2 - station_1 in ECEF meters, lambda = wavelength.
 *
 * LIMITS:
 *   - H = 0 (source on meridian): u = dY/lambda, v = -dX sin d/lambda + dZ cos d/lambda
 *   - d = 0 (equatorial source): v = dZ / lambda (independent of H)
 *   - d = +/-pi/2 (polar source): u = v = 0 (no projected baseline)
 *
 * References:
 *   - Thompson, Moran & Swenson (2017), Eq. 4.1
 *   - EHT Collaboration (2019), ApJ 875, L3, Appendix A
 *
 * @param s1          First station (reference)
 * @param s2          Second station
 * @param hourAngle   Source hour angle [rad] (H < 0: source East of meridian)
 * @param declination Source declination [rad]
 * @param wavelength  Observing wavelength [m]
 * @return UVW coordinates in wavelengths
 */
[[nodiscard]] inline UVW uvwCoordinates(const TelescopeStation& s1,
                                         const TelescopeStation& s2,
                                         double hourAngle,
                                         double declination,
                                         double wavelength) noexcept {
    const double dX = s2.X - s1.X;
    const double dY = s2.Y - s1.Y;
    const double dZ = s2.Z - s1.Z;

    const double sinH   = std::sin(hourAngle);
    const double cosH   = std::cos(hourAngle);
    const double sinD   = std::sin(declination);
    const double cosD   = std::cos(declination);

    return {
        (dX * sinH + dY * cosH) / wavelength,
        (-dX * sinD * cosH + dY * sinD * sinH + dZ * cosD) / wavelength,
        ( dX * cosD * cosH - dY * cosD * sinH + dZ * sinD) / wavelength,
    };
}

/**
 * @brief Sample the UV track (ellipse) of a baseline over a range of hour angles.
 *
 * The UV track is the set of (u,v) coordinates sampled as Earth rotates.  It
 * forms an ellipse (full-track period = one sidereal day) or an arc (limited
 * observation window).
 *
 * @param s1          First station
 * @param s2          Second station
 * @param haBeg       Start hour angle [rad]
 * @param haEnd       End hour angle [rad]
 * @param declination Source declination [rad]
 * @param wavelength  Observing wavelength [m]
 * @param nPoints     Number of points to sample
 * @return Vector of (u, v) coordinate pairs in wavelengths
 */
[[nodiscard]] inline std::vector<std::pair<double, double>> uvTrack(
    const TelescopeStation& s1, const TelescopeStation& s2,
    double haBeg, double haEnd,
    double declination, double wavelength,
    std::size_t nPoints = 64) {
    std::vector<std::pair<double, double>> track;
    track.reserve(nPoints);
    const std::size_t denom = (nPoints > 1) ? nPoints - 1 : 1;
    for (std::size_t k = 0; k < nPoints; ++k) {
        const double ha  = haBeg + (haEnd - haBeg) * static_cast<double>(k) / static_cast<double>(denom);
        const auto   uvw = uvwCoordinates(s1, s2, ha, declination, wavelength);
        track.emplace_back(uvw.u, uvw.v);
    }
    return track;
}

// ============================================================================
// Visibility computation (direct 2D DFT)
// ============================================================================

/**
 * @brief Complex visibility by direct DFT of a 2D intensity image.
 *
 * WHY: The van Cittert-Zernike theorem states that the complex visibility
 * V(u,v) equals the 2D Fourier transform of the sky brightness distribution
 * I(x,y) for a compact, incoherent source:
 *
 *   V(u,v) = integral I(x,y) * exp(-2 pi i (u x + v y)) dx dy
 *
 * This function evaluates the DFT sum directly for a discretised image.
 * For large images use an FFT; this is O(N^4) per (u,v) point.
 *
 * WHAT: Pixel (row, col) maps to angular position
 *   x = (col - N/2) * pixelSizeRad   [East offset, positive right]
 *   y = (row - N/2) * pixelSizeRad   [North offset, positive up]
 * The image is stored row-major: index = row * N + col.
 *
 * NORMALISATION: V(0,0) = sum_{i,j} I(i,j) * dOmega = total integrated flux.
 * The normalised visibility V_norm = V / V(0,0) has |V_norm| in [0, 1].
 *
 * @param image        Flattened N*N intensity image (row-major, non-negative)
 * @param N            Image side length [pixels]
 * @param pixelSizeRad Angular pixel size [rad]
 * @param u            East-West spatial frequency [wavelengths]
 * @param v            North-South spatial frequency [wavelengths]
 * @return Complex visibility [same units as image * sr]
 */
[[nodiscard]] inline ComplexVis complexVisibility(const std::vector<double>& image,
                                                   std::size_t N,
                                                   double pixelSizeRad,
                                                   double u, double v) noexcept {
    if (image.size() < N * N || N == 0) { return {}; }

    const double dOmega  = pixelSizeRad * pixelSizeRad;
    const double twoPi   = 2.0 * std::numbers::pi;
    const double halfN   = 0.5 * static_cast<double>(N);

    double re = 0.0, im = 0.0;
    for (std::size_t row = 0; row < N; ++row) {
        const double y = (static_cast<double>(row) - halfN) * pixelSizeRad;
        for (std::size_t col = 0; col < N; ++col) {
            const double flux = image[row * N + col];
            if (flux == 0.0) { continue; }
            const double x     = (static_cast<double>(col) - halfN) * pixelSizeRad;
            const double phase = twoPi * (u * x + v * y);
            re += flux * std::cos(phase);
            im -= flux * std::sin(phase);  // convention: -2 pi i
        }
    }
    return {re * dOmega, im * dOmega};
}

/**
 * @brief Normalised complex visibility V(u,v) / V(0,0).
 *
 * |V_norm| = 1 for a point source.  |V_norm| < 1 for an extended source.
 * Returns {0, 0} if the total flux is zero.
 *
 * @param image        N*N intensity image (row-major)
 * @param N            Image side length
 * @param pixelSizeRad Angular pixel size [rad]
 * @param u            Spatial frequency u [wavelengths]
 * @param v            Spatial frequency v [wavelengths]
 * @return Normalised visibility; amplitude in [0, 1]
 */
[[nodiscard]] inline ComplexVis normalisedVisibility(const std::vector<double>& image,
                                                      std::size_t N,
                                                      double pixelSizeRad,
                                                      double u, double v) noexcept {
    const ComplexVis v00 = complexVisibility(image, N, pixelSizeRad, 0.0, 0.0);
    const double     a00 = v00.amplitude();
    if (a00 < 1.0e-30) { return {}; }
    const ComplexVis vuv = complexVisibility(image, N, pixelSizeRad, u, v);
    return {vuv.re / a00, vuv.im / a00};
}

// ============================================================================
// Closure quantities
// ============================================================================

/**
 * @brief Closure phase for a three-station triangle [radians].
 *
 * WHY: Atmospheric phase errors phi_k are station-based: the observed phase
 * of baseline ij is phi_ij^obs = phi_ij^true + psi_i - psi_j.  Forming the
 * closure phase over a closed triangle 1->2->3->1:
 *
 *   Phi_123 = arg(V_12 * V_23 * V_31)
 *
 * the station-dependent terms cancel: (psi_1-psi_2)+(psi_2-psi_3)+(psi_3-psi_1)=0.
 * The closure phase thus equals the true source phase and is INDEPENDENT of
 * atmospheric or instrumental phase corruption.
 *
 * LIMITS:
 *   - Point source: Phi = 0 for all triangles (all true phases zero).
 *   - Centrosymmetric source (V real): Phi = 0 or pi.
 *
 * NOTE: v31 is the visibility on baseline 3->1, which equals conj(v13).
 *       The caller must supply the correctly oriented visibility.
 *
 * Reference: Jennison (1958), MNRAS 118, 276.
 *
 * @param v12 Visibility on baseline 1->2
 * @param v23 Visibility on baseline 2->3
 * @param v31 Visibility on baseline 3->1  (= conj(v13))
 * @return Closure phase [rad] in (-pi, pi]
 */
[[nodiscard]] inline double closurePhase(const ComplexVis& v12,
                                          const ComplexVis& v23,
                                          const ComplexVis& v31) noexcept {
    const ComplexVis bispectrum = v12 * v23 * v31;
    return std::atan2(bispectrum.im, bispectrum.re);
}

/**
 * @brief Closure amplitude for a four-station quadrangle (dimensionless).
 *
 * WHY: Station gain errors G_k are multiplicative: |V_ij^obs| = |G_i||G_j||V_ij^true|.
 * The four-station closure amplitude
 *
 *   C = |V_12 * V_34| / |V_13 * V_24|
 *
 * equals the true closure amplitude because each station gain appears exactly
 * once in the numerator and once in the denominator:
 * (|G1||G2||G3||G4|) / (|G1||G3||G2||G4|) = 1.
 *
 * LIMITS:
 *   - Point source: C = 1 for all quadrangles.
 *
 * @param v12 Visibility on baseline 1-2
 * @param v34 Visibility on baseline 3-4
 * @param v13 Visibility on baseline 1-3
 * @param v24 Visibility on baseline 2-4
 * @return Closure amplitude; NaN if denominator is zero.
 */
[[nodiscard]] inline double closureAmplitude(const ComplexVis& v12,
                                              const ComplexVis& v34,
                                              const ComplexVis& v13,
                                              const ComplexVis& v24) noexcept {
    const double denom = v13.amplitude() * v24.amplitude();
    if (denom < 1.0e-30) { return std::numeric_limits<double>::quiet_NaN(); }
    return (v12.amplitude() * v34.amplitude()) / denom;
}

// ============================================================================
// Analytical visibility models
// ============================================================================

/**
 * @brief Visibility of an infinitely thin ring of angular radius R.
 *
 * For a thin ring (delta-function annulus) of total flux F and angular radius R:
 *
 *   V(q) = F * J_0(2 pi R q)
 *
 * where q = sqrt(u^2 + v^2) is the baseline length in wavelengths and J_0 is
 * the Bessel function of the first kind, order zero.
 *
 * WHY: The EHT M87* shadow measurement uses the first null of the ring
 * visibility to infer the photon ring diameter:
 *   First null of J_0 at x_0 = 2.4048 ->
 *   2 pi R q_null = 2.4048 -> q_null = 2.4048 / (2 pi R) = 0.3828 / R
 *
 * For M87* shadow of 42 microarcseconds (R = 21 uas = 1.019e-10 rad) at 230 GHz:
 *   q_null = 0.3828 / 1.019e-10 ~ 3.76e9 wavelengths
 *   Physical baseline = q_null * lambda = 3.76e9 * 1.3e-3 ~ 4900 km
 *
 * @param ringRadius  Angular ring radius [rad]
 * @param totalFlux   Integrated ring flux [arbitrary units]
 * @param q           Baseline length [wavelengths] (q = sqrt(u^2+v^2))
 * @return Real visibility [same units as totalFlux]; J_0 oscillates around 0.
 */
[[nodiscard]] inline double analyticalRingVisibility(double ringRadius,
                                                      double totalFlux,
                                                      double q) noexcept {
    return totalFlux * std::cyl_bessel_j(0, 2.0 * std::numbers::pi * ringRadius * q);
}

/**
 * @brief Baseline length at which a thin ring's visibility first reaches zero.
 *
 * The first null of J_0 occurs at argument 2.4048, giving:
 *   q_null = 2.4048 / (2 pi R) = 0.3828 / R
 *
 * @param ringRadius Angular ring radius [rad]
 * @return Baseline length [wavelengths] at first visibility null
 */
[[nodiscard]] inline double ringVisibilityFirstNull(double ringRadius) noexcept {
    if (ringRadius <= 0.0) { return 0.0; }
    // First zero of J_0: x_0 = 2.404825557695773
    constexpr double kJ0FirstZero = 2.404825557695773;
    return kJ0FirstZero / (2.0 * std::numbers::pi * ringRadius);
}

// ============================================================================
// EHT 2017 array preset
// ============================================================================

/**
 * @brief EHT 2017 station identifiers.
 *
 * The 2017 EHT array observed at 1.3 mm (230 GHz) and produced the first
 * resolved images of M87* (EHT Collaboration 2019) and Sgr A* (2022).
 */
enum class EhtStation : int {
    ALMA  = 0,   ///< Atacama Large Millimeter Array, Chile
    SPT   = 1,   ///< South Pole Telescope, Antarctica
    JCMT  = 2,   ///< James Clerk Maxwell Telescope, Hawaii
    SMA   = 3,   ///< Submillimeter Array, Hawaii (co-located with JCMT)
    SMT   = 4,   ///< Submillimeter Telescope, Arizona
    IRAM  = 5,   ///< IRAM 30m Telescope, Spain
    LMT   = 6,   ///< Large Millimeter Telescope, Mexico
    COUNT = 7
};

/**
 * @brief ECEF geocentric station positions for the EHT 2017 array.
 *
 * Source: EHT Collaboration (2019), ApJ 875, L3, Table 1.
 * Coordinates in WGS84 geocentric meters.  Positive Z toward geographic North.
 *
 * JCMT and SMA are co-located (same pad on Mauna Kea); they appear as two
 * independent antennas for intra-station baseline closure tests.
 *
 * @param id  EhtStation enumerator
 * @return TelescopeStation with ECEF coordinates and aperture diameter
 */
[[nodiscard]] inline TelescopeStation ehtStation(EhtStation id) noexcept {
    static constexpr std::array<TelescopeStation, 7> kStations = {{
        {"ALMA",  2225144.2, -5441197.6, -2479303.4,  73.0},  // Chile
        {"SPT",         0.0,       0.0,  -6359587.3,  10.0},  // South Pole
        {"JCMT", -5464075.2, -2493028.4,  2150612.2,  15.0},  // Hawaii
        {"SMA",  -5464075.2, -2493028.4,  2150612.2,   8.0},  // Hawaii (co-located)
        {"SMT",  -1828796.2, -5054406.8,  3427865.2,  10.0},  // Arizona
        {"IRAM",  5088967.9,  -301681.2,  3825012.3,  30.0},  // Spain
        {"LMT",   -768715.6, -5988507.1,  2063353.0,  50.0},  // Mexico
    }};
    return kStations.at(static_cast<std::size_t>(id));
}

/// EHT standard observing wavelength: 1.3 mm (230 GHz).
inline constexpr double kEhtWavelength = 1.3e-3;    // [m]

/// EHT observing frequency: 230 GHz.
inline constexpr double kEhtFrequency  = 230.0e9;   // [Hz]

/// M87* declination in radians (J2000, +12.391 deg).
inline constexpr double kM87DecRad = 12.391 * std::numbers::pi / 180.0;

/// Sgr A* declination in radians (J2000, -29.008 deg).
inline constexpr double kSgrADecRad = -29.008 * std::numbers::pi / 180.0;

/// 1 microarcsecond in radians.
inline constexpr double kMicroarcsecRad = std::numbers::pi / (180.0 * 3600.0 * 1.0e6);

} // namespace physics

#endif // PHYSICS_EHT_VISIBILITY_H
