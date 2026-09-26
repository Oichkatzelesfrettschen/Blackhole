/**
 * @file observer_sky_view.h
 * @brief The observer-sky scene: the sky seen from an equatorial Kerr
 *        observer (canonically Miller's planet), drawn by
 *        shader/observer_sky.frag from the precomputed maps of
 *        physics/observer_sky_lut.h.
 *
 * The maps are keyed by (epsilon, x, v) and built off the render thread, from
 * the assets/luts cache when present. Time runs on the observer's clock: one
 * wall second advances its proper time by skyTimeScale seconds and the
 * coordinate time by that over dtau/dt, and the sky at infinity turns about
 * the spin axis by Omega t. All of it is double precision on the CPU; the
 * shader receives the phase modulo 2 pi.
 */

#ifndef BLACKHOLE_RENDER_OBSERVER_SKY_VIEW_H
#define BLACKHOLE_RENDER_OBSERVER_SKY_VIEW_H

#include <array>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <future>
#include <optional>
#include <string>
#include <vector>

#include <glbinding/gl/types.h>

#include <glm/ext/matrix_float3x3.hpp>

#include "physics/observer_sky_lut.h"
#include "physics/observer_sky_map.h"

namespace blackhole {

struct RenderState;

/** @brief Which observer at the chosen radius: the circular geodesic of each
 *         sense, the ZAMO, or the static observer (outside the ergoregion). */
enum class ObserverKind : std::uint8_t { Prograde = 0, Retrograde = 1, Zamo = 2, Static = 3 };

/** @brief Gargantua's spin deficit 1 - a (Opatrny, Richterek & Bakala,
 *         arXiv:1601.02897; game::CampaignScenario::GargantuaCanon). */
inline constexpr double K_GARGANTUA_SPIN_DEFICIT = 1.33e-14;

/** @brief GM_sun / c^3 in seconds (IAU 2015 nominal GM_sun). */
inline constexpr double K_SOLAR_TIME_SECONDS = 4.925490947641267e-6;

/** @brief The observer key for a kind at (epsilon, x), or nothing where that
 *         observer is not timelike there. */
[[nodiscard]] std::optional<physics::observer_sky::ObserverKey>
observerKeyFor(double epsilon, double x, ObserverKind kind);

/**
 * @brief The observer's clock and azimuthal motion. For ZAMO-frame speed v,
 *        dtau/dt = alpha sqrt(1 - v^2) and Omega = omega + v alpha / varpi,
 *        which reproduce circularOrbit()'s rate and Omega on a geodesic.
 */
struct ObserverClockModel {
  double properTimeRate = 1.0;          ///< dtau/dt.
  double angularVelocity = 0.0;         ///< Omega = dphi/dt, in 1/M.
  double secondsPerM = 0.0;             ///< GM/c^3 for the chosen mass.
  double coordinatePeriodSeconds = 0.0; ///< 2 pi / |Omega| in coordinate seconds; 0 if static.
  double properPeriodSeconds = 0.0;     ///< The same period on the observer's clock.
};
[[nodiscard]] ObserverClockModel observerClockModel(const physics::observer_sky::ObserverKey &key,
                                                    double massSolar);

/** @brief Azimuth (radians, [0, 2 pi)) the sky at infinity has turned after
 *         `properSeconds` on the observer's clock: fmod(Omega t, 2 pi) with
 *         t = properSeconds / (dtau/dt), in double. */
[[nodiscard]] double skyPhaseRadians(const ObserverClockModel &clock, double properSeconds);

/** @brief blackbody_cie_lut.csv: row k at log10 T = k * log10Step holds linear
 *         sRGB at unit luminance and log10 luminance (cd/m^2). */
struct BlackbodyTable {
  double log10Step = 0.01;
  std::vector<std::array<float, 4>> rows;

  /** @brief Linear interpolation at log10 T, clamped to the table. */
  [[nodiscard]] std::array<double, 4> at(double log10T) const;
};
[[nodiscard]] std::optional<BlackbodyTable> loadBlackbodyTable(const std::filesystem::path &csv);

/** @brief Per tile ring i, the CMB luminance flux (cd/m^2 sr, linear sRGB)
 *         received inside ring i inclusive: the sum over rings j <= i and all
 *         azimuths of dOmega_j times the blackbody at cmbTemperature g. */
[[nodiscard]] std::vector<std::array<float, 4>>
cumulativeCmbRingFlux(const physics::observer_sky::ObserverSkyLut &lut, const BlackbodyTable &table,
                      double cmbTemperature);

/** @brief Camera basis on the observer's (r, theta, phi) legs: columns right,
 *         up, forward, with forward along the given local-sky direction and up
 *         toward the spin axis. */
[[nodiscard]] std::array<physics::observer_sky::Vec3, 3> observerViewBasis(double longitude,
                                                                           double latitude);

/** @brief Pixel (x right, y up, origin bottom-left) whose area contains
 *         `look`, for a camera basis and tan(fov_y / 2), or nothing when the
 *         direction is behind the camera or off screen. */
[[nodiscard]] std::optional<std::array<double, 2>>
projectToPixel(const std::array<physics::observer_sky::Vec3, 3> &basis,
               const physics::observer_sky::Vec3 &look, double tanHalfFov, int width, int height);

/**
 * @brief How the observer's own light leaves: the emission-side reading of
 *        the traced sky. (t, phi) -> (-t, -phi) is an isometry of Kerr that
 *        maps the observer's worldline to itself and keeps a photon's E, L,
 *        and Carter constant, so every photon the observer receives from
 *        infinity with blueshift g has a twin it emits to infinity with
 *        nu_inf / nu_emit = g_emit = 1/g = (dtau/dt) / (1 - Omega lambda),
 *        over the same solid angle of its sky.
 */
struct EmissionSummary {
  double escapingFraction = 0.0; ///< Of the emission sphere.
  /// g_emit below 1e-3: light that climbs straight out of the throat, with
  /// g_emit near dtau/dt (lambda near 0).
  double directFraction = 0.0;
  /// g_emit above 0.1: near-superradiant light (lambda near 1/Omega) that
  /// reaches infinity on the NHEKline with g_emit up to sqrt(3).
  double nhekFraction = 0.0;
  double gEmitMin = 0.0;
  double gEmitMax = 0.0;
  double log10Min = -7.0; ///< Histogram of log10 g_emit: first bin edge.
  double log10Step = 0.1;
  std::vector<float> histogram; ///< Emission-sphere fraction per bin.
};
[[nodiscard]] EmissionSummary summarizeEmission(const physics::observer_sky::ObserverSkyLut &lut);

/** @brief Upper half of the extremal Kerr shadow edge seen from inclination
 *         `inclination` (Gralla, Lupsasca & Strominger 2017, arXiv:1710.11112,
 *         Eq. A.5, M = 1): alpha = (r^2 - 1 - 2r) / sin(i), beta = sqrt(r^3 (4 - r)
 *         + cos^2 i - (r^2 - 1 - 2r)^2 cot^2 i) for r in [1, 4] where beta is real. */
[[nodiscard]] std::vector<std::array<double, 2>> extremalShadowEdge(double inclination,
                                                                    int samples);

/** @brief The NHEKline (ibid., Eq. A.12a): alpha = -2 / sin(i), |beta| <
 *         sqrt(3 + cos^2 i - 4 cot^2 i); it exists only for i above
 *         arctan((4/3)^(1/4)) = 47 deg (and below its mirror). */
struct NhekLine {
  double alpha = 0.0;
  double halfLength = 0.0;
};
[[nodiscard]] std::optional<NhekLine> nhekLine(double inclination);

/** @brief Coordinate seconds light takes from the observer to radius
 *         1 + xFar along the equatorial principal null congruence
 *         (kerr_observer::principalNullDelay), the radial lower bound for any
 *         path out of the throat. */
[[nodiscard]] double signalDelaySeconds(const physics::observer_sky::ObserverKey &key,
                                        const ObserverClockModel &clock, double xFar);

/**
 * @brief GPU residency for one observer's maps. request() starts a background
 *        load-or-build for a key; poll() uploads the finished bundle on the
 *        GL thread. Textures stay bound to the last completed key until a new
 *        one finishes, so a slider drag keeps drawing the previous sky.
 */
class ObserverSkyRenderer {
public:
  enum class Status : std::uint8_t { Idle = 0, Building = 1, Ready = 2, Failed = 3 };

  ObserverSkyRenderer() = default;
  ObserverSkyRenderer(const ObserverSkyRenderer &) = delete;
  ObserverSkyRenderer &operator=(const ObserverSkyRenderer &) = delete;
  ObserverSkyRenderer(ObserverSkyRenderer &&) = delete;
  ObserverSkyRenderer &operator=(ObserverSkyRenderer &&) = delete;
  ~ObserverSkyRenderer() = default;

  /** @brief Loads or builds the bundle for `key` unless it is already
   *         resident or in flight. `cacheDirectory` holds observer_sky_*.bin. */
  void request(const physics::observer_sky::ObserverKey &key,
               const physics::observer_sky::LutDimensions &dimensions,
               const std::filesystem::path &cacheDirectory);
  /** @brief Uploads a finished bundle; call once per frame on the GL thread. */
  void poll(const std::filesystem::path &blackbodyCsv, double cmbTemperature);
  void shutdown();

  [[nodiscard]] Status status() const { return status_; }
  [[nodiscard]] bool ready() const { return lut_.has_value() && skyTexture_ != 0; }
  [[nodiscard]] const std::optional<physics::observer_sky::ObserverSkyLut> &lut() const {
    return lut_;
  }
  [[nodiscard]] const std::string &message() const { return message_; }
  [[nodiscard]] const EmissionSummary &emission() const { return emission_; }
  [[nodiscard]] gl::GLuint skyTexture() const { return skyTexture_; }
  [[nodiscard]] gl::GLuint skySpanTexture() const { return skySpanTexture_; }
  [[nodiscard]] gl::GLuint tileTexture() const { return tileTexture_; }
  [[nodiscard]] gl::GLuint tileSpanTexture() const { return tileSpanTexture_; }
  [[nodiscard]] gl::GLuint tileFluxTexture() const { return tileFluxTexture_; }
  [[nodiscard]] gl::GLuint blackbodyTexture() const { return blackbodyTexture_; }

private:
  void upload(const physics::observer_sky::ObserverSkyLut &lut, const BlackbodyTable &table,
              double cmbTemperature);

  Status status_ = Status::Idle;
  std::optional<std::uint64_t> residentHash_;
  std::optional<std::uint64_t> pendingHash_;
  std::future<std::optional<physics::observer_sky::ObserverSkyLut>> pending_;
  std::optional<physics::observer_sky::ObserverSkyLut> lut_;
  std::optional<BlackbodyTable> blackbody_;
  EmissionSummary emission_;
  std::string message_;
  gl::GLuint skyTexture_ = 0;
  gl::GLuint skySpanTexture_ = 0;
  gl::GLuint tileTexture_ = 0;
  gl::GLuint tileSpanTexture_ = 0;
  gl::GLuint tileFluxTexture_ = 0;
  gl::GLuint blackbodyTexture_ = 0;
};

/**
 * @brief Draws the observer-sky scene into rs.targets.texBlackhole: requests
 *        and polls the maps for rs.observerView's observer, advances its clock
 *        by deltaSeconds * skyTimeScale proper seconds, and runs
 *        observer_sky.frag. With followCamera set, cameraBasis (world right,
 *        up, forward) steers the look direction; otherwise the view's look
 *        angles do.
 */
void renderObserverSkyScene(RenderState &rs, const glm::mat3 &cameraBasis, float deltaSeconds);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_OBSERVER_SKY_VIEW_H
