/**
 * @file observer_sky_view.cpp
 * @brief Observer-sky scene: clock model, blackbody table, CMB ring flux,
 *        camera geometry, background map residency, and the per-frame pass.
 */

#include "render/observer_sky_view.h"

#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <filesystem>
#include <format>
#include <fstream>
#include <future>
#include <numbers>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <stop_token>
#include <string>
#include <thread>
#include <utility>
#include <vector>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions-patches.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/vector_float3.hpp>

#include "physics/kerr_observer.h"
#include "physics/observer_sky_lut.h"
#include "physics/observer_sky_map.h"
#include "platform/resource_paths.h"
#include "render.h"
#include "render/render_state.h"

using namespace gl;

namespace blackhole {

namespace {

namespace ko = physics::kerr_observer;
namespace sky = physics::observer_sky;

constexpr double K_TWO_PI = 2.0 * std::numbers::pi;

sky::Vec3 cross(const sky::Vec3 &a, const sky::Vec3 &b) {
  return {(a.at(1) * b.at(2)) - (a.at(2) * b.at(1)), (a.at(2) * b.at(0)) - (a.at(0) * b.at(2)),
          (a.at(0) * b.at(1)) - (a.at(1) * b.at(0))};
}

double dot(const sky::Vec3 &a, const sky::Vec3 &b) {
  return (a.at(0) * b.at(0)) + (a.at(1) * b.at(1)) + (a.at(2) * b.at(2));
}

sky::Vec3 normalized(const sky::Vec3 &v) {
  const double length = std::sqrt(dot(v, v));
  return {v.at(0) / length, v.at(1) / length, v.at(2) / length};
}

/** @brief Uploads a float texture with `channels` components per texel (3
 *         for the RGB32F source-span maps, 4 for the RGBA32F sky maps). */
GLuint uploadFloatTexture(int width, int height, const float *pixels, GLenum filter,
                          int channels = 4) {
  const GLenum internalFormat = channels == 3 ? GL_RGB32F : GL_RGBA32F;
  const GLenum format = channels == 3 ? GL_RGB : GL_RGBA;
  GLuint texture = 0;
  glGenTextures(1, &texture);
  glBindTexture(GL_TEXTURE_2D, texture);
  glTexImage2D(GL_TEXTURE_2D, 0, internalFormat, width, height, 0, format, GL_FLOAT, pixels);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, static_cast<GLint>(filter));
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, static_cast<GLint>(filter));
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, static_cast<GLint>(GL_CLAMP_TO_EDGE));
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, static_cast<GLint>(GL_CLAMP_TO_EDGE));
  glBindTexture(GL_TEXTURE_2D, 0);
  return texture;
}

/** @brief Whether the cubemap bound to GL_TEXTURE_CUBE_MAP has a mip level 1,
 *         or cannot have one (a base level at most one texel wide). The
 *         texture object answers for itself, so a name that GL reuses for a
 *         new cubemap after a background swap reads as unmipmapped; every
 *         galaxy cubemap is a new object whose level 0 is specified once
 *         (loadCubemap). */
bool boundCubemapHasMipChain() {
  GLint baseWidth = 0;
  GLint levelOneWidth = 0;
  glGetTexLevelParameteriv(GL_TEXTURE_CUBE_MAP_POSITIVE_X, 0, GL_TEXTURE_WIDTH, &baseWidth);
  glGetTexLevelParameteriv(GL_TEXTURE_CUBE_MAP_POSITIVE_X, 1, GL_TEXTURE_WIDTH, &levelOneWidth);
  return baseWidth <= 1 || levelOneWidth > 0;
}

void deleteTexture(GLuint &texture) {
  if (texture != 0) {
    glDeleteTextures(1, &texture);
    texture = 0;
  }
}

/**
 * @brief Background half of ObserverSkyRenderer: the blackbody table, the
 *        cached bundle for `key` (or a fresh build, then cached), and the
 *        emission summary and CMB ring flux derived from them. Nothing when
 *        `stop` ended the build; throws with the reason on failure.
 */
std::optional<PreparedObserverSky> prepareObserverSky(const sky::ObserverKey &key,
                                                      const sky::LutDimensions &dimensions,
                                                      const std::filesystem::path &cacheDirectory,
                                                      const std::filesystem::path &blackbodyCsv,
                                                      double cmbTemperature,
                                                      const std::stop_token &stop) {
  std::optional<BlackbodyTable> blackbody = loadBlackbodyTable(blackbodyCsv);
  if (!blackbody) {
    throw std::runtime_error("missing " + blackbodyCsv.string() +
                             " (run $PYTHON scripts/generate_blackbody_cie_lut.py)");
  }
  const sky::TraceSettings settings;
  const std::uint64_t bundleHash = sky::lutHash(key, dimensions, settings);
  const std::filesystem::path file = cacheDirectory / (sky::lutStem(bundleHash) + ".bin");
  std::optional<sky::ObserverSkyLut> lut = sky::readObserverSkyLut(file, bundleHash);
  if (!lut) {
    lut = sky::tryBuildObserverSkyLut(key, dimensions, settings, observerSkyBuildThreads(), stop);
    if (!lut) {
      return std::nullopt;
    }
    // Evict whether or not the sidecar landed: a published .bin alone is
    // readable and counts against the budget. Only the user cache is managed;
    // the source-tree fallback may hold explicit --out bundles, never pruned.
    (void)sky::writeObserverSkyLut(*lut, cacheDirectory);
    if (cacheDirectory == platform::userCacheDirectory() / "observer_sky") {
      sky::evictObserverSkyBundles(cacheDirectory, sky::K_OBSERVER_SKY_CACHE_BYTES, bundleHash);
    }
  }
  PreparedObserverSky prepared{
      .lut = std::move(*lut), .blackbody = std::move(*blackbody), .emission = {}, .ringFlux = {}};
  prepared.emission = summarizeEmission(prepared.lut);
  prepared.ringFlux = cumulativeCmbRingFlux(prepared.lut, prepared.blackbody, cmbTemperature);
  return prepared;
}

/** @brief Why no observer of `kind` exists at (epsilon, x), for the panels. */
std::string invalidObserverReason(ObserverKind kind, double epsilon, double x) {
  const std::string where = std::format("r - 1 = {:.6e} M, 1 - a = {:.3e}", x, epsilon);
  switch (kind) {
  case ObserverKind::Prograde:
  case ObserverKind::Retrograde:
    return std::format("No {} circular orbit at {}: no timelike circular geodesic of that "
                       "sense exists at this radius.",
                       kind == ObserverKind::Prograde ? "prograde" : "retrograde", where);
  case ObserverKind::Zamo:
    return std::format("No ZAMO at {}: the radius is inside the outer horizon.", where);
  case ObserverKind::Static:
    return std::format("No static observer at {}: the radius is inside the ergoregion, where "
                       "every observer must co-rotate with the hole.",
                       where);
  }
  return std::format("No observer at {}.", where);
}

/**
 * @brief Advances the observer's clock for one frame and returns the proper
 *        seconds the frame spans (the motion-blur interval). The clock follows
 *        the resident sky, so time and image always agree, and stands still
 *        while no sky is resident. A recording sets it from the output clock:
 *        the proper time at the first recorded frame's call is the origin and
 *        frame N shows origin + skyTimeScale * N / fps, so warmup frames, which
 *        keep N, leave it in place and the frames depend on N alone.
 */
double advanceObserverClock(RenderState::ObserverViewGroup &view, bool skyResident,
                            float deltaSeconds, const std::optional<ObserverRecordClock> &record) {
  if (!record) {
    view.recordClockOrigin.reset();
    const double step =
        view.paused || !skyResident ? 0.0 : static_cast<double>(deltaSeconds) * view.skyTimeScale;
    view.properSeconds += step;
    return step;
  }
  if (!view.recordClockOrigin) {
    view.recordClockOrigin = view.properSeconds;
  }
  if (!skyResident) {
    return 0.0;
  }
  view.properSeconds = *view.recordClockOrigin + (record->outputSeconds * view.skyTimeScale);
  return record->frameSeconds * view.skyTimeScale;
}

} // namespace

unsigned observerSkyBuildThreads() {
  const unsigned hardware = std::thread::hardware_concurrency();
  return hardware > 1U ? hardware - 1U : 1U;
}

std::optional<sky::ObserverKey> observerKeyFor(double epsilon, double x, ObserverKind kind) {
  switch (kind) {
  case ObserverKind::Prograde:
    return sky::orbitingObserver(epsilon, x, ko::OrbitSense::Prograde);
  case ObserverKind::Retrograde:
    return sky::orbitingObserver(epsilon, x, ko::OrbitSense::Retrograde);
  case ObserverKind::Zamo:
    if (!(x > ko::horizonOffset(epsilon))) {
      return std::nullopt;
    }
    return sky::ObserverKey{.epsilon = epsilon, .x = x, .velocity = 0.0};
  case ObserverKind::Static: {
    if (!(x > ko::horizonOffset(epsilon))) {
      return std::nullopt;
    }
    const double velocity = ko::staticObserverVelocity(ko::equatorialFrame(epsilon, x));
    if (!(std::fabs(velocity) < 1.0)) {
      return std::nullopt; // Inside the ergoregion no observer can stay static.
    }
    return sky::ObserverKey{.epsilon = epsilon, .x = x, .velocity = velocity};
  }
  }
  return std::nullopt;
}

ObserverClockModel observerClockModel(const sky::ObserverKey &key, double massSolar) {
  const ko::EquatorialFrame frame = ko::equatorialFrame(key.epsilon, key.x);
  ObserverClockModel clock;
  clock.properTimeRate = frame.alpha * std::sqrt((1.0 - key.velocity) * (1.0 + key.velocity));
  clock.angularVelocity = frame.omega + (key.velocity * frame.alpha / frame.varpi);
  clock.secondsPerM = K_SOLAR_TIME_SECONDS * massSolar;
  if (std::fabs(clock.angularVelocity) > 0.0) {
    clock.coordinatePeriodSeconds = K_TWO_PI / std::fabs(clock.angularVelocity) * clock.secondsPerM;
    clock.properPeriodSeconds = clock.coordinatePeriodSeconds * clock.properTimeRate;
  }
  return clock;
}

double skyPhaseRadians(const ObserverClockModel &clock, double properSeconds) {
  const double coordinateM = properSeconds / clock.properTimeRate / clock.secondsPerM;
  const double phase = std::fmod(clock.angularVelocity * coordinateM, K_TWO_PI);
  return phase < 0.0 ? phase + K_TWO_PI : phase;
}

std::array<double, 4> BlackbodyTable::at(double log10T) const {
  if (rows.empty()) {
    return {0.0, 0.0, 0.0, -1.0e30};
  }
  const double position = std::clamp(log10T / log10Step, 0.0, static_cast<double>(rows.size() - 1));
  const auto low = static_cast<std::size_t>(position);
  const std::size_t high = std::min(low + 1, rows.size() - 1);
  const double t = position - static_cast<double>(low);
  std::array<double, 4> value{};
  for (std::size_t channel = 0; channel < 4; ++channel) {
    value.at(channel) = ((1.0 - t) * static_cast<double>(rows.at(low).at(channel))) +
                        (t * static_cast<double>(rows.at(high).at(channel)));
  }
  return value;
}

std::optional<BlackbodyTable> loadBlackbodyTable(const std::filesystem::path &csv) {
  std::ifstream file(csv);
  std::string line;
  if (!file || !std::getline(file, line)) {
    return std::nullopt;
  }
  BlackbodyTable table;
  while (std::getline(file, line)) {
    std::replace(line.begin(), line.end(), ',', ' ');
    std::istringstream fields(line);
    double log10T = 0.0;
    std::array<float, 4> row{};
    if (!(fields >> log10T >> row.at(0) >> row.at(1) >> row.at(2) >> row.at(3))) {
      return std::nullopt;
    }
    table.rows.push_back(row);
  }
  if (table.rows.size() < 2) {
    return std::nullopt;
  }
  return table;
}

std::vector<std::array<float, 4>> cumulativeCmbRingFlux(const sky::ObserverSkyLut &lut,
                                                        const BlackbodyTable &table,
                                                        double cmbTemperature) {
  const sky::SkyImage &image = lut.tileImage;
  std::vector<std::array<float, 4>> flux(image.height, std::array<float, 4>{});
  std::array<double, 3> running{0.0, 0.0, 0.0};
  const double log10Temperature = std::log10(cmbTemperature);
  for (std::size_t ring = 0; ring < image.height; ++ring) {
    const double solidAngle = sky::tileTexelSolidAngle(lut.tile, ring);
    for (std::size_t column = 0; column < image.width; ++column) {
      const float logG = image.rgba.at((((ring * image.width) + column) * 4) + 3);
      if (!(logG > sky::K_NO_SKY_THRESHOLD)) {
        continue;
      }
      const std::array<double, 4> color =
          table.at(log10Temperature + (static_cast<double>(logG) / std::numbers::ln10));
      const double luminance = std::pow(10.0, color.at(3)) * solidAngle;
      for (std::size_t channel = 0; channel < 3; ++channel) {
        running.at(channel) += color.at(channel) * luminance;
      }
    }
    flux.at(ring) = {static_cast<float>(running.at(0)), static_cast<float>(running.at(1)),
                     static_cast<float>(running.at(2)), 1.0F};
  }
  return flux;
}

std::array<sky::Vec3, 3> observerViewBasis(double longitude, double latitude) {
  const sky::Vec3 forward = sky::lookDirection(longitude, latitude);
  // Up toward the spin axis (-e_theta); near a pole fall back to the motion.
  sky::Vec3 upHint{0.0, -1.0, 0.0};
  if (std::fabs(dot(forward, upHint)) > 0.999) {
    upHint = sky::Vec3{0.0, 0.0, 1.0};
  }
  const sky::Vec3 right = normalized(cross(forward, upHint));
  const sky::Vec3 up = cross(right, forward);
  return {right, up, forward};
}

std::optional<std::array<double, 2>> projectToPixel(const std::array<sky::Vec3, 3> &basis,
                                                    const sky::Vec3 &look, double tanHalfFov,
                                                    int width, int height) {
  const double depth = dot(look, basis.at(2));
  if (!(depth > 0.0) || width <= 0 || height <= 0) {
    return std::nullopt;
  }
  const double aspect = static_cast<double>(width) / static_cast<double>(height);
  const double ndcX = dot(look, basis.at(0)) / depth / (tanHalfFov * aspect);
  const double ndcY = dot(look, basis.at(1)) / depth / tanHalfFov;
  if (std::fabs(ndcX) >= 1.0 || std::fabs(ndcY) >= 1.0) {
    return std::nullopt;
  }
  return std::array<double, 2>{0.5 * (ndcX + 1.0) * static_cast<double>(width),
                               0.5 * (ndcY + 1.0) * static_cast<double>(height)};
}

EmissionSummary summarizeEmission(const sky::ObserverSkyLut &lut) {
  EmissionSummary summary;
  constexpr std::size_t bins = 80;
  std::vector<double> histogram(bins, 0.0);
  bool any = false;
  const auto add = [&](float logG, double solidAngle) {
    if (!(logG > sky::K_NO_SKY_THRESHOLD)) {
      return;
    }
    const double gEmit = std::exp(-static_cast<double>(logG));
    summary.escapingFraction += solidAngle;
    summary.directFraction += gEmit < 1.0e-3 ? solidAngle : 0.0;
    summary.nhekFraction += gEmit > 0.1 ? solidAngle : 0.0;
    summary.gEmitMin = any ? std::fmin(summary.gEmitMin, gEmit) : gEmit;
    summary.gEmitMax = any ? std::fmax(summary.gEmitMax, gEmit) : gEmit;
    any = true;
    const double position = (std::log10(gEmit) - summary.log10Min) / summary.log10Step;
    const auto bin =
        static_cast<std::size_t>(std::clamp(position, 0.0, static_cast<double>(bins - 1)));
    histogram.at(bin) += solidAngle;
  };
  // The tile replaces the equirectangular map inside its outer radius.
  const sky::LogPolarTile &tile = lut.tile;
  const double cosRhoMax = std::cos(tile.rhoMax);
  for (std::size_t row = 0; row < lut.sky.height; ++row) {
    const double solidAngle = sky::equirectPixelSolidAngle(row, lut.sky.width, lut.sky.height);
    for (std::size_t column = 0; column < lut.sky.width; ++column) {
      const sky::Vec3 look = sky::equirectLook(column, row, lut.sky.width, lut.sky.height);
      if (dot(look, tile.center) > cosRhoMax) {
        continue; // Counted through the tile below.
      }
      add(lut.sky.rgba.at((((row * lut.sky.width) + column) * 4) + 3), solidAngle);
    }
  }
  for (std::size_t ring = 0; ring < lut.tileImage.height; ++ring) {
    const double solidAngle = sky::tileTexelSolidAngle(tile, ring);
    for (std::size_t column = 0; column < lut.tileImage.width; ++column) {
      add(lut.tileImage.rgba.at((((ring * lut.tileImage.width) + column) * 4) + 3), solidAngle);
    }
  }
  const double sphere = 4.0 * std::numbers::pi;
  summary.escapingFraction /= sphere;
  summary.directFraction /= sphere;
  summary.nhekFraction /= sphere;
  summary.histogram.resize(bins);
  std::ranges::transform(histogram, summary.histogram.begin(),
                         [sphere](double value) { return static_cast<float>(value / sphere); });
  return summary;
}

std::vector<std::array<double, 2>> extremalShadowEdge(double inclination, int samples) {
  const double sinI = std::sin(inclination);
  const double cosI = std::cos(inclination);
  const double cot2 = (cosI * cosI) / (sinI * sinI);
  std::vector<std::array<double, 2>> edge;
  for (int index = 0; index <= samples; ++index) {
    const double r = 1.0 + (3.0 * static_cast<double>(index) / static_cast<double>(samples));
    const double shifted = (r * r) - 1.0 - (2.0 * r);
    const double beta2 = (r * r * r * (4.0 - r)) + (cosI * cosI) - (shifted * shifted * cot2);
    if (beta2 >= 0.0) {
      edge.push_back({shifted / sinI, std::sqrt(beta2)});
    }
  }
  return edge;
}

std::optional<NhekLine> nhekLine(double inclination) {
  const double sinI = std::sin(inclination);
  const double cosI = std::cos(inclination);
  const double halfLength2 = 3.0 + (cosI * cosI) - (4.0 * cosI * cosI / (sinI * sinI));
  if (!(halfLength2 > 0.0)) {
    return std::nullopt;
  }
  return NhekLine{.alpha = -2.0 / sinI, .halfLength = std::sqrt(halfLength2)};
}

double signalDelaySeconds(const sky::ObserverKey &key, const ObserverClockModel &clock,
                          double xFar) {
  return ko::principalNullDelay(key.epsilon, key.x, xFar) * clock.secondsPerM;
}

ObserverSkyRenderer::~ObserverSkyRenderer() {
  stop_.request_stop();
}

void ObserverSkyRenderer::request(const sky::ObserverKey &key, const sky::LutDimensions &dimensions,
                                  const std::filesystem::path &cacheDirectory,
                                  const std::filesystem::path &blackbodyCsv,
                                  double cmbTemperature) {
  const std::uint64_t hash = sky::lutHash(key, dimensions, sky::TraceSettings{});
  wantedHash_ = hash;
  if (failedHash_ != hash) {
    failedHash_.reset(); // A failure latches only while its key stays requested.
  }
  if (status_ == Status::InvalidObserver) {
    status_ = Status::Idle;
    message_.clear();
  }
  if (pending_.valid()) {
    if (pendingHash_ != hash) {
      stop_.request_stop(); // Superseded: it lands stopped and this key starts next.
    }
    return;
  }
  if (residentHash_ == hash) {
    return;
  }
  if (failedHash_ == hash) {
    releaseSky();
    status_ = Status::Failed;
    message_ = failureMessage_;
    return;
  }
  stop_ = std::stop_source{};
  pendingHash_ = hash;
  status_ = Status::Building;
  message_ = "tracing the observer's sky (about 20 s on first use; cached afterwards)";
  pending_ = std::async(std::launch::async, prepareObserverSky, key, dimensions, cacheDirectory,
                        blackbodyCsv, cmbTemperature, stop_.get_token());
}

void ObserverSkyRenderer::invalidate(const std::string &reason) {
  wantedHash_.reset();
  failedHash_.reset();
  if (pending_.valid()) {
    stop_.request_stop();
  }
  releaseSky();
  status_ = Status::InvalidObserver;
  message_ = reason;
}

void ObserverSkyRenderer::poll() {
  if (!pending_.valid() ||
      pending_.wait_for(std::chrono::seconds(0)) != std::future_status::ready) {
    return;
  }
  const std::optional<std::uint64_t> finishedHash = pendingHash_;
  pendingHash_.reset();
  std::optional<PreparedObserverSky> prepared;
  try {
    prepared = pending_.get();
  } catch (const std::exception &error) {
    failedHash_ = finishedHash;
    failureMessage_ = std::string("observer sky build failed: ") + error.what();
    if (wantedHash_ == finishedHash) {
      releaseSky();
      status_ = Status::Failed;
      message_ = failureMessage_;
    }
    return;
  }
  if (!prepared || wantedHash_ != finishedHash) {
    // Stopped, or no longer the requested observer: the next request()
    // starts the wanted key, and an invalid observer keeps its status.
    if (status_ == Status::Building) {
      status_ = lut_ ? Status::Ready : Status::Idle;
      message_.clear();
    }
    return;
  }
  upload(*prepared);
  emission_ = std::move(prepared->emission);
  lut_ = std::move(prepared->lut);
  residentHash_ = finishedHash;
  status_ = Status::Ready;
  message_.clear();
}

void ObserverSkyRenderer::upload(const PreparedObserverSky &prepared) {
  const sky::ObserverSkyLut &bundle = prepared.lut;
  releaseSky();
  skySpanTexture_ =
      uploadFloatTexture(static_cast<int>(bundle.sky.width), static_cast<int>(bundle.sky.height),
                         bundle.sky.sourceSpan.data(), GL_NEAREST, 3);
  tileSpanTexture_ = uploadFloatTexture(static_cast<int>(bundle.tileImage.width),
                                        static_cast<int>(bundle.tileImage.height),
                                        bundle.tileImage.sourceSpan.data(), GL_NEAREST, 3);
  skyTexture_ =
      uploadFloatTexture(static_cast<int>(bundle.sky.width), static_cast<int>(bundle.sky.height),
                         bundle.sky.rgba.data(), GL_NEAREST);
  tileTexture_ = uploadFloatTexture(static_cast<int>(bundle.tileImage.width),
                                    static_cast<int>(bundle.tileImage.height),
                                    bundle.tileImage.rgba.data(), GL_NEAREST);
  const auto flatten = [](const std::vector<std::array<float, 4>> &rows) {
    std::vector<float> flat;
    flat.reserve(rows.size() * 4);
    std::ranges::for_each(rows, [&flat](const std::array<float, 4> &row) {
      flat.insert(flat.end(), row.begin(), row.end());
    });
    return flat;
  };
  const std::vector<float> flux = flatten(prepared.ringFlux);
  tileFluxTexture_ =
      uploadFloatTexture(static_cast<int>(flux.size() / 4), 1, flux.data(), GL_NEAREST);
  if (blackbodyTexture_ == 0) {
    const std::vector<float> rows = flatten(prepared.blackbody.rows);
    blackbodyTexture_ =
        uploadFloatTexture(static_cast<int>(rows.size() / 4), 1, rows.data(), GL_LINEAR);
  }
}

void ObserverSkyRenderer::releaseSky() {
  deleteTexture(skyTexture_);
  deleteTexture(skySpanTexture_);
  deleteTexture(tileTexture_);
  deleteTexture(tileSpanTexture_);
  deleteTexture(tileFluxTexture_);
  lut_.reset();
  residentHash_.reset();
  emission_ = EmissionSummary{};
}

namespace {

/** @brief The bundle cache: <user cache>/observer_sky when it can be written,
 *         else the source tree's LUT directory; observer_sky_lut publishes
 *         to the same place by default.
 *         Resolved once per process, so a frame does no filesystem work. */
const std::filesystem::path &observerSkyCacheDirectory(const std::filesystem::path &fallback) {
  static const std::filesystem::path directory = [&fallback] {
    const std::filesystem::path cache = platform::writableCacheSubdirectory("observer_sky");
    return cache.empty() ? fallback : cache;
  }();
  return directory;
}

} // namespace

void renderObserverSkyScene(RenderState &rs, const glm::mat3 &cameraBasis, float deltaSeconds,
                            const std::optional<ObserverRecordClock> &record) {
  RenderState::ObserverViewGroup &view = rs.observerView;
  const ko::OrbitSense sense =
      view.kind == ObserverKind::Retrograde ? ko::OrbitSense::Retrograde : ko::OrbitSense::Prograde;
  view.x = view.atIsco ? ko::iscoOffset(view.epsilon, sense) : view.x;
  const std::optional<sky::ObserverKey> key = observerKeyFor(view.epsilon, view.x, view.kind);
  const std::filesystem::path sourceLutDirectory = platform::resourceRoot() / "assets" / "luts";
  const std::filesystem::path &lutDirectory = observerSkyCacheDirectory(sourceLutDirectory);
  if (key) {
    view.renderer.request(*key, sky::LutDimensions{}, lutDirectory,
                          sourceLutDirectory / "blackbody_cie_lut.csv", view.cmbTemperature);
  } else {
    view.renderer.invalidate(invalidObserverReason(view.kind, view.epsilon, view.x));
  }
  view.renderer.poll();
  const std::optional<sky::ObserverSkyLut> &lut = view.renderer.lut();

  const ObserverClockModel clock =
      lut ? observerClockModel(lut->key, view.massSolar) : ObserverClockModel{};
  const double properStep = advanceObserverClock(view, lut.has_value(), deltaSeconds, record);
  const double phase = lut ? skyPhaseRadians(clock, view.properSeconds) : 0.0;
  // Sky rotation during this frame, unwrapped, for the motion blur.
  const double frameTurn =
      lut ? clock.angularVelocity * properStep / clock.properTimeRate / clock.secondsPerM : 0.0;

  if (view.lookAtPatch && lut) {
    const sky::SkyAngles peak = sky::lookAngles(lut->peak.look);
    view.lookLongitudeDeg = peak.longitude * 180.0 / std::numbers::pi;
    view.lookLatitudeDeg = peak.latitude * 180.0 / std::numbers::pi;
  }
  std::array<sky::Vec3, 3> basis{};
  if (view.followCamera) {
    // World (x, y up, z) to the tetrad legs (r, theta, phi) = (z, -y, x): the
    // default camera on +z looks at the hole, and world up is the spin axis.
    for (int column = 0; column < 3; ++column) {
      const glm::vec3 &axis = cameraBasis[column];
      basis.at(static_cast<std::size_t>(column)) = sky::Vec3{
          static_cast<double>(axis.z), -static_cast<double>(axis.y), static_cast<double>(axis.x)};
    }
  } else {
    basis = observerViewBasis(view.lookLongitudeDeg * std::numbers::pi / 180.0,
                              view.lookLatitudeDeg * std::numbers::pi / 180.0);
  }
  view.fovDeg = std::clamp(view.fovDeg, K_OBSERVER_FOV_MIN_DEG, K_OBSERVER_FOV_MAX_DEG);
  const double tanHalfFov = std::tan(0.5 * view.fovDeg * std::numbers::pi / 180.0);

  RenderToTextureInfo rtti;
  rtti.fragShader = "shader/observer_sky.frag";
  rtti.targetTexture = rs.targets.texBlackhole;
  rtti.width = rs.targets.renderWidth;
  rtti.height = rs.targets.renderHeight;
  const bool ready = view.renderer.ready();
  const GLuint fallback = rs.background.fallback2D;
  rtti.textureUniforms["skyMap"] = ready ? view.renderer.skyTexture() : fallback;
  rtti.textureUniforms["skySpan"] = ready ? view.renderer.skySpanTexture() : fallback;
  rtti.textureUniforms["skyTile"] = ready ? view.renderer.tileTexture() : fallback;
  rtti.textureUniforms["tileSpan"] = ready ? view.renderer.tileSpanTexture() : fallback;
  rtti.textureUniforms["tileFluxLut"] = ready ? view.renderer.tileFluxTexture() : fallback;
  rtti.textureUniforms["blackbodyLut"] = ready ? view.renderer.blackbodyTexture() : fallback;
  rtti.cubemapUniforms["galaxy"] =
      rs.background.galaxy != 0 ? rs.background.galaxy : rs.background.fallbackCubemap;
  rtti.floatUniforms["skyReady"] = ready ? 1.0F : 0.0F;
  rtti.mat3Uniforms["viewBasis"] =
      glm::mat3(glm::vec3(basis.at(0).at(0), basis.at(0).at(1), basis.at(0).at(2)),
                glm::vec3(basis.at(1).at(0), basis.at(1).at(1), basis.at(1).at(2)),
                glm::vec3(basis.at(2).at(0), basis.at(2).at(1), basis.at(2).at(2)));
  rtti.floatUniforms["tanHalfFov"] = static_cast<float>(tanHalfFov);
  rtti.floatUniforms["skyPhiOffset"] = static_cast<float>(phase);
  // Once the sky turns more than 0.01 rad per frame the shader averages 4 to
  // 16 sub-frame positions over the turn it made during the frame.
  const bool blur = view.motionBlur && std::fabs(frameTurn) > 0.01;
  rtti.floatUniforms["skyPhiBlurSpan"] = blur ? static_cast<float>(frameTurn) : 0.0F;
  rtti.floatUniforms["blurSamples"] = blur ? 4.0F : 1.0F;
  rtti.floatUniforms["cmbEnabled"] = view.cmbEnabled ? 1.0F : 0.0F;
  rtti.floatUniforms["cmbTemperature"] = static_cast<float>(view.cmbTemperature);
  rtti.floatUniforms["starsEnabled"] = view.starsEnabled ? 1.0F : 0.0F;
  rtti.floatUniforms["starSkyLuminance"] = view.starSkyLuminance;
  rtti.floatUniforms["logLuminanceMin"] = view.logLuminanceMin;
  rtti.floatUniforms["logLuminanceMax"] = view.logLuminanceMax;
  rtti.floatUniforms["displayPeak"] = view.displayPeak;
  if (lut) {
    const sky::LogPolarTile &tile = lut->tile;
    const auto vec3 = [](const sky::Vec3 &v) {
      return glm::vec3(static_cast<float>(v.at(0)), static_cast<float>(v.at(1)),
                       static_cast<float>(v.at(2)));
    };
    rtti.vec3Uniforms["tileCenter"] = vec3(tile.center);
    rtti.vec3Uniforms["tileEast"] = vec3(tile.axisEast);
    rtti.vec3Uniforms["tileNorth"] = vec3(tile.axisNorth);
    rtti.floatUniforms["tileLogRhoMin"] = static_cast<float>(std::log(tile.rhoMin));
    rtti.floatUniforms["tileLogRhoMax"] = static_cast<float>(std::log(tile.rhoMax));
    rtti.floatUniforms["useTile"] = 1.0F;
    const auto pixel = projectToPixel(basis, tile.center, tanHalfFov, rtti.width, rtti.height);
    rtti.floatUniforms["splatEnabled"] = pixel ? 1.0F : 0.0F;
    if (pixel) {
      rtti.floatUniforms["splatPixelX"] = static_cast<float>(pixel->at(0));
      rtti.floatUniforms["splatPixelY"] = static_cast<float>(pixel->at(1));
      // A pixel at tangent-plane offset (u, v) subtends p^2 / (1 + u^2 + v^2)^(3/2).
      const double pitch = 2.0 * tanHalfFov / static_cast<double>(rtti.height);
      const double u =
          ((pixel->at(0) / static_cast<double>(rtti.height)) -
           (0.5 * static_cast<double>(rtti.width) / static_cast<double>(rtti.height))) *
          2.0 * tanHalfFov;
      const double v = ((pixel->at(1) / static_cast<double>(rtti.height)) - 0.5) * 2.0 * tanHalfFov;
      const double solidAngle = pitch * pitch / std::pow(1.0 + (u * u) + (v * v), 1.5);
      rtti.floatUniforms["pixelSolidAngle"] = static_cast<float>(solidAngle);
    }
  } else {
    rtti.floatUniforms["useTile"] = 0.0F;
    rtti.floatUniforms["splatEnabled"] = 0.0F;
  }
  // The star lookup picks a mip level from each pixel's footprint on the sky
  // at infinity. The shared galaxy cubemap samples its base level only
  // (GL_LINEAR), so the pass adds the mip chain when the bound cubemap lacks
  // one and switches the minification filter to trilinear for its own draw.
  const GLuint galaxy = rs.background.galaxy;
  if (galaxy != 0) {
    glBindTexture(GL_TEXTURE_CUBE_MAP, galaxy);
    if (!boundCubemapHasMipChain()) {
      glGenerateMipmap(GL_TEXTURE_CUBE_MAP);
    }
    glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_MIN_FILTER,
                    static_cast<GLint>(GL_LINEAR_MIPMAP_LINEAR));
    glBindTexture(GL_TEXTURE_CUBE_MAP, 0);
  }
  renderToTexture(rtti);
  if (galaxy != 0) {
    glBindTexture(GL_TEXTURE_CUBE_MAP, galaxy);
    glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_MIN_FILTER, static_cast<GLint>(GL_LINEAR));
    glBindTexture(GL_TEXTURE_CUBE_MAP, 0);
  }
  view.lastClock = clock;
}

SceneCaptureState sceneCaptureState(const RenderState &rs) {
  if (rs.scene.mode != RenderState::SceneMode::ObserverSky) {
    return SceneCaptureState::Ready;
  }
  const ObserverSkyRenderer &renderer = rs.observerView.renderer;
  switch (renderer.status()) {
  case ObserverSkyRenderer::Status::Ready:
    return renderer.ready() ? SceneCaptureState::Ready : SceneCaptureState::Pending;
  case ObserverSkyRenderer::Status::Failed:
  case ObserverSkyRenderer::Status::InvalidObserver:
    return SceneCaptureState::Failed;
  case ObserverSkyRenderer::Status::Idle:
  case ObserverSkyRenderer::Status::Building:
    break;
  }
  return SceneCaptureState::Pending;
}

void ObserverSkyRenderer::shutdown() {
  stop_.request_stop();
  if (pending_.valid()) {
    pending_.wait();
    pending_ = {};
  }
  pendingHash_.reset();
  wantedHash_.reset();
  releaseSky();
  deleteTexture(blackbodyTexture_);
  status_ = Status::Idle;
  message_.clear();
}

} // namespace blackhole
