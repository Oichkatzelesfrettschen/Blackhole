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
#include <fstream>
#include <future>
#include <numbers>
#include <optional>
#include <sstream>
#include <string>
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

GLuint uploadFloatTexture(int width, int height, const float *pixels, GLenum filter,
                          bool twoChannels = false) {
  GLuint texture = 0;
  glGenTextures(1, &texture);
  glBindTexture(GL_TEXTURE_2D, texture);
  glTexImage2D(GL_TEXTURE_2D, 0, twoChannels ? GL_RG32F : GL_RGBA32F, width, height, 0,
               twoChannels ? GL_RG : GL_RGBA, GL_FLOAT, pixels);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, static_cast<GLint>(filter));
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, static_cast<GLint>(filter));
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, static_cast<GLint>(GL_CLAMP_TO_EDGE));
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, static_cast<GLint>(GL_CLAMP_TO_EDGE));
  glBindTexture(GL_TEXTURE_2D, 0);
  return texture;
}

void deleteTexture(GLuint &texture) {
  if (texture != 0) {
    glDeleteTextures(1, &texture);
    texture = 0;
  }
}

/** @brief Loads the cached bundle for `key`, or builds and caches it. */
std::optional<sky::ObserverSkyLut> loadOrBuild(const sky::ObserverKey &key,
                                               const sky::LutDimensions &dimensions,
                                               const std::filesystem::path &cacheDirectory) {
  const sky::TraceSettings settings;
  const std::uint64_t bundleHash = sky::lutHash(key, dimensions, settings);
  const std::filesystem::path file = cacheDirectory / (sky::lutStem(bundleHash) + ".bin");
  std::optional<sky::ObserverSkyLut> cached = sky::readObserverSkyLut(file, bundleHash);
  if (cached.has_value()) {
    return cached;
  }
  sky::ObserverSkyLut lut = sky::buildObserverSkyLut(key, dimensions, settings);
  // A read-only asset tree only costs the cache; the bundle is still usable.
  (void)sky::writeObserverSkyLut(lut, cacheDirectory);
  return lut;
}

} // namespace

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

void ObserverSkyRenderer::request(const sky::ObserverKey &key, const sky::LutDimensions &dimensions,
                                  const std::filesystem::path &cacheDirectory) {
  const std::uint64_t hash = sky::lutHash(key, dimensions, sky::TraceSettings{});
  if (residentHash_ == hash || pendingHash_ == hash) {
    return;
  }
  if (pending_.valid()) {
    return; // One build at a time; the newest request starts when it lands.
  }
  pendingHash_ = hash;
  status_ = Status::Building;
  message_ = "tracing the observer's sky (about 20 s on first use; cached afterwards)";
  pending_ = std::async(std::launch::async, loadOrBuild, key, dimensions, cacheDirectory);
}

void ObserverSkyRenderer::poll(const std::filesystem::path &blackbodyCsv, double cmbTemperature) {
  if (!pending_.valid() ||
      pending_.wait_for(std::chrono::seconds(0)) != std::future_status::ready) {
    return;
  }
  std::optional<sky::ObserverSkyLut> built;
  try {
    built = pending_.get();
  } catch (const std::exception &error) {
    message_ = std::string("observer sky build failed: ") + error.what();
  }
  const std::optional<std::uint64_t> finishedHash = pendingHash_;
  pendingHash_.reset();
  if (!blackbody_) {
    blackbody_ = loadBlackbodyTable(blackbodyCsv);
  }
  if (!built || !blackbody_) {
    status_ = Status::Failed;
    if (!blackbody_) {
      message_ = "missing " + blackbodyCsv.string() +
                 " (run $PYTHON scripts/generate_blackbody_cie_lut.py)";
    }
    return;
  }
  upload(*built, *blackbody_, cmbTemperature);
  lut_ = std::move(built);
  residentHash_ = finishedHash;
  status_ = Status::Ready;
  message_.clear();
}

void ObserverSkyRenderer::upload(const sky::ObserverSkyLut &lut, const BlackbodyTable &table,
                                 double cmbTemperature) {
  deleteTexture(skyTexture_);
  deleteTexture(skySpanTexture_);
  deleteTexture(tileTexture_);
  deleteTexture(tileSpanTexture_);
  deleteTexture(tileFluxTexture_);
  skySpanTexture_ =
      uploadFloatTexture(static_cast<int>(lut.sky.width), static_cast<int>(lut.sky.height),
                         lut.sky.sourceSpan.data(), GL_NEAREST, true);
  tileSpanTexture_ = uploadFloatTexture(static_cast<int>(lut.tileImage.width),
                                        static_cast<int>(lut.tileImage.height),
                                        lut.tileImage.sourceSpan.data(), GL_NEAREST, true);
  skyTexture_ =
      uploadFloatTexture(static_cast<int>(lut.sky.width), static_cast<int>(lut.sky.height),
                         lut.sky.rgba.data(), GL_NEAREST);
  tileTexture_ = uploadFloatTexture(static_cast<int>(lut.tileImage.width),
                                    static_cast<int>(lut.tileImage.height),
                                    lut.tileImage.rgba.data(), GL_NEAREST);
  const auto flatten = [](const std::vector<std::array<float, 4>> &rows) {
    std::vector<float> flat;
    flat.reserve(rows.size() * 4);
    std::ranges::for_each(rows, [&flat](const std::array<float, 4> &row) {
      flat.insert(flat.end(), row.begin(), row.end());
    });
    return flat;
  };
  const std::vector<float> flux = flatten(cumulativeCmbRingFlux(lut, table, cmbTemperature));
  tileFluxTexture_ =
      uploadFloatTexture(static_cast<int>(flux.size() / 4), 1, flux.data(), GL_NEAREST);
  if (blackbodyTexture_ == 0) {
    const std::vector<float> rows = flatten(table.rows);
    blackbodyTexture_ =
        uploadFloatTexture(static_cast<int>(rows.size() / 4), 1, rows.data(), GL_LINEAR);
  }
}

void renderObserverSkyScene(RenderState &rs, const glm::mat3 &cameraBasis, float deltaSeconds) {
  RenderState::ObserverViewGroup &view = rs.observerView;
  const ko::OrbitSense sense =
      view.kind == ObserverKind::Retrograde ? ko::OrbitSense::Retrograde : ko::OrbitSense::Prograde;
  view.x = view.atIsco ? ko::iscoOffset(view.epsilon, sense) : view.x;
  const std::optional<sky::ObserverKey> key = observerKeyFor(view.epsilon, view.x, view.kind);
  const std::filesystem::path lutDirectory = platform::resourceRoot() / "assets" / "luts";
  if (key) {
    view.renderer.request(*key, sky::LutDimensions{}, lutDirectory);
  }
  view.renderer.poll(lutDirectory / "blackbody_cie_lut.csv", view.cmbTemperature);
  const std::optional<sky::ObserverSkyLut> &lut = view.renderer.lut();

  // The clock follows the resident sky, so time and image always agree.
  const ObserverClockModel clock =
      lut ? observerClockModel(lut->key, view.massSolar) : ObserverClockModel{};
  const double properStep =
      view.paused ? 0.0 : static_cast<double>(deltaSeconds) * view.skyTimeScale;
  view.properSeconds += properStep;
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
  // Four sub-frame samples once the sky moves more than 0.01 rad per frame.
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
  // (GL_LINEAR), so the pass adds the mip chain once and switches the
  // minification filter to trilinear for its own draw.
  const GLuint galaxy = rs.background.galaxy;
  if (galaxy != 0) {
    glBindTexture(GL_TEXTURE_CUBE_MAP, galaxy);
    if (view.galaxyMipmapped != galaxy) {
      glGenerateMipmap(GL_TEXTURE_CUBE_MAP);
      view.galaxyMipmapped = galaxy;
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

void ObserverSkyRenderer::shutdown() {
  if (pending_.valid()) {
    pending_.wait();
  }
  deleteTexture(skyTexture_);
  deleteTexture(skySpanTexture_);
  deleteTexture(tileTexture_);
  deleteTexture(tileSpanTexture_);
  deleteTexture(tileFluxTexture_);
  deleteTexture(blackbodyTexture_);
  lut_.reset();
  residentHash_.reset();
  status_ = Status::Idle;
}

} // namespace blackhole
