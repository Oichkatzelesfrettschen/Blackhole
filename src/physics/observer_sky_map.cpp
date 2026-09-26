/**
 * @file observer_sky_map.cpp
 * @brief Backward null-geodesic tracing from an equatorial Kerr observer's
 *        local sky, in spin-deficit form (see observer_sky_map.h).
 */

#include "observer_sky_map.h"

#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstddef>
#include <numbers>
#include <numeric>
#include <optional>
#include <thread>
#include <utility>
#include <vector>

#include "kerr_observer.h"
#include "safe_limits.h"

namespace physics::observer_sky {

namespace {

using kerr_observer::Vec4;

constexpr double K_PI = std::numbers::pi;

/// Floor on sin^2(theta) in the polar terms; only a ray with lambda = 0
/// exactly reaches the pole, and there both terms vanish anyway.
constexpr double K_MIN_SIN2 = 1.0e-300;

/** @brief Constants of the backward ray, normalized to E = 1. */
struct RayConstants {
  double spin = 0.0;
  double spin2 = 0.0;
  double h = 0.0;      ///< Outer horizon offset sqrt(1 - a^2).
  double lambda = 0.0; ///< L / E.
  double lambda2 = 0.0;
  double q = 0.0;  ///< eta + (lambda - a)^2, the coefficient of Delta in R.
  double k0 = 0.0; ///< 1 + a^2 - a lambda, so P(x) = x (2 + x) + k0.
};

/** @brief Mino-time state: vr = dr/dsigma, vtheta = dtheta/dsigma along the
 *         photon's forward direction; the trace steps sigma downward. */
struct RayState {
  double x = 0.0;
  double theta = 0.0;
  double vr = 0.0;
  double vtheta = 0.0;
  double phi = 0.0;
};

struct RayRates {
  double dx = 0.0;
  double dtheta = 0.0;
  double dvr = 0.0;
  double dvtheta = 0.0;
  double dphi = 0.0;
};

/**
 * @brief Right-hand side of the second-order Mino system in x:
 *   x'' = R'(r)/2 = 2 r P - x Q,  theta'' = Theta'(theta)/2 = -a^2 cos sin + lambda^2 cos / sin^3,
 *   phi' = a P / Delta - a + lambda / sin^2,
 * with Delta = (x - h)(x + h) so that no O(1) term cancels near the horizon.
 */
RayRates rayRates(const RayConstants &c, const RayState &s) {
  const double r = 1.0 + s.x;
  const double p = (s.x * (2.0 + s.x)) + c.k0;
  const double delta = (s.x - c.h) * (s.x + c.h);
  const double sinT = std::sin(s.theta);
  const double cosT = std::cos(s.theta);
  const double sin2 = std::fmax(sinT * sinT, K_MIN_SIN2);
  RayRates rates;
  rates.dx = s.vr;
  rates.dtheta = s.vtheta;
  rates.dvr = (2.0 * r * p) - (s.x * c.q);
  rates.dvtheta = (-c.spin2 * cosT * sinT) + (c.lambda2 * cosT / (sin2 * std::sqrt(sin2)));
  rates.dphi = (c.spin * p / delta) - c.spin + (c.lambda / sin2);
  return rates;
}

RayState advance(const RayState &s, const RayRates &k, double step) {
  return RayState{.x = s.x + (step * k.dx),
                  .theta = s.theta + (step * k.dtheta),
                  .vr = s.vr + (step * k.dvr),
                  .vtheta = s.vtheta + (step * k.dvtheta),
                  .phi = s.phi + (step * k.dphi)};
}

/** @brief One classical RK4 step of size `step` (negative: backward). */
RayState rk4Step(const RayConstants &c, const RayState &s, double step) {
  const RayRates k1 = rayRates(c, s);
  const RayRates k2 = rayRates(c, advance(s, k1, 0.5 * step));
  const RayRates k3 = rayRates(c, advance(s, k2, 0.5 * step));
  const RayRates k4 = rayRates(c, advance(s, k3, step));
  const auto combine = [step](double y, double a, double b, double d, double e) {
    return y + (step / 6.0 * (a + (2.0 * b) + (2.0 * d) + e));
  };
  return RayState{.x = combine(s.x, k1.dx, k2.dx, k3.dx, k4.dx),
                  .theta = combine(s.theta, k1.dtheta, k2.dtheta, k3.dtheta, k4.dtheta),
                  .vr = combine(s.vr, k1.dvr, k2.dvr, k3.dvr, k4.dvr),
                  .vtheta = combine(s.vtheta, k1.dvtheta, k2.dvtheta, k3.dvtheta, k4.dvtheta),
                  .phi = combine(s.phi, k1.dphi, k2.dphi, k3.dphi, k4.dphi)};
}

bool stateFinite(const RayState &s) {
  return physics::safeIsfinite(s.x) && physics::safeIsfinite(s.theta) &&
         physics::safeIsfinite(s.vr) && physics::safeIsfinite(s.vtheta) &&
         physics::safeIsfinite(s.phi);
}

/**
 * @brief Step size: the Mino interval over which the ray covers stepFraction
 *        of its radial scale (x - h) and of a radian in theta. Each rate adds
 *        the time to cross the scale from rest under the current
 *        acceleration, so turning points (v = 0) keep a finite step.
 */
double minoStep(const RayConstants &c, const RayState &s, const RayRates &k, double stepFraction) {
  const double radialScale = s.x - c.h;
  const double radialRate =
      (std::fabs(s.vr) / radialScale) + std::sqrt(std::fabs(k.dvr) / (2.0 * radialScale));
  const double polarRate = std::fabs(s.vtheta) + std::sqrt(std::fabs(k.dvtheta));
  return stepFraction / (radialRate + polarRate);
}

Vec3 scale(const Vec3 &v, double factor) {
  return {v.at(0) * factor, v.at(1) * factor, v.at(2) * factor};
}

Vec3 add(const Vec3 &a, const Vec3 &b) {
  return {a.at(0) + b.at(0), a.at(1) + b.at(1), a.at(2) + b.at(2)};
}

double dot(const Vec3 &a, const Vec3 &b) {
  return (a.at(0) * b.at(0)) + (a.at(1) * b.at(1)) + (a.at(2) * b.at(2));
}

Vec3 normalized(const Vec3 &v) {
  return scale(v, 1.0 / std::sqrt(dot(v, v)));
}

/**
 * @brief Source direction at infinity from the escape state. Beyond the
 *        escape radius spacetime is flat to O(M/r) and the photon moves on a
 *        straight line, so its momentum there -- (vr, r vtheta,
 *        r sin(theta) phi') on the (r, theta, phi) unit vectors, all scaled by
 *        Sigma -- is its direction at infinity; the source lies opposite.
 */
Vec3 sourceDirection(const RayConstants &c, const RayState &s) {
  const RayRates k = rayRates(c, s);
  const double r = 1.0 + s.x;
  const double sinT = std::sin(s.theta);
  const double cosT = std::cos(s.theta);
  const double sinP = std::sin(s.phi);
  const double cosP = std::cos(s.phi);
  const Vec3 radial{sinT * cosP, sinT * sinP, cosT};
  const Vec3 polar{cosT * cosP, cosT * sinP, -sinT};
  const Vec3 azimuthal{-sinP, cosP, 0.0};
  const Vec3 momentum = add(add(scale(radial, s.vr), scale(polar, r * s.vtheta)),
                            scale(azimuthal, r * sinT * k.dphi));
  return scale(normalized(momentum), -1.0);
}

/** @brief Photon four-momentum in ZAMO components for unit observed energy,
 *         received from `look` (propagating along -look). */
Vec4 receivedZamoMomentum(const Tetrad &tetrad, const Vec3 &look) {
  Vec4 zamo{};
  for (std::size_t component = 0; component < 4; ++component) {
    zamo.at(component) = tetrad.lorentz.at(0).at(component) -
                         (look.at(0) * tetrad.lorentz.at(1).at(component)) -
                         (look.at(1) * tetrad.lorentz.at(2).at(component)) -
                         (look.at(2) * tetrad.lorentz.at(3).at(component));
  }
  return zamo;
}

template <typename Body> void parallelRows(std::size_t rows, unsigned threads, const Body &body) {
  const unsigned hardware = std::max(1U, std::thread::hardware_concurrency());
  const unsigned count =
      static_cast<unsigned>(std::min<std::size_t>(threads == 0 ? hardware : threads, rows));
  std::atomic<std::size_t> next{0};
  const auto worker = [&next, rows, &body]() {
    for (std::size_t row = next.fetch_add(1); row < rows; row = next.fetch_add(1)) {
      body(row);
    }
  };
  std::vector<std::jthread> pool;
  pool.reserve(count);
  for (unsigned index = 0; index < count; ++index) {
    pool.emplace_back(worker);
  }
}

void storeRay(std::vector<float> &rgba, std::size_t texel, const SkyRay &ray) {
  const std::size_t base = texel * 4;
  if (ray.fate == RayFate::Escaped) {
    rgba.at(base + 0) = static_cast<float>(ray.sourceDirection.at(0));
    rgba.at(base + 1) = static_cast<float>(ray.sourceDirection.at(1));
    rgba.at(base + 2) = static_cast<float>(ray.sourceDirection.at(2));
    rgba.at(base + 3) = static_cast<float>(std::log(ray.g));
  } else {
    rgba.at(base + 0) = 0.0F;
    rgba.at(base + 1) = 0.0F;
    rgba.at(base + 2) = 0.0F;
    rgba.at(base + 3) = ray.fate == RayFate::Trapped ? K_TRAPPED_LOG_G : K_CAPTURED_LOG_G;
  }
}

/** @brief Traces `look` and reports whether photonConstants' static
 *         connectivity agrees with the integrated fate. */
std::pair<SkyRay, bool> traceAndCompare(const Tetrad &tetrad, const Vec3 &look,
                                        const TraceSettings &settings) {
  const SkyRay ray = traceSkyRay(tetrad, look, settings);
  const kerr_observer::PhotonConstants constants =
      kerr_observer::photonConstants(tetrad, scale(look, -1.0));
  const bool escaped = ray.fate == RayFate::Escaped;
  return {ray, escaped != constants.fromInfinity};
}

template <typename LookAt>
SkyImage traceImage(const ObserverKey &key, std::size_t width, std::size_t height,
                    const TraceSettings &settings, unsigned threads, const LookAt &lookAt) {
  const Tetrad tetrad = observerTetrad(key);
  SkyImage image;
  image.width = width;
  image.height = height;
  image.rgba.assign(width * height * 4, 0.0F);
  std::vector<std::size_t> disagreements(height, 0);
  parallelRows(height, threads, [&](std::size_t row) {
    for (std::size_t column = 0; column < width; ++column) {
      const auto [ray, disagrees] = traceAndCompare(tetrad, lookAt(column, row), settings);
      storeRay(image.rgba, (row * width) + column, ray);
      disagreements.at(row) += disagrees ? 1U : 0U;
    }
  });
  image.connectivityDisagreements =
      std::accumulate(disagreements.begin(), disagreements.end(), std::size_t{0});
  return image;
}

double texelLogG(const SkyImage &image, std::size_t texel) {
  return static_cast<double>(image.rgba.at((texel * 4) + 3));
}

bool texelShowsSky(const SkyImage &image, std::size_t texel) {
  return image.rgba.at((texel * 4) + 3) > K_NO_SKY_THRESHOLD;
}

bool texelTrapped(const SkyImage &image, std::size_t texel) {
  return image.rgba.at((texel * 4) + 3) < 0.5F * (K_CAPTURED_LOG_G + K_TRAPPED_LOG_G);
}

} // namespace

std::optional<ObserverKey> orbitingObserver(double epsilon, double x,
                                            kerr_observer::OrbitSense sense) {
  const kerr_observer::CircularOrbit orbit = kerr_observer::circularOrbit(epsilon, x, sense);
  if (!orbit.exists) {
    return std::nullopt;
  }
  return ObserverKey{.epsilon = epsilon, .x = x, .velocity = orbit.zamoVelocity};
}

Tetrad observerTetrad(const ObserverKey &key) {
  return kerr_observer::boostedTetrad(kerr_observer::zamoTetrad(key.epsilon, key.x),
                                      Vec3{0.0, 0.0, key.velocity});
}

Vec3 lookDirection(double longitude, double latitude) {
  const double cosB = std::cos(latitude);
  return {-cosB * std::cos(longitude), -std::sin(latitude), cosB * std::sin(longitude)};
}

SkyAngles lookAngles(const Vec3 &look) {
  return SkyAngles{.longitude = std::atan2(look.at(2), -look.at(0)),
                   .latitude = std::atan2(-look.at(1), std::hypot(look.at(0), look.at(2)))};
}

SkyRay traceSkyRay(const Tetrad &tetrad, const Vec3 &look, const TraceSettings &settings) {
  SkyRay ray;
  const kerr_observer::EquatorialFrame &frame = tetrad.frame;
  const Vec4 zamo = receivedZamoMomentum(tetrad, look);
  const double angularMomentum = frame.varpi * zamo.at(3);
  const double energy = (frame.alpha * zamo.at(0)) + (frame.omega * angularMomentum);
  if (!(energy > 0.0)) {
    // E <= 0 photons exist only inside the ergoregion and connect to infinity
    // in neither direction.
    ray.fate = RayFate::Captured;
    return ray;
  }
  const double spin = frame.spin;
  const double r = frame.r;
  const double x = frame.x;
  const double h2 = frame.epsilon * (2.0 - frame.epsilon);
  const double h = std::sqrt(h2);
  // E k0 = E (1 + a^2) - a L = alpha P^t (1 + a^2) - a L D1 / A with
  // D1 = A - 2 r (1 + a^2) = r (x (x^2 + 3x + 4) - h^2 r): the O(1) parts of
  // omega (1 + a^2) and a cancel analytically, not in floating point.
  const double d1 = r * ((x * ((x * x) + (3.0 * x) + 4.0)) - (h2 * r));
  const double energyK0 = (frame.alpha * zamo.at(0) * (1.0 + (spin * spin))) -
                          (spin * angularMomentum * d1 / frame.bigA);
  RayConstants constants;
  constants.spin = spin;
  constants.spin2 = spin * spin;
  constants.h = h;
  constants.lambda = angularMomentum / energy;
  constants.lambda2 = constants.lambda * constants.lambda;
  const double pTheta = r * zamo.at(2) / energy;
  const double eta = pTheta * pTheta;
  constants.q = eta + ((constants.lambda - spin) * (constants.lambda - spin));
  constants.k0 = energyK0 / energy;
  ray.g = 1.0 / energy;

  RayState state{.x = x,
                 .theta = 0.5 * K_PI,
                 .vr = r * frame.sqrtDelta * zamo.at(1) / energy,
                 .vtheta = pTheta,
                 .phi = 0.0};
  const double captureOffset = std::fmax(settings.captureFraction * h, settings.captureFloor);
  for (int step = 0;; ++step) {
    ray.steps = step;
    if (!stateFinite(state) || !(state.x > h)) {
      ray.fate = state.x > h ? RayFate::Trapped : RayFate::Captured;
      return ray;
    }
    // Backward in time the ray moves along -vr.
    if (state.vr < 0.0 && 1.0 + state.x > settings.escapeRadius) {
      ray.fate = RayFate::Escaped;
      ray.sourceDirection = sourceDirection(constants, state);
      ray.sweptPhi = state.phi;
      return ray;
    }
    if (state.vr > 0.0 && state.x - h < captureOffset) {
      ray.fate = RayFate::Captured;
      return ray;
    }
    if (step >= settings.maxSteps) {
      ray.fate = RayFate::Trapped;
      return ray;
    }
    const RayRates rates = rayRates(constants, state);
    state = rk4Step(constants, state, -minoStep(constants, state, rates, settings.stepFraction));
  }
}

Vec3 equirectLook(std::size_t column, std::size_t row, std::size_t width, std::size_t height) {
  const double longitude =
      -K_PI + (2.0 * K_PI * (static_cast<double>(column) + 0.5) / static_cast<double>(width));
  const double latitude =
      (0.5 * K_PI) - (K_PI * (static_cast<double>(row) + 0.5) / static_cast<double>(height));
  return lookDirection(longitude, latitude);
}

double equirectPixelSolidAngle(std::size_t row, std::size_t width, std::size_t height) {
  const double pitch = K_PI / static_cast<double>(height);
  const double top = (0.5 * K_PI) - (pitch * static_cast<double>(row));
  const double bottom = top - pitch;
  return (std::sin(top) - std::sin(bottom)) * 2.0 * K_PI / static_cast<double>(width);
}

LogPolarTile tileAround(const Vec3 &center, double rhoMin, double rhoMax, std::size_t radialCount,
                        std::size_t azimuthCount) {
  const SkyAngles angles = lookAngles(center);
  const double sinL = std::sin(angles.longitude);
  const double cosL = std::cos(angles.longitude);
  const double sinB = std::sin(angles.latitude);
  const double cosB = std::cos(angles.latitude);
  LogPolarTile tile;
  tile.center = normalized(center);
  tile.axisEast = Vec3{sinL, 0.0, cosL};
  tile.axisNorth = Vec3{sinB * cosL, -cosB, -sinB * sinL};
  tile.rhoMin = rhoMin;
  tile.rhoMax = rhoMax;
  tile.radialCount = radialCount;
  tile.azimuthCount = azimuthCount;
  return tile;
}

Vec3 tileLook(const LogPolarTile &tile, std::size_t radial, std::size_t azimuthal) {
  const double logSpan = std::log(tile.rhoMax / tile.rhoMin);
  const double rho = tile.rhoMin * std::exp(logSpan * (static_cast<double>(radial) + 0.5) /
                                            static_cast<double>(tile.radialCount));
  const double psi =
      2.0 * K_PI * (static_cast<double>(azimuthal) + 0.5) / static_cast<double>(tile.azimuthCount);
  const Vec3 tangent =
      add(scale(tile.axisEast, std::cos(psi)), scale(tile.axisNorth, std::sin(psi)));
  return normalized(add(scale(tile.center, std::cos(rho)), scale(tangent, std::sin(rho))));
}

double tileTexelSolidAngle(const LogPolarTile &tile, std::size_t radial) {
  const double logSpan = std::log(tile.rhoMax / tile.rhoMin);
  const auto count = static_cast<double>(tile.radialCount);
  const double inner = tile.rhoMin * std::exp(logSpan * static_cast<double>(radial) / count);
  const double outer =
      tile.rhoMin * std::exp(logSpan * (static_cast<double>(radial) + 1.0) / count);
  // cos(inner) - cos(outer) without cancellation at arcsecond radii.
  const double ring = 2.0 * std::sin(0.5 * (outer + inner)) * std::sin(0.5 * (outer - inner));
  return ring * 2.0 * K_PI / static_cast<double>(tile.azimuthCount);
}

SkyImage traceEquirect(const ObserverKey &key, std::size_t width, std::size_t height,
                       const TraceSettings &settings, unsigned threads) {
  return traceImage(key, width, height, settings, threads,
                    [width, height](std::size_t column, std::size_t row) {
                      return equirectLook(column, row, width, height);
                    });
}

SkyImage traceTile(const ObserverKey &key, const LogPolarTile &tile, const TraceSettings &settings,
                   unsigned threads) {
  return traceImage(
      key, tile.azimuthCount, tile.radialCount, settings, threads,
      [&tile](std::size_t column, std::size_t row) { return tileLook(tile, row, column); });
}

Vec3 zamoZenithLook(double velocity) {
  return lookDirection(K_PI - std::asin(velocity), 0.0);
}

PeakResult findPeakBlueshift(const Tetrad &tetrad, const std::vector<Vec3> &seeds,
                             const PeakSearch &search, const TraceSettings &settings) {
  PeakResult best;
  const auto consider = [&best, &tetrad, &settings](const Vec3 &look) {
    const SkyRay ray = traceSkyRay(tetrad, look, settings);
    if (ray.fate == RayFate::Escaped && ray.g > best.g) {
      best = PeakResult{.look = look, .g = ray.g};
    }
  };
  std::ranges::for_each(seeds, consider);
  if (!(best.g > 0.0)) {
    return best;
  }
  const std::size_t points = std::max<std::size_t>(search.gridPoints, 3);
  const double half = 0.5 * static_cast<double>(points - 1);
  // Levels are counted in integers; the half-width follows geometrically.
  const auto levels =
      static_cast<int>(std::floor(std::log(search.initialHalfWidth / search.finestHalfWidth) /
                                  std::log(search.shrink))) +
      1;
  for (int level = 0; level < levels; ++level) {
    const double width = search.initialHalfWidth * std::pow(search.shrink, -level);
    const LogPolarTile frame = tileAround(best.look, 1.0, 2.0, 1, 1);
    for (std::size_t i = 0; i < points; ++i) {
      for (std::size_t j = 0; j < points; ++j) {
        const double east = width * (static_cast<double>(i) - half) / half;
        const double north = width * (static_cast<double>(j) - half) / half;
        consider(normalized(
            add(frame.center, add(scale(frame.axisEast, east), scale(frame.axisNorth, north)))));
      }
    }
  }
  return best;
}

SkyStatistics equirectStatistics(const SkyImage &image) {
  SkyStatistics stats;
  double total = 0.0;
  double noSky = 0.0;
  double trapped = 0.0;
  double gMin = 0.0;
  double gMax = 0.0;
  bool any = false;
  for (std::size_t row = 0; row < image.height; ++row) {
    const double solidAngle = equirectPixelSolidAngle(row, image.width, image.height);
    for (std::size_t column = 0; column < image.width; ++column) {
      const std::size_t texel = (row * image.width) + column;
      total += solidAngle;
      if (!texelShowsSky(image, texel)) {
        noSky += solidAngle;
        trapped += texelTrapped(image, texel) ? solidAngle : 0.0;
        continue;
      }
      const double g = std::exp(texelLogG(image, texel));
      gMin = any ? std::fmin(gMin, g) : g;
      gMax = any ? std::fmax(gMax, g) : g;
      any = true;
    }
  }
  stats.capturedFraction = noSky / total;
  stats.trappedFraction = trapped / total;
  stats.gMin = gMin;
  stats.gMax = gMax;
  return stats;
}

EnergyRegion tileEnergyRegion(const SkyImage &image, const LogPolarTile &tile, double fraction) {
  struct Texel {
    double weight = 0.0; ///< g^4 dOmega.
    double g = 0.0;
    double solidAngle = 0.0;
    std::size_t radial = 0;
    std::size_t azimuthal = 0;
  };
  std::vector<Texel> texels;
  texels.reserve(image.width * image.height);
  for (std::size_t radial = 0; radial < image.height; ++radial) {
    const double solidAngle = tileTexelSolidAngle(tile, radial);
    for (std::size_t azimuthal = 0; azimuthal < image.width; ++azimuthal) {
      const std::size_t texel = (radial * image.width) + azimuthal;
      if (!texelShowsSky(image, texel)) {
        continue;
      }
      const double g = std::exp(texelLogG(image, texel));
      const double g2 = g * g;
      texels.push_back(Texel{.weight = g2 * g2 * solidAngle,
                             .g = g,
                             .solidAngle = solidAngle,
                             .radial = radial,
                             .azimuthal = azimuthal});
    }
  }
  EnergyRegion region;
  region.tileEnergy = std::accumulate(texels.begin(), texels.end(), 0.0,
                                      [](double sum, const Texel &t) { return sum + t.weight; });
  std::ranges::sort(texels, [](const Texel &a, const Texel &b) { return a.g > b.g; });
  const SkyAngles centerAngles = lookAngles(tile.center);
  double accumulated = 0.0;
  double lonMin = 0.0;
  double lonMax = 0.0;
  double latMin = 0.0;
  double latMax = 0.0;
  bool first = true;
  for (const Texel &texel : texels) {
    if (accumulated >= fraction * region.tileEnergy) {
      break;
    }
    accumulated += texel.weight;
    region.solidAngle += texel.solidAngle;
    region.thresholdG = texel.g;
    const SkyAngles angles = lookAngles(tileLook(tile, texel.radial, texel.azimuthal));
    // Longitude offsets wrap through +-pi only for a tile centered behind the
    // observer; remainder keeps them continuous.
    const double lon = std::remainder(angles.longitude - centerAngles.longitude, 2.0 * K_PI);
    const double lat = angles.latitude - centerAngles.latitude;
    lonMin = first ? lon : std::fmin(lonMin, lon);
    lonMax = first ? lon : std::fmax(lonMax, lon);
    latMin = first ? lat : std::fmin(latMin, lat);
    latMax = first ? lat : std::fmax(latMax, lat);
    first = false;
  }
  region.longitudeSpan = lonMax - lonMin;
  region.latitudeSpan = latMax - latMin;
  return region;
}

} // namespace physics::observer_sky
