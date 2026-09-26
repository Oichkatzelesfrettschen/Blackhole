/**
 * @file observer_sky_lut.cpp
 * @brief Build, hash, serialize, and read the observer-sky lookup bundle.
 */

#include "observer_sky_lut.h"

#include <algorithm>
#include <array>
#include <bit>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <ios>
#include <iterator>
#include <numbers>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

#include "observer_sky_map.h"

namespace physics::observer_sky {

namespace {

constexpr std::array<char, 8> K_MAGIC{'B', 'H', 'O', 'S', 'K', 'Y', '0', '1'};

/** @brief Little-endian byte sink with FNV-1a folding of everything written. */
class ByteWriter {
public:
  void u64(std::uint64_t value) {
    for (int shift = 0; shift < 64; shift += 8) {
      byte(static_cast<std::uint8_t>((value >> shift) & 0xFFU));
    }
  }
  void u32(std::uint32_t value) {
    for (int shift = 0; shift < 32; shift += 8) {
      byte(static_cast<std::uint8_t>((value >> shift) & 0xFFU));
    }
  }
  void f64(double value) { u64(std::bit_cast<std::uint64_t>(value)); }
  void f32(float value) { u32(std::bit_cast<std::uint32_t>(value)); }
  void size(std::size_t value) { u64(static_cast<std::uint64_t>(value)); }
  void byte(std::uint8_t value) {
    bytes_.push_back(value);
    hash_ = (hash_ ^ value) * 0x100000001b3ULL;
  }
  [[nodiscard]] const std::vector<std::uint8_t> &bytes() const { return bytes_; }
  [[nodiscard]] std::uint64_t hash() const { return hash_; }

private:
  std::vector<std::uint8_t> bytes_;
  std::uint64_t hash_ = 0xcbf29ce484222325ULL;
};

class ByteReader {
public:
  explicit ByteReader(std::span<const std::uint8_t> bytes) : bytes_(bytes) {}
  bool u64(std::uint64_t &value) {
    if (offset_ + 8 > bytes_.size()) {
      return false;
    }
    value = 0;
    for (int shift = 0; shift < 64; shift += 8) {
      value |= static_cast<std::uint64_t>(bytes_[offset_++]) << shift;
    }
    return true;
  }
  bool u32(std::uint32_t &value) {
    if (offset_ + 4 > bytes_.size()) {
      return false;
    }
    value = 0;
    for (int shift = 0; shift < 32; shift += 8) {
      value |= static_cast<std::uint32_t>(bytes_[offset_++]) << shift;
    }
    return true;
  }
  bool f64(double &value) {
    std::uint64_t bits = 0;
    const bool ok = u64(bits);
    value = std::bit_cast<double>(bits);
    return ok;
  }
  bool f32(float &value) {
    std::uint32_t bits = 0;
    const bool ok = u32(bits);
    value = std::bit_cast<float>(bits);
    return ok;
  }
  bool size(std::size_t &value) {
    std::uint64_t raw = 0;
    const bool ok = u64(raw);
    value = static_cast<std::size_t>(raw);
    return ok;
  }
  bool magic() {
    return std::ranges::all_of(K_MAGIC, [this](char expected) {
      if (offset_ >= bytes_.size()) {
        return false;
      }
      const std::uint8_t actual = bytes_[offset_];
      ++offset_;
      return actual == static_cast<std::uint8_t>(expected);
    });
  }
  [[nodiscard]] bool exhausted() const { return offset_ == bytes_.size(); }

private:
  std::span<const std::uint8_t> bytes_;
  std::size_t offset_ = 0;
};

/** @brief The hashed inputs, in one fixed order for the hash and the file. */
void writeInputs(ByteWriter &out, const ObserverKey &key, const LutDimensions &dimensions,
                 const TraceSettings &settings) {
  out.u32(K_LUT_FORMAT_VERSION);
  out.f64(key.epsilon);
  out.f64(key.x);
  out.f64(key.velocity);
  out.size(dimensions.width);
  out.size(dimensions.height);
  out.size(dimensions.tileRadial);
  out.size(dimensions.tileAzimuth);
  out.f64(dimensions.tileRhoMin);
  out.f64(dimensions.tileRhoMax);
  out.f64(settings.stepFraction);
  out.f64(settings.escapeRadius);
  out.f64(settings.captureFraction);
  out.f64(settings.captureFloor);
  out.u32(static_cast<std::uint32_t>(settings.maxSteps));
}

bool readInputs(ByteReader &in, ObserverKey &key, LutDimensions &dimensions,
                TraceSettings &settings) {
  std::uint32_t version = 0;
  std::uint32_t maxSteps = 0;
  const bool ok = in.u32(version) && in.f64(key.epsilon) && in.f64(key.x) && in.f64(key.velocity) &&
                  in.size(dimensions.width) && in.size(dimensions.height) &&
                  in.size(dimensions.tileRadial) && in.size(dimensions.tileAzimuth) &&
                  in.f64(dimensions.tileRhoMin) && in.f64(dimensions.tileRhoMax) &&
                  in.f64(settings.stepFraction) && in.f64(settings.escapeRadius) &&
                  in.f64(settings.captureFraction) && in.f64(settings.captureFloor) &&
                  in.u32(maxSteps);
  settings.maxSteps = static_cast<int>(maxSteps);
  return ok && version == K_LUT_FORMAT_VERSION;
}

void writeVec3(ByteWriter &out, const Vec3 &v) {
  std::ranges::for_each(v, [&out](double component) { out.f64(component); });
}

bool readVec3(ByteReader &in, Vec3 &v) {
  return std::ranges::all_of(v, [&in](double &component) { return in.f64(component); });
}

/** @brief The floating-point statistics in declaration order; the file and
 *         the sidecar both walk this list. */
std::array<double *, 12> statisticsFields(LutStatistics &s) {
  return {&s.capturedFraction,
          &s.trappedFraction,
          &s.gMin,
          &s.gMax,
          &s.patch99LongitudeSpan,
          &s.patch99LatitudeSpan,
          &s.patch99SolidAngle,
          &s.patch99ThresholdG,
          &s.tileEnergy,
          &s.energyOutsideTile,
          &s.equivalentIsotropicG,
          &s.energyWeightedG};
}

constexpr std::array<const char *, 12> K_STATISTICS_NAMES{"capturedFraction",
                                                          "trappedFraction",
                                                          "gMin",
                                                          "gMax",
                                                          "patch99LongitudeSpan",
                                                          "patch99LatitudeSpan",
                                                          "patch99SolidAngle",
                                                          "patch99ThresholdG",
                                                          "tileEnergy",
                                                          "energyOutsideTile",
                                                          "equivalentIsotropicG",
                                                          "energyWeightedG"};

/** @brief g^4 and g^5 moments (times dOmega) of the escaping texels an
 *         include predicate accepts. */
struct EnergyMoments {
  double g4 = 0.0;
  double g5 = 0.0;
};

template <typename SolidAngle, typename Include>
EnergyMoments energyMoments(const SkyImage &image, const SolidAngle &solidAngle,
                            const Include &include) {
  EnergyMoments moments;
  for (std::size_t row = 0; row < image.height; ++row) {
    const double omega = solidAngle(row);
    for (std::size_t column = 0; column < image.width; ++column) {
      const float logG = image.rgba.at((((row * image.width) + column) * 4) + 3);
      if (!(logG > K_NO_SKY_THRESHOLD) || !include(column, row)) {
        continue;
      }
      const double g = std::exp(static_cast<double>(logG));
      const double g4 = g * g * g * g * omega;
      moments.g4 += g4;
      moments.g5 += g4 * g;
    }
  }
  return moments;
}

void writeImage(ByteWriter &out, const SkyImage &image) {
  out.size(image.width);
  out.size(image.height);
  out.u64(image.connectivityDisagreements);
  std::ranges::for_each(image.rgba, [&out](float value) { out.f32(value); });
  std::ranges::for_each(image.sourceSpan, [&out](float value) { out.f32(value); });
}

bool readImage(ByteReader &in, SkyImage &image) {
  std::uint64_t disagreements = 0;
  if (!in.size(image.width) || !in.size(image.height) || !in.u64(disagreements)) {
    return false;
  }
  image.connectivityDisagreements = static_cast<std::size_t>(disagreements);
  constexpr std::size_t maxTexels = std::size_t{1} << 26U;
  if (image.width * image.height > maxTexels) {
    return false;
  }
  image.rgba.assign(image.width * image.height * 4, 0.0F);
  image.sourceSpan.assign(image.width * image.height * 2, 0.0F);
  const auto read = [&in](float &value) { return in.f32(value); };
  return std::ranges::all_of(image.rgba, read) && std::ranges::all_of(image.sourceSpan, read);
}

std::vector<std::uint8_t> serialize(const ObserverSkyLut &lut) {
  ByteWriter out;
  std::ranges::for_each(K_MAGIC, [&out](char c) { out.byte(static_cast<std::uint8_t>(c)); });
  writeInputs(out, lut.key, lut.dimensions, lut.settings);
  writeVec3(out, lut.tile.center);
  writeVec3(out, lut.tile.axisEast);
  writeVec3(out, lut.tile.axisNorth);
  writeVec3(out, lut.peak.look);
  out.f64(lut.peak.g);
  LutStatistics statistics = lut.statistics;
  std::ranges::for_each(statisticsFields(statistics),
                        [&out](const double *field) { out.f64(*field); });
  out.u64(statistics.connectivityDisagreements);
  writeImage(out, lut.sky);
  writeImage(out, lut.tileImage);
  return out.bytes();
}

std::string formatDouble(double value) {
  std::array<char, 40> text{};
  (void)std::snprintf(text.data(), text.size(), "%.17g", value);
  return text.data();
}

} // namespace

std::uint64_t lutHash(const ObserverKey &key, const LutDimensions &dimensions,
                      const TraceSettings &settings) {
  ByteWriter writer;
  writeInputs(writer, key, dimensions, settings);
  return writer.hash();
}

std::string lutStem(std::uint64_t hash) {
  std::array<char, 17> hex{};
  (void)std::snprintf(hex.data(), hex.size(), "%016llx", static_cast<unsigned long long>(hash));
  return std::string("observer_sky_") + hex.data();
}

ObserverSkyLut buildObserverSkyLut(const ObserverKey &key, const LutDimensions &dimensions,
                                   const TraceSettings &settings, unsigned threads) {
  ObserverSkyLut lut;
  lut.key = key;
  lut.dimensions = dimensions;
  lut.settings = settings;
  lut.sky = traceEquirect(key, dimensions.width, dimensions.height, settings, threads);
  const SkyStatistics sky = equirectStatistics(lut.sky);

  // Seed the peak search with the brightest equirect pixel and with the
  // aberrated ZAMO zenith, where the distant universe converges near an
  // extremal horizon; the global map can miss an arcsecond patch entirely.
  std::size_t brightest = 0;
  float brightestLogG = K_NO_SKY_THRESHOLD;
  for (std::size_t texel = 0; texel < dimensions.width * dimensions.height; ++texel) {
    const float logG = lut.sky.rgba.at((texel * 4) + 3);
    if (logG > brightestLogG) {
      brightestLogG = logG;
      brightest = texel;
    }
  }
  const std::vector<Vec3> seeds{equirectLook(brightest % dimensions.width,
                                             brightest / dimensions.width, dimensions.width,
                                             dimensions.height),
                                zamoZenithLook(key.velocity)};
  PeakSearch search;
  search.initialHalfWidth = 4.0 * std::numbers::pi / static_cast<double>(dimensions.width);
  lut.peak = findPeakBlueshift(observerTetrad(key), seeds, search, settings);

  lut.tile = tileAround(lut.peak.look, dimensions.tileRhoMin, dimensions.tileRhoMax,
                        dimensions.tileRadial, dimensions.tileAzimuth);
  lut.tileImage = traceTile(key, lut.tile, settings, threads);
  const EnergyRegion region = tileEnergyRegion(lut.tileImage, lut.tile, 0.99);

  const LogPolarTile &tile = lut.tile;
  const double cosRhoMax = std::cos(tile.rhoMax);
  const EnergyMoments inside = energyMoments(
      lut.tileImage, [&tile](std::size_t radial) { return tileTexelSolidAngle(tile, radial); },
      [](std::size_t, std::size_t) { return true; });
  const EnergyMoments outside = energyMoments(
      lut.sky,
      [&dimensions](std::size_t row) {
        return equirectPixelSolidAngle(row, dimensions.width, dimensions.height);
      },
      [&dimensions, &tile, cosRhoMax](std::size_t column, std::size_t row) {
        const Vec3 look = equirectLook(column, row, dimensions.width, dimensions.height);
        const double cosine = (look.at(0) * tile.center.at(0)) + (look.at(1) * tile.center.at(1)) +
                              (look.at(2) * tile.center.at(2));
        return cosine <= cosRhoMax;
      });

  LutStatistics &stats = lut.statistics;
  stats.capturedFraction = sky.capturedFraction;
  stats.trappedFraction = sky.trappedFraction;
  stats.gMin = sky.gMin;
  stats.gMax = std::fmax(sky.gMax, lut.peak.g);
  stats.patch99LongitudeSpan = region.longitudeSpan;
  stats.patch99LatitudeSpan = region.latitudeSpan;
  stats.patch99SolidAngle = region.solidAngle;
  stats.patch99ThresholdG = region.thresholdG;
  stats.tileEnergy = inside.g4;
  stats.energyOutsideTile = outside.g4;
  const double total = inside.g4 + outside.g4;
  stats.equivalentIsotropicG = std::pow(total / (4.0 * std::numbers::pi), 0.25);
  stats.energyWeightedG = total > 0.0 ? (inside.g5 + outside.g5) / total : 0.0;
  stats.connectivityDisagreements =
      static_cast<std::uint64_t>(lut.sky.connectivityDisagreements) +
      static_cast<std::uint64_t>(lut.tileImage.connectivityDisagreements);
  return lut;
}

std::string lutSidecarJson(const ObserverSkyLut &lut) {
  constexpr char quote = '"';
  const auto quoted = [](std::string_view text) {
    return std::string(1, quote) + std::string(text) + quote;
  };
  const auto vec3 = [](const Vec3 &v) {
    return "[" + formatDouble(v.at(0)) + ", " + formatDouble(v.at(1)) + ", " +
           formatDouble(v.at(2)) + "]";
  };
  // Members of one object, each `"name": value`, joined by commas.
  using Members = std::vector<std::pair<std::string_view, std::string>>;
  const auto object = [&quoted](const Members &members) {
    std::string text = "{";
    for (std::size_t index = 0; index < members.size(); ++index) {
      text += (index == 0 ? "" : ", ") + quoted(members.at(index).first) + ": " +
              members.at(index).second;
    }
    return text + "}";
  };
  const auto count = [](std::size_t value) { return std::to_string(value); };
  LutStatistics statistics = lut.statistics;
  const auto fields = statisticsFields(statistics);
  Members statisticsMembers;
  for (std::size_t index = 0; index < fields.size(); ++index) {
    statisticsMembers.emplace_back(K_STATISTICS_NAMES.at(index), formatDouble(*fields.at(index)));
  }
  statisticsMembers.emplace_back("connectivityDisagreements",
                                 std::to_string(statistics.connectivityDisagreements));
  const Members top{
      {"format", quoted("observer_sky")},
      {"formatVersion", std::to_string(K_LUT_FORMAT_VERSION)},
      {"stem", quoted(lutStem(lutHash(lut.key, lut.dimensions, lut.settings)))},
      {"units", quoted("G = c = M = 1; angles in radians")},
      {"key", object({{"epsilon", formatDouble(lut.key.epsilon)},
                      {"x", formatDouble(lut.key.x)},
                      {"velocity", formatDouble(lut.key.velocity)}})},
      {"equirect",
       object({{"width", count(lut.dimensions.width)},
               {"height", count(lut.dimensions.height)},
               {"layout", quoted("RGBA32F row-major, row 0 at latitude +pi/2; rgb = source "
                                 "direction (X to phi_obs, Z spin axis), a = ln g, -1e4 "
                                 "captured, -2e4 trapped")}})},
      {"tile", object({{"radial", count(lut.dimensions.tileRadial)},
                       {"azimuthal", count(lut.dimensions.tileAzimuth)},
                       {"rhoMin", formatDouble(lut.tile.rhoMin)},
                       {"rhoMax", formatDouble(lut.tile.rhoMax)},
                       {"center", vec3(lut.tile.center)},
                       {"axisEast", vec3(lut.tile.axisEast)},
                       {"axisNorth", vec3(lut.tile.axisNorth)}})},
      {"trace", object({{"stepFraction", formatDouble(lut.settings.stepFraction)},
                        {"escapeRadius", formatDouble(lut.settings.escapeRadius)},
                        {"captureFraction", formatDouble(lut.settings.captureFraction)},
                        {"captureFloor", formatDouble(lut.settings.captureFloor)},
                        {"maxSteps", std::to_string(lut.settings.maxSteps)}})},
      {"peak", object({{"look", vec3(lut.peak.look)}, {"g", formatDouble(lut.peak.g)}})},
      {"statistics", object(statisticsMembers)}};
  std::string text = "{\n";
  for (std::size_t index = 0; index < top.size(); ++index) {
    text += "  " + quoted(top.at(index).first) + ": " + top.at(index).second +
            (index + 1 < top.size() ? ",\n" : "\n");
  }
  return text + "}\n";
}

bool writeObserverSkyLut(const ObserverSkyLut &lut, const std::filesystem::path &directory) {
  std::error_code error;
  std::filesystem::create_directories(directory, error);
  if (error) {
    return false;
  }
  const std::string stem = lutStem(lutHash(lut.key, lut.dimensions, lut.settings));
  const std::vector<std::uint8_t> bytes = serialize(lut);
  // Write to a temporary name and rename, so a reader never sees a partial file.
  const std::filesystem::path binary = directory / (stem + ".bin");
  const std::filesystem::path partial = directory / (stem + ".bin.partial");
  {
    std::ofstream file(partial, std::ios::binary | std::ios::trunc);
    std::vector<char> chars(bytes.size());
    std::ranges::transform(bytes, chars.begin(),
                           [](std::uint8_t b) { return std::bit_cast<char>(b); });
    file.write(chars.data(), static_cast<std::streamsize>(chars.size()));
    if (!file) {
      return false;
    }
  }
  std::filesystem::rename(partial, binary, error);
  if (error) {
    return false;
  }
  std::ofstream sidecar(directory / (stem + ".json"), std::ios::trunc);
  sidecar << lutSidecarJson(lut);
  return static_cast<bool>(sidecar);
}

std::optional<ObserverSkyLut> readObserverSkyLut(const std::filesystem::path &file,
                                                 std::uint64_t expectedHash) {
  std::ifstream stream(file, std::ios::binary);
  if (!stream) {
    return std::nullopt;
  }
  std::vector<std::uint8_t> bytes;
  std::ranges::transform(std::istreambuf_iterator<char>(stream), std::istreambuf_iterator<char>(),
                         std::back_inserter(bytes),
                         [](char c) { return std::bit_cast<std::uint8_t>(c); });
  ByteReader in(bytes);
  ObserverSkyLut lut;
  if (!in.magic() || !readInputs(in, lut.key, lut.dimensions, lut.settings) ||
      lutHash(lut.key, lut.dimensions, lut.settings) != expectedHash) {
    return std::nullopt;
  }
  lut.tile.rhoMin = lut.dimensions.tileRhoMin;
  lut.tile.rhoMax = lut.dimensions.tileRhoMax;
  lut.tile.radialCount = lut.dimensions.tileRadial;
  lut.tile.azimuthCount = lut.dimensions.tileAzimuth;
  LutStatistics &statistics = lut.statistics;
  const auto fields = statisticsFields(statistics);
  const bool ok = readVec3(in, lut.tile.center) && readVec3(in, lut.tile.axisEast) &&
                  readVec3(in, lut.tile.axisNorth) && readVec3(in, lut.peak.look) &&
                  in.f64(lut.peak.g) &&
                  std::ranges::all_of(fields, [&in](double *field) { return in.f64(*field); }) &&
                  in.u64(statistics.connectivityDisagreements) && readImage(in, lut.sky) &&
                  readImage(in, lut.tileImage) && in.exhausted();
  const bool shapesMatch = lut.sky.width == lut.dimensions.width &&
                           lut.sky.height == lut.dimensions.height &&
                           lut.tileImage.width == lut.dimensions.tileAzimuth &&
                           lut.tileImage.height == lut.dimensions.tileRadial;
  if (!ok || !shapesMatch) {
    return std::nullopt;
  }
  return lut;
}

} // namespace physics::observer_sky
