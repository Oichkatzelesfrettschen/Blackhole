#include "grmhd_packed_loader.h"

#include <algorithm>
#include <array>
#include <cctype>
#include <cmath>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <limits>
#include <sstream>

#include <nlohmann/json.hpp>

#include "render.h"

namespace {

std::string toUpper(std::string value) {
  for (char &c : value) {
    c = static_cast<char>(std::toupper(static_cast<unsigned char>(c)));
  }
  return value;
}

std::string toLower(std::string value) {
  for (char &c : value) {
    c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
  }
  return value;
}

bool readTextFile(const std::filesystem::path &path, std::string &out) {
  std::ifstream file(path);
  if (!file) {
    return false;
  }
  std::ostringstream buffer;
  buffer << file.rdbuf();
  out = buffer.str();
  return true;
}

bool readBinaryFile(const std::filesystem::path &path, std::vector<float> &out) {
  std::ifstream file(path, std::ios::binary | std::ios::ate);
  if (!file) {
    return false;
  }
  const std::streamsize size = file.tellg();
  if (size <= 0) {
    return false;
  }
  if (size % static_cast<std::streamsize>(sizeof(float)) != 0) {
    return false;
  }
  file.seekg(0, std::ios::beg);
  const auto count =
      static_cast<std::size_t>(size / static_cast<std::streamsize>(sizeof(float)));
  out.resize(count);
  if (!file.read(reinterpret_cast<char *>(out.data()), size)) {
    return false;
  }
  return true;
}

std::string checksumFnv1a64(const std::vector<float> &data) {
  constexpr std::uint64_t kOffset = 14695981039346656037ull;
  constexpr std::uint64_t kPrime = 1099511628211ull;
  std::uint64_t hash = kOffset;
  const auto *bytes = reinterpret_cast<const std::uint8_t *>(data.data());
  std::size_t count = data.size() * sizeof(float);
  for (std::size_t i = 0; i < count; ++i) {
    hash ^= bytes[i];
    hash *= kPrime;
  }
  std::ostringstream out;
  out << std::hex << std::setw(16) << std::setfill('0') << hash;
  return out.str();
}

void computeMinMax(const std::vector<float> &blob, std::array<float, 4> &minValues,
                   std::array<float, 4> &maxValues) {
  minValues.fill(std::numeric_limits<float>::infinity());
  maxValues.fill(-std::numeric_limits<float>::infinity());
  for (std::size_t i = 0; i + 3 < blob.size(); i += 4) {
    for (std::size_t c = 0; c < 4; ++c) {
      float value = blob[i + c];
      minValues[c] = std::min(minValues[c], value);
      maxValues[c] = std::max(maxValues[c], value);
    }
  }
}

bool withinTolerance(float a, float b) {
  float scale = std::max(1.0f, std::max(std::abs(a), std::abs(b)));
  return std::abs(a - b) <= 1e-3f * scale;
}

} // namespace

bool loadGrmhdPackedTexture(const std::string &metadataPath, GrmhdPackedTexture &out,
                            std::string &error, bool validate, bool upload) {
  destroyGrmhdPackedTexture(out);

  std::filesystem::path metaPath(metadataPath);
  std::string text;
  if (!readTextFile(metaPath, text)) {
    error = "Failed to read metadata JSON.";
    return false;
  }

  auto json = nlohmann::json::parse(text, nullptr, false);
  if (json.is_discarded()) {
    error = "Failed to parse metadata JSON.";
    return false;
  }

  const std::string format = toUpper(json.value("format", "RGBA32F"));
  if (format != "RGBA32F") {
    error = "Unsupported texture format: " + format;
    return false;
  }

  std::string checksumExpected;
  if (json.contains("checksum_fnv1a64")) {
    checksumExpected = json["checksum_fnv1a64"].get<std::string>();
  }

  std::filesystem::path binPath = json.value("bin", "");
  if (binPath.empty()) {
    error = "Metadata missing 'bin' path.";
    return false;
  }
  if (binPath.is_relative()) {
    binPath = metaPath.parent_path() / binPath;
  }

  if (!json.contains("grid_dims") || !json["grid_dims"].is_array() ||
      json["grid_dims"].size() != 3) {
    error = "Metadata missing grid_dims[3].";
    return false;
  }

  int width = json["grid_dims"][0].get<int>();
  int height = json["grid_dims"][1].get<int>();
  int depth = json["grid_dims"][2].get<int>();
  if (width <= 0 || height <= 0 || depth <= 0) {
    error = "Invalid grid_dims.";
    return false;
  }

  std::vector<float> blob;
  if (!readBinaryFile(binPath, blob)) {
    error = "Failed to read binary blob.";
    return false;
  }

  std::size_t expected = static_cast<std::size_t>(width) *
                         static_cast<std::size_t>(height) *
                         static_cast<std::size_t>(depth) * 4;
  if (blob.size() < expected) {
    error = "Binary blob smaller than expected RGBA volume.";
    return false;
  }

  if (validate && !checksumExpected.empty()) {
    const std::string checksumActual = checksumFnv1a64(blob);
    if (toLower(checksumActual) != toLower(checksumExpected)) {
      error = "Checksum mismatch in packed blob.";
      return false;
    }
  }

  std::array<float, 4> actualMin{};
  std::array<float, 4> actualMax{};
  computeMinMax(blob, actualMin, actualMax);

  std::vector<float> metaMin;
  std::vector<float> metaMax;
  if (json.contains("min") && json["min"].is_array()) {
    for (const auto &item : json["min"]) {
      metaMin.push_back(item.get<float>());
    }
  }
  if (json.contains("max") && json["max"].is_array()) {
    for (const auto &item : json["max"]) {
      metaMax.push_back(item.get<float>());
    }
  }
  if (validate && metaMin.size() >= 4 && metaMax.size() >= 4) {
    for (std::size_t c = 0; c < 4; ++c) {
      if (!withinTolerance(actualMin[c], metaMin[c]) ||
          !withinTolerance(actualMax[c], metaMax[c])) {
        error = "Packed min/max metadata does not match blob contents.";
        return false;
      }
    }
  }

  if (upload) {
    out.texture = createRGBA32FTexture3D(width, height, depth, blob);
  }
  out.width = width;
  out.height = height;
  out.depth = depth;
  out.format = format;
  out.layout = json.value("layout", "channels-last");

  if (json.contains("channels") && json["channels"].is_array()) {
    out.channels.clear();
    for (const auto &item : json["channels"]) {
      out.channels.push_back(item.get<std::string>());
    }
  }
  if (!metaMin.empty()) {
    out.minValues = std::move(metaMin);
  } else {
    out.minValues.assign(actualMin.begin(), actualMin.end());
  }
  if (!metaMax.empty()) {
    out.maxValues = std::move(metaMax);
  } else {
    out.maxValues.assign(actualMax.begin(), actualMax.end());
  }

  return true;
}

void destroyGrmhdPackedTexture(GrmhdPackedTexture &texture) {
  if (texture.texture != 0) {
    glDeleteTextures(1, &texture.texture);
    texture.texture = 0;
  }
}
