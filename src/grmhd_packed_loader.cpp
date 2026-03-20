#include "grmhd_packed_loader.h"

// C++ system headers
#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <ios>
#include <iterator>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// Third-party library headers
// NOLINTBEGIN(misc-include-cleaner)
// glbinding/gl/gl.h is the conventional umbrella header; include-cleaner
// prefers per-symbol sub-headers but the umbrella is required for 'using namespace gl'.
#include <glbinding/gl/gl.h>
// nlohmann/json.hpp defines nlohmann::json; include-cleaner false-positive.
#include <nlohmann/json.hpp>
// NOLINTEND(misc-include-cleaner)

#include "render.h"

using namespace gl;

namespace {

std::string toUpper(std::string value) {
  std::ranges::transform(value, value.begin(),
                         [](unsigned char c) { return static_cast<char>(std::toupper(c)); });
  return value;
}

std::string toLower(std::string value) {
  std::ranges::transform(value, value.begin(),
                         [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
  return value;
}

bool readBinaryFile(const std::filesystem::path &path, std::vector<float> &out) {
  std::ifstream file(path, std::ios::binary | std::ios::ate);
  if (!file.is_open()) {
    return false;
  }

  const std::streamsize fileSize = file.tellg();
  file.seekg(0, std::ios::beg);

  if (fileSize <= 0 || fileSize % static_cast<std::streamsize>(sizeof(float)) != 0) {
    return false;
  }

  const auto floatCount =
      static_cast<std::size_t>(fileSize / static_cast<std::streamsize>(sizeof(float)));
  out.resize(floatCount);

  return static_cast<bool>(file.read(reinterpret_cast<char *>(out.data()), fileSize));
}

std::string checksumFnv1a64(const std::vector<float> &data) {
  constexpr std::uint64_t kOffset = 14695981039346656037ull;
  constexpr std::uint64_t kPrime  = 1099511628211ull;
  std::uint64_t hash = kOffset;
  const auto *bytes = reinterpret_cast<const std::uint8_t *>(data.data());
  const std::size_t byteCount = data.size() * sizeof(float);
  for (std::size_t i = 0; i < byteCount; ++i) {
    hash ^= bytes[i];
    hash *= kPrime;
  }
  std::stringstream ss;
  ss << std::hex << std::setw(16) << std::setfill('0') << hash;
  return ss.str();
}

}  // namespace

bool loadGrmhdPackedTexture(const std::string &metadataPath, GrmhdPackedTexture &texture,
                            std::string &error, [[maybe_unused]] bool validate,
                            bool upload) {
  std::vector<float> blob;
  const std::filesystem::path metaFsPath(metadataPath);

  if (!std::filesystem::exists(metaFsPath)) {
    error = "Metadata file not found: " + metadataPath;
    return false;
  }

  std::ifstream metaFile(metaFsPath);
  const std::string text((std::istreambuf_iterator<char>(metaFile)), std::istreambuf_iterator<char>());
  
  if (text.empty()) {
    error = "Empty metadata file";
    return false;
  }

  auto json = nlohmann::json::parse(text, nullptr, false); // NOLINT(misc-include-cleaner)
  if (json.is_discarded()) {
    error = "Invalid JSON in metadata file";
    return false;
  }

  const std::string textureFormat = toUpper(json.value("format", "RGBA32F"));
  if (textureFormat != "RGBA32F") {
    error = "Unsupported texture format: " + textureFormat;
    return false;
  }

  /* nubhlight_pack writes "bin"; accept "binary_file" for legacy metadata. */
  const std::string binaryFilename = json.contains("bin")
      ? json.value("bin", "")
      : json.value("binary_file", "");
  if (binaryFilename.empty()) {
    error = "Missing 'bin' (or 'binary_file') field in metadata";
    return false;
  }

  const std::filesystem::path binaryPath = metaFsPath.parent_path() / binaryFilename;
  if (!readBinaryFile(binaryPath, blob)) {
    error = "Failed to read binary file: " + binaryPath.string();
    return false;
  }

  // Validate dimensions
  if (!json.contains("grid_dims") || !json.at("grid_dims").is_array() ||
      json.at("grid_dims").size() != 3) {
    error = "Invalid or missing 'grid_dims' (expected [w, h, d])";
    return false;
  }

  const auto& gridDims  = json.at("grid_dims");
  const int gridWidth   = gridDims.at(0).get<int>();
  const int gridHeight  = gridDims.at(1).get<int>();
  const int gridDepth   = gridDims.at(2).get<int>();

  const std::size_t expectedCount = static_cast<std::size_t>(gridWidth) *
                                    static_cast<std::size_t>(gridHeight) *
                                    static_cast<std::size_t>(gridDepth) * 4u;

  if (blob.size() != expectedCount) {
    error = "Data size mismatch. Expected " + std::to_string(expectedCount) + " floats, got " +
            std::to_string(blob.size());
    return false;
  }

  // Verify checksum if present
  if (json.contains("checksum_fnv1a64")) {
    const std::string checksumExpected = json.at("checksum_fnv1a64").get<std::string>();
    const std::string checksumActual   = checksumFnv1a64(blob);
    if (toLower(checksumActual) != toLower(checksumExpected)) {
      error = "Checksum mismatch! Expected " + checksumExpected + ", calculated " +
              checksumActual;
      return false;
    }
  }

  // Parse channel metadata
  std::vector<std::string> channels;
  std::vector<float> metaMin;
  std::vector<float> metaMax;

  if (json.contains("channels") && json.at("channels").is_array()) {
    const auto& chans = json.at("channels");
    /* nubhlight_pack writes channels as a flat string array with top-level
     * "min"/"max" arrays.  Legacy format uses per-channel objects. */
    const bool isObjectArray = !chans.empty() && chans.front().is_object();
    const bool hasMin = json.contains("min") && json.at("min").is_array();
    const bool hasMax = json.contains("max") && json.at("max").is_array();
    /* Use stable references to avoid repeated key lookups inside the loop. */
    const nlohmann::json emptyArr = nlohmann::json::array();
    const auto& jMin = hasMin ? json.at("min") : emptyArr;
    const auto& jMax = hasMax ? json.at("max") : emptyArr;
    std::size_t idx = 0;
    for (const auto &c : chans) {
      if (isObjectArray) {
        channels.push_back(c.value("name", "unknown"));
        metaMin.push_back(c.value("min", 0.0f));
        metaMax.push_back(c.value("max", 1.0f));
      } else {
        channels.push_back(c.get<std::string>());
        metaMin.push_back(idx < jMin.size() ? jMin.at(idx).get<float>() : 0.0f);
        metaMax.push_back(idx < jMax.size() ? jMax.at(idx).get<float>() : 1.0f);
      }
      ++idx;
    }
  }

  if (channels.size() != 4) {
    error = "Expected 4 channels, found " + std::to_string(channels.size());
    return false;
  }

  // Populate metadata; only create GL texture when a context is available.
  destroyGrmhdPackedTexture(texture);

  texture.width = gridWidth;
  texture.height = gridHeight;
  texture.depth = gridDepth;
  texture.channels = std::move(channels);
  texture.minValues = std::move(metaMin);
  texture.maxValues = std::move(metaMax);
  /* WHY: upload=false lets headless tests (no GL context) validate metadata
   * without crashing on glGenTextures.  Pass true from the render path. */
  texture.texture = upload
      ? createFloatTexture3D(gridWidth, gridHeight, gridDepth, blob) : 0;

  return true;
}

void destroyGrmhdPackedTexture(GrmhdPackedTexture &texture) {
  if (texture.texture != 0) {
    glDeleteTextures(1, &texture.texture); // NOLINT(misc-include-cleaner)
    texture.texture = 0;
  }
  texture.width = 0;
  texture.height = 0;
  texture.depth = 0;
  texture.channels.clear();
  texture.minValues.clear();
  texture.maxValues.clear();
}