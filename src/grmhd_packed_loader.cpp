#include "grmhd_packed_loader.h"

// C++ system headers
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// Third-party library headers
#include <glbinding/gl/gl.h>
#include <nlohmann/json.hpp>

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

  const std::streamsize FILE_SIZE = file.tellg();
  file.seekg(0, std::ios::beg);

  if (FILE_SIZE <= 0 || FILE_SIZE % static_cast<std::streamsize>(sizeof(float)) != 0) {
    return false;
  }

  const auto COUNT =
      static_cast<std::size_t>(FILE_SIZE / static_cast<std::streamsize>(sizeof(float)));
  out.resize(COUNT);

  if (!file.read(reinterpret_cast<char *>(out.data()), FILE_SIZE)) {
    return false;
  }
  return true;
}

std::string checksumFnv1a64(const std::vector<float> &data) {
  constexpr std::uint64_t K_OFFSET = 14695981039346656037ull;
  constexpr std::uint64_t K_PRIME = 1099511628211ull;
  std::uint64_t hash = K_OFFSET;
  const auto *bytes = reinterpret_cast<const std::uint8_t *>(data.data());
  const std::size_t COUNT = data.size() * sizeof(float);
  for (std::size_t i = 0; i < COUNT; ++i) {
    hash ^= bytes[i];
    hash *= K_PRIME;
  }
  std::stringstream ss;
  ss << std::hex << std::setw(16) << std::setfill('0') << hash;
  return ss.str();
}

}  // namespace

bool loadGrmhdPackedTexture(const std::string &metadataPath, GrmhdPackedTexture &texture,
                            std::string &error, [[maybe_unused]] bool validate,
                            [[maybe_unused]] bool upload) {
  std::vector<float> blob;
  const std::filesystem::path META_PATH(metadataPath);
  
  if (!std::filesystem::exists(META_PATH)) {
    error = "Metadata file not found: " + metadataPath;
    return false;
  }

  std::ifstream metaFile(META_PATH);
  std::string text((std::istreambuf_iterator<char>(metaFile)), std::istreambuf_iterator<char>());
  
  if (text.empty()) {
    error = "Empty metadata file";
    return false;
  }

  auto json = nlohmann::json::parse(text, nullptr, false);
  if (json.is_discarded()) {
    error = "Invalid JSON in metadata file";
    return false;
  }

  const std::string FORMAT = toUpper(json.value("format", "RGBA32F"));
  if (FORMAT != "RGBA32F") {
    error = "Unsupported texture format: " + FORMAT;
    return false;
  }

  const std::string BINARY_FILENAME = json.value("binary_file", "");
  if (BINARY_FILENAME.empty()) {
    error = "Missing 'binary_file' field in metadata";
    return false;
  }

  const std::filesystem::path BINARY_PATH = META_PATH.parent_path() / BINARY_FILENAME;
  if (!readBinaryFile(BINARY_PATH, blob)) {
    error = "Failed to read binary file: " + BINARY_PATH.string();
    return false;
  }

  // Validate dimensions
  if (!json.contains("grid_dims") || !json["grid_dims"].is_array() ||
      json["grid_dims"].size() != 3) {
    error = "Invalid or missing 'grid_dims' (expected [w, h, d])";
    return false;
  }

  const int WIDTH = json["grid_dims"][0].get<int>();
  const int HEIGHT = json["grid_dims"][1].get<int>();
  const int DEPTH = json["grid_dims"][2].get<int>();

  const std::size_t EXPECTED = static_cast<std::size_t>(WIDTH) *
                               static_cast<std::size_t>(HEIGHT) *
                               static_cast<std::size_t>(DEPTH) * 4u;

  if (blob.size() != EXPECTED) {
    error = "Data size mismatch. Expected " + std::to_string(EXPECTED) + " floats, got " +
            std::to_string(blob.size());
    return false;
  }

  // Verify checksum if present
  if (json.contains("checksum_fnv1a64")) {
    const std::string CHECKSUM_EXPECTED = json["checksum_fnv1a64"].get<std::string>();
    const std::string CHECKSUM_ACTUAL = checksumFnv1a64(blob);
    if (toLower(CHECKSUM_ACTUAL) != toLower(CHECKSUM_EXPECTED)) {
      error = "Checksum mismatch! Expected " + CHECKSUM_EXPECTED + ", calculated " +
              CHECKSUM_ACTUAL;
      return false;
    }
  }

  // Parse channel metadata
  std::vector<std::string> channels;
  std::vector<float> metaMin;
  std::vector<float> metaMax;
  
  if (json.contains("channels") && json["channels"].is_array()) {
    for (const auto &c : json["channels"]) {
      channels.push_back(c.value("name", "unknown"));
      metaMin.push_back(c.value("min", 0.0f));
      metaMax.push_back(c.value("max", 1.0f));
    }
  }

  if (channels.size() != 4) {
    error = "Expected 4 channels, found " + std::to_string(channels.size());
    return false;
  }

  // Create texture
  destroyGrmhdPackedTexture(texture);
  
  texture.width = WIDTH;
  texture.height = HEIGHT;
  texture.depth = DEPTH;
  texture.channels = std::move(channels);
  texture.minValues = std::move(metaMin);
  texture.maxValues = std::move(metaMax);
  texture.texture = createFloatTexture3D(WIDTH, HEIGHT, DEPTH, blob);

  return true;
}

void destroyGrmhdPackedTexture(GrmhdPackedTexture &texture) {
  if (texture.texture != 0) {
    glDeleteTextures(1, &texture.texture);
    texture.texture = 0;
  }
  texture.width = 0;
  texture.height = 0;
  texture.depth = 0;
  texture.channels.clear();
  texture.minValues.clear();
  texture.maxValues.clear();
}