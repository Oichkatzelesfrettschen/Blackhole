#include "render/background_loader.h"

#include <cstddef>
#include <filesystem>
#include <string>
#include <utility>
#include <vector>

#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include "platform/resource_paths.h"
#include "render/render_state.h"
#include "texture.h"

using namespace gl;
using platform::readTextFile;
using platform::resourcePath;

namespace blackhole {

namespace {

std::vector<BackgroundAsset> loadBackgroundAssets() {
  std::vector<BackgroundAsset> assets;
  std::string text;
  if (!readTextFile(resourcePath("assets/backgrounds/manifest.json"), text)) {
    return assets;
  }
  auto json = nlohmann::json::parse(text, nullptr, false);
  if (json.is_discarded() || !json.contains("assets") || !json.at("assets").is_array()) {
    return assets;
  }
  for (const auto &entry : json.at("assets")) {
    BackgroundAsset asset;
    asset.id = entry.value("id", "");
    asset.title = entry.value("title", asset.id);
    asset.path = entry.value("path", "");
    asset.skyboxDir = entry.value("skyboxDir", "");
    if (!asset.path.empty() && !std::filesystem::path(asset.path).is_absolute()) {
      asset.path = resourcePath(asset.path);
    }
    if (!asset.skyboxDir.empty() && !std::filesystem::path(asset.skyboxDir).is_absolute()) {
      asset.skyboxDir = resourcePath(asset.skyboxDir);
    }
    if (!asset.id.empty() && !asset.path.empty()) {
      assets.push_back(std::move(asset));
    }
  }
  return assets;
}

int findBackgroundIndex(const std::vector<BackgroundAsset> &assets, const std::string &id) {
  for (std::size_t i = 0; i < assets.size(); ++i) {
    if (assets.at(i).id == id) {
      return static_cast<int>(i);
    }
  }
  return 0;
}

} // namespace

void updateActiveBackground(RenderState &rs, const std::string &backgroundId) {
  if (rs.background.backgroundAssets.empty()) {
    rs.background.backgroundAssets = loadBackgroundAssets();
  }
  if (!rs.background.backgroundAssets.empty()) {
    rs.background.backgroundIndex = findBackgroundIndex(rs.background.backgroundAssets, backgroundId);
    if (rs.background.backgroundIndex < 0 ||
        std::cmp_greater_equal(rs.background.backgroundIndex, rs.background.backgroundAssets.size())) {
      rs.background.backgroundIndex = 0;
    }
    const auto &asset = rs.background.backgroundAssets.at(static_cast<std::size_t>(rs.background.backgroundIndex));
    if (rs.background.backgroundLoadedId != asset.id) {
      GLuint const nextTexture = loadTexture2D(asset.path, true);
      // Mark this id attempted whether or not the load succeeded, so a missing
      // asset is tried once per selection rather than re-decoded (and re-logged)
      // every frame. A failed load keeps the previous background base.
      rs.background.backgroundLoadedId = asset.id;
      if (nextTexture != 0) {
        if (rs.background.backgroundBase != 0) {
          glDeleteTextures(1, &rs.background.backgroundBase);
        }
        rs.background.backgroundBase = nextTexture;
      }
      // Swap cubemap skybox if the asset specifies one.
      if (!asset.skyboxDir.empty() && rs.background.skyboxLoadedDir != asset.skyboxDir) {
        GLuint const nextCubemap = loadCubemap(asset.skyboxDir);
        if (nextCubemap != 0) {
          if (rs.background.galaxy != 0) {
            glDeleteTextures(1, &rs.background.galaxy);
          }
          rs.background.galaxy = nextCubemap;
          rs.background.skyboxLoadedDir = asset.skyboxDir;
        }
      }
    }
  }
}

} // namespace blackhole
