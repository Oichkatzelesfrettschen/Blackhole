/**
 * @file resource_paths.cpp
 * @brief Resource-root detection by upward landmark search.
 */

#include "resource_paths.h"

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <ios>
#include <random>
#include <sstream>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

namespace platform {
namespace {

/** @brief The resolved root, built on first use so a failed allocation throws
 *         into the caller rather than during static initialization. */
std::filesystem::path &resourceRootStorage() {
  static std::filesystem::path root = ".";
  return root;
}

bool isValidResourceRoot(const std::filesystem::path &root) {
  std::error_code ec;
  return std::filesystem::exists(root / "shader" / "simple.vert", ec) &&
         std::filesystem::exists(root / "assets" / "backgrounds" / "manifest.json", ec) &&
         std::filesystem::exists(root / "src" / "main.cpp", ec);
}

std::filesystem::path detectResourceRoot(const char *argv0) {
  std::error_code ec;
  std::vector<std::filesystem::path> seeds;
  seeds.push_back(std::filesystem::current_path(ec));
  if (argv0 != nullptr && argv0[0] != '\0') {
    std::filesystem::path const exePath = std::filesystem::absolute(argv0, ec);
    if (!ec) {
      seeds.push_back(exePath.parent_path());
    }
  }

  for (const auto &seed : seeds) {
    std::filesystem::path probe = seed;
    while (!probe.empty()) {
      if (isValidResourceRoot(probe)) {
        return probe;
      }
      std::filesystem::path const parent = probe.parent_path();
      if (parent == probe) {
        break;
      }
      probe = parent;
    }
  }
  return std::filesystem::current_path(ec);
}

} // namespace

void initResourceRoot(const char *argv0) { resourceRootStorage() = detectResourceRoot(argv0); }

const std::filesystem::path &resourceRoot() { return resourceRootStorage(); }

std::filesystem::path userCacheDirectory() {
  const char *xdgCacheHome = std::getenv("XDG_CACHE_HOME");
  if (xdgCacheHome != nullptr && xdgCacheHome[0] != '\0') {
    const std::filesystem::path cacheHome(xdgCacheHome);
    if (cacheHome.is_absolute()) {
      return cacheHome / "blackhole";
    }
  }
  const char *home = std::getenv("HOME");
  return home != nullptr && home[0] != '\0' ? std::filesystem::path(home) / ".cache" / "blackhole"
                                              : std::filesystem::path{};
}

std::filesystem::path writableCacheSubdirectory(std::string_view name) {
  const std::filesystem::path cache = userCacheDirectory();
  if (cache.empty()) {
    return {};
  }
  std::filesystem::path directory = cache / std::filesystem::path(name);
  std::error_code error;
  std::filesystem::create_directories(directory, error);
  if (error) {
    return {};
  }
  // An existing directory can still refuse writes (e.g. owned by another
  // user). The probe gets a fresh name, so a leftover file cannot pass for a
  // successful create, and it must be removable.
  const std::filesystem::path probe =
      directory / (".write_probe_" + std::to_string(std::random_device{}()));
  {
    std::ofstream stream(probe, std::ios::binary | std::ios::trunc);
    if (!stream || !(stream << 'x') || !stream.flush()) {
      return {};
    }
  }
  if (!std::filesystem::remove(probe, error) || error) {
    return {};
  }
  std::filesystem::directory_iterator iterator(directory, error);
  if (error) {
    return {};
  }
  const std::filesystem::directory_iterator end;
  while (iterator != end) {
    iterator.increment(error);
    if (error) {
      return {};
    }
  }
  return directory;
}

std::string resourcePath(std::string_view relativePath) {
  return (resourceRootStorage() / std::filesystem::path(relativePath)).string();
}

bool readTextFile(const std::string &path, std::string &out) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::ostringstream buffer;
  buffer << file.rdbuf();
  out = buffer.str();
  return !out.empty();
}

} // namespace platform
