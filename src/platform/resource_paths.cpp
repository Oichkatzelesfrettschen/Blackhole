/**
 * @file resource_paths.cpp
 * @brief Resource-root detection by upward landmark search.
 */

#include "resource_paths.h"

#include <fstream>
#include <sstream>
#include <system_error>
#include <vector>

namespace platform {
namespace {

std::filesystem::path gResourceRoot = ".";

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

void initResourceRoot(const char *argv0) { gResourceRoot = detectResourceRoot(argv0); }

const std::filesystem::path &resourceRoot() { return gResourceRoot; }

std::string resourcePath(std::string_view relativePath) {
  return (gResourceRoot / std::filesystem::path(relativePath)).string();
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
