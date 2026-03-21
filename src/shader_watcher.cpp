/**
 * @file shader_watcher.cpp
 * @brief Implementation of ShaderWatcher: filesystem event handling, debouncing,
 *        and the wtr/watcher integration (or stub when the feature is disabled).
 */

#include "shader_watcher.h"

#include <algorithm>
#include <cctype>
#include <chrono>
#include <iostream>
#include <mutex>
#include <string>
#include <vector>

ShaderWatcher &ShaderWatcher::instance() {
  static ShaderWatcher inst;
  return inst;
}

ShaderWatcher::~ShaderWatcher() { stop(); }

bool ShaderWatcher::isShaderSource(const std::string &path) {
  // Shader source extensions (not compiled .spv files)
  static const std::vector<std::string> extensions = {
      ".vert", ".frag", ".comp", ".geom", ".tesc", ".tese", ".glsl"};

  std::string lowerPath = path;
  std::ranges::transform(lowerPath, lowerPath.begin(), ::tolower);

  // Skip .spv files
  if (lowerPath.size() >= 4 &&
      lowerPath.substr(lowerPath.size() - 4) == ".spv") {
    return false;
  }

  return std::ranges::any_of(extensions, [&](const auto &ext) {
    return lowerPath.size() >= ext.size() &&
           lowerPath.substr(lowerPath.size() - ext.size()) == ext;
  });
}

void ShaderWatcher::onFileEvent(const std::string &path, bool /*isModify*/) {
  if (!isShaderSource(path)) {
    return;
  }

  // Debounce: skip events that come too quickly
  auto now = std::chrono::steady_clock::now();
  auto elapsed =
      std::chrono::duration_cast<std::chrono::milliseconds>(now - lastEventTime_)
          .count();

  if (elapsed < debounceMs_) {
    return;
  }
  lastEventTime_ = now;

  // Add to pending set
  {
    std::scoped_lock const lock(pendingMutex_);
    pendingShaders_.insert(path);
  }

  std::cout << "[ShaderWatcher] Shader modified: " << path << '\n';
}

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER

#include <filesystem>
namespace fs = std::filesystem;

bool ShaderWatcher::start(const std::string &shaderDir,
                          const ReloadCallback &onReload) {
  if (running_) {
    std::cerr << "[ShaderWatcher] Already running" << std::endl;
    return false;
  }

  // Validate directory
  std::error_code ec;
  if (!fs::is_directory(shaderDir, ec)) {
    std::cerr << "[ShaderWatcher] Not a directory: " << shaderDir << std::endl;
    return false;
  }

  watchedDir_ = fs::absolute(shaderDir).string();
  reloadCallback_ = onReload;
  lastEventTime_ = std::chrono::steady_clock::now();

  try {
    watcher_ = std::make_unique<wtr::watcher::watch>(
        watchedDir_, [this](const wtr::watcher::event &ev) {
          // Skip watcher status events
          if (ev.path_type == wtr::watcher::event::path_type::watcher) {
            return;
          }

          // Only care about file modifications and creations
          if (ev.path_type != wtr::watcher::event::path_type::file) {
            return;
          }

          bool isModify =
              (ev.effect_type == wtr::watcher::event::effect_type::modify ||
               ev.effect_type == wtr::watcher::event::effect_type::create);

          if (isModify) {
            onFileEvent(ev.path_name.string(), true);
          }
        });

    running_ = true;
    std::cout << "[ShaderWatcher] Watching: " << watchedDir_ << std::endl;
    return true;

  } catch (const std::exception &e) {
    std::cerr << "[ShaderWatcher] Failed to start: " << e.what() << std::endl;
    return false;
  }
}

void ShaderWatcher::stop() {
  if (!running_) {
    return;
  }

  running_ = false;

  if (watcher_) {
    watcher_->close();
    watcher_.reset();
  }

  std::cout << "[ShaderWatcher] Stopped" << std::endl;
}

#else // !BLACKHOLE_ENABLE_SHADER_WATCHER

bool ShaderWatcher::start(const std::string &shaderDir, // NOLINT(readability-convert-member-functions-to-static) -- stub for disabled build
                          const ReloadCallback &onReload) {
  (void)shaderDir;
  (void)onReload;
  std::cout << "[ShaderWatcher] Hot-reload disabled (build without "
               "ENABLE_SHADER_WATCHER)"
            << '\n';
  return false;
}

void ShaderWatcher::stop() {
  // No-op when disabled
}

#endif // BLACKHOLE_ENABLE_SHADER_WATCHER

bool ShaderWatcher::isRunning() const { return running_; }

std::vector<std::string> ShaderWatcher::pollChangedShaders() {
  std::scoped_lock const lock(pendingMutex_);
  std::vector<std::string> result(pendingShaders_.begin(),
                                  pendingShaders_.end());
  return result;
}

bool ShaderWatcher::hasPendingReloads() const {
  std::scoped_lock const lock(pendingMutex_);
  return !pendingShaders_.empty();
}

void ShaderWatcher::clearPendingReloads() {
  std::scoped_lock const lock(pendingMutex_);
  pendingShaders_.clear();
}

void ShaderWatcher::setDebounceMs(int ms) { debounceMs_ = ms; }
