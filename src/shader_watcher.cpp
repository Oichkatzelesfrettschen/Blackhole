#include "shader_watcher.h"

#include <algorithm>
#include <filesystem>
#include <iostream>

namespace fs = std::filesystem;

ShaderWatcher &ShaderWatcher::instance() {
  static ShaderWatcher inst;
  return inst;
}

ShaderWatcher::~ShaderWatcher() { stop(); }

bool ShaderWatcher::isShaderSource(const std::string &path) const {
  // Shader source extensions (not compiled .spv files)
  static const std::vector<std::string> extensions = {
      ".vert", ".frag", ".comp", ".geom", ".tesc", ".tese", ".glsl"};

  std::string lowerPath = path;
  std::transform(lowerPath.begin(), lowerPath.end(), lowerPath.begin(),
                 ::tolower);

  // Skip .spv files
  if (lowerPath.size() >= 4 &&
      lowerPath.substr(lowerPath.size() - 4) == ".spv") {
    return false;
  }

  for (const auto &ext : extensions) {
    if (lowerPath.size() >= ext.size() &&
        lowerPath.substr(lowerPath.size() - ext.size()) == ext) {
      return true;
    }
  }
  return false;
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
    std::lock_guard<std::mutex> lock(pendingMutex_);
    pendingShaders_.insert(path);
  }

  std::cout << "[ShaderWatcher] Shader modified: " << path << std::endl;
}

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER

bool ShaderWatcher::start(const std::string &shaderDir,
                          ReloadCallback onReload) {
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
  reloadCallback_ = std::move(onReload);
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

bool ShaderWatcher::start(const std::string &shaderDir,
                          ReloadCallback onReload) {
  (void)shaderDir;
  (void)onReload;
  std::cout << "[ShaderWatcher] Hot-reload disabled (build without "
               "ENABLE_SHADER_WATCHER)"
            << std::endl;
  return false;
}

void ShaderWatcher::stop() {
  // No-op when disabled
}

#endif // BLACKHOLE_ENABLE_SHADER_WATCHER

bool ShaderWatcher::isRunning() const { return running_; }

std::vector<std::string> ShaderWatcher::pollChangedShaders() {
  std::lock_guard<std::mutex> lock(pendingMutex_);
  std::vector<std::string> result(pendingShaders_.begin(),
                                  pendingShaders_.end());
  return result;
}

bool ShaderWatcher::hasPendingReloads() const {
  std::lock_guard<std::mutex> lock(pendingMutex_);
  return !pendingShaders_.empty();
}

void ShaderWatcher::clearPendingReloads() {
  std::lock_guard<std::mutex> lock(pendingMutex_);
  pendingShaders_.clear();
}

void ShaderWatcher::setDebounceMs(int ms) { debounceMs_ = ms; }
