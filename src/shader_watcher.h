#ifndef SHADER_WATCHER_H
#define SHADER_WATCHER_H

#include <atomic>
#include <chrono>
#include <functional>
#include <memory>
#include <mutex>
#include <set>
#include <string>
#include <vector>

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
#include <wtr/watcher.hpp>
#endif

/// Shader hot-reload file watcher
///
/// Monitors shader source directory for changes and triggers recompilation.
/// Thread-safe design allows main loop to poll for pending reloads.
class ShaderWatcher {
public:
  using ReloadCallback = std::function<void(const std::vector<std::string> &)>;

  /// Singleton access
  static ShaderWatcher &instance();

  /// Start watching shader directory
  /// @param shaderDir Path to shader source directory
  /// @param onReload Callback invoked with list of changed shader paths
  /// @return true if watcher started successfully
  bool start(const std::string &shaderDir, ReloadCallback onReload = nullptr);

  /// Stop watching
  void stop();

  /// Check if watcher is active
  bool isRunning() const;

  /// Poll for pending shader changes (call from main thread)
  /// @return List of shader paths that need recompilation
  std::vector<std::string> pollChangedShaders();

  /// Check if any shaders need reloading
  bool hasPendingReloads() const;

  /// Clear pending reloads (after processing)
  void clearPendingReloads();

  /// Set debounce interval (default 100ms)
  void setDebounceMs(int ms);

  /// Get watched directory
  const std::string &getWatchedDir() const { return watchedDir_; }

private:
  ShaderWatcher() = default;
  ~ShaderWatcher();
  ShaderWatcher(const ShaderWatcher &) = delete;
  ShaderWatcher &operator=(const ShaderWatcher &) = delete;

  /// Check if file extension is a shader source
  bool isShaderSource(const std::string &path) const;

  /// Handle filesystem event
  void onFileEvent(const std::string &path, bool isModify);

  std::string watchedDir_;
  ReloadCallback reloadCallback_;
  std::atomic<bool> running_{false};

  // Pending changes protected by mutex
  mutable std::mutex pendingMutex_;
  std::set<std::string> pendingShaders_;

  // Debounce tracking
  std::chrono::steady_clock::time_point lastEventTime_;
  int debounceMs_ = 100;

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
  std::unique_ptr<wtr::watcher::watch> watcher_;
#endif
};

#endif // SHADER_WATCHER_H
