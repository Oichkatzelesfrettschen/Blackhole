/**
 * @file shader_watcher.h
 * @brief Hot-reload file watcher for GLSL shader sources.
 *
 * ShaderWatcher monitors a shader directory for modifications and exposes a
 * poll-based interface so the main render loop can safely query and consume
 * pending reload events on the main thread.  The underlying filesystem watch
 * is provided by the wtr/watcher library when the project is built with
 * BLACKHOLE_ENABLE_SHADER_WATCHER; otherwise all operations are stubs.
 */

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

/**
 * @brief Singleton file watcher that detects shader source modifications.
 *
 * Monitors a shader directory on a background thread and accumulates changed
 * paths in a mutex-protected set.  The main thread calls pollChangedShaders()
 * each frame to consume pending events without blocking.
 */
class ShaderWatcher {
public:
  /** @brief Callback type invoked with the list of changed shader file paths. */
  using ReloadCallback = std::function<void(const std::vector<std::string> &)>;

  /** @brief Returns the process-wide singleton instance. */
  static ShaderWatcher &instance();

  /**
   * @brief Begin watching a shader directory for source file changes.
   *
   * @param shaderDir Path to the directory containing GLSL source files.
   * @param onReload  Optional callback invoked from the watcher thread when
   *                  files change.  The main thread should prefer pollChangedShaders().
   * @return true if the watcher started successfully; false otherwise.
   */
  bool start(const std::string &shaderDir, const ReloadCallback &onReload = nullptr);

  /** @brief Stop the file watcher and release resources. */
  void stop();

  /** @brief Return true if the watcher is currently active. */
  bool isRunning() const;

  /**
   * @brief Consume and return all pending changed shader paths.
   *
   * Safe to call from the main thread at any time.  Does NOT clear the pending
   * set; call clearPendingReloads() after processing the returned paths.
   *
   * @return Snapshot of paths that have been modified since the last poll.
   */
  std::vector<std::string> pollChangedShaders();

  /** @brief Return true if there are unprocessed shader change events. */
  bool hasPendingReloads() const;

  /** @brief Discard all accumulated pending reload events. */
  void clearPendingReloads();

  /**
   * @brief Set the debounce window in milliseconds (default 100 ms).
   *
   * Events arriving faster than this interval are coalesced into a single
   * notification to avoid recompiling during rapid saves.
   *
   * @param ms Debounce duration in milliseconds.
   */
  void setDebounceMs(int ms);

  /** @brief Return the absolute path of the currently watched directory. */
  const std::string &getWatchedDir() const { return watchedDir_; }

  ShaderWatcher(const ShaderWatcher &) = delete;
  ShaderWatcher &operator=(const ShaderWatcher &) = delete;

private:
  ShaderWatcher() = default;
  ~ShaderWatcher();

  /** @brief Return true if the file extension is a recognized GLSL source extension. */
  static bool isShaderSource(const std::string &path);

  /**
   * @brief Process a single filesystem event.
   *
   * Applies debounce logic and, if the path is a shader source, inserts it
   * into the pending set.
   *
   * @param path     Absolute path of the changed file.
   * @param isModify True for modify/create events; false for deletions (ignored).
   */
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
