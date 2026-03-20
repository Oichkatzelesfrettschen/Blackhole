/**
 * @file grmhd_streaming.h
 * @brief Real-time GRMHD data streaming with tile-based caching
 *
 * WHY: Enable visualization of multi-GB GRMHD time-series without loading entire dataset
 * WHAT: Asynchronous tile streaming, LRU cache, PBO-based GPU upload
 * HOW: Demand-driven loading, octree spatial indexing, frame interpolation
 *
 * Architecture:
 *   1. Tile Cache (CPU): LRU eviction, configurable size (e.g., 2GB)
 *   2. Tile Loader (Async): Background thread reads from packed binary
 *   3. GPU Uploader (PBO): Asynchronous transfer via pixel buffer objects
 *   4. Octree Index (GPU): Spatial lookup structure for ray marching
 *
 * Performance Targets:
 *   - Cache hit rate: >90% during smooth playback
 *   - Frame load time: <16ms (60 fps budget)
 *   - Memory footprint: <4GB resident (for 50GB+ datasets)
 *   - Concurrent frames: 3 (current, next, prev for interpolation)
 *
 * Usage:
 *   GRMHDStreamer streamer("timeseries.json", "timeseries.bin");
 *   streamer.seekFrame(42);
 *   auto tile = streamer.getTile(x, y, z, level);
 *   if (tile.ready()) {
 *     uploadToGPU(tile.data());
 *   }
 *
 * References:
 *   - Porth et al. (2019) ApJS 243, 26 (GRMHD simulation methods)
 *   - Event Horizon Telescope Collaboration (2019) ApJ 875, L1 (M87* imaging)
 */

#pragma once

#include <atomic>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <mutex>
#include <queue>
#include <string>
#include <thread>
#include <unordered_map>
#include <vector>

namespace blackhole {

// Forward declarations
struct GRMHDFrame;
struct GRMHDTile;
struct GRMHDMetadata;

/**
 * @brief Tile identifier for spatial indexing
 */
struct TileID {
    uint32_t frame;
    uint16_t x, y, z;
    uint8_t level;  // Octree level (0 = full resolution)
    
    bool operator==(const TileID& other) const noexcept {
        return frame == other.frame && x == other.x && 
               y == other.y && z == other.z && level == other.level;
    }
};

} // namespace blackhole

// Hash function for TileID (for unordered_map)
namespace std {
template <>
struct hash<blackhole::TileID> {
    size_t operator()(const blackhole::TileID& id) const noexcept {
        size_t h = 0;
        h ^= hash<uint32_t>()(id.frame) + 0x9e3779b9 + (h << 6) + (h >> 2);
        h ^= hash<uint16_t>()(id.x) + 0x9e3779b9 + (h << 6) + (h >> 2);
        h ^= hash<uint16_t>()(id.y) + 0x9e3779b9 + (h << 6) + (h >> 2);
        h ^= hash<uint16_t>()(id.z) + 0x9e3779b9 + (h << 6) + (h >> 2);
        h ^= hash<uint8_t>()(id.level) + 0x9e3779b9 + (h << 6) + (h >> 2);
        return h;
    }
};
} // namespace std

namespace blackhole {

/**
 * @brief GRMHD data tile (RGBA32F texture chunk)
 */
struct GRMHDTile {
  TileID id{};
  std::vector<float> data; // RGBA32F packed (4 channels × width × height × depth)
  size_t width{}, height{}, depth{};

  [[nodiscard]] bool ready() const noexcept { return !data.empty(); }

  [[nodiscard]] size_t sizeBytes() const noexcept { return data.size() * sizeof(float); }
};

/**
 * @brief GRMHD frame metadata
 */
struct GRMHDFrame {
    uint32_t frameIndex;
    double time;  // Simulation time in M units
    size_t byteOffset;  // Offset in binary file
    size_t byteSize;    // Frame data size
};

/**
 * @brief GRMHD time-series metadata
 */
struct GRMHDMetadata {
    std::string jsonPath;
    std::string binPath;
    size_t frameCount{};
    size_t gridX{}, gridY{}, gridZ{}; // Full resolution grid dimensions
    std::vector<GRMHDFrame> frames;
    std::vector<std::string> channels;  // e.g., ["rho", "u", "v1", "v2"]
};

/**
 * @brief Thread-safe LRU tile cache bounded by a configurable byte budget.
 *
 * Evicts the least-recently-used tile when inserting a new tile would exceed
 * @p maxBytes.  All public methods are protected by an internal mutex and
 * are safe to call from both the main thread and the background loader thread.
 */
class TileCache {
public:
    /**
     * @brief Construct a cache with the given memory budget.
     * @param maxBytes Maximum resident cache size in bytes.
     */
    explicit TileCache(size_t maxBytes);
    ~TileCache() = default;

    /**
     * @brief Look up a tile by ID; returns nullptr on a cache miss.
     * @param id Tile identifier (frame + spatial coordinates + octree level).
     * @return Shared pointer to the tile, or nullptr if not cached.
     */
    std::shared_ptr<GRMHDTile> get(const TileID& id);

    /**
     * @brief Insert a tile into the cache, evicting LRU entries if needed.
     * @param id   Tile identifier used as the cache key.
     * @param tile Tile data to store; its sizeBytes() counts against the budget.
     */
    void put(const TileID &id, const std::shared_ptr<GRMHDTile> &tile);

    /** @brief Flush all cached tiles and reset hit/miss counters. */
    void clear();

    /**
     * @brief Cache hit rate as an integer percentage (0-100).
     * @return hits / (hits + misses) * 100, or 0 if no accesses yet.
     */
    size_t hitRate() const noexcept;

    /** @brief Total bytes currently resident in the cache. */
    size_t currentBytes() const noexcept;
    
private:
    struct CacheEntry {
        std::shared_ptr<GRMHDTile> tile;
        size_t accessCount{};
        uint64_t lastAccess{}; // Timestamp for LRU
    };
    
    mutable std::mutex mutex_;
    std::unordered_map<TileID, CacheEntry> cache_;
    size_t maxBytes_;
    size_t currentBytes_{0};
    size_t hits_{0};
    size_t misses_{0};
    
    void evictLRU();
};

/**
 * @brief Asynchronous GRMHD tile streamer with LRU cache and background loading.
 *
 * Parses a nubhlight_pack JSON + binary pair on init(), then streams spatial
 * tiles on demand.  A single background thread drains the load queue so that
 * getTile() never blocks the render thread on a cache miss -- it enqueues the
 * request and returns nullptr; the tile will be available on a subsequent call.
 *
 * Prefetch: seekFrame() automatically enqueues the next 3 frames so that
 * sequential playback achieves >90% cache hit rate at 60 fps.
 */
class GRMHDStreamer {
public:
    /**
     * @brief Construct a streamer for the given dataset paths.
     * @param jsonPath Path to the nubhlight_pack JSON metadata file.
     * @param binPath  Path to the companion flat binary data file.
     */
    explicit GRMHDStreamer(const std::string& jsonPath, const std::string& binPath);

    /** @brief Calls shutdown() to stop the loader thread before destruction. */
    ~GRMHDStreamer();

    GRMHDStreamer(const GRMHDStreamer&) = delete;
    GRMHDStreamer& operator=(const GRMHDStreamer&) = delete;

    /**
     * @brief Parse metadata and start the background loader thread.
     * @return true on success; false if the JSON is missing or malformed.
     */
    bool init();

    /** @brief Stop the loader thread and drain the work queue. */
    void shutdown();

    /**
     * @brief Seek to a specific frame and prefetch adjacent frames.
     * @param frameIndex Zero-based frame index (clamped to frameCount-1).
     */
    void seekFrame(uint32_t frameIndex);

    /**
     * @brief Set the animation playback speed multiplier.
     * @param speed Multiplier relative to real-time (1.0 = normal, 2.0 = double speed).
     */
    void setPlaybackSpeed(double speed);

    /** @brief Resume playback from the current frame. */
    void play();

    /** @brief Pause playback at the current frame. */
    void pause();

    /**
     * @brief Return the tile for the current frame at the given grid coordinates.
     *
     * On a cache hit returns the tile immediately.  On a miss, enqueues an
     * async load and returns nullptr; the caller should retry on the next frame.
     *
     * @param x     Tile X grid index.
     * @param y     Tile Y grid index.
     * @param z     Tile Z grid index.
     * @param level Octree level (0 = full resolution, higher = coarser).
     * @return Shared pointer to the tile data, or nullptr if not yet loaded.
     */
    std::shared_ptr<GRMHDTile> getTile(uint16_t x, uint16_t y, uint16_t z, uint8_t level);

    /** @brief Read-only access to the parsed dataset metadata. */
    const GRMHDMetadata& metadata() const noexcept { return metadata_; }

    /** @brief Index of the frame currently being streamed. */
    uint32_t currentFrame() const noexcept { return currentFrame_.load(); }

    /**
     * @brief Cache hit rate as a fraction in [0.0, 1.0].
     * @return hits / (hits + misses), or 0.0 if no accesses yet.
     */
    double cacheHitRate() const noexcept;

    /** @brief Number of tile load requests currently queued for the background thread. */
    size_t queueDepth() const noexcept;
    
private:
    GRMHDMetadata metadata_;
    TileCache cache_;

    std::atomic<uint32_t> currentFrame_{0};
    std::atomic<bool> running_{false};
    std::atomic<bool> playing_{false};
    std::atomic<double> playbackSpeed_{1.0};

    // Async work queue: main thread enqueues, loaderThread_ drains.
    // Queue element is TileID (load request type private to .cpp).
    mutable std::mutex queueMutex_;
    std::condition_variable queueCV_;
    std::queue<TileID> loadQueue_;

    std::thread loaderThread_;

    void loaderThreadFunc();
    std::shared_ptr<GRMHDTile> loadTile(const TileID& id);
};

} // namespace blackhole
