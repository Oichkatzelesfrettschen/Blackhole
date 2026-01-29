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
#include <cstddef>
#include <cstdint>
#include <memory>
#include <mutex>
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
    TileID id;
    std::vector<float> data;  // RGBA32F packed (4 channels × width × height × depth)
    size_t width, height, depth;
    
    bool ready() const noexcept {
        return !data.empty();
    }
    
    size_t sizeBytes() const noexcept {
        return data.size() * sizeof(float);
    }
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
    size_t frameCount;
    size_t gridX, gridY, gridZ;  // Full resolution grid dimensions
    std::vector<GRMHDFrame> frames;
    std::vector<std::string> channels;  // e.g., ["rho", "u", "v1", "v2"]
};

/**
 * @brief LRU tile cache
 */
class TileCache {
public:
    explicit TileCache(size_t maxBytes);
    ~TileCache() = default;
    
    // Thread-safe cache operations
    std::shared_ptr<GRMHDTile> get(const TileID& id);
    void put(const TileID& id, std::shared_ptr<GRMHDTile> tile);
    void clear();
    
    // Statistics
    size_t hitRate() const noexcept;
    size_t currentBytes() const noexcept;
    
private:
    struct CacheEntry {
        std::shared_ptr<GRMHDTile> tile;
        size_t accessCount;
        uint64_t lastAccess;  // Timestamp for LRU
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
 * @brief Asynchronous GRMHD tile streamer
 */
class GRMHDStreamer {
public:
    explicit GRMHDStreamer(const std::string& jsonPath, const std::string& binPath);
    ~GRMHDStreamer();
    
    // Lifecycle
    bool init();
    void shutdown();
    
    // Playback control
    void seekFrame(uint32_t frameIndex);
    void setPlaybackSpeed(double speed);  // 1.0 = real-time
    void play();
    void pause();
    
    // Data access (thread-safe)
    std::shared_ptr<GRMHDTile> getTile(uint16_t x, uint16_t y, uint16_t z, uint8_t level);
    const GRMHDMetadata& metadata() const noexcept { return metadata_; }
    uint32_t currentFrame() const noexcept { return currentFrame_.load(); }
    
    // Statistics
    double cacheHitRate() const noexcept;
    size_t queueDepth() const noexcept;
    
private:
    GRMHDMetadata metadata_;
    TileCache cache_;
    
    std::atomic<uint32_t> currentFrame_{0};
    std::atomic<bool> running_{false};
    std::atomic<bool> playing_{false};
    std::atomic<double> playbackSpeed_{1.0};
    
    std::thread loaderThread_;
    
    void loaderThreadFunc();
    std::shared_ptr<GRMHDTile> loadTile(const TileID& id);
};

} // namespace blackhole
