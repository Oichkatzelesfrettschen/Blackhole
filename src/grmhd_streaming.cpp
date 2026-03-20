/**
 * @file grmhd_streaming.cpp
 * @brief GRMHD async tile streaming implementation.
 *
 * WHY: Multi-GB GRMHD time-series cannot be held entirely in GPU memory.
 *      Tile-based LRU streaming with background loading is required to achieve
 *      >90% cache hit rate and >=24 fps during smooth playback.
 *
 * WHAT: JSON metadata parsing, binary tile read, background thread loading,
 *       LRU cache eviction, and prefetch of adjacent frames.
 *
 * HOW: nlohmann_json parses the nubhlight_pack JSON format. std::fstream reads
 *      binary slabs. std::thread (with condition_variable work queue) loads
 *      tiles off the main thread. TileCache handles LRU eviction.
 *
 * Format: nubhlight_pack emits one JSON + one flat binary per invocation.
 *   JSON fields: schema_version, grid_dims [X, Y, Z], channels [], bin,
 *               format ("rgba32f"), dataset_dims, checksum_fnv1a64.
 *   Binary:     raw RGBA32F (4 x float32 per voxel), row-major Z-Y-X order.
 *
 * References:
 *   - tools/nubhlight_pack.cpp (writeMetadata)
 *   - Porth et al. (2019) ApJS 243, 26 (GRMHD simulation conventions)
 */

#include "grmhd_streaming.h"

#include <algorithm>
#include <condition_variable>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <ios>
#include <memory>
#include <mutex>
#include <queue>
#include <string>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

using json = nlohmann::json;

namespace blackhole {

// ============================================================================
// TileCache Implementation
// ============================================================================

TileCache::TileCache(size_t maxBytes) : maxBytes_(maxBytes) {}

std::shared_ptr<GRMHDTile> TileCache::get(const TileID& id) {
  std::scoped_lock const lock(mutex_);

  auto it = cache_.find(id);
  if (it != cache_.end()) {
    it->second.accessCount++;
    it->second.lastAccess = hits_ + misses_;
    hits_++;
    return it->second.tile;
  }

    misses_++;
    return nullptr;
}

void TileCache::put(const TileID &id, const std::shared_ptr<GRMHDTile> &tile) {
  std::scoped_lock const lock(mutex_);

  size_t const tileSize = tile->sizeBytes();

  // Evict LRU tiles while over memory budget
  while (currentBytes_ + tileSize > maxBytes_ && !cache_.empty()) {
    evictLRU();
  }

  CacheEntry entry;
  entry.tile = tile;
  entry.accessCount = 1;
  entry.lastAccess = hits_ + misses_;

  cache_[id] = entry;
  currentBytes_ += tileSize;
}

void TileCache::clear() {
  std::scoped_lock const lock(mutex_);
  cache_.clear();
  currentBytes_ = 0;
  hits_ = 0;
  misses_ = 0;
}

size_t TileCache::hitRate() const noexcept {
  std::scoped_lock const lock(mutex_);
  size_t const total = hits_ + misses_;
  return total > 0 ? (hits_ * 100) / total : 0;
}

size_t TileCache::currentBytes() const noexcept {
  std::scoped_lock const lock(mutex_);
  return currentBytes_;
}

void TileCache::evictLRU() {
    // Caller must hold mutex_.
    auto oldest = cache_.begin();
    for (auto it = cache_.begin(); it != cache_.end(); ++it) {
        if (it->second.lastAccess < oldest->second.lastAccess) {
            oldest = it;
        }
    }
    if (oldest != cache_.end()) {
        currentBytes_ -= oldest->second.tile->sizeBytes();
        cache_.erase(oldest);
    }
}

// ============================================================================
// GRMHDStreamer Implementation
// ============================================================================

GRMHDStreamer::GRMHDStreamer(const std::string& jsonPath,
                             const std::string& binPath)
    : cache_(2ULL * 1024 * 1024 * 1024)  // 2 GB default LRU budget
{
    metadata_.jsonPath = jsonPath;
    metadata_.binPath  = binPath;
}

GRMHDStreamer::~GRMHDStreamer() {
    shutdown();
}

// ---------------------------------------------------------------------------
// init(): parse JSON metadata, open binary file, start loader thread.
// ---------------------------------------------------------------------------
bool GRMHDStreamer::init() {
    // 1. Parse JSON metadata (nubhlight_pack schema_version 1)
    {
        std::ifstream jf(metadata_.jsonPath);
        if (!jf.is_open()) {
            return false;  // JSON not found -- no dataset loaded
        }

        json doc;
        try {
            jf >> doc;
        } catch (const json::parse_error&) {
            return false;
        }

        // WHY: schema_version field guards against future format changes.
        int const schemaVer = doc.value("schema_version", 0);
        if (schemaVer < 1) {
            return false;
        }

        // Resolve binary path: prefer JSON "bin" field, fall back to
        // the binPath passed in the constructor.
        if (doc.contains("bin") && doc.at("bin").is_string()) {
            std::string binRelative = doc.at("bin").get<std::string>();
            // If relative, resolve against the JSON directory.
            if (!binRelative.empty() && binRelative.front() != '/') {
                auto dir = metadata_.jsonPath.rfind('/');
                if (dir != std::string::npos) {
                    binRelative = metadata_.jsonPath.substr(0, dir + 1) + binRelative;
                }
            }
            metadata_.binPath = binRelative;
        }

        // Grid dimensions: "grid_dims": [X, Y, Z]
        if (doc.contains("grid_dims") && doc.at("grid_dims").is_array()
                && doc.at("grid_dims").size() >= 3) {
            metadata_.gridX = doc.at("grid_dims").at(0).get<size_t>();
            metadata_.gridY = doc.at("grid_dims").at(1).get<size_t>();
            metadata_.gridZ = doc.at("grid_dims").at(2).get<size_t>();
        } else {
            return false;
        }

        // Channel names
        if (doc.contains("channels") && doc.at("channels").is_array()) {
            metadata_.channels.clear();
            for (const auto& ch : doc.at("channels")) {
                metadata_.channels.push_back(ch.get<std::string>());
            }
        }

        // nubhlight_pack writes a single dataset snapshot per file, not a
        // time-series.  Treat it as a single frame at time 0.
        // A future multi-frame format can add "frames": [...] to the JSON.
        if (doc.contains("frames") && doc.at("frames").is_array()) {
            metadata_.frames.clear();
            for (const auto& fr : doc.at("frames")) {
                GRMHDFrame frame{};
                frame.frameIndex = fr.value("index",  0u);
                frame.time       = fr.value("time",   0.0);
                frame.byteOffset = fr.value("offset", static_cast<size_t>(0));
                frame.byteSize   = fr.value("size",   static_cast<size_t>(0));
                metadata_.frames.push_back(frame);
            }
        } else {
            // Single-frame: the whole binary file is frame 0
            GRMHDFrame frame0{};
            frame0.frameIndex = 0;
            frame0.time       = 0.0;
            frame0.byteOffset = 0;
            // byteSize is determined when we open the binary below
            metadata_.frames.push_back(frame0);
        }
        metadata_.frameCount = metadata_.frames.size();
    }

    // 2. Open binary file and determine frame byte sizes
    {
        std::ifstream binCheck(metadata_.binPath, std::ios::binary | std::ios::ate);
        if (!binCheck.is_open()) {
            // Binary file not present -- streaming unavailable, not an error
            // if the caller will provide data another way.
            metadata_.frameCount = 0;
        } else {
          std::streamsize const binSize = binCheck.tellg();
          if (metadata_.frames.size() == 1 && metadata_.frames.at(0).byteSize == 0) {
            metadata_.frames.at(0).byteSize = static_cast<size_t>(binSize);
          }
        }
    }

    // 3. Start background loader thread
    running_ = true;
    loaderThread_ = std::thread(&GRMHDStreamer::loaderThreadFunc, this);

    return true;
}

void GRMHDStreamer::shutdown() {
    {
      std::scoped_lock const lk(queueMutex_);
      running_ = false;
    }
    queueCV_.notify_all();
    if (loaderThread_.joinable()) {
        loaderThread_.join();
    }
}

// ---------------------------------------------------------------------------
// Playback control
// ---------------------------------------------------------------------------

void GRMHDStreamer::seekFrame(uint32_t frameIndex) {
    currentFrame_ = frameIndex;
    // Prefetch: enqueue the next N_PREFETCH frames so they are warm in cache.
    static constexpr uint32_t nPrefetch = 3;
    for (uint32_t i = 1; i <= nPrefetch; ++i) {
      uint32_t const nextFrame = frameIndex + i;
      if (nextFrame < static_cast<uint32_t>(metadata_.frameCount)) {
        TileID const id{.frame = nextFrame, .x = 0, .y = 0, .z = 0, .level = 0};
        if (!cache_.get(id)) {
          std::scoped_lock const lk(queueMutex_);
          loadQueue_.push(id);
          queueCV_.notify_one();
        }
      }
    }
}

void GRMHDStreamer::setPlaybackSpeed(double speed) {
    playbackSpeed_ = speed;
}

void GRMHDStreamer::play() {
    playing_ = true;
}

void GRMHDStreamer::pause() {
    playing_ = false;
}

// ---------------------------------------------------------------------------
// getTile(): check cache; on miss, enqueue async load and return nullptr.
// ---------------------------------------------------------------------------

std::shared_ptr<GRMHDTile> GRMHDStreamer::getTile(uint16_t x, uint16_t y,
                                                    uint16_t z, uint8_t level) {
  TileID const id{.frame = currentFrame_.load(), .x = x, .y = y, .z = z, .level = level};

  auto tile = cache_.get(id);
  if (tile) {
    return tile;
  }

    // Queue an async load for this tile
    {
      std::scoped_lock const lk(queueMutex_);
      loadQueue_.push(id);
    }
    queueCV_.notify_one();
    return nullptr;
}

double GRMHDStreamer::cacheHitRate() const noexcept {
    return static_cast<double>(cache_.hitRate()) / 100.0;
}

size_t GRMHDStreamer::queueDepth() const noexcept {
  std::scoped_lock const lk(queueMutex_);
  return loadQueue_.size();
}

// ---------------------------------------------------------------------------
// loaderThreadFunc(): drain the work queue in a background thread.
// ---------------------------------------------------------------------------

void GRMHDStreamer::loaderThreadFunc() {
    while (true) {
        TileID id{};
        {
            std::unique_lock<std::mutex> lk(queueMutex_);
            queueCV_.wait(lk, [this] {
                return !running_.load() || !loadQueue_.empty();
            });
            if (!running_.load() && loadQueue_.empty()) {
                break;
            }
            if (loadQueue_.empty()) {
              continue;
            }
            id = loadQueue_.front();
            loadQueue_.pop();
        }

        // Check cache again -- another thread may have loaded it already.
        if (cache_.get(id)) {
          continue;
        }

        auto tile = loadTile(id);
        if (tile) {
            cache_.put(id, tile);
        }
    }
}

// ---------------------------------------------------------------------------
// loadTile(): read a single tile from the binary file.
//
// WHY: For the nubhlight_pack single-frame format the "tile" is the entire
// frame slab.  A future multi-frame streaming format can split frames into
// spatial tiles here.
// ---------------------------------------------------------------------------

std::shared_ptr<GRMHDTile> GRMHDStreamer::loadTile(const TileID& id) {
  uint32_t const frame = id.frame;
  if (frame >= static_cast<uint32_t>(metadata_.frames.size())) {
    return nullptr;
  }
    const GRMHDFrame& fi = metadata_.frames.at(frame);
    if (fi.byteSize == 0 || metadata_.binPath.empty()) {
        return nullptr;
    }

    std::ifstream bin(metadata_.binPath, std::ios::binary);
    if (!bin.is_open()) {
        return nullptr;
    }

    // Seek to the frame's byte offset in the binary
    bin.seekg(static_cast<std::streamoff>(fi.byteOffset));
    if (!bin.good()) {
        return nullptr;
    }

    // Compute voxel count and RGBA32F element count
    size_t const voxels = metadata_.gridX * metadata_.gridY * metadata_.gridZ;
    size_t const nChannels = 4; // RGBA32F always 4 channels
    size_t const nFloats = voxels * nChannels;
    size_t const expectedBytes = nFloats * sizeof(float);

    // Guard: only read as many bytes as available in the frame slab
    size_t const readBytes = std::min(expectedBytes, fi.byteSize);
    size_t const readFloats = readBytes / sizeof(float);

    auto tile = std::make_shared<GRMHDTile>();
    tile->id     = id;
    tile->width  = metadata_.gridX;
    tile->height = metadata_.gridY;
    tile->depth  = metadata_.gridZ;
    tile->data.resize(readFloats, 0.0f);

    // Read the raw float data
    bin.read(reinterpret_cast<char *>(tile->data.data()), static_cast<std::streamsize>(readBytes));

    if (!bin) {
        // Partial read -- fill remainder with zero (already done by resize)
        tile->data.resize(nFloats, 0.0f);
    }

    return tile;
}

} // namespace blackhole
