/**
 * @file grmhd_streaming.cpp
 * @brief Implementation of GRMHD metadata, tile caching, and GPU pipeline
 */

#include "grmhd_streaming.h"

#include <algorithm>
#include <fstream>
#include <iostream>
#include <sstream>

namespace grmhd {

// ============================================================================
// TileCache Implementation
// ============================================================================

TileCache::TileCache(uint32_t maxTiles)
    : maxTiles_(maxTiles) {}

TileCache::~TileCache() = default;

std::optional<std::shared_ptr<GRMHDTile>>
TileCache::getTile(uint32_t x, uint32_t y, uint32_t dumpIdx) {
    auto key = std::make_tuple(x, y, dumpIdx);
    auto it = tiles_.find(key);

    if (it != tiles_.end()) {
        // Cache hit: update LRU and return
        it->second->accessTime = std::chrono::high_resolution_clock::now();
        hitCount_++;
        return it->second;
    }

    // Cache miss
    missCount_++;
    return std::nullopt;
}

void TileCache::insertTile(std::shared_ptr<GRMHDTile> tile) {
    if (!tile) return;

    auto key = std::make_tuple(tile->tileX, tile->tileY, tile->dumpIndex);
    tiles_[key] = tile;
    lruOrder_.push_back(key);

    // Evict if over capacity
    while (tiles_.size() > maxTiles_) {
        evictLRU();
    }
}

void TileCache::evictLRU() {
    if (lruOrder_.empty()) return;

    // Find least recently used tile
    auto minTime = std::chrono::high_resolution_clock::now();
    size_t minIdx = 0;

    for (size_t i = 0; i < lruOrder_.size(); ++i) {
        const auto& key = lruOrder_[i];
        auto it = tiles_.find(key);
        if (it != tiles_.end() && it->second->accessTime < minTime) {
            minTime = it->second->accessTime;
            minIdx = i;
        }
    }

    // Evict the LRU tile
    if (minIdx < lruOrder_.size()) {
        const auto& lruKey = lruOrder_[minIdx];
        tiles_.erase(lruKey);
        lruOrder_.erase(lruOrder_.begin() + minIdx);
    }
}

// ============================================================================
// GRMHDReader Implementation
// ============================================================================

GRMHDReader::GRMHDReader(const std::string& metadataPath)
    : basePath_(metadataPath) {}

GRMHDReader::~GRMHDReader() = default;

bool GRMHDReader::loadSequenceMetadata(const std::string& jsonPath) {
    std::ifstream file(jsonPath);
    if (!file.is_open()) {
        std::cerr << "Failed to open metadata file: " << jsonPath << "\n";
        return false;
    }

    std::stringstream buffer;
    buffer << file.rdbuf();
    std::string jsonContent = buffer.str();

    return parseJsonMetadata(jsonContent);
}

bool GRMHDReader::parseJsonMetadata(const std::string& jsonContent) {
    // Simple JSON parsing for metadata
    // Expected format:
    // {
    //   "name": "M87 simulation",
    //   "dumps": [
    //     {
    //       "time": 0.0,
    //       "file": "dump_0000.h5",
    //       "dataset": "/primitives",
    //       "grid": {"nx": 128, "ny": 128, "nz": 128, ...},
    //       "variables": ["rho", "uu", "u1", "u2", "u3", "B1", "B2", "B3"]
    //     },
    //     ...
    //   ]
    // }

    sequence_.sequenceName = "GRMHD Sequence";
    sequence_.dumpCount = 0;
    sequence_.tStart = 0.0;
    sequence_.tEnd = 0.0;
    sequence_.estimatedTotalSize = 0;

    // Placeholder: full JSON parsing would use nlohmann/json library
    // For now, return true (indicating successful parse structure)
    // Phase 6.2a extended will add full nlohmann/json integration

    return true;  // Indicates phase 6.2a skeleton complete
}

DumpMetadata GRMHDReader::parseDumpEntry(const std::string& jsonEntry) {
    DumpMetadata dump;
    // Placeholder for JSON entry parsing
    // Full implementation will extract:
    // - time
    // - filepath
    // - grid dimensions (nx, ny, nz)
    // - variable list
    return dump;
}

std::optional<DumpMetadata>
GRMHDReader::getDumpMetadata(size_t dumpIndex) const {
    if (dumpIndex >= sequence_.dumps.size()) {
        return std::nullopt;
    }
    return sequence_.dumps[dumpIndex];
}

std::optional<DumpMetadata>
GRMHDReader::getDumpAtTime(double time) const {
    auto it = sequence_.timeIndex.find(time);
    if (it == sequence_.timeIndex.end()) {
        return std::nullopt;
    }
    return sequence_.dumps[it->second];
}

bool GRMHDReader::readHDF5Dump(size_t dumpIndex, std::vector<float>& buffer) {
    // Placeholder: HDF5 file reading
    // Phase 6.2a extended will integrate highfive library:
    // 1. Open HDF5 file from dumps[dumpIndex].filepath
    // 2. Read dataset at dumps[dumpIndex].datasetName
    // 3. Populate buffer with float array

    if (dumpIndex >= sequence_.dumps.size()) {
        return false;
    }

    // Allocate buffer based on grid dimensions
    const auto& dump = sequence_.dumps[dumpIndex];
    uint32_t totalCells = dump.grid.nx * dump.grid.ny * dump.grid.nz;
    uint32_t varsPerCell = dump.variables.varCount;
    buffer.resize(totalCells * varsPerCell, 0.0f);

    return true;  // Placeholder: success
}

bool GRMHDReader::readHDF5Variable(size_t dumpIndex, const std::string& varName,
                                   std::vector<float>& buffer) {
    // Placeholder: selective HDF5 variable reading
    if (dumpIndex >= sequence_.dumps.size()) {
        return false;
    }

    buffer.clear();
    return true;  // Placeholder: success
}

// ============================================================================
// GRMHDPipeline Implementation
// ============================================================================

GRMHDPipeline::GRMHDPipeline(uint32_t maxConcurrentUploads)
    : maxConcurrentUploads_(maxConcurrentUploads) {}

GRMHDPipeline::~GRMHDPipeline() = default;

void GRMHDPipeline::queueTileUpload(std::shared_ptr<GRMHDTile> tile) {
    if (!tile) return;

    pendingUploads_.push_back(tile);

    // If over capacity, wait for uploads to complete
    if (pendingUploads_.size() > maxConcurrentUploads_) {
        waitForCompletion();
    }
}

void GRMHDPipeline::waitForCompletion() {
    // Placeholder: GPU fence synchronization
    // Phase 6.2b extended will:
    // 1. Poll GPU fence for each pending tile
    // 2. Mark tile as gpuResident when transfer complete
    // 3. Clear pendingUploads_ on completion

    pendingUploads_.clear();
}

} // namespace grmhd

