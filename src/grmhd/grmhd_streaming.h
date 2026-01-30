/**
 * @file grmhd_streaming.h
 * @brief GRMHD magnetohydrodynamics time-series streaming and GPU pipeline
 *
 * Phase 6.2a: GRMHD metadata parsing and file I/O for multi-dump time series
 * - JSON metadata parsing (dump times, grid dims, variable names)
 * - HDF5 multi-dump file reading with incremental loading
 * - Tile-based caching (32x32 pixel footprints)
 * - Async GPU upload via PBO (pixel buffer object)
 *
 * Data Flow:
 * 1. Load metadata JSON (lists all HDF5 dumps with timestamps)
 * 2. Index HDF5 files (time, resolution, variables)
 * 3. On-demand tile loading (LRU cache with eviction)
 * 4. GPU memcpy via PBO for async readback overlap
 * 5. GLSL octree traversal for raytracing through cell data
 */

#pragma once

#include <string>
#include <vector>
#include <map>
#include <memory>
#include <optional>
#include <chrono>
#include <cstdint>

namespace grmhd {

// ============================================================================
// GRMHD Metadata Structures
// ============================================================================

/**
 * Dump metadata: one GRMHD snapshot from HDF5 file
 * Tracks: time coordinate, grid dimensions, variable names, file location
 */
struct DumpMetadata {
    double time;                        // Simulation time (gravitational units)
    std::string filepath;               // HDF5 file path
    std::string datasetName;            // HDF5 dataset path (e.g., "/primitives")

    struct GridInfo {
        uint32_t nx, ny, nz;            // Grid dimensions
        double xmin, xmax;              // Boyer-Lindquist r range
        double ymin, ymax;              // Boyer-Lindquist theta range
        double zmin, zmax;              // Boyer-Lindquist phi range
    } grid;

    struct Variables {
        std::vector<std::string> names; // ["rho", "uu", "u1", "u2", "u3", "B1", "B2", "B3"]
        std::vector<uint32_t> indices;  // Indices into HDF5 dataset
        uint32_t varCount;              // Total variable count
    } variables;

    bool valid = false;                 // Metadata successfully loaded
};

/**
 * Sequence metadata: all dumps in a simulation
 * Loaded from JSON file describing multi-dump time series
 */
struct SequenceMetadata {
    std::string sequenceName;
    std::string description;
    std::vector<DumpMetadata> dumps;

    // Lookup helpers
    std::map<double, size_t> timeIndex;     // time -> dump index
    std::map<std::string, size_t> filenameIndex;  // filename -> dump index

    // Statistics
    double tStart, tEnd;
    uint32_t dumpCount;
    size_t estimatedTotalSize;              // Bytes
};

// ============================================================================
// Tile-Based GPU Streaming Cache
// ============================================================================

/**
 * Tile: 32x32 pixel footprint for one GRMHD cell (or interpolated region)
 * Cached in LRU order; evicted when capacity exceeded
 */
struct GRMHDTile {
    uint32_t tileX, tileY;              // Position in tile grid (0-based)
    uint32_t dumpIndex;                 // Index into SequenceMetadata::dumps

    struct CellData {
        // Conservative variables (8 floats per cell)
        float rho, uu;                  // Density, internal energy density
        float u1, u2, u3;               // 3-velocity components (CONTRAVARIANT)
        float B1, B2, B3;               // Magnetic field (CONTRAVARIANT)
    };

    std::vector<CellData> data;         // 32*32 = 1024 cells

    // GPU resource
    uint32_t pboId;                     // Pixel buffer object ID
    bool gpuResident;                   // Cached on GPU

    std::chrono::high_resolution_clock::time_point accessTime;
};

/**
 * TileCache: LRU cache for GRMHD tiles
 * Holds at most MAX_TILES_CACHED (default 256 = ~32MB for floats)
 */
class TileCache {
public:
    static constexpr uint32_t MAX_TILES_CACHED = 256;

    explicit TileCache(uint32_t maxTiles = MAX_TILES_CACHED);
    ~TileCache();

    // Tile access
    std::optional<std::shared_ptr<GRMHDTile>> getTile(uint32_t x, uint32_t y, uint32_t dumpIdx);
    void insertTile(std::shared_ptr<GRMHDTile> tile);
    void evictLRU();

    // Statistics
    uint32_t getCurrentSize() const { return tiles_.size(); }
    uint32_t getHitCount() const { return hitCount_; }
    uint32_t getMissCount() const { return missCount_; }

private:
    std::map<std::tuple<uint32_t, uint32_t, uint32_t>, std::shared_ptr<GRMHDTile>> tiles_;
    std::vector<std::tuple<uint32_t, uint32_t, uint32_t>> lruOrder_;
    uint32_t maxTiles_;

    uint32_t hitCount_ = 0;
    uint32_t missCount_ = 0;
};

// ============================================================================
// GRMHD File I/O
// ============================================================================

/**
 * GRMHDReader: JSON metadata and HDF5 dump I/O
 * Implements Phase 6.2a: metadata parsing and multi-dump streaming
 */
class GRMHDReader {
public:
    explicit GRMHDReader(const std::string& metadataPath);
    ~GRMHDReader();

    // Load sequence metadata from JSON
    bool loadSequenceMetadata(const std::string& jsonPath);

    // Get metadata for specific dump
    std::optional<DumpMetadata> getDumpMetadata(size_t dumpIndex) const;
    std::optional<DumpMetadata> getDumpAtTime(double time) const;

    // Dump statistics
    size_t getDumpCount() const { return sequence_.dumps.size(); }
    double getTimeSpan() const { return sequence_.tEnd - sequence_.tStart; }

    // Low-level HDF5 I/O
    bool readHDF5Dump(size_t dumpIndex, std::vector<float>& buffer);
    bool readHDF5Variable(size_t dumpIndex, const std::string& varName,
                         std::vector<float>& buffer);

private:
    SequenceMetadata sequence_;
    std::string basePath_;

    // JSON parsing helpers
    bool parseJsonMetadata(const std::string& jsonContent);
    DumpMetadata parseDumpEntry(const std::string& jsonEntry);
};

// ============================================================================
// GPU Streaming Pipeline
// ============================================================================

/**
 * GRMHDPipeline: Async GPU upload of GRMHD data via PBO
 * Implements Phase 6.2b: overlaps CPU I/O with GPU uploads
 */
class GRMHDPipeline {
public:
    GRMHDPipeline(uint32_t maxConcurrentUploads = 4);
    ~GRMHDPipeline();

    // Queue tile for async GPU upload
    void queueTileUpload(std::shared_ptr<GRMHDTile> tile);

    // Wait for all pending uploads
    void waitForCompletion();

    // Check upload progress
    uint32_t getPendingCount() const { return pendingUploads_.size(); }

private:
    std::vector<std::shared_ptr<GRMHDTile>> pendingUploads_;
    uint32_t maxConcurrentUploads_;
};

} // namespace grmhd

