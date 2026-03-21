/*
 * grmhd_streamer_test.cpp
 * End-to-end validation of GRMHDStreamer: JSON parse, binary load,
 * background tile loading, LRU cache hit, getAdjacentTile, and prefetch.
 *
 * WHY: GRMHDStreamer bridges the CPU streaming path and the CUDA/GL upload
 *      pipeline.  C1d temporal interpolation relies on getTile() +
 *      getAdjacentTile() returning consistent RGBA32F data from adjacent frames.
 *      This test verifies the full load -> stream -> cache cycle using
 *      deterministic synthetic data so failures are reproducible without a
 *      real GRMHD dataset.
 *
 * WHAT: Writes a synthetic nubhlight_pack JSON + flat binary to /tmp, creates
 *       a real GRMHDStreamer, and validates:
 *       1. init() parses metadata correctly (grid dims, frame count)
 *       2. seekFrame(0) + getTile() returns tile with correct dims and data
 *       3. Frame 0 data (all 1.0f) differs from frame 1 data (all 2.0f)
 *       4. getAdjacentTile() returns the frame+1 tile from the prefetch cache
 *       5. cacheHitRate() is > 0 after multiple successful tile accesses
 *       6. shutdown() joins the loader thread cleanly
 *
 * HOW: Standalone assert-based test (no external test framework required).
 *      Polls getTile() with a bounded retry loop (50 x 10ms = 500ms max) to
 *      allow the background loader thread to complete without busy-waiting.
 */

#include <cassert>
#include <chrono>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <thread>
#include <vector>

#include <unistd.h>  // getpid

#include "grmhd_streaming.h"

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

namespace {

/* Write a minimal nubhlight_pack-compatible JSON file. */
void writeJson(const std::string &path, const std::string &binRelPath,
               size_t frame0Bytes, size_t frame1Bytes) {
    std::ofstream f(path);
    assert(f.is_open());
    // NOLINTNEXTLINE(modernize-raw-string-literal)
    f << "{\n"
      << R"(  "schema_version": 1,)" << "\n"
      << R"(  "grid_dims": [4, 4, 4],)" << "\n"
      << R"(  "channels": ["rho", "u", "v1", "v2"],)" << "\n"
      << R"(  "format": "rgba32f",)" << "\n"
      << R"(  "bin": ")" << binRelPath << "\",\n"
      << R"(  "frames": [)" << "\n"
      << R"(    {"index": 0, "time": 0.0, "offset": 0,)"
      << "    \"size\": " << frame0Bytes << "},\n"
      << R"(    {"index": 1, "time": 1.0, "offset": )" << frame0Bytes << ","
      << "    \"size\": " << frame1Bytes << "}\n"
      << "  ]\n"
      << "}\n";
}

/* Write the flat binary: frame0 all 1.0f, frame1 all 2.0f. */
void writeBin(const std::string &path, size_t floatsPerFrame) {
    std::vector<float> frame0(floatsPerFrame, 1.0f);
    std::vector<float> frame1(floatsPerFrame, 2.0f);

    std::ofstream f(path, std::ios::binary);
    assert(f.is_open());
    f.write(reinterpret_cast<const char *>(frame0.data()),
            static_cast<std::streamsize>(floatsPerFrame * sizeof(float)));
    f.write(reinterpret_cast<const char *>(frame1.data()),
            static_cast<std::streamsize>(floatsPerFrame * sizeof(float)));
}

/* Poll getTile() until it returns a non-null result or we time out. */
std::shared_ptr<blackhole::GRMHDTile>
pollTile(blackhole::GRMHDStreamer &streamer, int maxRetries = 50,
         int sleepMs = 10) {
    for (int i = 0; i < maxRetries; ++i) {
        auto tile = streamer.getTile(0, 0, 0, 0);
        if (tile) {
            return tile;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(sleepMs));
    }
    return nullptr;
}

// ---------------------------------------------------------------------------
// Tests (kept in anonymous namespace to satisfy misc-use-anonymous-namespace)
// ---------------------------------------------------------------------------

// Test: metadata parsed correctly
int testMetadata(const std::string &jsonPath, const std::string &binPath) {
    blackhole::GRMHDStreamer streamer(jsonPath, binPath);
    if (!streamer.init()) {
        std::cerr << "FAIL testMetadata: init() returned false\n";
        return 1;
    }

    const auto &meta = streamer.metadata();
    if (meta.gridX != 4 || meta.gridY != 4 || meta.gridZ != 4) {
        std::cerr << "FAIL testMetadata: expected grid 4x4x4, got "
                  << meta.gridX << "x" << meta.gridY << "x" << meta.gridZ << "\n";
        return 1;
    }
    if (meta.frameCount != 2) {
        std::cerr << "FAIL testMetadata: expected 2 frames, got " << meta.frameCount << "\n";
        return 1;
    }
    if (meta.channels.size() != 4) {
        std::cerr << "FAIL testMetadata: expected 4 channels, got " << meta.channels.size() << "\n";
        return 1;
    }

    streamer.shutdown();
    std::cout << "PASS testMetadata\n";
    return 0;
}

// Test: getTile() returns correct data for frame 0
int testFrame0Data(const std::string &jsonPath, const std::string &binPath) {
    blackhole::GRMHDStreamer streamer(jsonPath, binPath);
    if (!streamer.init()) {
        std::cerr << "FAIL testFrame0Data: init() returned false\n";
        return 1;
    }

    streamer.seekFrame(0);
    auto tile = pollTile(streamer);
    if (!tile) {
        std::cerr << "FAIL testFrame0Data: tile never loaded within timeout\n";
        return 1;
    }

    if (tile->width != 4 || tile->height != 4 || tile->depth != 4) {
        std::cerr << "FAIL testFrame0Data: tile dims "
                  << tile->width << "x" << tile->height << "x" << tile->depth
                  << " != 4x4x4\n";
        return 1;
    }

    /* Frame 0 binary is all 1.0f */
    for (size_t i = 0; i < tile->data.size(); ++i) {
        if (tile->data.at(i) != 1.0f) {
            std::cerr << "FAIL testFrame0Data: data[" << i << "]="
                      << tile->data.at(i) << " != 1.0f\n";
            return 1;
        }
    }

    streamer.shutdown();
    std::cout << "PASS testFrame0Data\n";
    return 0;
}

// Test: frame 1 data differs from frame 0
int testFrame1Distinct(const std::string &jsonPath, const std::string &binPath) {
    blackhole::GRMHDStreamer streamer(jsonPath, binPath);
    if (!streamer.init()) {
        std::cerr << "FAIL testFrame1Distinct: init() returned false\n";
        return 1;
    }

    streamer.seekFrame(1);
    auto tile = pollTile(streamer);
    if (!tile) {
        std::cerr << "FAIL testFrame1Distinct: frame 1 tile never loaded within timeout\n";
        return 1;
    }

    if (tile->data.empty()) {
        std::cerr << "FAIL testFrame1Distinct: tile data is empty\n";
        return 1;
    }

    /* Frame 1 binary is all 2.0f -- differs from frame 0 (all 1.0f) */
    for (size_t i = 0; i < tile->data.size(); ++i) {
        if (tile->data.at(i) != 2.0f) {
            std::cerr << "FAIL testFrame1Distinct: data[" << i << "]="
                      << tile->data.at(i) << " != 2.0f\n";
            return 1;
        }
    }

    streamer.shutdown();
    std::cout << "PASS testFrame1Distinct\n";
    return 0;
}

// Test: getAdjacentTile() returns frame+1 after seekFrame(0)
int testAdjacentTile(const std::string &jsonPath, const std::string &binPath) {
    blackhole::GRMHDStreamer streamer(jsonPath, binPath);
    if (!streamer.init()) {
        std::cerr << "FAIL testAdjacentTile: init() returned false\n";
        return 1;
    }

    streamer.seekFrame(0);

    /* Wait for current frame tile to be loaded -- this also warms the prefetch
     * queue that seekFrame() enqueues for frames 1, 2, 3. */
    auto tile0 = pollTile(streamer);
    if (!tile0) {
        std::cerr << "FAIL testAdjacentTile: frame 0 tile never loaded\n";
        return 1;
    }

    /* Poll getAdjacentTile() -- frame 1 should be in cache via prefetch */
    std::shared_ptr<blackhole::GRMHDTile> adjTile;
    for (int i = 0; i < 50; ++i) {
        adjTile = streamer.getAdjacentTile(0, 0, 0, 0);
        if (adjTile) {
            break;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(10));
    }

    if (!adjTile) {
        std::cerr << "FAIL testAdjacentTile: adjacent tile (frame 1) never available\n";
        return 1;
    }

    /* Adjacent tile (frame 1) must contain all 2.0f */
    for (size_t i = 0; i < adjTile->data.size(); ++i) {
        if (adjTile->data.at(i) != 2.0f) {
            std::cerr << "FAIL testAdjacentTile: adjacent data[" << i << "]="
                      << adjTile->data.at(i) << " != 2.0f\n";
            return 1;
        }
    }

    /* Adjacent tile must differ from frame 0 */
    if (tile0->data.at(0) == adjTile->data.at(0)) {
        std::cerr << "FAIL testAdjacentTile: frame 0 and adjacent tile have same data[0]\n";
        return 1;
    }

    streamer.shutdown();
    std::cout << "PASS testAdjacentTile\n";
    return 0;
}

// Test: cacheHitRate() > 0 after re-requesting a cached tile
int testCacheHitRate(const std::string &jsonPath, const std::string &binPath) {
    blackhole::GRMHDStreamer streamer(jsonPath, binPath);
    if (!streamer.init()) {
        std::cerr << "FAIL testCacheHitRate: init() returned false\n";
        return 1;
    }

    streamer.seekFrame(0);

    /* Warm the cache */
    auto tile = pollTile(streamer);
    if (!tile) {
        std::cerr << "FAIL testCacheHitRate: tile never loaded\n";
        return 1;
    }

    /* Second request must be a cache hit */
    auto tile2 = streamer.getTile(0, 0, 0, 0);
    if (!tile2) {
        std::cerr << "FAIL testCacheHitRate: second getTile() returned null (expected cache hit)\n";
        return 1;
    }

    const double hitRate = streamer.cacheHitRate();
    if (hitRate <= 0.0) {
        std::cerr << "FAIL testCacheHitRate: cacheHitRate=" << hitRate << " (expected > 0)\n";
        return 1;
    }

    streamer.shutdown();
    std::cout << "PASS testCacheHitRate (hitRate=" << hitRate << ")\n";
    return 0;
}

// Test: getAdjacentTile() at last frame returns nullptr
int testAdjacentTileAtLastFrame(const std::string &jsonPath,
                                 const std::string &binPath) {
    blackhole::GRMHDStreamer streamer(jsonPath, binPath);
    if (!streamer.init()) {
        std::cerr << "FAIL testAdjacentTileAtLastFrame: init() returned false\n";
        return 1;
    }

    /* Seek to last frame (index 1 out of 2) */
    streamer.seekFrame(1);

    /* getAdjacentTile() at the last frame must return nullptr immediately */
    auto adj = streamer.getAdjacentTile(0, 0, 0, 0);
    if (adj != nullptr) {
        std::cerr << "FAIL testAdjacentTileAtLastFrame: expected nullptr at last frame, got tile\n";
        return 1;
    }

    streamer.shutdown();
    std::cout << "PASS testAdjacentTileAtLastFrame\n";
    return 0;
}

// Test: init() returns false for missing JSON
int testMissingJson() {
    blackhole::GRMHDStreamer streamer("/tmp/does_not_exist_grmhd_42.json", "");
    if (streamer.init()) {
        std::cerr << "FAIL testMissingJson: init() should return false for missing JSON\n";
        /* Shut down cleanly even if init returned true unexpectedly */
        streamer.shutdown();
        return 1;
    }
    std::cout << "PASS testMissingJson\n";
    return 0;
}

} // namespace

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

int main() {
    /* Unique temp prefix per process to avoid test parallelism collisions */
    const std::string base     = "/tmp/grmhd_streamer_test_" + std::to_string(getpid());
    const std::string jsonPath = base + ".json";
    const std::string binPath  = base + ".bin";

    /* 4x4x4 grid x 4 channels = 256 floats = 1024 bytes per frame */
    constexpr size_t floatsPerFrame = static_cast<size_t>(4) * 4 * 4 * 4;
    constexpr size_t bytesPerFrame  = floatsPerFrame * sizeof(float);

    /* Write synthetic dataset */
    writeJson(jsonPath, binPath, bytesPerFrame, bytesPerFrame);
    writeBin(binPath, floatsPerFrame);

    int failures = 0;
    failures += testMetadata(jsonPath, binPath);
    failures += testFrame0Data(jsonPath, binPath);
    failures += testFrame1Distinct(jsonPath, binPath);
    failures += testAdjacentTile(jsonPath, binPath);
    failures += testCacheHitRate(jsonPath, binPath);
    failures += testAdjacentTileAtLastFrame(jsonPath, binPath);
    failures += testMissingJson();

    /* Cleanup temp files (ignore return value -- best-effort) */
    (void)std::remove(jsonPath.c_str());
    (void)std::remove(binPath.c_str());

    if (failures == 0) {
        std::cout << "All grmhd_streamer tests passed.\n";
        return 0;
    }
    std::cerr << failures << " test(s) failed.\n";
    return 1;
}
