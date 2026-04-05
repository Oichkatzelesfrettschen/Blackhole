/**
 * @file grmhd_gpu_uploader.h
 * @brief Async transfer queue: GRMHDStreamer tiles -> GPU 3D texture.
 *
 * WHY: After GRMHDStreamer's background thread loads a tile into CPU RAM the
 *      data must reach the GPU before the shader can sample it.  This class
 *      bridges the tile cache to the existing double-buffered PBO uploader
 *      (GrmhdPBOUploader) so the transfer is non-blocking on the render thread.
 *
 *      This is roadmap item 6.2.4 "Async transfer queue (post-tile-loading)".
 *
 * WHAT: On each render frame the host calls uploadPendingTiles().  The method:
 *   1. Calls streamer.getTile(0,0,0,0) for the current frame.
 *   2. If the tile is ready, packs its data into RGBA32F and calls
 *      pboUploader_.upload() -- the double-buffered PBO path in
 *      GrmhdPBOUploader hands off to the GPU asynchronously.
 *   3. Returns the count of tiles transferred this call.
 *
 * HOW (integration with GrmhdPBOUploader):
 *   - For full-frame tiles (width x height x depth == grid dimensions):
 *     delegate directly to GrmhdPBOUploader::upload() (0-copy packing).
 *   - For sub-tiles (future multi-tile streaming):
 *     pack into a staging buffer and call glTexSubImage3D with a bound PBO.
 *
 * Thread safety: all public methods are render-thread only.
 *
 * References:
 *   - grmhd_pbo_uploader.h   (the low-level double-buffered PBO primitive)
 *   - grmhd_streaming.h      (GRMHDStreamer tile cache interface)
 *   - OpenGL 4.6 spec 8.4.2  (Pixel Buffer Objects)
 */

#pragma once

#include <cstddef>
#include <vector>

#include "../grmhd_pbo_uploader.h"
#include "../grmhd_streaming.h"

namespace gpu {

/**
 * @brief Transfer queue that moves ready GRMHDStreamer tiles to the GPU.
 *
 * Owns a GrmhdPBOUploader (the 3D texture + PBO pool) and a staging buffer
 * used when tile dimensions differ from the full texture (sub-tile path).
 *
 * Typical usage:
 * @code
 *   GRMHDGpuUploader uploader(streamer);
 *   uploader.init(meta.gridX, meta.gridY, meta.gridZ);
 *   // ... render loop ...
 *   uploader.uploadPendingTiles();
 *   glBindTexture(GL_TEXTURE_3D, uploader.texture3D());
 * @endcode
 */
class GRMHDGpuUploader {
public:
    /**
     * @brief Construct with a reference to an initialized GRMHDStreamer.
     *
     * @param streamer GRMHD tile source.  Must outlive this object.
     */
    explicit GRMHDGpuUploader(blackhole::GRMHDStreamer& streamer);

    /** @brief Calls shutdown() before destruction. */
    ~GRMHDGpuUploader();

    // Non-copyable, non-movable (owns GL objects).
    GRMHDGpuUploader(const GRMHDGpuUploader&) = delete;
    GRMHDGpuUploader& operator=(const GRMHDGpuUploader&) = delete;

    /**
     * @brief Allocate the 3D texture and PBO pool.
     *
     * Must be called from the render thread with a current GL context.
     * Dimensions should match the GRMHD grid (metadata.gridX/Y/Z).
     *
     * @param width  GRMHD root-grid X size.
     * @param height GRMHD root-grid Y size.
     * @param depth  GRMHD root-grid Z size.
     * @return true on success.
     */
    bool init(int width, int height, int depth);

    /**
     * @brief Check the streamer for ready tiles and upload up to maxPerFrame.
     *
     * Full-frame tiles (covering the entire grid) are handed to
     * GrmhdPBOUploader::upload() directly.  Sub-tile uploads are packed into
     * the staging buffer and transferred via glTexSubImage3D.
     *
     * @param maxPerFrame Maximum number of tiles to upload per call (default 1
     *                    since most GRMHD frames are single-tile full-frame).
     * @return Number of tiles uploaded this call.
     */
    int uploadPendingTiles(int maxPerFrame = 1);

    /**
     * @brief The GL_TEXTURE_3D texture handle.
     *
     * Bind to a texture unit before each draw call:
     *   glActiveTexture(GL_TEXTURE0 + unit);
     *   glBindTexture(GL_TEXTURE_3D, uploader.texture3D());
     *   glUniform1i(uniformLoc, unit);
     *
     * @return GLuint handle, or 0 if not initialized.
     */
    [[nodiscard]] GLuint texture3D() const noexcept {
        return pboUploader_.texture();
    }

    /** @brief True once at least one tile has been uploaded. */
    [[nodiscard]] bool ready() const noexcept {
        return pboUploader_.ready();
    }

    /** @brief Total tiles uploaded since init(). */
    [[nodiscard]] int tilesUploaded() const noexcept { return tilesUploaded_; }

    /** @brief Release all GL resources. Safe to call multiple times. */
    void shutdown();

    /** @brief True if init() succeeded. */
    [[nodiscard]] bool initialized() const noexcept { return initialized_; }

private:
    blackhole::GRMHDStreamer& streamer_;
    blackhole::GrmhdPBOUploader pboUploader_;

    int texWidth_  = 0;
    int texHeight_ = 0;
    int texDepth_  = 0;

    bool initialized_   = false;
    int  tilesUploaded_ = 0;

    // Staging buffer for sub-tile packing (reused across calls to avoid
    // repeated allocations on frames with multiple tiles).
    std::vector<float> stagingBuf_;

    /**
     * @brief Pack GRMHDTile data into RGBA32F staging buffer.
     *
     * Channel layout: R=rho, G=uu, B=|B|, A=|u|.
     * If the tile is already 4-channel RGBA32F (nubhlight_pack format) the
     * data is copied without reinterpretation.
     *
     * @param tile     Ready tile to pack.
     * @param dst      Destination float buffer (4 * nVoxels entries).
     * @param nVoxels  Total voxel count (tile.width * height * depth).
     */
    static void packRGBA(const blackhole::GRMHDTile& tile,
                         float* dst, std::size_t nVoxels);
};

} // namespace gpu
