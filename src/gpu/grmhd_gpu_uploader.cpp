/**
 * @file grmhd_gpu_uploader.cpp
 * @brief Async transfer queue implementation: GRMHDStreamer tiles -> GPU.
 *
 * WHY: See grmhd_gpu_uploader.h.
 *
 * Full-frame path (most common):
 *   streamer_.getTile(0,0,0,0) returns a tile whose dimensions equal the full
 *   3D texture.  We call GrmhdPBOUploader::upload() with the tile's raw data
 *   pointer -- no staging copy needed, the PBO path handles it.
 *
 * Sub-tile path (future multi-tile datasets):
 *   tile dimensions < texture dimensions.  We copy into stagingBuf_ (packing
 *   7+ GRMHD channels into 4-channel RGBA32F), then call glTexSubImage3D with
 *   a bound PBO (via the pboUploader_'s underlying texture) at the tile's grid
 *   offset.  This path avoids uploading unchanged regions of the texture on
 *   every frame.
 *
 * HOW (packing):
 *   nubhlight_pack emits tiles as 4-channel RGBA32F: (rho, uu, v1, v2) per
 *   voxel.  If the tile has exactly 4 floats/voxel the data is used as-is.
 *   If the tile has 8 floats/voxel (full GRMHD variable set) we pack:
 *     R = rho    (rest-mass density)
 *     G = uu     (internal energy)
 *     B = |B|    = sqrt(B1^2 + B2^2 + B3^2)  (magnetic field magnitude)
 *     A = |u|    = sqrt(u1^2 + u2^2 + u3^2)  (3-velocity magnitude)
 *   These 4 channels are the minimum needed by grmhdEmission() /
 *   grmhdAbsorption() in grmhd_octree.glsl.
 */

// Include the GL loader before the project header so gl:: types are defined.
// NOLINTBEGIN(misc-include-cleaner)
#include "../gl_loader.h"
// NOLINTEND(misc-include-cleaner)

#include "grmhd_gpu_uploader.h"

#include <algorithm>
#include <cmath>
#include <cstring>

namespace gpu {

// ============================================================================
// Construction / destruction
// ============================================================================

GRMHDGpuUploader::GRMHDGpuUploader(blackhole::GRMHDStreamer& streamer)
    : streamer_(streamer) {}

GRMHDGpuUploader::~GRMHDGpuUploader() {
    shutdown();
}

// ============================================================================
// init()
// ============================================================================

bool GRMHDGpuUploader::init(int width, int height, int depth) {
    if (initialized_) shutdown();

    texWidth_  = width;
    texHeight_ = height;
    texDepth_  = depth;

    if (!pboUploader_.init(width, height, depth)) {
        return false;
    }

    initialized_   = true;
    tilesUploaded_ = 0;
    return true;
}

// ============================================================================
// shutdown()
// ============================================================================

void GRMHDGpuUploader::shutdown() {
    if (!initialized_) return;
    pboUploader_.shutdown();
    stagingBuf_.clear();
    stagingBuf_.shrink_to_fit();
    initialized_   = false;
    tilesUploaded_ = 0;
}

// ============================================================================
// uploadPendingTiles()
// ============================================================================

int GRMHDGpuUploader::uploadPendingTiles(int maxPerFrame) {
    if (!initialized_) return 0;

    const auto& meta = streamer_.metadata();
    if (meta.frameCount == 0) return 0;

    int uploaded = 0;

    // For the current implementation we treat each frame as a single tile
    // at grid coordinate (0, 0, 0), level 0.  This matches the nubhlight_pack
    // binary format which stores the full frame as one contiguous block.
    //
    // Future work: iterate over (x, y, z, level) sub-tiles when the dataset
    // uses multi-tile streaming with tiles smaller than the full grid.

    for (int attempt = 0; attempt < maxPerFrame; ++attempt) {
        auto tile = streamer_.getTile(0, 0, 0, 0);
        if (!tile || !tile->ready()) {
            break; // Background loader hasn't delivered data yet -- retry next frame
        }

        const std::size_t nVoxels =
            tile->width * tile->height * tile->depth;
        if (nVoxels == 0) break;

        const bool isFullFrame =
            (static_cast<int>(tile->width)  == texWidth_  &&
             static_cast<int>(tile->height) == texHeight_ &&
             static_cast<int>(tile->depth)  == texDepth_);

        if (isFullFrame && tile->data.size() == nVoxels * 4) {
            // Fast path: tile data is already RGBA32F for the full texture.
            // Delegate directly to the double-buffered PBO uploader.
            if (pboUploader_.upload(tile->data.data(), tile->data.size())) {
                ++uploaded;
                ++tilesUploaded_;
            }
        } else {
            // Packing path: channels > 4, or tile is a sub-region.
            // Pack into stagingBuf_ first.
            const std::size_t dstFloats = nVoxels * 4;
            stagingBuf_.resize(dstFloats);
            packRGBA(*tile, stagingBuf_.data(), nVoxels);

            if (isFullFrame) {
                // Full texture, packed -> delegate to PBO uploader.
                if (pboUploader_.upload(stagingBuf_.data(), dstFloats)) {
                    ++uploaded;
                    ++tilesUploaded_;
                }
            } else {
                // Sub-tile: upload to the sub-region of the existing texture.
                // Bind the uploader's texture and use glTexSubImage3D.
                // Note: this bypasses the PBO double-buffer for sub-tiles
                // (acceptable until multi-tile streaming is fully plumbed).
                const GLuint tex = pboUploader_.texture();
                if (tex != 0u) {
                    const int xOff =
                        static_cast<int>(tile->id.x) *
                        static_cast<int>(tile->width);
                    const int yOff =
                        static_cast<int>(tile->id.y) *
                        static_cast<int>(tile->height);
                    const int zOff =
                        static_cast<int>(tile->id.z) *
                        static_cast<int>(tile->depth);

                    glBindTexture(GL_TEXTURE_3D, tex);
                    glTexSubImage3D(
                        GL_TEXTURE_3D, 0,
                        xOff, yOff, zOff,
                        static_cast<GLsizei>(tile->width),
                        static_cast<GLsizei>(tile->height),
                        static_cast<GLsizei>(tile->depth),
                        GL_RGBA, GL_FLOAT,
                        stagingBuf_.data());
                    glBindTexture(GL_TEXTURE_3D, 0u);
                    ++uploaded;
                    ++tilesUploaded_;
                }
            }
        }

        break; // Only one full-frame tile per frame in the current architecture
    }

    return uploaded;
}

// ============================================================================
// packRGBA() -- static
// ============================================================================

void GRMHDGpuUploader::packRGBA(const blackhole::GRMHDTile& tile,
                                  float* dst, std::size_t nVoxels) {
    const float* src = tile.data.data();
    const std::size_t srcTotal = tile.data.size();

    if (srcTotal == 0 || nVoxels == 0) return;

    const std::size_t srcChannels = srcTotal / nVoxels;

    if (srcChannels == 4) {
        // Already 4-channel RGBA32F: direct copy.
        std::memcpy(dst, src, nVoxels * 4 * sizeof(float));
        return;
    }

    // Pack 7+ GRMHD variables -> (rho, uu, |B|, |u|).
    for (std::size_t v = 0; v < nVoxels; ++v) {
        const float* vx = src + v * srcChannels;

        const float rho = (srcChannels > 0) ? vx[0] : 0.0f;
        const float uu  = (srcChannels > 1) ? vx[1] : 0.0f;
        const float u1  = (srcChannels > 2) ? vx[2] : 0.0f;
        const float u2  = (srcChannels > 3) ? vx[3] : 0.0f;
        const float u3  = (srcChannels > 4) ? vx[4] : 0.0f;
        const float B1  = (srcChannels > 5) ? vx[5] : 0.0f;
        const float B2  = (srcChannels > 6) ? vx[6] : 0.0f;
        const float B3  = (srcChannels > 7) ? vx[7] : 0.0f;

        const float Bmag = std::sqrt(B1*B1 + B2*B2 + B3*B3);
        const float umag = std::sqrt(u1*u1 + u2*u2 + u3*u3);

        float* out = dst + v * 4;
        out[0] = rho;
        out[1] = uu;
        out[2] = Bmag;
        out[3] = umag;
    }
}

} // namespace gpu
