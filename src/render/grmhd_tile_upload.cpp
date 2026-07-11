#include "render/grmhd_tile_upload.h"

#include <algorithm>
#include <cmath>

#include <glbinding/gl/enum.h>

#include "render/render_state.h"

using namespace gl;

namespace blackhole {

void uploadGrmhdStreamingTiles(RenderState &rs) {
  /* Per-frame streaming tile upload: when GRMHDStreamer is running and the
   * PBOUploader is initialized, obtain the current frame tile and upload.
   * getTile() is non-blocking; on a cache miss it enqueues the request. */
  if (rs.grmhd.grmhdStreamer && rs.grmhd.grmhdPboUploader.texture() != 0) {
    auto tile = rs.grmhd.grmhdStreamer->getTile(0, 0, 0, 0);
    if (tile && tile->ready()) {
      rs.grmhd.grmhdPboUploader.upload(tile->data.data(), tile->data.size());
    }
  }
  /* C1d: upload adjacent (next) frame into the right PBO uploader for
   * temporal interpolation.  getAdjacentTile() returns nullptr at the last
   * frame or on a cache miss (seekFrame prefetch keeps it warm).
   * rs.grmhd.grmhdFrameAlpha is the sub-frame blend fraction; sub-frame position is
   * approximated as the fractional part of (current_frame + time_bias). */
  rs.grmhd.grmhdFrameAlpha = 0.0f;
  if (rs.grmhd.grmhdStreamer && rs.grmhd.grmhdPboUploaderRight.texture() != 0) {
    auto rightTile = rs.grmhd.grmhdStreamer->getAdjacentTile(0, 0, 0, 0);
    if (rightTile && rightTile->ready()) {
      rs.grmhd.grmhdPboUploaderRight.upload(rightTile->data.data(), rightTile->data.size());
    }
    /* Advance CUDA slot 7 registration when the right PBO first becomes ready */
#if BLACKHOLE_HAS_CUDA
    if (rs.grmhd.grmhdPboUploaderRight.ready()) {
      if (rs.grmhd.registeredRightTex != rs.grmhd.grmhdPboUploaderRight.texture()) {
        rs.grmhd.registeredRightTex = rs.grmhd.grmhdPboUploaderRight.texture();
        rs.dispatch.cudaManager.registerLut(7 /*BhLutGrmhdRight*/, rs.grmhd.registeredRightTex,
                                static_cast<unsigned int>(GL_TEXTURE_3D));
      }
    }
#endif
    if (rs.grmhd.grmhdPboUploaderRight.ready()) {
      /* Sub-frame alpha: fraction of inter-frame interval elapsed.
       * rs.grmhd.grmhdPlaybackSpeed controls simulation-time advance per real second. */
      rs.grmhd.grmhdFrameAlpha = std::fmod(
          static_cast<float>(rs.grmhd.grmhdCurrentFrame) * rs.grmhd.grmhdPlaybackSpeed, 1.0f);
      rs.grmhd.grmhdFrameAlpha = std::max(0.0f, std::min(1.0f, rs.grmhd.grmhdFrameAlpha));
    }
  }
}

} // namespace blackhole
