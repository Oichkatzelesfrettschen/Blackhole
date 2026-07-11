#ifndef BLACKHOLE_RENDER_GRMHD_TILE_UPLOAD_H
#define BLACKHOLE_RENDER_GRMHD_TILE_UPLOAD_H

namespace blackhole {

struct RenderState;

// Per-frame GRMHD tile upload: when the streamer is running and the PBO
// uploaders are initialized, pull the current-frame tile into the primary
// uploader and the adjacent-frame tile into the right uploader for temporal
// interpolation, register the right texture into CUDA slot 7 on first ready,
// and compute the sub-frame blend fraction grmhdFrameAlpha. getTile is
// non-blocking; a cache miss enqueues the request and leaves the texture
// untouched this frame.
void uploadGrmhdStreamingTiles(RenderState &rs);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_GRMHD_TILE_UPLOAD_H
