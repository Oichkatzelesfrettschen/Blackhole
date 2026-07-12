/**
 * @file render_targets.h
 * @brief Off-screen render-target lifecycle for the scene render passes.
 *
 * recreateRenderTargets rebuilds the full set of framebuffer textures the
 * render loop draws into (the HDR scene and its compare copy, the brightness /
 * bloom / tonemap / depth-effect targets, and the bloom mip pyramids) at a new
 * size, releasing the previous set first, and resizes the CUDA backend to match.
 */

#ifndef BLACKHOLE_RENDER_RENDER_TARGETS_H
#define BLACKHOLE_RENDER_RENDER_TARGETS_H

namespace blackhole {

struct RenderState;

/** @brief Releases and recreates every off-screen render target in rs.targets at
 *         newWidth x newHeight, and resizes the CUDA backend. */
void recreateRenderTargets(RenderState &rs, int newWidth, int newHeight);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_RENDER_TARGETS_H
