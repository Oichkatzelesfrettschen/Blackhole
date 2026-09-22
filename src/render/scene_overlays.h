#ifndef BLACKHOLE_RENDER_SCENE_OVERLAYS_H
#define BLACKHOLE_RENDER_SCENE_OVERLAYS_H

#include <glbinding/gl/types.h>

class InputManager;

namespace blackhole {

struct RenderState;

// Binds the scene framebuffer to the post-processed final texture and draws the
// overlay passes on top before the texture is shown in the viewport: the GRMHD
// slice (when enabled and data is ready), the RmlUi overlay, and the HUD
// controls/perf overlays. Leaves the default framebuffer bound on return.
void composeSceneOverlays(RenderState &rs, const InputManager &input, gl::GLuint finalTexture,
                          bool grmhdReady);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_SCENE_OVERLAYS_H
