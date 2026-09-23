#ifndef BLACKHOLE_RENDER_POST_PIPELINE_H
#define BLACKHOLE_RENDER_POST_PIPELINE_H

#include <glbinding/gl/types.h>

class InputManager;

namespace blackhole {

struct RenderState;

// Fullscreen post chain on the raytraced texBlackhole: bloom (brightness,
// downsample, upsample, composite), tonemap, and the optional depth-cue pass.
// Returns the texture to display -- texTonemapped, or texDepthEffects when the
// depth pass ran. The UI panels for each stage render inline when visible.
gl::GLuint runPostProcessPipeline(RenderState &rs, const InputManager &input);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_POST_PIPELINE_H
