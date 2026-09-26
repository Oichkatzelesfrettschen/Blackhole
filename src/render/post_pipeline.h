#ifndef BLACKHOLE_RENDER_POST_PIPELINE_H
#define BLACKHOLE_RENDER_POST_PIPELINE_H

#include <glbinding/gl/types.h>

#include "render.h"

class InputManager;

namespace blackhole {

struct RenderState;

// Fullscreen post chain on the raytraced texBlackhole: bloom (brightness,
// downsample, upsample, composite), tonemap, and the optional depth-cue pass.
// Returns the texture to display -- texTonemapped, or texDepthEffects when the
// depth pass ran. The UI panels for each stage render inline when visible.
// contentSeconds (frameContentSeconds) drives the film grain and depth-cue
// motion "time" uniform, so a recorded frame's post output follows its index.
gl::GLuint runPostProcessPipeline(RenderState &rs, const InputManager &input,
                                  double contentSeconds);

// The tonemap pass for this frame: exposure, gamma, lens effects, and the
// film-grain "time" uniform from contentSeconds.
RenderToTextureInfo tonemapPass(const RenderState &rs, double contentSeconds);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_POST_PIPELINE_H
