/**
 * @file uniform_binding.h
 * @brief Shared raytracer uniform binders. Both interop binders expand the
 *        BH_INTEROP_UNIFORM_FLOATS registry so the fragment (RenderToTextureInfo)
 *        and compute (glUniform) GPU paths cannot drift on which float uniforms
 *        exist; the Hawking binder forwards glow parameters to a program.
 */

#ifndef BLACKHOLE_RENDER_UNIFORM_BINDING_H
#define BLACKHOLE_RENDER_UNIFORM_BINDING_H

#include <glbinding/gl/types.h>

#include "physics/hawking_renderer.h"
#include "render.h"
#include "render/interop_uniforms.h"

namespace blackhole {

/**
 * @brief Fills the fragment-path float and typed uniforms on @p rtti from the
 *        interop registry, plus the parity-mode and Hawking-glow extras.
 */
void applyInteropUniforms(RenderToTextureInfo &rtti, const InteropUniforms &interop,
                          bool parityMode, bool hawkingEnabled, float hawkingTempScale,
                          float hawkingIntensity, bool hawkingUseLUTs, double blackHoleMass);

/**
 * @brief Sets the same registry float uniforms plus typed specials (resolution,
 *        camera basis/position, max steps) on the bound compute @p program.
 */
void applyInteropComputeUniforms(gl::GLuint program, const InteropUniforms &interop, int width,
                                 int height);

/**
 * @brief Forwards Hawking-glow parameters to @p program via
 *        HawkingRenderer::setShaderUniforms; a no-op when the renderer is not ready.
 */
void applyHawkingUniforms(gl::GLuint program, const physics::HawkingRenderer &renderer, bool enabled,
                          float tempScale, float intensity, bool useLUTs, double blackHoleMass);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_UNIFORM_BINDING_H
