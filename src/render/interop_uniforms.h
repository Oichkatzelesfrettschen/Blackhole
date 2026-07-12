/**
 * @file interop_uniforms.h
 * @brief Aggregated uniform values shared between the GL fragment shader and
 *        the CUDA compute path.
 *
 * applyInteropUniforms() copies these fields into a RenderToTextureInfo
 * uniform map before each render call, ensuring both paths receive identical
 * inputs for the compute/fragment parity comparison (Issue-009).
 */

#ifndef BLACKHOLE_RENDER_INTEROP_UNIFORMS_H
#define BLACKHOLE_RENDER_INTEROP_UNIFORMS_H

#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/vector_float3.hpp>

#include "render/interop_uniform_registry.h"

namespace blackhole {

struct InteropUniforms {
  // Typed specials: two paths differ in call shape, so they stay
  // explicit rather than joining the float registry.
  glm::vec3 cameraPos{};
  glm::mat3 cameraBasis{1.0f};
  int maxSteps = 0;
  // Carried for the compare CSV and the CUDA fill; never a GL uniform.
  float iscoRadius = 0.0f;
  // Every shared float uniform, generated from the registry: one table
  // row expands into this field, the fragment map write, and the
  // compute glUniform1f call (src/render/interop_uniform_registry.h).
#define BH_X(field, glslName, defaultValue) float field = defaultValue;
  BH_INTEROP_UNIFORM_FLOATS(BH_X)
#undef BH_X
};

} // namespace blackhole

#endif // BLACKHOLE_RENDER_INTEROP_UNIFORMS_H
