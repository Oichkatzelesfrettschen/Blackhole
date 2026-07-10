/**
 * @file uniform_binding.cpp
 * @brief Implementations of the shared raytracer uniform binders declared in
 *        uniform_binding.h.
 */

#include "render/uniform_binding.h"

#include <glbinding/gl/functions.h>
#include <glm/gtc/type_ptr.hpp>

#include "render/interop_uniform_registry.h"

using namespace gl;

namespace blackhole {

void applyInteropUniforms(RenderToTextureInfo &rtti, const InteropUniforms &interop,
                          bool parityMode, bool hawkingEnabled, float hawkingTempScale,
                          float hawkingIntensity, bool hawkingUseLUTs, double blackHoleMass) {
  // Registry-driven float uniforms: one row in
  // interop_uniform_registry.h writes the struct field, this map entry,
  // and the compute-path call below.
#define BH_X(field, glslName, defaultValue)                                  \
  rtti.floatUniforms[glslName] = interop.field;
  BH_INTEROP_UNIFORM_FLOATS(BH_X)
#undef BH_X

  // Typed specials and per-call extras.
  rtti.vec3Uniforms["cameraPos"] = interop.cameraPos;
  rtti.mat3Uniforms["cameraBasis"] = interop.cameraBasis;
  rtti.floatUniforms["interopMaxSteps"] = static_cast<float>(interop.maxSteps);
  rtti.floatUniforms["interopParityMode"] = parityMode ? 1.0f : 0.0f;

  // Hawking radiation uniforms
  rtti.floatUniforms["hawkingGlowEnabled"] = hawkingEnabled ? 1.0f : 0.0f;
  rtti.floatUniforms["hawkingTempScale"] = hawkingTempScale;
  rtti.floatUniforms["hawkingGlowIntensity"] = hawkingIntensity;
  rtti.floatUniforms["useHawkingLUTs"] = hawkingUseLUTs ? 1.0f : 0.0f;
  rtti.floatUniforms["blackHoleMass"] = static_cast<float>(blackHoleMass);
  // Wiregrid BL-coord overlay (task A2) -- filled by caller via wiregridEnabled flag
  // (wiregridEnabled/ShowErgo/GridScale are set in the render loop after this call)
}

void applyInteropComputeUniforms(GLuint program, const InteropUniforms &interop, int width,
                                 int height) {
  // Registry-driven float uniforms: same table rows as the fragment
  // path, so the two paths cannot drift on which uniforms exist.
#define BH_X(field, glslName, defaultValue)                                  \
  glUniform1f(glGetUniformLocation(program, glslName), interop.field);
  BH_INTEROP_UNIFORM_FLOATS(BH_X)
#undef BH_X

  // Typed specials.
  glUniform2f(glGetUniformLocation(program, "resolution"), static_cast<float>(width),
              static_cast<float>(height));
  glUniformMatrix3fv(glGetUniformLocation(program, "cameraBasis"), 1, GL_FALSE,
                     glm::value_ptr(interop.cameraBasis));
  glUniform3f(glGetUniformLocation(program, "cameraPos"), interop.cameraPos.x, interop.cameraPos.y,
              interop.cameraPos.z);
  glUniform1i(glGetUniformLocation(program, "interopMaxSteps"), interop.maxSteps);
}

void applyHawkingUniforms(GLuint program, const physics::HawkingRenderer &renderer, bool enabled,
                          float tempScale, float intensity, bool useLUTs, double blackHoleMass) {
  if (!renderer.isReady()) {
    return;
  }

  physics::HawkingGlowParams params;
  params.enabled = enabled;
  params.tempScale = tempScale;
  params.intensity = intensity;
  params.useLUTs = useLUTs;

  renderer.setShaderUniforms(program, blackHoleMass, params);
}

} // namespace blackhole
