/**
 * @file uniform_binding.cpp
 * @brief Implementations of the shared raytracer uniform binders declared in
 *        uniform_binding.h.
 */

#include "render/uniform_binding.h"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstring>

#include <glbinding/gl/functions.h>
#include <glm/gtc/type_ptr.hpp>

#include "render/interop_uniform_registry.h"

#if BLACKHOLE_HAS_CUDA
#include "cuda/kernel_launch.h"
#endif

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

#if BLACKHOLE_HAS_CUDA
void bindCudaLaunchParams(BH_LaunchParams &cp, const RenderState &rs,
                          const InteropUniforms &interop, const FrameBindingInputs &in) {
  cp.rs = interop.schwarzschildRadius;
  cp.spin = interop.kerrSpin;
  cp.isco = interop.iscoRadius;
  cp.step_size = interop.stepSize;
  cp.fov_scale = interop.fovScale;
  cp.max_dist = interop.depthFar;
  cp.cam_pos[0] = interop.cameraPos.x;
  cp.cam_pos[1] = interop.cameraPos.y;
  cp.cam_pos[2] = interop.cameraPos.z;
  /* glm mat3 is column-major, same layout as our flat array */
  std::memcpy(cp.cam_basis, glm::value_ptr(interop.cameraBasis), 9 * sizeof(float));
  cp.max_steps = interop.maxSteps;
  cp.width = rs.targets.renderWidth;
  cp.height = rs.targets.renderHeight;
  cp.adisk_enabled = in.adiskEnabledEffective ? 1 : 0;
  cp.redshift_enabled = in.enableRedshiftEffective ? 1 : 0;
  cp.kerr_enabled = (fabsf(interop.kerrSpin) > 1e-6f) ? 1 : 0;
  cp.use_luts = (interop.useLUTs > 0.5f) ? 1 : 0;
  cp.lut_radius_min = interop.lutRadiusMin;
  cp.lut_radius_max = interop.lutRadiusMax;
  cp.redshift_radius_min = interop.redshiftRadiusMin;
  cp.redshift_radius_max = interop.redshiftRadiusMax;
  cp.spectral_radius_min = interop.spectralRadiusMin;
  cp.spectral_radius_max = interop.spectralRadiusMax;
  cp.time_sec = interop.timeSec;
  cp.doppler_strength = rs.disk.dopplerStrength;
  cp.background_intensity = in.backgroundIntensity;
  cp.background_enabled = in.backgroundEnabledEffective ? 1 : 0;
  cp.photon_glow_strength = in.enablePhotonSphereEffective ? rs.disk.photonSphereGlowStrength : 0.0f;
  cp.debug_pre_redshift_background = rs.debug.debugPreRedshiftBackground ? 1 : 0;
  cp.debug_pre_shaping_background = rs.debug.debugPreShapingBackground ? 1 : 0;
  cp.debug_post_shaping_background = rs.debug.debugPostShapingBackground ? 1 : 0;
  cp.debug_shaper_inputs = rs.debug.debugShaperInputs ? 1 : 0;
  cp.debug_closest_approach_state = rs.debug.debugClosestApproachState ? 1 : 0;
  cp.debug_closest_approach_timeline = rs.debug.debugClosestApproachTimeline ? 1 : 0;
  cp.debug_closest_approach_direction = rs.debug.debugClosestApproachDirection ? 1 : 0;
  cp.debug_escaped_direction = rs.debug.debugEscapedDirection ? 1 : 0;
  cp.background_yaw_rad = rs.background.backgroundYawRad;
  cp.background_pitch_rad = rs.background.backgroundPitchRad;
  cp.background_filter_radius = 0.0f;
  cp.frame_shift_x = in.frameShiftX;
  cp.frame_shift_y = in.frameShiftY;
  for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
    auto const &params = rs.background.backgroundLayerParams.at(static_cast<std::size_t>(i));
    cp.background_layer_params[i * 4 + 0] = params.x;
    cp.background_layer_params[i * 4 + 1] = params.y;
    cp.background_layer_params[i * 4 + 2] = params.z;
    cp.background_layer_params[i * 4 + 3] = params.w;
    cp.background_layer_lod_bias[i] =
        std::max(rs.background.backgroundLayerLodBias.at(static_cast<std::size_t>(i)), 0.0f);
  }
  // Wiregrid BL-coord overlay (task A4)
  cp.wiregrid_enabled    = rs.wiregrid.wiregridEnabled ? 1 : 0;
  cp.wiregrid_show_ergo  = rs.wiregrid.wiregridParams.showErgosphere ? 1.0f : 0.0f;
  cp.wiregrid_grid_scale = rs.wiregrid.wiregridParams.gridScale;
  cp.wiregrid_motion_scale = rs.wiregrid.wiregridParams.motionScale;
  cp.wiregrid_infall_scale = rs.wiregrid.wiregridParams.infallScale;
  cp.wiregrid_strength = rs.wiregrid.wiregridParams.strength;
  cp.wiregrid_scene_preserve = rs.wiregrid.wiregridParams.scenePreserve;
  cp.wiregrid_color[0] = rs.wiregrid.wiregridColor.r;
  cp.wiregrid_color[1] = rs.wiregrid.wiregridColor.g;
  cp.wiregrid_color[2] = rs.wiregrid.wiregridColor.b;
  cp.wiregrid_color[3] = rs.wiregrid.wiregridColor.a;
  // GRMHD volume radial bounds (task C1l) + temporal blend (C1d)
  cp.grmhd_r_min  = rs.grmhd.grmhdTexture.rMin;
  cp.grmhd_r_max  = rs.grmhd.grmhdTexture.rMax;
  cp.grmhd_alpha  = rs.grmhd.grmhdFrameAlpha;
  // Volumetric RTE (D3): mirrors GLSL rteEnabled path
  cp.rte_enabled       = (interop.rteEnabled > 0.5f) ? 1 : 0;
  cp.rte_opacity_scale = interop.rteOpacityScale;
  // D4: polarized Stokes IQUV
  cp.stokes_enabled     = rs.stokes.stokesEnabled ? 1 : 0;
  cp.stokes_b_field_angle = rs.stokes.stokesBFieldAngle;
  cp.stokes_ne_scale    = rs.stokes.stokesNeScale;
  // Disk brightness: matches adiskLit GLSL uniform (record mode sets 0.35)
  cp.adisk_lit = rs.disk.adiskLit;
}
#endif

} // namespace blackhole
