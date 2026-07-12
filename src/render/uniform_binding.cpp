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
#include <string>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glm/gtc/type_ptr.hpp>

#include "physics/constants.h"
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

void bindComputeUniforms(GLuint program, const RenderState &rs, const FrameBindingInputs &in) {
  // Wiregrid BL-coord overlay (parity with fragment path)
  glUniform1f(glGetUniformLocation(program, "wiregridEnabled"),
              rs.wiregrid.wiregridEnabled ? 1.0f : 0.0f);
  glUniform1f(glGetUniformLocation(program, "wiregridShowErgo"),
              rs.wiregrid.wiregridParams.showErgosphere ? 1.0f : 0.0f);
  glUniform1f(glGetUniformLocation(program, "wiregridGridScale"),
              rs.wiregrid.wiregridParams.gridScale);
  glUniform1f(glGetUniformLocation(program, "wiregridMotionScale"),
              rs.wiregrid.wiregridParams.motionScale);
  glUniform1f(glGetUniformLocation(program, "wiregridInfallScale"),
              rs.wiregrid.wiregridParams.infallScale);
  glUniform1f(glGetUniformLocation(program, "wiregridStrength"),
              rs.wiregrid.wiregridParams.strength);
  glUniform1f(glGetUniformLocation(program, "wiregridScenePreserve"),
              rs.wiregrid.wiregridParams.scenePreserve);
  glUniform4f(glGetUniformLocation(program, "wiregridColor"),
              rs.wiregrid.wiregridColor.r, rs.wiregrid.wiregridColor.g, rs.wiregrid.wiregridColor.b, rs.wiregrid.wiregridColor.a);

  // D4: polarized Stokes IQUV (parity with fragment path)
  glUniform1f(glGetUniformLocation(program, "stokesEnabled"),
              rs.stokes.stokesEnabled ? 1.0f : 0.0f);
  glUniform1f(glGetUniformLocation(program, "stokesBFieldAngle"),
              rs.stokes.stokesBFieldAngle);
  glUniform1f(glGetUniformLocation(program, "stokesNeScale"),
              rs.stokes.stokesNeScale);

  GLint texUnit = 0;
  glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
  glBindTexture(GL_TEXTURE_2D, in.lutReady ? rs.luts.texEmissivityLUT : rs.background.fallback2D);
  glUniform1i(glGetUniformLocation(program, "emissivityLUT"), texUnit);
  texUnit++;
  glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
  glBindTexture(GL_TEXTURE_2D, in.lutReady ? rs.luts.texRedshiftLUT : rs.background.fallback2D);
  glUniform1i(glGetUniformLocation(program, "redshiftLUT"), texUnit);
  texUnit++;
  glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
  glBindTexture(GL_TEXTURE_2D, in.spectralEnabled ? rs.luts.texSpectralLUT : rs.background.fallback2D);
  glUniform1i(glGetUniformLocation(program, "spectralLUT"), texUnit);
  texUnit++;
  glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
  glBindTexture(GL_TEXTURE_2D, in.grbModulationEnabled ? rs.luts.texGrbModulationLUT : rs.background.fallback2D);
  glUniform1i(glGetUniformLocation(program, "grbModulationLUT"), texUnit);
  texUnit++;
  glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
  glBindTexture(GL_TEXTURE_CUBE_MAP, rs.background.galaxy != 0 ? rs.background.galaxy : rs.background.fallbackCubemap);
  glUniform1i(glGetUniformLocation(program, "galaxy"), texUnit);
  texUnit++;
  for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
    glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
    glBindTexture(GL_TEXTURE_2D, rs.background.backgroundTextures.at(static_cast<std::size_t>(i)));
    std::string const name = "backgroundLayers[" + std::to_string(i) + "]";
    glUniform1i(glGetUniformLocation(program, name.c_str()), texUnit);
    texUnit++;
  }
  glUniform1f(glGetUniformLocation(program, "backgroundEnabled"),
              in.backgroundEnabledEffective ? 1.0f : 0.0f);
  glUniform1f(glGetUniformLocation(program, "bhDebugFlags"),
              static_cast<float>(rs.compare.integratorDebugFlags));
  glUniform1f(glGetUniformLocation(program, "backgroundIntensity"),
              in.backgroundIntensity);
  for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
    std::string const name = "backgroundLayerParams[" + std::to_string(i) + "]";
    const auto &params = rs.background.backgroundLayerParams.at(static_cast<std::size_t>(i));
    glUniform4f(glGetUniformLocation(program, name.c_str()), params.x, params.y,
                params.z, params.w);
  }
  for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
    std::string const name = "backgroundLayerLodBias[" + std::to_string(i) + "]";
    float const bias =
        std::max(rs.background.backgroundLayerLodBias.at(static_cast<std::size_t>(i)), 0.0f);
    glUniform1f(glGetUniformLocation(program, name.c_str()), bias);
  }
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

void bindFragmentUniforms(RenderToTextureInfo &rtti, const RenderState &rs,
                          const InteropUniforms &interop, const FrameBindingInputs &in) {
  // Post-derivation texture/scalar re-writes (final readiness values).
  rtti.texture3DUniforms["noiseTexture"] = in.noiseReady ? rs.disk.texNoiseVolume : rs.background.fallback3D;
  rtti.texture3DUniforms["grmhdTexture"] = in.grmhdEnabled ? in.grmhdTexId : rs.background.fallback3D;
  rtti.textureUniforms["spectralLUT"] = in.spectralEnabled ? rs.luts.texSpectralLUT : rs.background.fallback2D;
  rtti.textureUniforms["grbModulationLUT"] =
      in.grbModulationEnabled ? rs.luts.texGrbModulationLUT : rs.background.fallback2D;
  rtti.textureUniforms["hawkingTempLUT"] =
      rs.hawking.hawkingLutsLoaded ? rs.hawking.hawkingRenderer.getTempLUTTexture() : rs.background.fallback2D;
  rtti.textureUniforms["hawkingSpectrumLUT"] =
      rs.hawking.hawkingLutsLoaded ? rs.hawking.hawkingRenderer.getSpectrumLUTTexture() : rs.background.fallback2D;
  rtti.floatUniforms["useNoiseTexture"] = in.noiseReady ? 1.0f : 0.0f;
  rtti.floatUniforms["useGrmhd"] = in.grmhdEnabled ? 1.0f : 0.0f;
  rtti.floatUniforms["backgroundEnabled"] = in.backgroundEnabledEffective ? 1.0f : 0.0f;
  rtti.floatUniforms["bhDebugFlags"] = static_cast<float>(rs.compare.integratorDebugFlags);

  // Convert black hole mass to grams (CGS units for Hawking calculation)
  double const bhMassGrams = static_cast<double>(rs.physicsCore.blackHoleMass) * physics::M_SUN;
  applyInteropUniforms(rtti, interop, in.compareActive, rs.hawking.hawkingGlowEnabled, rs.hawking.hawkingTempScale,
                       rs.hawking.hawkingGlowIntensity, rs.hawking.hawkingUseLUTs, bhMassGrams);

  rtti.floatUniforms["wiregridEnabled"]   = rs.wiregrid.wiregridEnabled ? 1.0f : 0.0f;
  rtti.floatUniforms["wiregridShowErgo"]  = rs.wiregrid.wiregridParams.showErgosphere ? 1.0f : 0.0f;
  rtti.floatUniforms["wiregridGridScale"] = rs.wiregrid.wiregridParams.gridScale;
  rtti.floatUniforms["wiregridMotionScale"] = rs.wiregrid.wiregridParams.motionScale;
  rtti.floatUniforms["wiregridInfallScale"] = rs.wiregrid.wiregridParams.infallScale;
  rtti.floatUniforms["wiregridStrength"] = rs.wiregrid.wiregridParams.strength;
  rtti.floatUniforms["wiregridScenePreserve"] = rs.wiregrid.wiregridParams.scenePreserve;
  rtti.vec4Uniforms["wiregridColor"] = rs.wiregrid.wiregridColor;
  // D4: polarized Stokes IQUV
  rtti.floatUniforms["stokesEnabled"]     = rs.stokes.stokesEnabled ? 1.0f : 0.0f;
  rtti.floatUniforms["stokesBFieldAngle"] = rs.stokes.stokesBFieldAngle;
  rtti.floatUniforms["stokesNeScale"]     = rs.stokes.stokesNeScale;
  rtti.floatUniforms["gravitationalLensing"] = rs.disk.gravitationalLensing ? 1.0f : 0.0f;
  rtti.floatUniforms["renderBlackHole"] = rs.disk.renderBlackHole ? 1.0f : 0.0f;
  rtti.floatUniforms["adiskParticle"] = in.adiskParticleEffective ? 1.0f : 0.0f;
  // adiskDensityV removed: consumed by LUT generation.
  rtti.floatUniforms["adiskDensityH"] = rs.disk.adiskDensityH;
  rtti.floatUniforms["adiskHeight"] = rs.disk.adiskHeight;
  rtti.floatUniforms["adiskLit"] = rs.disk.adiskLit;
  rtti.floatUniforms["adiskNoiseLOD"] = rs.disk.adiskNoiseLOD;
  rtti.floatUniforms["adiskNoiseScale"] = rs.disk.adiskNoiseScale;
  rtti.floatUniforms["adiskSpeed"] = rs.disk.adiskSpeed;
  rtti.floatUniforms["dopplerStrength"] = rs.disk.dopplerStrength;
  rtti.floatUniforms["photonSphereGlowStrength"] = rs.disk.photonSphereGlowStrength;
  rtti.floatUniforms["enablePhotonSphere"] = in.enablePhotonSphereEffective ? 1.0f : 0.0f;
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
