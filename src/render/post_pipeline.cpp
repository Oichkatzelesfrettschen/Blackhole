#include "render/post_pipeline.h"

#include <algorithm>
#include <cstddef>

#include <glbinding/gl/types.h>

#include "input.h"
#include "render.h"
#include "render/render_state.h"
#include "tracy_support.h"
#include "ui/settings_window.h"

using namespace gl;

using ui::renderBloomPanel;
using ui::renderDepthEffectsPanel;
using ui::renderTonemapPanel;

namespace blackhole {

GLuint runPostProcessPipeline(RenderState &rs, const InputManager &input) {
  // Bound texture indexing and mip-level shifts for every caller.
  const int bloomIterations = std::clamp(rs.post.bloomIterations, 1, K_MAX_BLOOM_ITERATIONS);
  if (rs.timing.gpuTimers.initialized) {
    rs.timing.gpuTimers.bloom.begin();
  }
  {
    ZONE_SCOPED_N("Bloom Brightness");
    RenderToTextureInfo rtti;
    rtti.fragShader = "shader/bloom_brightness_pass.frag";
    rtti.textureUniforms["texture0"] = rs.targets.texBlackhole;
    rtti.targetTexture = rs.targets.texBrightness;
    rtti.width = rs.targets.renderWidth;
    rtti.height = rs.targets.renderHeight;
    rtti.floatUniforms["brightPassThreshold"] = rs.post.bloomThreshold;
    rtti.floatUniforms["brightPassKnee"]      = rs.post.bloomKnee;
    renderToTexture(rtti);
  }

  // Post Processing panel moved to Main Settings

  {
    ZONE_SCOPED_N("Bloom Downsample");
    for (int level = 0; level < bloomIterations; level++) {
      auto const levelIndex = static_cast<std::size_t>(level);
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/bloom_downsample.frag";
      rtti.textureUniforms["texture0"] =
          level == 0 ? rs.targets.texBrightness : rs.targets.texDownsampled.at(static_cast<std::size_t>(level - 1));
      rtti.targetTexture = rs.targets.texDownsampled.at(levelIndex);
      int const downWidth = std::max(1, rs.targets.renderWidth >> (level + 1));
      int const downHeight = std::max(1, rs.targets.renderHeight >> (level + 1));
      rtti.width = downWidth;
      rtti.height = downHeight;
      renderToTexture(rtti);
    }
  }

  {
    ZONE_SCOPED_N("Bloom Upsample");
    for (int level = bloomIterations - 1; level >= 0; level--) {
      auto const levelIndex = static_cast<std::size_t>(level);
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/bloom_upsample.frag";
      rtti.textureUniforms["texture0"] =
          level == bloomIterations - 1
              ? rs.targets.texDownsampled.at(levelIndex)
              : rs.targets.texUpsampled.at(static_cast<std::size_t>(level) + 1);
      rtti.textureUniforms["texture1"] =
          level == 0 ? rs.targets.texBrightness : rs.targets.texDownsampled.at(static_cast<std::size_t>(level - 1));
      rtti.targetTexture = rs.targets.texUpsampled.at(levelIndex);
      int const upWidth = std::max(1, rs.targets.renderWidth >> level);
      int const upHeight = std::max(1, rs.targets.renderHeight >> level);
      rtti.width = upWidth;
      rtti.height = upHeight;
      renderToTexture(rtti);
    }
  }

  {
    ZONE_SCOPED_N("Bloom Composite");
    RenderToTextureInfo rtti;
    rtti.fragShader = "shader/bloom_composite.frag";
    rtti.textureUniforms["texture0"] = rs.targets.texBlackhole;
    rtti.textureUniforms["texture1"] = rs.targets.texUpsampled.at(0);
    rtti.targetTexture = rs.targets.texBloomFinal;
    rtti.width = rs.targets.renderWidth;
    rtti.height = rs.targets.renderHeight;

    if (input.isUIVisible()) {
      renderBloomPanel(rs);
    }
    rtti.floatUniforms["bloomStrength"] = rs.post.bloomStrength;
    rtti.floatUniforms["tone"]          = rs.post.bloomTone;

    renderToTexture(rtti);
  }
  if (rs.timing.gpuTimers.initialized) {
    rs.timing.gpuTimers.bloom.end();
  }

  if (rs.timing.gpuTimers.initialized) {
    rs.timing.gpuTimers.tonemap.begin();
  }
  {
    ZONE_SCOPED_N("Tonemap");
    RenderToTextureInfo rtti;
    rtti.fragShader = "shader/tonemapping.frag";
    rtti.textureUniforms["texture0"] = rs.targets.texBloomFinal;
    rtti.targetTexture = rs.targets.texTonemapped;
    rtti.width = rs.targets.renderWidth;
    rtti.height = rs.targets.renderHeight;

    if (input.isUIVisible()) {
      renderTonemapPanel(rs);
    }
    rtti.floatUniforms["tonemappingEnabled"] = rs.post.tonemappingEnabled ? 1.0f : 0.0f;
    rtti.floatUniforms["exposure"] = rs.post.toneExposure;
    rtti.floatUniforms["gamma"] = rs.post.gamma;
    rtti.floatUniforms["chromaticAberrationStrength"] = rs.post.tonemapChromaticAberrationStrength;
    rtti.floatUniforms["vignetteStrength"] = rs.post.tonemapVignetteStrength;
    rtti.floatUniforms["filmGrainStrength"] = rs.post.tonemapFilmGrainStrength;

    renderToTexture(rtti);
  }
  if (rs.timing.gpuTimers.initialized) {
    rs.timing.gpuTimers.tonemap.end();
  }


  if (input.isUIVisible()) {
    renderDepthEffectsPanel(rs);
  }

  GLuint finalTexture = rs.targets.texTonemapped;
  if (rs.depthFx.depthEffectsEnabled) {
    ZONE_SCOPED_N("Depth Cues");
    if (rs.timing.gpuTimers.initialized) {
      rs.timing.gpuTimers.depth.begin();
    }
    RenderToTextureInfo rtti;
    rtti.fragShader = "shader/depth_cues.frag";
    rtti.textureUniforms["texture0"] = rs.targets.texTonemapped;
    rtti.textureUniforms["depthTexture"] = rs.targets.texBlackhole;
    rtti.targetTexture = rs.targets.texDepthEffects;
    rtti.width = rs.targets.renderWidth;
    rtti.height = rs.targets.renderHeight;
    rtti.floatUniforms["depthEffectsEnabled"] = 1.0f;
    rtti.floatUniforms["fogEnabled"] = rs.depthFx.fogEnabled ? 1.0f : 0.0f;
    rtti.floatUniforms["fogDensity"] = rs.depthFx.fogDensity;
    rtti.floatUniforms["fogStart"] = rs.depthFx.fogStart;
    rtti.floatUniforms["fogEnd"] = rs.depthFx.fogEnd;
    rtti.floatUniforms["fogColorR"] = rs.depthFx.fogColor[0];
    rtti.floatUniforms["fogColorG"] = rs.depthFx.fogColor[1];
    rtti.floatUniforms["fogColorB"] = rs.depthFx.fogColor[2];
    rtti.floatUniforms["edgeOutlinesEnabled"] = rs.depthFx.edgeOutlinesEnabled ? 1.0f : 0.0f;
    rtti.floatUniforms["edgeThreshold"] = rs.depthFx.edgeThreshold;
    rtti.floatUniforms["edgeWidth"] = rs.depthFx.edgeWidth;
    rtti.floatUniforms["edgeColorR"] = rs.depthFx.edgeColor[0];
    rtti.floatUniforms["edgeColorG"] = rs.depthFx.edgeColor[1];
    rtti.floatUniforms["edgeColorB"] = rs.depthFx.edgeColor[2];
    rtti.floatUniforms["depthDesatEnabled"] = rs.depthFx.depthDesatEnabled ? 1.0f : 0.0f;
    rtti.floatUniforms["desatStrength"] = rs.depthFx.desatStrength;
    rtti.floatUniforms["chromaDepthEnabled"] = rs.depthFx.chromaDepthEnabled ? 1.0f : 0.0f;
    rtti.floatUniforms["motionParallaxHint"] = rs.depthFx.motionParallaxHint ? 1.0f : 0.0f;
    rtti.floatUniforms["dofEnabled"] = rs.depthFx.dofEnabled ? 1.0f : 0.0f;
    rtti.floatUniforms["dofFocusNear"] = rs.depthFx.dofFocusNear;
    rtti.floatUniforms["dofFocusFar"] = rs.depthFx.dofFocusFar;
    rtti.floatUniforms["dofMaxRadius"] = rs.depthFx.dofMaxRadius;
    rtti.floatUniforms["depthCurve"] = rs.depthFx.depthCurve;
    renderToTexture(rtti);
    finalTexture = rs.targets.texDepthEffects;
    if (rs.timing.gpuTimers.initialized) {
      rs.timing.gpuTimers.depth.end();
    }
  }

  return finalTexture;
}

} // namespace blackhole
