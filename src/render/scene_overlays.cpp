#include "render/scene_overlays.h"

#include <algorithm>
#include <cstddef>
#include <string>
#include <vector>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

#include <glm/ext/vector_float4.hpp>

#include "hud_overlay.h"
#include "input.h"
#include "render.h"
#include "render/render_state.h"
#include "render/tesseract/tesseract_renderer.h"
#include "tracy_support.h"

using namespace gl;

namespace blackhole {

void composeSceneOverlays(RenderState &rs, const InputManager &input, GLuint finalTexture,
                          bool grmhdReady) {
  if (rs.targets.sceneFbo == 0) {
    glGenFramebuffers(1, &rs.targets.sceneFbo);
  }
  glBindFramebuffer(GL_FRAMEBUFFER, rs.targets.sceneFbo);
  glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, finalTexture,
                         0);
  glViewport(0, 0, rs.targets.renderWidth, rs.targets.renderHeight);

  // 1. Wiregrid BL-coord overlay -- implemented in task A2 (fragment shader)

  // 2. GRMHD Slice
  if (rs.grmhd.grmhdSliceEnabled && grmhdReady) {
    ZONE_SCOPED_N("GRMHD Slice");
    rs.grmhd.grmhdSliceAxis = std::clamp(rs.grmhd.grmhdSliceAxis, 0, 2);
    rs.grmhd.grmhdSliceChannel = std::clamp(rs.grmhd.grmhdSliceChannel, 0, 3);
    rs.grmhd.grmhdSliceCoord = std::clamp(rs.grmhd.grmhdSliceCoord, 0.0f, 1.0f);
    rs.grmhd.grmhdSliceSize = std::clamp(rs.grmhd.grmhdSliceSize, 64, 1024);

    const auto channelIndex = static_cast<std::size_t>(rs.grmhd.grmhdSliceChannel);
    if (rs.grmhd.grmhdSliceAutoRange && channelIndex < rs.grmhd.grmhdTexture.minValues.size() &&
        channelIndex < rs.grmhd.grmhdTexture.maxValues.size()) {
      rs.grmhd.grmhdSliceMin = rs.grmhd.grmhdTexture.minValues.at(channelIndex);
      rs.grmhd.grmhdSliceMax = rs.grmhd.grmhdTexture.maxValues.at(channelIndex);
    }
    if (rs.grmhd.grmhdSliceMax <= rs.grmhd.grmhdSliceMin) {
      rs.grmhd.grmhdSliceMax = rs.grmhd.grmhdSliceMin + 1.0f;
    }

    if (rs.grmhd.texGrmhdSlice == 0 || rs.grmhd.grmhdSliceSizeCached != rs.grmhd.grmhdSliceSize) {
      if (rs.grmhd.texGrmhdSlice != 0) {
        glDeleteTextures(1, &rs.grmhd.texGrmhdSlice);
        rs.grmhd.texGrmhdSlice = 0;
      }
      rs.grmhd.texGrmhdSlice = createColorTexture32f(rs.grmhd.grmhdSliceSize, rs.grmhd.grmhdSliceSize);
      rs.grmhd.grmhdSliceSizeCached = rs.grmhd.grmhdSliceSize;
    }

    RenderToTextureInfo sliceRtti;
    sliceRtti.fragShader = "shader/grmhd_slice.frag";
    sliceRtti.texture3DUniforms["grmhdTexture"] =
        (rs.grmhd.grmhdTimeSeriesLoaded && rs.grmhd.grmhdPboUploader.ready())
            ? rs.grmhd.grmhdPboUploader.texture()
            : rs.grmhd.grmhdTexture.texture;
    sliceRtti.textureUniforms["colorMap"] = rs.background.colorMap;
    sliceRtti.floatUniforms["sliceAxis"] = static_cast<float>(rs.grmhd.grmhdSliceAxis);
    sliceRtti.floatUniforms["sliceCoord"] = rs.grmhd.grmhdSliceCoord;
    sliceRtti.floatUniforms["sliceChannel"] = static_cast<float>(rs.grmhd.grmhdSliceChannel);
    sliceRtti.floatUniforms["sliceMin"] = rs.grmhd.grmhdSliceMin;
    sliceRtti.floatUniforms["sliceMax"] = rs.grmhd.grmhdSliceMax;
    sliceRtti.floatUniforms["useColorMap"] = rs.grmhd.grmhdSliceUseColorMap ? 1.0f : 0.0f;
    sliceRtti.targetTexture = rs.grmhd.texGrmhdSlice;
    sliceRtti.width = rs.grmhd.grmhdSliceSize;
    sliceRtti.height = rs.grmhd.grmhdSliceSize;
    if (rs.timing.gpuTimers.initialized) {
      rs.timing.gpuTimers.grmhdSlice.begin();
    }
    renderToTexture(sliceRtti); // Note: renderToTexture manages its own FBO binding
    if (rs.timing.gpuTimers.initialized) {
      rs.timing.gpuTimers.grmhdSlice.end();
    }

    // Re-bind Scene FBO to draw the slice texture on top?
    // Actually, renderToTexture renders TO texGrmhdSlice.
    // We need to composite texGrmhdSlice onto the scene?
    // The original code rendered the slice to a separate texture, then displayed it in ImGui
    // Image? "ImGui::Image(sliceId, ...)" in the UI panel. So we don't need to composite it
    // here.

    // Restore FBO for subsequent passes if any
    glBindFramebuffer(GL_FRAMEBUFFER, rs.targets.sceneFbo);
  }

  // 3. RmlUi Overlay
  if (rs.overlays.rmluiReady) {
    rs.overlays.rmluiOverlay.render();
  }

  // The tesseract scene always carries its provenance label, drawn into the
  // presented texture so recorded frames keep it too.
  if (rs.scene.mode == RenderState::SceneMode::Tesseract) {
    // Refit whenever the render width changes so the label never clips.
    if (rs.tesseract.speculativeLabelWidth != rs.targets.renderWidth) {
      const SpeculativeLabelLayout layout = layoutSpeculativeLabel(rs.targets.renderWidth);
      HudOverlayOptions opts;
      opts.scale = layout.scale;
      opts.margin = SPECULATIVE_LABEL_MARGIN;
      opts.align = HudOverlayOptions::Align::Center;
      opts.drawBackground = true;
      rs.tesseract.speculativeLabel.setOptions(opts);
      std::vector<HudOverlayLine> lines(layout.lines.size());
      std::ranges::transform(layout.lines, lines.begin(), [](const std::string &text) {
        return HudOverlayLine{.text = text,
                              .color = glm::vec4(1.0f, 0.86f, 0.55f, 1.0f),
                              .background = glm::vec4(0.0f, 0.0f, 0.0f, 0.6f)};
      });
      rs.tesseract.speculativeLabel.setLines(lines);
      rs.tesseract.speculativeLabelWidth = rs.targets.renderWidth;
    }
    rs.tesseract.speculativeLabel.render(rs.targets.renderWidth, rs.targets.renderHeight);
  }

  // 4. HUD Overlays (Perf/Controls)
  // Note: These renderers assume default framebuffer dimensions.
  // We set viewport to renderWidth/Height, which matches our FBO.
  if (rs.overlays.controlsOverlayEnabled && !input.isUIVisible()) {
    if (!rs.overlays.controlsOverlayReady) {
      HudOverlayOptions opts;
      opts.scale = rs.overlays.controlsOverlayScale;
      opts.margin = 16.0f;
      opts.align = HudOverlayOptions::Align::Left;
      rs.overlays.controlsOverlay.setOptions(opts);
      rs.overlays.controlsOverlayReady = true;
    }
    if (rs.overlays.controlsOverlayReady) {
      rs.overlays.controlsOverlay.render(rs.targets.renderWidth, rs.targets.renderHeight);
    }
    if (rs.overlays.perfOverlayReady) {
      rs.overlays.perfOverlay.render(rs.targets.renderWidth, rs.targets.renderHeight);
    }
  }

  glBindFramebuffer(GL_FRAMEBUFFER, 0);
}

} // namespace blackhole
