/**
 * @file render_targets.cpp
 * @brief Off-screen render-target (re)allocation.
 */

#include "render/render_targets.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

#include "render.h"              // createColorTexture*, clearRenderToTextureCache
#include "render/render_state.h" // RenderState, K_MAX_BLOOM_ITERATIONS

using namespace gl;

namespace blackhole {
namespace {

void deleteTexture(GLuint &texture) {
  if (texture != 0) {
    glDeleteTextures(1, &texture);
    texture = 0;
  }
}

} // namespace

void recreateRenderTargets(RenderState &rs, int newWidth, int newHeight) {
  clearRenderToTextureCache();
  if (rs.terminalDiagnostics.codesBuffer != 0) {
    glDeleteBuffers(1, &rs.terminalDiagnostics.codesBuffer);
    rs.terminalDiagnostics.codesBuffer = 0;
  }
  deleteTexture(rs.terminalDiagnostics.debugTexture);
  rs.terminalDiagnostics.valid = false;
  deleteTexture(rs.targets.texBlackhole);
  deleteTexture(rs.targets.texBlackholeCompare);
  deleteTexture(rs.targets.texBrightness);
  deleteTexture(rs.targets.texBloomFinal);
  deleteTexture(rs.targets.texTonemapped);
  deleteTexture(rs.targets.texDepthEffects);
  for (auto &texture : rs.targets.texDownsampled) {
    deleteTexture(texture);
  }
  for (auto &texture : rs.targets.texUpsampled) {
    deleteTexture(texture);
  }

  rs.targets.texBlackhole = createColorTexture32f(newWidth, newHeight);
  rs.targets.texBlackholeCompare = createColorTexture32f(newWidth, newHeight);
  rs.targets.texBrightness = createColorTexture(newWidth, newHeight);
  rs.targets.texBloomFinal = createColorTexture(newWidth, newHeight);
  rs.targets.texTonemapped = createColorTexture(newWidth, newHeight);
  rs.targets.texDepthEffects = createColorTexture(newWidth, newHeight);
  const std::size_t pixelCount = static_cast<std::size_t>(newWidth) *
                                 static_cast<std::size_t>(newHeight);
  rs.terminalDiagnostics.codes.resize(pixelCount);
  glCreateBuffers(1, &rs.terminalDiagnostics.codesBuffer);
  glNamedBufferData(rs.terminalDiagnostics.codesBuffer,
                    static_cast<GLsizeiptr>(pixelCount * sizeof(std::uint32_t)), nullptr,
                    GL_DYNAMIC_READ);
  glCreateTextures(GL_TEXTURE_2D, 1, &rs.terminalDiagnostics.debugTexture);
  glTextureStorage2D(rs.terminalDiagnostics.debugTexture, 1, GL_RGBA8, newWidth, newHeight);
  // glbinding declares texture parameters in the included generated functions header.
  // NOLINTNEXTLINE(misc-include-cleaner)
  gl::glTextureParameteri(rs.terminalDiagnostics.debugTexture, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
  // NOLINTNEXTLINE(misc-include-cleaner)
  gl::glTextureParameteri(rs.terminalDiagnostics.debugTexture, GL_TEXTURE_MAG_FILTER, GL_NEAREST);

  for (int i = 0; i < K_MAX_BLOOM_ITERATIONS; ++i) {
    auto const index = static_cast<std::size_t>(i);
    int const downWidth = std::max(1, newWidth >> (i + 1));
    int const downHeight = std::max(1, newHeight >> (i + 1));
    int const upWidth = std::max(1, newWidth >> i);
    int const upHeight = std::max(1, newHeight >> i);
    rs.targets.texDownsampled.at(index) = createColorTexture(downWidth, downHeight);
    rs.targets.texUpsampled.at(index) = createColorTexture(upWidth, upHeight);
  }

  rs.targets.renderWidth = newWidth;
  rs.targets.renderHeight = newHeight;

#if BLACKHOLE_HAS_CUDA
  rs.dispatch.cudaManager.resize(rs.targets.texBlackhole, newWidth, newHeight);
#endif
}

} // namespace blackhole
