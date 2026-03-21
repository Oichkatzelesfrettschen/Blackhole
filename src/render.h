/**
 * @file render.h
 * @author Ross Ning (rossning92@gmail.com)
 * @brief Utility functions for GL rendering including framebuffer creation,
 * render to texture, etc.
 * @version 0.1
 * @date 2020-08-29
 *
 * @copyright Copyright (c) 2020
 *
 */

#ifndef RENDER_H
#define RENDER_H

#include <map>
#include <string>
#include <vector>

#include "gl_loader.h"
#include <glm/glm.hpp>

/**
 * @brief Create an empty 2D color texture suitable as a framebuffer attachment.
 *
 * @param width  Texture width in pixels.
 * @param height Texture height in pixels.
 * @param hdr    When true, allocates GL_RGBA16F; otherwise GL_RGBA (8-bit).
 * @return Non-zero GL texture name on success.
 */
GLuint createColorTexture(int width, int height, bool hdr = true);

/**
 * @brief Create an empty 2D RGBA32F texture for full-precision color output.
 *
 * @param width  Texture width in pixels.
 * @param height Texture height in pixels.
 * @return Non-zero GL texture name on success.
 */
GLuint createColorTexture32f(int width, int height);

/**
 * @brief Create a single-channel (R32F) 2D texture from a float array.
 *
 * @param width  Texture width in pixels.
 * @param height Texture height in pixels.
 * @param data   Row-major pixel data; must contain at least width*height values.
 *               Passing fewer values uploads NULL pixels.
 * @return Non-zero GL texture name on success.
 */
GLuint createFloatTexture2D(int width, int height, const std::vector<float> &data);

/**
 * @brief Create a single-channel (R32F) 3D texture from a float array.
 *
 * @param width  Texture width in voxels.
 * @param height Texture height in voxels.
 * @param depth  Texture depth in voxels.
 * @param data   Flat voxel data; must contain at least width*height*depth values.
 * @return Non-zero GL texture name on success.
 */
GLuint createFloatTexture3D(int width, int height, int depth, const std::vector<float> &data);

/**
 * @brief Create an RGBA32F 3D texture from a float array.
 *
 * @param width  Texture width in voxels.
 * @param height Texture height in voxels.
 * @param depth  Texture depth in voxels.
 * @param data   Flat RGBA voxel data; must contain at least width*height*depth*4 values.
 * @return Non-zero GL texture name on success.
 */
GLuint createRGBA32FTexture3D(int width, int height, int depth, const std::vector<float> &data);

/** @brief Parameters for creating an OpenGL framebuffer object. */
struct FramebufferCreateInfo {
  GLuint colorTexture = 0;     ///< Pre-created color texture to attach as COLOR_ATTACHMENT0.
  int width = 256;             ///< Framebuffer width (used when creating the depth renderbuffer).
  int height = 256;            ///< Framebuffer height.
  bool createDepthBuffer = false; ///< When true, attach a DEPTH24_STENCIL8 renderbuffer.
};

/**
 * @brief Create and validate a framebuffer object with the given color texture attachment.
 *
 * @param info Configuration including the target texture and optional depth buffer.
 * @return Non-zero GL framebuffer name on success, 0 if the framebuffer is incomplete.
 */
GLuint createFramebuffer(const FramebufferCreateInfo &info);

/**
 * @brief Create a full-screen quad VAO covering NDC [-1,1] x [-1,1].
 *
 * The VAO has a single vertex attribute (location 0, vec3 position) and
 * covers the clip-space quad with two triangles (6 vertices).
 *
 * @return Non-zero GL VAO name.
 */
GLuint createQuadVAO();

/**
 * @brief Parameters for a single render-to-texture pass via a full-screen quad.
 *
 * Shader programs and framebuffers are created lazily on first use and cached
 * for subsequent calls with the same fragment shader / target texture pair.
 */
struct RenderToTextureInfo {
  std::string vertexShader = "shader/simple.vert"; ///< Path to vertex shader source.
  std::string fragShader;                          ///< Path to fragment shader source.
  std::map<std::string, float>      floatUniforms;    ///< Float uniforms to set before draw.
  std::map<std::string, glm::vec3>  vec3Uniforms;     ///< vec3 uniforms to set before draw.
  std::map<std::string, glm::vec4>  vec4Uniforms;     ///< vec4 uniforms to set before draw.
  std::map<std::string, glm::mat3>  mat3Uniforms;     ///< mat3 uniforms to set before draw.
  std::map<std::string, GLuint>     textureUniforms;  ///< 2D texture samplers.
  std::map<std::string, GLuint>     texture3DUniforms;///< 3D texture samplers.
  std::map<std::string, GLuint>     cubemapUniforms;  ///< Cubemap texture samplers.
  GLuint targetTexture{};  ///< Destination GL texture name.
  int width{};             ///< Viewport and framebuffer width in pixels.
  int height{};            ///< Viewport and framebuffer height in pixels.

  // Out-of-line destructor prevents -Winline warnings from std::string/std::map expansion.
  ~RenderToTextureInfo();
};

/**
 * @brief Execute a render-to-texture pass using a full-screen quad.
 *
 * Lazily creates the framebuffer and shader program on first use.  Uniforms,
 * textures, and the viewport are configured from @p rtti before drawing.
 *
 * @param rtti All rendering parameters for this pass.
 */
void renderToTexture(const RenderToTextureInfo &rtti);

/**
 * @brief Release all cached framebuffers and uniform location caches.
 *
 * Call when shader programs are recompiled or the GL context is about to be
 * destroyed to avoid stale GL object references.
 */
void clearRenderToTextureCache();

/**
 * @brief Recompile every cached render-to-texture shader program in place.
 *
 * WHY: The ShaderWatcher hot-reload path needs to re-issue all GL program
 *      links when a fragment or vertex source file changes on disk.
 * WHAT: Iterates the internal frag->program map, calls createShaderProgram()
 *       for each entry, swaps the handle, and clears stale uniform caches.
 *       Programs that fail to recompile are left unchanged so rendering
 *       continues with the last working version.
 * HOW: Call once per hot-reload event, after all changed paths are detected.
 *      The compute shader is owned by main.cpp and must be reloaded separately.
 */
void reloadAllRenderShaders();

#endif /* RENDER_H */
