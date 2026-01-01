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

GLuint createColorTexture(int width, int height, bool hdr = true);
GLuint createColorTexture32f(int width, int height);
GLuint createFloatTexture2D(int width, int height, const std::vector<float> &data);
GLuint createFloatTexture3D(int width, int height, int depth, const std::vector<float> &data);
GLuint createRGBA32FTexture3D(int width, int height, int depth, const std::vector<float> &data);

struct FramebufferCreateInfo {
  GLuint colorTexture = 0;
  int width = 256;
  int height = 256;
  bool createDepthBuffer = false;
};

GLuint createFramebuffer(const FramebufferCreateInfo &info);

GLuint createQuadVAO();

struct RenderToTextureInfo {
  std::string vertexShader = "shader/simple.vert";
  std::string fragShader;
  std::map<std::string, float> floatUniforms;
  std::map<std::string, glm::vec3> vec3Uniforms;
  std::map<std::string, glm::vec4> vec4Uniforms;
  std::map<std::string, glm::mat3> mat3Uniforms;
  std::map<std::string, GLuint> textureUniforms;
  std::map<std::string, GLuint> texture3DUniforms;
  std::map<std::string, GLuint> cubemapUniforms;
  GLuint targetTexture;
  int width;
  int height;

  // Explicitly declare destructor (defined out-of-line in render.cpp)
  // This prevents -Winline warnings from implicit inline expansion of
  // std::string and std::map destructor chains
  ~RenderToTextureInfo();
};

void renderToTexture(const RenderToTextureInfo &rtti);
void clearRenderToTextureCache();

#endif /* RENDER_H */
