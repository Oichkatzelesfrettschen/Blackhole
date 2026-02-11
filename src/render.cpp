#include "render.h"

// C++ system headers
#include <iostream>
#include <unordered_map>

// Third-party library headers
#include <GLFW/glfw3.h>
#include <glm/gtc/type_ptr.hpp>

// Local headers
#include "gl_loader.h"
#include "shader.h"

// Out-of-line destructor definition to prevent -Winline warnings.
// When the compiler tries to inline the implicit destructor, it must expand
// all std::string and std::map destructor calls, which exceeds the
// --param large-function-growth limit. Defining it here forces the compiler
// to emit a single non-inlined destructor call site.
RenderToTextureInfo::~RenderToTextureInfo() = default;

GLuint createColorTexture(int width, int height, bool hdr) {
  GLuint colorTexture;
  glGenTextures(1, &colorTexture);

  glBindTexture(GL_TEXTURE_2D, colorTexture);
  glTexImage2D(GL_TEXTURE_2D, 0, hdr ? GL_RGBA16F : GL_RGBA, width, height, 0, GL_RGBA,
               hdr ? GL_FLOAT : GL_UNSIGNED_BYTE, NULL);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);

  return colorTexture;
}

GLuint createColorTexture32f(int width, int height) {
  GLuint colorTexture;
  glGenTextures(1, &colorTexture);

  glBindTexture(GL_TEXTURE_2D, colorTexture);
  glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA32F, width, height, 0, GL_RGBA, GL_FLOAT, nullptr);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);

  return colorTexture;
}

GLuint createFloatTexture2D(int width, int height, const std::vector<float> &data) {
  GLuint texture;
  glGenTextures(1, &texture);

  glBindTexture(GL_TEXTURE_2D, texture);

  const std::size_t expected = static_cast<std::size_t>(width) * static_cast<std::size_t>(height);
  const float *pixels = data.size() >= expected ? data.data() : nullptr;

  glTexImage2D(GL_TEXTURE_2D, 0, GL_R32F, width, height, 0, GL_RED, GL_FLOAT, pixels);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);

  return texture;
}

GLuint createFloatTexture3D(int width, int height, int depth, const std::vector<float> &data) {
  GLuint texture;
  glGenTextures(1, &texture);

  glBindTexture(GL_TEXTURE_3D, texture);

  const std::size_t expected = static_cast<std::size_t>(width) *
                               static_cast<std::size_t>(height) *
                               static_cast<std::size_t>(depth);
  const float *pixels = data.size() >= expected ? data.data() : nullptr;

  glTexImage3D(GL_TEXTURE_3D, 0, GL_R32F, width, height, depth, 0, GL_RED, GL_FLOAT, pixels);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_S, GL_REPEAT);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_T, GL_REPEAT);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_R, GL_REPEAT);

  return texture;
}

GLuint createRGBA32FTexture3D(int width, int height, int depth, const std::vector<float> &data) {
  GLuint texture;
  glGenTextures(1, &texture);

  glBindTexture(GL_TEXTURE_3D, texture);

  const std::size_t expected = static_cast<std::size_t>(width) *
                               static_cast<std::size_t>(height) *
                               static_cast<std::size_t>(depth) * 4;
  const float *pixels = data.size() >= expected ? data.data() : nullptr;

  glTexImage3D(GL_TEXTURE_3D, 0, GL_RGBA32F, width, height, depth, 0, GL_RGBA, GL_FLOAT, pixels);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_R, GL_CLAMP_TO_EDGE);

  return texture;
}

GLuint createFramebuffer(const FramebufferCreateInfo &info) {
  GLuint framebuffer;

  // Create new framebuffer object.
  glGenFramebuffers(1, &framebuffer);
  glBindFramebuffer(GL_FRAMEBUFFER, framebuffer);

  // Bind color attachement.
  glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, info.colorTexture, 0);

  if (info.createDepthBuffer) {
    // Single renderbuffer object for both depth and stencil.
    GLuint rbo;
    glGenRenderbuffers(1, &rbo);
    glBindRenderbuffer(GL_RENDERBUFFER, rbo);
    glRenderbufferStorage(GL_RENDERBUFFER, GL_DEPTH24_STENCIL8, info.width, info.height);
    glFramebufferRenderbuffer(GL_FRAMEBUFFER, GL_DEPTH_STENCIL_ATTACHMENT, GL_RENDERBUFFER, rbo);
  }

  // Check the completeness of the framebuffer.
  if (glCheckFramebufferStatus(GL_FRAMEBUFFER) != GL_FRAMEBUFFER_COMPLETE) {
    std::cout << "ERROR: Framebuffer is not complete!" << std::endl;
    glBindFramebuffer(GL_FRAMEBUFFER, 0);
    return 0;
  }

  glBindFramebuffer(GL_FRAMEBUFFER, 0);

  return framebuffer;
}

GLuint createQuadVAO() {
  std::vector<glm::vec3> vertices;

  vertices.push_back(glm::vec3(-1, -1, 0));
  vertices.push_back(glm::vec3(-1, 1, 0));
  vertices.push_back(glm::vec3(1, 1, 0));

  vertices.push_back(glm::vec3(1, 1, 0));
  vertices.push_back(glm::vec3(1, -1, 0));
  vertices.push_back(glm::vec3(-1, -1, 0));

  // Create VBO
  GLuint vao;
  glGenVertexArrays(1, &vao);
  glBindVertexArray(vao);

  GLuint vbo;
  glGenBuffers(1, &vbo);
  glBindBuffer(GL_ARRAY_BUFFER, vbo);
  glBufferData(GL_ARRAY_BUFFER,
               static_cast<GLsizeiptr>(vertices.size() * sizeof(glm::vec3)),
               &vertices[0], GL_STATIC_DRAW);

  // 1st attribute buffer: positions
  glEnableVertexAttribArray(0);
  glBindBuffer(GL_ARRAY_BUFFER, vbo);
  glVertexAttribPointer(0,        // attribute
                        3,        // size
                        GL_FLOAT, // type
                        GL_FALSE, // normalized?
                        0,        // stride
                        nullptr // array buffer offset
  );

  glBindVertexArray(0);

  return vao;
}

static std::map<GLuint, GLuint> textureFramebufferMap;
static std::map<std::string, GLuint> shaderProgramMap;

// PERFORMANCE FIX: Cache uniform locations to avoid expensive glGetUniformLocation calls every frame
static std::unordered_map<GLuint, std::unordered_map<std::string, GLint>> uniformLocationCache;

// Helper function to get cached uniform location
static GLint getCachedUniformLocation(GLuint program, const std::string &name) {
  auto &cache = uniformLocationCache[program];
  auto it = cache.find(name);
  if (it != cache.end()) {
    return it->second;  // Cache hit - fast hash lookup
  }

  // Cache miss - query driver once and store result
  GLint loc = glGetUniformLocation(program, name.c_str());
  cache[name] = loc;
  return loc;
}

static bool bindToTextureUnit(GLuint program, const std::string &name, GLenum textureType,
                              GLuint texture, int textureUnitIndex) {
  GLint loc = getCachedUniformLocation(program, name);  // PERF FIX: Use cached location
  if (loc != -1) {
    glUniform1i(loc, textureUnitIndex);

    // Set up the texture units.
    glActiveTexture(GL_TEXTURE0 + static_cast<GLuint>(textureUnitIndex));
    glBindTexture(textureType, texture);
    return true;
  } else {
    static std::set<std::string> warnedMissing;
    const std::string key = std::to_string(program) + ":" + name;
    if (!warnedMissing.contains(key)) {
      std::cout << "WARNING: uniform " << name << " is not found in shader" << std::endl;
      warnedMissing.insert(key);
    }
    return false;
  }
}

void clearRenderToTextureCache() {
  for (auto const &[texture, framebuffer] : textureFramebufferMap) {
    glDeleteFramebuffers(1, &framebuffer);
  }
  textureFramebufferMap.clear();
  uniformLocationCache.clear();  // Clear uniform location cache too
}

void renderToTexture(const RenderToTextureInfo &rtti) {
  static GLuint quadVao = 0;
  if (quadVao == 0) {
    quadVao = createQuadVAO();
  }

  // Lazy creation of a framebuffer as the render target and attach the texture
  // as the color attachment.
  GLuint targetFramebuffer;
  if (!textureFramebufferMap.count(rtti.targetTexture)) {
    FramebufferCreateInfo createInfo;
    createInfo.colorTexture = rtti.targetTexture;
    targetFramebuffer = createFramebuffer(createInfo);
    textureFramebufferMap[rtti.targetTexture] = targetFramebuffer;
  } else {
    targetFramebuffer = textureFramebufferMap[rtti.targetTexture];
  }

  // Lazy-load the shader program.
  GLuint program;
  if (!shaderProgramMap.count(rtti.fragShader)) {
    program = createShaderProgram(rtti.vertexShader, rtti.fragShader);
    shaderProgramMap[rtti.fragShader] = program;
  } else {
    program = shaderProgramMap[rtti.fragShader];
  }

  // Rendering a quad.
  {
    glBindFramebuffer(GL_FRAMEBUFFER, targetFramebuffer);

    glViewport(0, 0, rtti.width, rtti.height);

    glDisable(GL_DEPTH_TEST);

    glClearColor(0.0f, 0.0f, 0.0f, 0.0f);
    glClear(GL_COLOR_BUFFER_BIT);

    glUseProgram(program);
    glBindVertexArray(quadVao);

    // Set up the uniforms.
    {
      // PERF FIX: Use cached uniform locations
      glUniform2f(getCachedUniformLocation(program, "resolution"),
                  static_cast<float>(rtti.width),
                  static_cast<float>(rtti.height));

      glUniform1f(getCachedUniformLocation(program, "time"),
                  static_cast<float>(glfwGetTime()));

      // Update float uniforms
      for (auto const &[name, val] : rtti.floatUniforms) {
        GLint loc = getCachedUniformLocation(program, name);  // PERF FIX: Use cached location
        if (loc != -1) {
          glUniform1f(loc, val);
        } else {
          static std::set<std::string> warnedMissing;
          const std::string key = std::to_string(program) + ":" + name;
          if (!warnedMissing.contains(key)) {
            std::cout << "WARNING: uniform " << name << " is not found" << std::endl;
            warnedMissing.insert(key);
          }
        }
      }

      // Update vec3 uniforms
      for (auto const &[name, val] : rtti.vec3Uniforms) {
        GLint loc = getCachedUniformLocation(program, name);  // PERF FIX: Use cached location
        if (loc != -1) {
          glUniform3f(loc, val.x, val.y, val.z);
        } else {
          static std::set<std::string> warnedMissing;
          const std::string key = std::to_string(program) + ":" + name;
          if (!warnedMissing.contains(key)) {
            std::cout << "WARNING: uniform " << name << " is not found" << std::endl;
            warnedMissing.insert(key);
          }
        }
      }

      // Update vec4 uniforms
      for (auto const &[name, val] : rtti.vec4Uniforms) {
        GLint loc = getCachedUniformLocation(program, name);  // PERF FIX: Use cached location
        if (loc != -1) {
          glUniform4f(loc, val.x, val.y, val.z, val.w);
        } else {
          static std::set<std::string> warnedMissing;
          const std::string key = std::to_string(program) + ":" + name;
          if (!warnedMissing.contains(key)) {
            std::cout << "WARNING: uniform " << name << " is not found" << std::endl;
            warnedMissing.insert(key);
          }
        }
      }

      // Update mat3 uniforms
      for (auto const &[name, val] : rtti.mat3Uniforms) {
        GLint loc = getCachedUniformLocation(program, name);  // PERF FIX: Use cached location
        if (loc != -1) {
          glUniformMatrix3fv(loc, 1, GL_FALSE, glm::value_ptr(val));
        } else {
          static std::set<std::string> warnedMissing;
          const std::string key = std::to_string(program) + ":" + name;
          if (!warnedMissing.contains(key)) {
            std::cout << "WARNING: uniform " << name << " is not found" << std::endl;
            warnedMissing.insert(key);
          }
        }
      }

      // Update texture uniforms
      int textureUnit = 0;
      for (auto const &[name, texture] : rtti.textureUniforms) {
        bindToTextureUnit(program, name, GL_TEXTURE_2D, texture, textureUnit++);
      }
      for (auto const &[name, texture] : rtti.texture3DUniforms) {
        bindToTextureUnit(program, name, GL_TEXTURE_3D, texture, textureUnit++);
      }
      for (auto const &[name, texture] : rtti.cubemapUniforms) {
        bindToTextureUnit(program, name, GL_TEXTURE_CUBE_MAP, texture, textureUnit++);
      }
    }

    glDrawArrays(GL_TRIANGLES, 0, 6);

    glUseProgram(0);
  }
}
