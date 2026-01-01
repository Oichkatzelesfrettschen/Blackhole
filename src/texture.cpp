#include "texture.h"

// C++ system headers
#include <algorithm>
#include <iostream>
#include <vector>

// Third-party library headers
#include <stb_image.h>

static bool supportsAnisotropy() {
  static bool checked = false;
  static bool supported = false;
  if (checked) {
    return supported;
  }
  checked = true;
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  bool hasExt = false;
  GLint count = 0;
  glGetIntegerv(GL_NUM_EXTENSIONS, &count);
  for (GLint i = 0; i < count; ++i) {
    const char *ext =
        reinterpret_cast<const char *>(glGetStringi(GL_EXTENSIONS, static_cast<GLuint>(i)));
    if (ext != nullptr &&
        (std::string(ext) == "GL_EXT_texture_filter_anisotropic" ||
         std::string(ext) == "GL_ARB_texture_filter_anisotropic")) {
      hasExt = true;
      break;
    }
  }
  supported = versionIs46 || hasExt;
  return supported;
}

static void applyAnisotropy(GLenum target) {
  if (!supportsAnisotropy()) {
    return;
  }
  GLfloat maxAniso = 0.0f;
  glGetFloatv(GL_MAX_TEXTURE_MAX_ANISOTROPY, &maxAniso);
  if (maxAniso <= 0.0f) {
    return;
  }
  constexpr GLfloat kDefaultAniso = 8.0f;
  GLfloat aniso = std::min(maxAniso, kDefaultAniso);
  glTexParameterf(target, GL_TEXTURE_MAX_ANISOTROPY, aniso);
}

GLuint loadTexture2D(const std::string &file, bool repeat) {
  GLuint textureID;
  glGenTextures(1, &textureID);

  int width, height, comp;
  unsigned char *data = stbi_load(file.c_str(), &width, &height, &comp, 0);
  if (data) {
    GLenum format = GL_RGB;
    GLenum internalFormat = GL_RGB;
    if (comp == 1) {
      format = GL_RED;
      internalFormat = GL_RED;
    } else if (comp == 3) {
      format = GL_RGB;
      internalFormat = GL_SRGB;
    } else if (comp == 4) {
      format = GL_RGBA;
      internalFormat = GL_SRGB_ALPHA;
    }

    glBindTexture(GL_TEXTURE_2D, textureID);
    glTexImage2D(GL_TEXTURE_2D, 0, static_cast<GLint>(internalFormat), width, height, 0, format,
                 GL_UNSIGNED_BYTE, data);
    glGenerateMipmap(GL_TEXTURE_2D);

    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, repeat ? GL_REPEAT : GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, repeat ? GL_REPEAT : GL_CLAMP_TO_EDGE);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR_MIPMAP_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    applyAnisotropy(GL_TEXTURE_2D);

    stbi_image_free(data);
  } else {
    std::cout << "ERROR: Failed to load texture at: " << file << std::endl;
    stbi_image_free(data);
    glDeleteTextures(1, &textureID);
    textureID = 0;
  }

  return textureID;
}

GLuint loadCubemap(const std::string &cubemapDir) {
  const std::vector<std::string> faces = {"right", "left", "top", "bottom", "front", "back"};

  GLuint textureID;
  glGenTextures(1, &textureID);
  glBindTexture(GL_TEXTURE_CUBE_MAP, textureID);

  bool ok = true;
  int width, height, comp;
  for (GLuint i = 0; i < faces.size(); i++) {
    unsigned char *data =
        stbi_load((cubemapDir + "/" + faces[i] + ".png").c_str(), &width, &height, &comp, 0);
    if (data) {
      glTexImage2D(GL_TEXTURE_CUBE_MAP_POSITIVE_X + i, 0, GL_SRGB, width, height, 0, GL_RGB,
                   GL_UNSIGNED_BYTE, data);
      stbi_image_free(data);
    } else {
      std::cout << "Cubemap texture failed to load at path: "
                << (cubemapDir + "/" + faces[i] + ".png").c_str() << std::endl;
      stbi_image_free(data);
      ok = false;
    }
  }
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_WRAP_R, GL_CLAMP_TO_EDGE);
  applyAnisotropy(GL_TEXTURE_CUBE_MAP);

  if (!ok) {
    glDeleteTextures(1, &textureID);
    textureID = 0;
  }

  return textureID;
}

GLuint createSolidCubemap1x1(unsigned char r, unsigned char g, unsigned char b) {
  GLuint textureID = 0;
  glGenTextures(1, &textureID);
  glBindTexture(GL_TEXTURE_CUBE_MAP, textureID);

  unsigned char pixel[3] = {r, g, b};
  for (GLuint i = 0; i < 6; ++i) {
    glTexImage2D(GL_TEXTURE_CUBE_MAP_POSITIVE_X + i, 0, GL_SRGB, 1, 1, 0, GL_RGB,
                 GL_UNSIGNED_BYTE, pixel);
  }

  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_WRAP_R, GL_CLAMP_TO_EDGE);

  return textureID;
}
