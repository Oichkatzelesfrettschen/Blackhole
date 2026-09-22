/**
 * @file texture.cpp
 * @brief Implementation of OpenGL texture loading and creation helpers.
 *
 * Uses stb_image for image decoding and applies anisotropic filtering when
 * the GL_EXT/ARB_texture_filter_anisotropic extension (or OpenGL 4.6) is
 * available.
 */

#include "texture.h"

// C++ system headers
#include <algorithm>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

// Third-party library headers
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions-patches.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <stb_image.h>

namespace {
bool supportsAnisotropy() {
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
  bool const versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  bool hasExt = false;
  GLint count = 0;
  glGetIntegerv(GL_NUM_EXTENSIONS, &count);
  for (GLint i = 0; i < count; ++i) {
    const char *ext =
        reinterpret_cast<const char *>(glGetStringi(GL_EXTENSIONS, static_cast<GLuint>(i)));
    if (ext != nullptr && (std::string(ext) == "GL_EXT_texture_filter_anisotropic" ||
                           std::string(ext) == "GL_ARB_texture_filter_anisotropic")) {
      hasExt = true;
      break;
    }
  }
  supported = versionIs46 || hasExt;
  return supported;
}

void applyAnisotropy(GLenum target) {
  if (!supportsAnisotropy()) {
    return;
  }
  GLfloat maxAniso = 0.0f;
  glGetFloatv(GL_MAX_TEXTURE_MAX_ANISOTROPY, &maxAniso);
  if (maxAniso <= 0.0f) {
    return;
  }
  constexpr GLfloat kDefaultAniso = 8.0f;
  GLfloat const aniso = std::min(maxAniso, kDefaultAniso);
  glTexParameterf(target, GL_TEXTURE_MAX_ANISOTROPY, aniso);
}

// A Git-LFS pointer file opens with the spec line "version https://git-lfs...".
bool isGitLfsPointer(const std::string &file) {
  std::ifstream stream(file, std::ios::binary);
  if (!stream) {
    return false;
  }
  std::string firstLine;
  std::getline(stream, firstLine);
  return firstLine.starts_with("version https://git-lfs");
}
} // namespace

GLuint loadTexture2D(const std::string &file, bool repeat) {
  GLuint textureID;
  glGenTextures(1, &textureID);

  int width;
  int height;
  int comp;
  unsigned char *data = stbi_load(file.c_str(), &width, &height, &comp, 0);
  if (data != nullptr) {
    // stb_image returns the file's native channel count (desired_channels = 0),
    // so a two-channel grey+alpha image must map to GL_RG; without this branch it
    // would fall through to GL_RGB and read three bytes per texel from a
    // two-byte-per-texel buffer.
    GLenum format = GL_RGB;
    GLenum internalFormat = GL_RGB;
    if (comp == 1) {
      format = GL_RED;
      internalFormat = GL_RED;
    } else if (comp == 2) {
      format = GL_RG;
      internalFormat = GL_RG;
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
    // A Git-LFS-tracked asset that has not been fetched is a text pointer file,
    // not an image; name that case so the fix (git lfs pull) is obvious rather
    // than a bare decode failure.
    std::cerr << "ERROR: Failed to load texture at: " << file;
    if (isGitLfsPointer(file)) {
      std::cerr << " (Git-LFS pointer -- run 'git lfs pull' to fetch the image)";
    }
    std::cerr << '\n';
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
  int width;
  int height;
  int comp;
  for (GLuint i = 0; i < faces.size(); i++) {
    unsigned char *data =
        stbi_load((cubemapDir + "/" + faces.at(i) + ".png").c_str(), &width, &height, &comp, 0);
    if (data != nullptr) {
      glTexImage2D(GL_TEXTURE_CUBE_MAP_POSITIVE_X + i, 0, GL_SRGB, width, height, 0, GL_RGB,
                   GL_UNSIGNED_BYTE, data);
      stbi_image_free(data);
    } else {
      std::cout << "Cubemap texture failed to load at path: "
                << (cubemapDir + "/" + faces.at(i) + ".png").c_str() << '\n';
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
    glTexImage2D(GL_TEXTURE_CUBE_MAP_POSITIVE_X + i, 0, GL_SRGB, 1, 1, 0, GL_RGB, GL_UNSIGNED_BYTE,
                 pixel);
  }

  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_CUBE_MAP, GL_TEXTURE_WRAP_R, GL_CLAMP_TO_EDGE);

  return textureID;
}
