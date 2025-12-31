/**
 * @file texture.h
 * @author Ross
 * @brief Utility helpers for OpenGL texture creation and loading.
 *
 * The implementation uses stb_image to load image files (PNG/JPEG etc.).
 * - 1-component images -> GL_RED
 * - 3-component images -> GL_RGB (uploaded as GL_SRGB internal format)
 * - 4-component images -> GL_RGBA (uploaded as GL_SRGB_ALPHA internal format)
 *
 * All functions assume a valid OpenGL context and that the GL loader is
 * initialized (see `gl_loader.h`). On failure, the functions return 0.
 */

#pragma once

#include <string>
#include <filesystem>
#include <cstdint>

#include "gl_loader.h"

/**
 * Load a 2D texture from disk.
 *
 * - The function chooses an internal format based on the number of components
 *   reported by the image (see file-level description).
 * - Generates mipmaps and sets reasonable filtering/wrap state.
 * - Returns the generated GL texture name, or 0 on error.
 *
 * @param file Path to image file (any format supported by stb_image).
 * @param repeat When true, GL_REPEAT is used for S/T wrap; otherwise
 *               GL_CLAMP_TO_EDGE is used.
 */
GLuint loadTexture2D(const std::string &file, bool repeat = true);

/**
 * Convenience overload accepting a filesystem path.
 */
inline GLuint loadTexture2D(const std::filesystem::path &file, bool repeat = true) {
  return loadTexture2D(file.string(), repeat);
}

/**
 * Load a cubemap from a directory containing the six faces named:
 * right.png, left.png, top.png, bottom.png, front.png, back.png
 *
 * - All faces are expected to be the same size and 3-component RGB images.
 * - Returns the generated GL texture name, or 0 on error.
 */
GLuint loadCubemap(const std::string &cubemapDir);

/**
 * Convenience overload accepting a filesystem path.
 */
inline GLuint loadCubemap(const std::filesystem::path &cubemapDir) {
  return loadCubemap(cubemapDir.string());
}

/**
 * Create a tiny 1x1 cubemap filled with the given solid color (r,g,b).
 * Useful as a fallback when a real cubemap failed to load.
 *
 * @param r Red channel in [0,255]
 * @param g Green channel in [0,255]
 * @param b Blue channel in [0,255]
 * @return Generated GL texture name or 0 on error.
 */
GLuint createSolidCubemap1x1(std::uint8_t r, std::uint8_t g, std::uint8_t b);

