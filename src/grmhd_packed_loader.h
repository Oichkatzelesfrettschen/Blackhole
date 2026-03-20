/**
 * @file grmhd_packed_loader.h
 * @brief Load a nubhlight_pack GRMHD dataset into an OpenGL 3D texture.
 *
 * WHY: GRMHD simulation output (density, internal energy, velocity) is stored
 *      by nubhlight_pack as a flat RGBA32F binary with a companion JSON
 *      metadata file.  This loader parses the JSON, validates dimensions and
 *      an optional FNV-1a64 checksum, and uploads the voxel data to a
 *      GL_TEXTURE_3D for sampling in the ray-marching shaders.
 *
 * WHAT: GrmhdPackedTexture holds the GL texture handle and per-channel
 *       metadata (names, min/max normalization values).
 *       loadGrmhdPackedTexture() is the single entry point; pass upload=false
 *       for headless tests that have no GL context.
 *
 * HOW:
 *   GrmhdPackedTexture tex;
 *   std::string err;
 *   if (!loadGrmhdPackedTexture("data/grmhd.json", tex, err)) { ... }
 *   // bind tex.texture as sampler3D
 *   destroyGrmhdPackedTexture(tex); // on teardown
 *
 * References:
 *   - tools/nubhlight_pack.cpp (writeMetadata) -- canonical JSON schema
 *   - Porth et al. (2019) ApJS 243, 26 (GRMHD simulation conventions)
 */

#ifndef GRMHD_PACKED_LOADER_H
#define GRMHD_PACKED_LOADER_H

#include <string>
#include <vector>

#include "gl_loader.h"

/**
 * @brief OpenGL 3D texture and metadata for a loaded GRMHD packed dataset.
 *
 * Created by loadGrmhdPackedTexture() and released by destroyGrmhdPackedTexture().
 * The texture is RGBA32F; each channel corresponds to one physical field
 * (e.g., density, internal energy, v^1, v^2) as listed in @c channels.
 */
struct GrmhdPackedTexture {
  GLuint texture = 0;        /**< @brief GL texture object (GL_TEXTURE_3D, RGBA32F). */
  int width = 0;             /**< @brief Voxel grid width (X dimension). */
  int height = 0;            /**< @brief Voxel grid height (Y dimension). */
  int depth = 0;             /**< @brief Voxel grid depth (Z dimension). */
  std::string format;        /**< @brief Texture format string (always "RGBA32F"). */
  std::string layout;        /**< @brief Data layout string (reserved for future use). */
  std::vector<std::string> channels;  /**< @brief Physical field names per channel. */
  std::vector<float> minValues;       /**< @brief Per-channel minimum for normalization. */
  std::vector<float> maxValues;       /**< @brief Per-channel maximum for normalization. */
};

/**
 * @brief Parse a nubhlight_pack JSON metadata file and upload data to a 3D texture.
 *
 * Reads the JSON at @p metadataPath, resolves the binary data file path from
 * the "bin" (or legacy "binary_file") field, validates grid dimensions and
 * optional FNV-1a64 checksum, then creates a GL_TEXTURE_3D with the voxel data.
 *
 * @param metadataPath  Path to the nubhlight_pack JSON metadata file.
 * @param texture       Output: populated GrmhdPackedTexture on success.
 * @param error         Output: human-readable error message on failure.
 * @param validate      If true, enforce schema and checksum validation.
 * @param upload        If false, skip GL texture creation (for headless tests).
 * @return true on success; false with @p error set on any failure.
 */
bool loadGrmhdPackedTexture(const std::string &metadataPath, GrmhdPackedTexture &texture,
                            std::string &error, bool validate = true, bool upload = true);

/**
 * @brief Release all GL and CPU resources owned by a GrmhdPackedTexture.
 *
 * Deletes the GL texture object and clears all metadata vectors.
 * Safe to call on a default-constructed or already-destroyed texture.
 *
 * @param texture  Texture to destroy; fields are reset to zero/empty.
 */
void destroyGrmhdPackedTexture(GrmhdPackedTexture &texture);

#endif /* GRMHD_PACKED_LOADER_H */
