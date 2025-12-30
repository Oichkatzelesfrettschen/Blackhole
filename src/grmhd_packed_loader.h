#ifndef GRMHD_PACKED_LOADER_H
#define GRMHD_PACKED_LOADER_H

#include <string>
#include <vector>

#include "gl_loader.h"

struct GrmhdPackedTexture {
  GLuint texture = 0;
  int width = 0;
  int height = 0;
  int depth = 0;
  std::string format;
  std::string layout;
  std::vector<std::string> channels;
  std::vector<float> minValues;
  std::vector<float> maxValues;
};

bool loadGrmhdPackedTexture(const std::string &metadataPath, GrmhdPackedTexture &out,
                            std::string &error, bool validate = true, bool upload = true);
void destroyGrmhdPackedTexture(GrmhdPackedTexture &texture);

#endif /* GRMHD_PACKED_LOADER_H */
