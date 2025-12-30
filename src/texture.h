/**
 * @file render.h
 * @author Ross Ning (rossning92@gmail.com)
 * @brief Utility functions for GL texture management.
 * @version 0.1
 * @date 2020-08-29
 *
 * @copyright Copyright (c) 2020
 *
 */

#ifndef TEXTURE_H
#define TEXTURE_H

#include <string>

#include "gl_loader.h"

GLuint loadTexture2D(const std::string &file, bool repeat = true);

GLuint loadCubemap(const std::string &cubemapDir);

#endif /* TEXTURE_H */
