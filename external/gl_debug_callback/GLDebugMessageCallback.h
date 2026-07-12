/**
 * @file GLDebugMessageCallback.h
 * @brief OpenGL debug message callback declaration (originally by Plasmoxy 2020).
 */

// Header for GLDebugMessageCallback by Plasmoxy 2020
// Feel free to use this in any way.
#pragma once

#include <iostream>

#include "gl_loader.h"
#include <GLFW/glfw3.h>

/**
 * @brief OpenGL KHR_debug callback that prints driver diagnostics to stderr.
 *
 * Register with glDebugMessageCallback() during renderer initialisation.
 * All parameters are supplied by the OpenGL driver; @p data is unused.
 *
 * @param source   GL_DEBUG_SOURCE_* constant identifying the message origin.
 * @param type     GL_DEBUG_TYPE_* constant describing the message category.
 * @param id       Driver-assigned message identifier.
 * @param severity GL_DEBUG_SEVERITY_* constant (HIGH / MEDIUM / LOW / NOTIFICATION).
 * @param length   Byte length of @p msg, not including the null terminator.
 * @param msg      Null-terminated human-readable message string from the driver.
 * @param data     User pointer passed to glDebugMessageCallback (unused here).
 */
// NOLINTNEXTLINE(readability-identifier-naming) -- vendor callback must match OpenGL APIENTRY convention
void APIENTRY GLDebugMessageCallback(GLenum source, GLenum type, GLuint id, GLenum severity,
                                     GLsizei length, const GLchar *msg, const void *data);
