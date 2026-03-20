// Header for GLDebugMessageCallback by Plasmoxy 2020
// Feel free to use this in any way.
#pragma once

#include <iostream>

#include "gl_loader.h"
#include <GLFW/glfw3.h>

// NOLINTNEXTLINE(readability-identifier-naming) -- vendor callback must match OpenGL APIENTRY convention
void APIENTRY GLDebugMessageCallback(GLenum source, GLenum type, GLuint id, GLenum severity,
                                     GLsizei length, const GLchar *msg, const void *data);
