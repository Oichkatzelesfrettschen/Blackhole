/**
 * @file gl_loader.h
 * @brief Central include point for OpenGL bindings via glbinding.
 *
 * All translation units that need OpenGL symbols should include this header
 * rather than including glbinding or gl/gl.h directly.  The using-declaration
 * brings the gl:: namespace into scope project-wide.
 */

#ifndef GL_LOADER_H
#define GL_LOADER_H

#include <glbinding/glbinding.h>
#include <glbinding/gl/gl.h>

using namespace gl;

#endif // GL_LOADER_H
