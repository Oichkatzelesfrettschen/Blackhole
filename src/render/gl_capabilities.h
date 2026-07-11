/**
 * @file gl_capabilities.h
 * @brief Runtime OpenGL feature queries (extension presence and version-gated
 *        draw features) used to decide which render and probe paths the driver
 *        supports at startup.
 */

#ifndef BLACKHOLE_RENDER_GL_CAPABILITIES_H
#define BLACKHOLE_RENDER_GL_CAPABILITIES_H

namespace blackhole {

/** @brief True when the named GL extension is present in the current context. */
bool hasExtension(const char *name);

/** @brief True when gl_DrawID is available (GL 4.6 or GL_ARB_shader_draw_parameters). */
bool supportsDrawId();

/** @brief True when glMultiDrawArraysIndirect is available (GL 4.3 or
 *         GL_ARB_multi_draw_indirect). */
bool supportsMultiDrawIndirect();

/** @brief True when indirect draw-count is available (GL 4.6 or
 *         GL_ARB_indirect_parameters). */
bool supportsIndirectCount();

} // namespace blackhole

#endif // BLACKHOLE_RENDER_GL_CAPABILITIES_H
