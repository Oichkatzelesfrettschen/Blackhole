/**
 * @file tracy_support.h
 * @brief Lightweight wrapper for Tracy profiler integration.
 *
 * When TRACY_ENABLE is defined by the build (CMake / Conan profiles), the
 * official Tracy header is included and its full API is exposed.  When Tracy
 * is disabled, every macro is replaced with a no-op so instrumentation can
 * remain in place without scattering @c \#ifdef blocks across the codebase.
 *
 * To enable: add @c -DTRACY_ENABLE to the target via CMake (development
 * presets do this automatically).
 */

#pragma once

// NOLINTBEGIN(cppcoreguidelines-macro-usage) -- Tracy profiler macros capture source location via
// __LINE__/__FUNCTION__; cannot be replaced with constexpr
#ifdef TRACY_ENABLE
// Import the full Tracy API when enabled.
#include <tracy/Tracy.hpp>
#define BH_TRACY_ENABLED 1
#else
#define BH_TRACY_ENABLED 0

// ------------------------------
// No-op fallbacks (Tracy disabled)
// ------------------------------
// Zone macros
#define ZONE_SCOPED ((void)0)
#define ZONE_SCOPED_N(name) ((void)0)
#define ZONE_SCOPED_C(color) ((void)0)
#define ZONE_SCOPED_NC(name, color) ((void)0)
#define ZONE_NAMED(var, active) ((void)0)
#define ZONE_NAMED_N(var, name, active) ((void)0)
#define ZONE_NAMED_C(var, color, active) ((void)0)
#define ZONE_NAMED_NC(var, name, color, active) ((void)0)
#define ZONE_SCOPED_S(depth) ((void)0)
#define ZONE_SCOPED_NS(name, depth) ((void)0)
#define ZONE_SCOPED_CS(color, depth) ((void)0)
#define ZONE_SCOPED_NCS(name, color, depth) ((void)0)
#define ZONE_TEXT(text) ((void)0)

// Frame markers
#define FRAME_MARK ((void)0)
#define FRAME_MARK_NAMED(name) ((void)0)
#define FRAME_MARK_START(name) ((void)0)
#define FRAME_MARK_END(name) ((void)0)

// Plotting
#define TRACY_PLOT(name, value) ((void)0)
#define TRACY_PLOT_CONFIG(name, type, step, fill, color) ((void)0)

// Debug/Message API
#define TRACY_MESSAGE(msg) ((void)0)
#define TRACY_MESSAGE_L(msg, len) ((void)0)
#define TRACY_MESSAGE_C(msg, color) ((void)0)

// Memory tracking (allocation markers)
#define TRACY_ALLOC(ptr, size) ((void)0)
#define TRACY_FREE(ptr) ((void)0)

// C API fallbacks (useful for mixed C/C++ files)
#define TRACY_C_FRAME_MARK ((void)0)
#define TRACY_C_FRAME_MARK_NAMED(x) ((void)0)
#define TRACY_C_FRAME_MARK_START(x) ((void)0)
#define TRACY_C_FRAME_MARK_END(x) ((void)0)

#define TRACY_C_ZONE(ctx) ((void)0)
#define TRACY_C_ZONE_N(ctx, name, active) ((void)0)
#define TRACY_C_ZONE_END(ctx) ((void)0)

#endif // TRACY_ENABLE

// ------------------------------
// Project convenience macros
// ------------------------------
// Mark current scope with function name
#if BH_TRACY_ENABLED
#define BH_ZONE() ZoneScopedN(__func__)
#define BH_ZONE_N(name) ZoneScopedN(name)
#define BH_ZONE_COLOR(color) ZoneScopedC(color)
#define BH_ZONE_NAME_AND_COLOR(name, color) ZoneScopedNC(name, color)

// Frame helpers
#define BH_FRAME() FrameMark
#define BH_FRAME_N(name) FrameMarkNamed(name)

// Convenience wrappers for plots/messages/allocs
#define BH_PLOT(name, value) TracyPlot(name, value)
#define BH_PLOT_CFG(name, type, step, fill, color) TracyPlotConfig(name, type, step, fill, color)

#define BH_MSG(text) TracyMessage(text)
#define BH_MSG_LEN(text, len) TracyMessageL(text, len)
#define BH_MSG_COLOR(text, color) TracyMessageC(text, color)

#define BH_ALLOC(ptr, size) TracyAlloc(ptr, size)
#define BH_FREE(ptr) TracyFree(ptr)
#else
// No-op when Tracy is disabled
#define BH_ZONE() ((void)0)
#define BH_ZONE_N(name) ((void)0)
#define BH_ZONE_COLOR(color) ((void)0)
#define BH_ZONE_NAME_AND_COLOR(name, color) ((void)0)

#define BH_FRAME() ((void)0)
#define BH_FRAME_N(name) ((void)0)

#define BH_PLOT(name, value) ((void)0)
#define BH_PLOT_CFG(name, type, step, fill, color) ((void)0)

#define BH_MSG(text) ((void)0)
#define BH_MSG_LEN(text, len) ((void)0)
#define BH_MSG_COLOR(text, color) ((void)0)

#define BH_ALLOC(ptr, size) ((void)0)
#define BH_FREE(ptr) ((void)0)
#endif // BH_TRACY_ENABLED
// NOLINTEND(cppcoreguidelines-macro-usage)
