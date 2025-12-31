#pragma once

// tracy_support.h
// Lightweight wrapper for Tracy profiler integration used in this project.
//
// - When TRACY_ENABLE is defined by the build (CMake / Conan profiles), we
//   import the official Tracy header and expose its API.
// - When Tracy is not enabled, we provide no-op fallbacks for the macros the
//   codebase uses so instrumentation can remain in place without sprinkling
//   #ifdefs across the codebase.
//
// To enable: add -DTRACY_ENABLE to your target via CMake (the repo presets do
// this for development profiles).

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
#define ZoneScoped ((void)0)
#define ZoneScopedN(name) ((void)0)
#define ZoneScopedC(color) ((void)0)
#define ZoneScopedNC(name, color) ((void)0)
#define ZoneNamed(var, active) ((void)0)
#define ZoneNamedN(var, name, active) ((void)0)
#define ZoneNamedC(var, color, active) ((void)0)
#define ZoneNamedNC(var, name, color, active) ((void)0)
#define ZoneScopedS(depth) ((void)0)
#define ZoneScopedNS(name, depth) ((void)0)
#define ZoneScopedCS(color, depth) ((void)0)
#define ZoneScopedNCS(name, color, depth) ((void)0)
#define ZoneText(text) ((void)0)

// Frame markers
#define FrameMark ((void)0)
#define FrameMarkNamed(name) ((void)0)
#define FrameMarkStart(name) ((void)0)
#define FrameMarkEnd(name) ((void)0)

// Plotting
#define TracyPlot(name, value) ((void)0)
#define TracyPlotConfig(name, type, step, fill, color) ((void)0)

// Debug/Message API
#define TracyMessage(msg) ((void)0)
#define TracyMessageL(msg, len) ((void)0)
#define TracyMessageC(msg, color) ((void)0)

// Memory tracking (allocation markers)
#define TracyAlloc(ptr, size) ((void)0)
#define TracyFree(ptr) ((void)0)

// C API fallbacks (useful for mixed C/C++ files)
#define TracyCFrameMark ((void)0)
#define TracyCFrameMarkNamed(x) ((void)0)
#define TracyCFrameMarkStart(x) ((void)0)
#define TracyCFrameMarkEnd(x) ((void)0)

#define TracyCZone(ctx) ((void)0)
#define TracyCZoneN(ctx, name, active) ((void)0)
#define TracyCZoneEnd(ctx) ((void)0)

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
#define BH_PLOT_CFG(name, type, step, fill, color) \
    TracyPlotConfig(name, type, step, fill, color)

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
