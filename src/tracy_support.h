#pragma once

#ifdef TRACY_ENABLE
#include <tracy/Tracy.hpp>
#endif

#ifndef TRACY_ENABLE
#define ZoneScoped
#define ZoneScopedN(name)
#define FrameMark
#define FrameMarkNamed(name)
#define TracyPlot(name, value)
#endif
