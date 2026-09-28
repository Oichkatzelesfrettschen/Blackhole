#ifndef BLACKHOLE_RAY_TERMINAL_H
#define BLACKHOLE_RAY_TERMINAL_H

// Terminal values are shared by GLSL integer results and CUDA RayTerminal.
// NOLINTBEGIN(cppcoreguidelines-macro-to-enum,modernize-macro-to-enum,cppcoreguidelines-macro-usage)
#define BH_TERMINAL_RUNNING 0
#define BH_TERMINAL_HORIZON 1
#define BH_TERMINAL_ESCAPE 2
#define BH_TERMINAL_DISK_HIT 3
#define BH_TERMINAL_OPAQUE_MEDIUM 4
#define BH_TERMINAL_MAX_STEPS 5
#define BH_TERMINAL_NON_FINITE 6
#define BH_TERMINAL_OUTSIDE_DOMAIN 7
#define BH_TERMINAL_INVARIANT_FAILURE 8
// NOLINTEND(cppcoreguidelines-macro-to-enum,modernize-macro-to-enum,cppcoreguidelines-macro-usage)

#endif
