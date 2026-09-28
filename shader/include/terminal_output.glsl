#ifndef BLACKHOLE_TERMINAL_OUTPUT_GLSL
#define BLACKHOLE_TERMINAL_OUTPUT_GLSL

#include "include/ray_terminal.h"

layout(std430, binding = 7) buffer TerminalCodes {
  uint terminalCodes[];
};
layout(rgba8, binding = 1) uniform writeonly image2D terminalDebugImage;
uniform float terminalWriteEnabled = 0.0;
uniform float terminalDebugEnabled = 0.0;

vec3 bhTerminalColor(int terminal) {
  if (terminal == BH_TERMINAL_HORIZON) return vec3(0.85, 0.08, 0.08);
  if (terminal == BH_TERMINAL_ESCAPE) return vec3(0.08, 0.35, 0.95);
  if (terminal == BH_TERMINAL_DISK_HIT) return vec3(1.0, 0.72, 0.08);
  if (terminal == BH_TERMINAL_OPAQUE_MEDIUM) return vec3(0.55, 0.25, 0.85);
  if (terminal == BH_TERMINAL_MAX_STEPS) return vec3(0.0, 0.9, 0.9);
  if (terminal == BH_TERMINAL_NON_FINITE) return vec3(1.0, 0.0, 0.7);
  if (terminal == BH_TERMINAL_INVARIANT_FAILURE) return vec3(1.0);
  return vec3(0.12);
}

void bhRecordTerminal(ivec2 pixel, ivec2 imageExtent, int terminal) {
  if (terminalWriteEnabled < 0.5) return;
  uint index = uint(pixel.y * imageExtent.x + pixel.x);
  terminalCodes[index] = uint(terminal);
  if (terminalDebugEnabled > 0.5) {
    imageStore(terminalDebugImage, pixel, vec4(bhTerminalColor(terminal), 1.0));
  }
}

#endif
