#include "hud_overlay.h"

#include <vector>

int main() {
  // Validate that the header compiles and that basic non-GL operations work.
  HudOverlay overlay;
  HudOverlayOptions opts;
  opts.scale = 1.0f;
  opts.margin = 4.0f;
  overlay.setOptions(opts);

  std::vector<HudOverlayLine> lines;
  lines.push_back({"Test", {1.0f, 1.0f, 1.0f, 1.0f}});
  overlay.setLines(lines);

  // measureText should work without GL context.
  auto size = HudOverlay::measureText("Hello", 1.0f);
  (void)size;
  return 0;
}
