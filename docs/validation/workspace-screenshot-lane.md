# Workspace screenshot validation

The `ci` job runs `scripts/ci/workspace_screenshot_probe.sh build/CI` under
Xvfb with Mesa llvmpipe and OpenGL 4.6. The probe captures Simulator,
GOROROBA, and Diagnostics at 1280x720 and 1920x1080 with UI scale 1, plus
2560x1440 with UI scale 2. Each case retains a full window PNG, the first and
repeated layout JSON records, and the desktop log in
`build/CI/workspace-screenshot-artifacts/`. The upload runs even after a probe
failure.

The desktop accepts `--workspace-screenshot PREFIX --workspace NAME
--window-size WxH [--ui-scale S]`. Capture mode starts from default settings,
disables ImGui INI persistence, holds content time at zero, draws six frames,
rebuilds the workspace after frame three, and reads the back framebuffer after
ImGui draws frame six. `PREFIX.first.json` records frame three; `PREFIX.json`
and `PREFIX.png` record frame six. The PNG includes the UI and the scene.
The ordinary desktop startup path retains its settings and persistence behavior.

`check_workspace_layout.py` admits each default decision surface when its
visible window is fully within the viewport, is expanded, and meets a minimum
size. Simulator and Diagnostics require Viewport 500x300, Settings 300x180,
and Controls 300x180. GOROROBA requires Viewport 500x300, Operations 380x180,
and System/Strategic Map 380x180. The minimums reserve a readable scene area,
a usable control rail, and room for strategic map and operation cards at
1280x720. A two pixel edge tolerance absorbs viewport rounding. Two default
decision surfaces fail when their intersection exceeds four pixels on both
axes, except for tabs in the same dock node; a tab that its node hides behind
a sibling counts as present. The layout after Reset Layout must match the
first in window names, collapsed state, selected tabs, and dock grouping
(generated numeric dock node IDs are normalized), and every window edge must
lie within the two pixel tolerance of its first position: DockBuilder rounds
each split ratio to whole pixels, and the GOROROBA workspace at 2560x1440 and
scale 2 rebuilds one splitter a pixel from its first build.

Measured with Mesa llvmpipe under Xvfb, all nine captures (three workspaces at
1280x720 scale 1, 1920x1080 scale 1, and 2560x1440 scale 2) pass.

Set `PYTHON` to the configured interpreter before running the probe. Set
`BLACKHOLE_WORKSPACE_DISPLAY=existing` to use an existing llvmpipe display.
The JSON assertion tests run without a display through CTest test
`workspace_layout_json_validation`. A local run without a GL display can
verify the parser, script, and build, but cannot establish screenshot or
runtime layout acceptance.
