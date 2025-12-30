# MangoHUD Cleanroom HUD Scope

This doc scopes a cleanroom HUD port from MangoHUD into Blackhole.
No code reuse; only public behavior and metric definitions are referenced.

## Source references (MangoHUD)
- src/hud_elements.cpp/h: element list, ordering, formatting decisions.
- src/overlay_params.h: config flags and naming conventions.
- src/fps_metrics.h: frame time and FPS aggregation ideas.
- src/gl/gl_hud.cpp: OpenGL HUD glue (conceptual only).
- src/cpu.cpp, src/gpu.cpp, src/memory.cpp, src/net.cpp: metric categories.

## Overlay params (MangoHUD)
- overlay_params.h exposes a wide flag set for HUD elements and tuning knobs.
- Relevant minimal subset for Blackhole:
  - fps, frametime, frame_timing, frame_timing_detailed
  - resolution, present_mode, refresh_rate, vsync
  - text_outline, background_color, text_color, fps_color_change
  - hud_no_margin, hud_compact, horizontal
  - benchmark_percentiles, fps_sampling_period

## Target HUD elements for Blackhole
- FPS, CPU frame time, and frametime graph.
- GPU pass timings (fragment/compute/bloom/tonemap/depth).
- Resolution and render scale.
- VSync state (swap interval) and present mode (GL: on/off).
- CPU usage, GPU usage, temperatures, VRAM, RAM.
- Optional: battery status and network throughput.

## Config + vsync notes (from README)
- MANGOHUD_CONFIG supports comma-delimited options; `read_cfg` uses config files
  in addition to env options.
- OpenGL vsync values: `-1` adaptive, `0` off, `1` on, `n` sync to refresh/n.
- Present mode is shown as vsync status for OpenGL.
- Default-enabled metrics include `fps`, `frame_timing`, `cpu_stats`, `gpu_stats`.
- Logging controls include `output_folder`, `output_file`, `log_interval`, `log_duration`,
  `benchmark_percentiles`, and toggle hotkeys (`toggle_hud`, `toggle_logging`).

## Cleanroom integration plan
1. Define a lightweight HUD settings struct in Blackhole settings.
2. Sample metrics on a fixed cadence (e.g., 4-10 Hz) into a ring buffer.
3. Compute FPS/frametime summaries from frame timestamps.
4. Add an ImGui overlay panel that can be toggled and repositioned.
5. Export optional CSV logs for tuning and regression checks.

## Metric sources (planned)
- CPU usage: /proc/stat deltas (Linux) with fallback to std::thread count only.
- RAM: /proc/meminfo; VRAM: vendor-specific (NVML/AMDGPU sysfs) when available.
- GPU temps: vendor-specific (NVML/AMDGPU sysfs); optional stub if unavailable.
- Network: /proc/net/dev for RX/TX deltas.
- FPS metrics: `fpsMetrics` keeps a frametime ring (max_size=10k), sorts descending,
  and emits AVG plus percentile FPS (values in [0,1]) via `1000 / frametime`.

## Validation
- Compare FPS/frametime to MangoHUD overlay on the same scene.
- Validate GPU timings vs GL_TIME_ELAPSED queries.
- Sanity-check temps and memory vs external tools (nvidia-smi/radeontop).
- Validate logging summaries against MangoHud percentiles (97/avg/1/0.1 defaults).

## Notes
- Default HUD is minimal to avoid UI noise.
- All vendor-specific metrics are optional and should fail gracefully.
- UI naming should align with existing Controls/Performance panels.
