# Default renderer promotion evidence

The desktop contract starts with fragment dispatch, Kerr reference geodesics,
thin-surface emission, and balanced quality. The before path selects the
fragment-only legacy beauty geodesic. The after path selects the default
fragment and Kerr reference contract. Both runs use the same saved startup
settings and default startup camera. Preserve the settings file and display
configuration used for the runs with the evidence bundle.

Build the executable, then run the capture on a GL 4.6 GPU and an available
display:

```sh
cmake --build build/Release -j12 --target Blackhole camera_math_test
PYTHON=${PYTHON:-python3} scripts/renderer_promotion_evidence.sh build/Release build/Release/renderer-promotion-evidence
```

The script writes `legacy.png` and `default.png`, their `.json` sidecars, one
GPU timing CSV per path, a `glxinfo.txt` snapshot, process logs, and
`summary.md`. Use a new output directory for each run. The script hides the
GLFW window with `BLACKHOLE_WINDOW_HIDDEN=1`; it still requires a working
display and GL context. The sidecars record the effective contract, camera,
resolution, spin, and scene fields.

`--export-frames 180` exports the final image on settled frame 180 and ends
after that frame. The option fixes content time at zero for repeatable output.
Without the option, ordinary exports still capture on settled frame 5 and
exit after frame 6. The timing logger records every frame
with `BLACKHOLE_GPU_TIMING_LOG_STRIDE=1`; the script analyzes the final 170
rows to exclude the first ten settled frames. A GPU query can complete after
its issuing frame, so a CSV row reports the most recently resolved duration
for each pass. Empty pass cells mean the pass did not supply a resolved sample.

Each pass column is GPU elapsed milliseconds. `total_gpu_ms` sums available
pass durations in each selected row; it is a sum of measured pass work, not a
wall-clock frame time. Median is the middle value (or mean of two middle
values). p95 uses the nearest-rank value. The two images show the default
startup camera through different geodesic models; their difference is a
visual comparison, not a pixel-parity requirement. Record any changed
settings, scene, GPU driver, or resolution when interpreting the result.

## Promotion record

Measured on an NVIDIA GeForce RTX 4070 Ti (OpenGL 4.6.0 NVIDIA 615.71.09) at
1324 x 1032, commit `051852b`, with no saved settings (built-in defaults):
camera distance 240, pitch 10 degrees, vertical field of view 23.4 degrees,
spin 0, balanced tier at 300 steps of 0.1.

| Pass (ms, median / p95) | Legacy beauty | Default Kerr reference |
| --- | ---: | ---: |
| fragment | 4.285 / 5.527 | 1.986 / 3.925 |
| bloom | 0.111 / 0.364 | 0.112 / 0.186 |
| tone map | 0.017 / 0.085 | 0.017 / 0.032 |
| total GPU | 4.413 / 5.935 | 2.115 / 4.144 |

| Terminal class (pixels) | Legacy beauty | Default Kerr reference |
| --- | ---: | ---: |
| captured | 0 | 5626 |
| escaped | 0 | 313216 |
| disk hit | 0 | 1047526 |
| max steps | 1366368 | 0 |

The legacy tracer exhausts every pixel at the default camera: 300 steps of
0.1 cover 30 units of path from a camera 240 units out, so no ray reaches the
hole or the disk and the image is the sky alone
([before](figures/promotion-legacy-beauty.jpg)). The Kerr reference path
integrates in Mino time with the adaptive step of `bhAdaptiveStep`, reaches
the horizon, disk, and escape radius, and shows the shadow, the lensed far
side of the disk, and the disk
([after](figures/promotion-default-kerr.jpg)). Its lower fragment time
follows from rays that terminate on the disk or horizon, where the legacy
loop spends its whole budget on every pixel; the timing compares the two
paths as shipped, not equal work.

The rendered-output lane supplies the output metrics for the default
contract: the Kerr fragment path passes the critical-curve, spin-orientation,
disk-limb, disk-rotation, and quality-tier scenes of
[rendered-output-lane.md](rendered-output-lane.md) on this GPU and on Mesa
llvmpipe.
