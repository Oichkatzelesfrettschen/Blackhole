# Capture identity and fixed-parameter comparisons

Every recorded PNG and exported PNG or PFM has a `.json` sidecar. The sidecar
records `source_revision` from Git at CMake configure time, `scene_mode`,
`tracer_spin`, `lut_spin`, `lut_spin_clamped`, and `disk_transfer_mode`.
The LUT spin is the tracer spin limited to [-0.99, 0.99]; the black-hole
tracer retains its effective spin. `requested_backend` and
`requested_geodesic_model` record command-line selections when supplied;
their `effective_*` peers record the normalized contract. The requested and
effective step count and size show quality-tier and legacy-beauty adjustments.
Existing `backend`, `geodesic_model`, `max_steps`, and `step_size` remain the
effective values. `kerr_spin` remains the black-hole tracer spin.

The display fields are `tone_mapping_enabled`, `exposure`, `gamma`,
`bloom_strength`, `bloom_threshold`, `film_grain_active`, `vignette_active`,
and `chromatic_aberration_active`. Active means tone mapping is enabled and
the corresponding post-process strength is positive. Observer sidecars also record FOV, look angles, spin
deficit, and radius offset. The scene mode distinguishes observer-sky from
the black-hole and tesseract scenes; the black-hole tracer fields describe
the black-hole state even for an observer-sky capture.

Set `PYTHON` to the configured interpreter, build `Blackhole`, and run each
script into a new output directory on an OpenGL 4.6 machine:

```sh
PYTHON="$PYTHON" scripts/display_transform_comparison.sh build/Release captures/display
PYTHON="$PYTHON" scripts/observer_sampling_comparison.sh build/Release captures/observer
```

The display script uses the simulator's default camera from an empty output
working directory, so the repository's saved `settings.json` is not read.
Every tile fixes 960 x 720 pixels and content time
at zero. It compares bloom off/on at exposure 1, exposure 0.5/1/2 with bloom
off, and tone mapping off/on at exposure 1 with bloom off. Each invocation
sets exposure, bloom strength, and tone mapping explicitly. The script checks
those sidecar values and camera identity before writing `index.md`.

The observer script selects the Miller prograde ISCO view, tracks the bright
patch at 0.1-degree vertical FOV, and compares 640 x 480 with 1280 x 960.
Frozen content time gives zero observer motion and one shader sample per pixel.
The shader's motion blur sample count follows the angular turn and has no
independent export control. The script checks resolution and observer framing
in the sidecars before writing `index.md`.

Both indexes report mean and 99th-percentile raw PFM luminance and display
PNG code-value luminance. The PFM precedes bloom and tone mapping. PNG code
values represent the display output rather than linear radiance. Preserve the
paired PNG, PFM, sidecars, stdout/stderr logs, and index for each tile.

## Measured results

NVIDIA GeForce RTX 4070 Ti, OpenGL 4.6.0 NVIDIA 615.71.09, revision
`d8775d2` plus this change.

Display transform, simulator default view at 960 x 720 (raw mean 0.0173 and
raw P99 0.135 in every tile, so the controlled variable never reached the
pre-postprocess image):

| Controlled variable | Value | Display mean | Display P99 |
| --- | --- | ---: | ---: |
| bloom | off / on | 0.104 / 0.107 | 0.671 / 0.690 |
| exposure | 0.5 / 1 / 2 | 0.073 / 0.104 / 0.151 | 0.490 / 0.671 / 0.823 |
| tone mapping | off / on | 0.023 / 0.104 | 0.247 / 0.671 |

Bloom adds 2.4% to mean display luminance. The broad diffuse light in a
no-bloom Physical capture is therefore disk emission in the raw image lifted
by exposure and tone mapping, not bloom.

Observer view at the magnified patch (field of view 0.1 degrees), exposure
0.25 in both tiles:

| Resolution | Raw mean | Raw P99 | Display mean | Display P99 |
| --- | ---: | ---: | ---: | ---: |
| 640 x 480 | 2.8410 | 3.4853 | 0.857 | 0.951 |
| 1280 x 960 | 2.8429 | 3.4843 | 0.869 | 0.951 |

The magnified patch is smooth at both resolutions, and the raw statistics
agree within 0.1%, so frozen single-sample captures show no rectangular
streaks; streaks in a moving capture would come from the time-dependent sky
rotation and its motion-blur samples. At the default exposure the patch maps
to display white (display P99 1.0), which hides any structure; the script
fixes exposure at 0.25 for that reason. The full-sky inset shows color
fringes along the patch boundary at both resolutions.
