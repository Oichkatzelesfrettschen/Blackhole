# 05 Control usability audit

Scope: every ImGui control (slider, drag, checkbox, combo, radio, input, color) in the desktop app. Build audited: Blackhole main plus the hidden-window capture fix (no CUDA, no RmlUi, GCC/clang release, NVIDIA GL). Paths below are repository-relative.

## Summary

1. 245 controls audited across 12 windows and tabs (grouped rows carry an xN count); 64 carry no flag. Flag counts (overlapping): GATED 95, UNITS 59, LABEL 53, DEAD 37, RANGE 28, DUPLICATE 11.
2. DEAD on the default path (Kerr geodesic, volumetric RTE): Render Scale and Resolution Preset (measured: 0.25 and 1.0 both render 1324 x 1032), the 12-control legacy disk block (greyed with a tooltip, each with a live Kerr twin), Depth Effects edge/curve controls (depth is the constant 1 on RTE), tesseract Projection and Eye w distance (uniforms declared, never read), HUD Overlay/Scale, Gizmo Rotate/Scale/Local, RmlUi, Use Spectral LUT (asset missing), Use GRMHD Field and time series, Time Scale on the black-hole scene.
3. Worst offenders: Render Scale; the Depth Effects window (about 17 controls acting on a constant depth); the Visuals tab, whose basic view shows greyed legacy sliders while disk brightness, temperature, turbulence, thickness, transfer, spin, exposure, and bloom sit behind "Advanced controls".
4. Persisted-but-orphaned settings keys: `adisk*`, `gravitationalLensing`, `renderBlackHole` are saved and loaded but never reach RenderState, so those UI values do not persist and a `settings.json` cannot set them.
5. Measured, black-hole export path (floor 0.012): exposure 0.01 to 50 gives MAE 0.18 to 0.48 and saturates above 10; bloom strength 0..1 gives only 0.035 to 0.065; Bloom Iterations 1..8 gives 0.03; Tone mapping off darkens the frame 9x and bypasses exposure and gamma; Background Intensity has no effect while Enable Background is off (0.0106, floor).
6. Measured spin (record path, floor 0): -0.998 0.276, 0 0.226, 0.6 0.140, 0.9 0.057 against 0.998; the default spin 0 makes "Kerr reference" identical to Schwarzschild (0.019, floor).
7. Measured wiregrid: Diagnostic mode 0.19, strength 2.0 0.036, grid scale 4 0.071; Show Ergosphere (0.012) and Scene Preserve (0.010) sit at the floor at default spin and mode.
8. Tesseract: no scripted setter exists for any slider, so they cannot be regression-tested; only time (MAE 0.10 to 0.11 at any offset), record FOV (0.09 to 0.13), and record exposure (0.04 to 0.06) were measured; record distance is ignored (2.5e-6). Fog below 0.05 is an analytic dead zone; Corridor density is inverted (larger = sparser); Scene scale is a 0.03..0.3 slice tilt.
9. Cut: Render Scale, Resolution Preset, HUD Overlay/Scale, Depth Pre-pass, RmlUi, Gizmo Rotate/Scale/Mode, Use Spectral LUT and its radius sliders, tesseract Projection and Eye w distance; collapse the legacy disk block behind the legacy tracer; move the 21-control Compare harness to a developer window.
10. Merge: Bloom Iterations into Post Processing; Bloom tone into Exposure; Hawking Preset with its two sliders; Depth Far out of Depth Effects (it is the ray escape radius); one time control (Time Scale, Disk clock, Disk rotation speed).
11. Re-range: Exposure 0.3..12; Disk brightness 0.05..2; Parallax max 0.01 to about 0.001; Orbit Radius 4..400 (min 2 is the horizon); tesseract Fog floor 0.05; Swap Interval label "Triple (2)" means every second vblank.
12. Re-label: identifiers `blackHoleMass`, `kerrSpin(a/M)`, `enablePhotonSphere`, `enableRedshift`; "Accretion disk" help text names only the legacy tracer; two controls named "Disk thickness" with different meanings; add units to nine sliders (section 13).
13. Make Depth Effects work on RTE by writing depth to alpha, or grey the window; grey Exposure and Gamma when Tone mapping is off; grey Background Intensity when the backdrop is off.
14. Vignette (1.0), film grain, chromatic aberration, photon-glow strength, and observer `displayPeak` have state fields but no control.
15. Evidence: 67 renders on NVIDIA GeForce RTX 4070 Ti (GL_RENDERER), all hidden, serial; the input-device, game, and observer controls are static only.

## Method and evidence classes

Static trace: control source (`src/ui/*.cpp`), default (`src/render/render_state.h`, `src/settings.h`), uniform hop (`src/render/uniform_binding.cpp`, `src/render/interop_uniform_registry.h`, `src/main.cpp`), shader read (`shader/blackhole_main.frag`, `shader/include/interop_trace.glsl`, `shader/tesseract.frag`, `shader/depth_cues.frag`, `shader/tonemapping.frag`).

Default contract (`src/render/renderer_contract.h`): fragment backend, Kerr reference geodesic, volumetric RTE radiative model, Balanced quality, 300 steps, step 0.1. `kerrDiskShadingActive()` (`src/ui/settings_window.cpp:1038`) is true for that contract, so the Kerr tracer draws the disk and every legacy-tracer control is disabled with a tooltip. The default spin is 0, so "Kerr reference" equals Schwarzschild until the user moves spin.

Measured: GL_RENDERER = `NVIDIA GeForce RTX 4070 Ti/PCIe/SSE2` (OpenGL 4.6, logged by the `OpenGL Capabilities` block in every run; never llvmpipe). Every launch used `BLACKHOLE_WINDOW_HIDDEN=1`, `nice -n 10`, `timeout 120`, one at a time. MAE is `magick compare -metric MAE`, reported normalized to 0..1 (the Q16 value divided by 65535).

Setter matrix (what can reach RenderState without input injection in this binary):

| Setter | Reaches |
| --- | --- |
| `--export-frame` + `--export-size 960 540` | black-hole default path; used for all "export" rows |
| `--export-exposure/-bloom/-tone-mapping` | exposure, bloom strength, tone mapping |
| `settings.json` (with `presentationSchemaVersion: 2`) | gamma, bloomIterations, camera pose (yaw/pitch/roll/distance), background enable/intensity/parallax/drift, renderScale |
| `--renderer-radiative/-geodesic` | radiative model, geodesic model |
| `BLACKHOLE_DISK_TRANSFER`, `BLACKHOLE_WIREGRID_*`, `BLACKHOLE_SCENE` | disk transfer, wiregrid params, scene |
| `--record-frames DIR 1 --start-frame N` | record path (different post/disk/steps profile, so a separate baseline): `--record-spin`, `--record-fov`, `--record-distance`, `--record-exposure` |
| none | spin outside record, disk brightness/temperature/turbulence/thickness/clock, RTE opacity, bloom threshold/knee/tone, depth effects, Hawking, all legacy disk sliders, every tesseract slider |

Two setter traps found and verified: (1) `Settings::gravitationalLensing`, `renderBlackHole`, `adiskEnabled/Particle/DensityV/DensityH/Height/Lit/NoiseLOD/NoiseScale/Speed` are written and read by `src/settings.cpp` but no code copies them to or from `RenderState` (`git grep "settings\.adisk"` finds only the writer), so those keys in `settings.json` do nothing and the UI values do not persist; the renders `lens_off`, `hole_off`, `adisk_off` therefore equal the default (MAE 0.010 to 0.025, inside the floor) and are void, not evidence. (2) Every record profile rewrites disk, post, steps, background, and radiative model (`src/render/record_mode.cpp:280-420`), so record numbers only compare within the record path.

Noise floors. Export path: three default renders differ pairwise by 0.0098 to 0.0137 (film grain seeded by `time`, disk turbulence on wall clock); treat MAE below about 0.015 as "no effect". Record path: two identical renders differ by exactly 0 (content clock is the frame index), so any nonzero MAE is real.

Render count: 67 (export 45, record 20, dimension probes 2). Slightly above the requested 60; 7 of them are floor or void samples.

## 1. Scene and workspace selectors (Settings window header)

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Workspace combo | `settings_window.cpp:843` | Simulator / Proper Time / Diagnostics, 0 | `Settings::workspaceKind`, layout reset | none | selects which windows exist |
| Reset Layout (button) | `settings_window.cpp:847` | n/a | `overlays.firstLayout` | none | |
| Advanced controls | `settings_window.cpp:850` | off | `Settings::advancedControls` -> `diagnosticsVisible` (`main.cpp:1580`) | LABEL | gates the Physics, Compute, GRMHD tabs and the Post Processing, Depth Effects, Wiregrid, Performance, Gizmo windows; "Advanced" hides exposure and bloom |
| Scene combo | `settings_window.cpp:819` | Black hole / Tesseract / Observer sky, Black hole | `scene.mode` | none | locked during `--record-frames` (UI says so) |

## 2. Settings > Visuals

Basic view shows only rows V1-V4 as live controls plus a block of disabled legacy sliders; the controls that shape the default image (disk brightness, temperature, turbulence, thickness, transfer, spin) are on the Advanced-only Physics tab. Visibility is inverted relative to what the default path reads.

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Gravitational lensing | `settings_window.cpp:164` | bool, on | `disk.gravitationalLensing` -> uniform `gravitationalLensing` (`uniform_binding.cpp:109`) -> `bhMetricRadius/bhMetricSpin` (`interop_trace.glsl:314-316`) | LABEL | help says "bends the background"; off also flattens the metric under the disk and horizon (straight rays). Not measured (no setter; settings key orphaned) |
| Bloom Iterations | `settings_window.cpp:165` | 1..8, 8 | `post.bloomIterations` -> `post_pipeline.cpp:45-86` | RANGE | measured 1: MAE 0.032, 4: 0.030 vs default 8 (floor 0.012): weak, saturates by 4; default sits at the maximum. Lives here while the other bloom sliders live in Post Processing |
| Render event-horizon silhouette | `settings_window.cpp:167` | bool, on | `disk.renderBlackHole` -> `bhHoleRendered()` | LABEL | off removes hole and disk together (rays go straight to the sky) yet help says "shows the dark silhouette". Not measured |
| Accretion disk | `settings_window.cpp:168` | bool, on | `disk.adiskEnabled` -> `interop.adiskEnabled` (`interop_trace.glsl:407,849,989`) | LABEL | help text says "legacy tracer's disk" but the Kerr tracer reads it too. Also forced off by radiative model Background only. Proxy measurement: radiative background-only MAE 0.082 |
| Particle detail | `settings_window.cpp:174` | bool, on | `adiskParticle` -> legacy `adiskColor` only | DEAD | disabled + tooltip on default contract |
| Vertical density | `settings_window.cpp:176` | 0..10, 2.0 | `adiskDensityV` -> density LUT generation (`lut_manager.cpp:284`) -> legacy sampler only | DEAD | disabled |
| Radial density | `settings_window.cpp:178` | 0..10, 4.0 | uniform `adiskDensityH`, legacy `adiskColor` | DEAD | disabled |
| Disk thickness | `settings_window.cpp:180` | 0..1, 0.55 | `adiskHeight`, legacy | DEAD DUP LABEL | same label as Physics "Disk thickness (H/r)" (Kerr, 0.01..0.4, 0.03) with different meaning |
| Emission intensity | `settings_window.cpp:182` | 0..4, 0.25 | `adiskLit`, legacy (CUDA lane also reads it) | DEAD DUP | Kerr counterpart: Disk brightness |
| Turbulence detail | `settings_window.cpp:184` | 1..12, 5.0 | `adiskNoiseLOD`, legacy | DEAD DUP | Kerr counterpart: Disk turbulence |
| Turbulence scale | `settings_window.cpp:186` | 0..10, 0.8 | `adiskNoiseScale`, legacy | DEAD DUP | |
| Noise Texture | `settings_window.cpp:188` | bool, on | `disk.useNoiseTexture` -> noise volume | DEAD | not in presentation metadata; disabled |
| Noise Tex Scale | `settings_window.cpp:190` | 0.05..2, 0.25 | `noiseTextureScale`, legacy | DEAD | raw slider, no help text |
| Disk rotation speed | `settings_window.cpp:192` | 0..1, 0.5 | `adiskSpeed`, legacy | DEAD DUP | Kerr counterpart: Disk clock (M per second) |
| Doppler beaming | `settings_window.cpp:194` | 0..5, 1.0 | `dopplerStrength`, legacy (and CUDA `doppler_strength`) | DEAD DUP | the Kerr path derives beaming from the g-factor (Disk transfer combo); no strength control exists there |
| RTE Opacity Scale | `settings_window.cpp:207` | 0..5, 0.5 | `rte.rteOpacityScale` -> `alpha_nu = scale * rho` (`interop_trace.glsl:852`) | GATED LABEL | control appears only when radiative = Volumetric RTE (default); header reads "Volumetric RTE (D2)" (phase jargon), empty header otherwise. Advanced only. Not measured |
| B Field Angle (rad) | `settings_window.cpp:218` | -pi..pi, 0 | `stokes.stokesBFieldAngle` -> `stokes_transport.glsl` | GATED UNITS | Stokes model only, Advanced only; radians on a slider. Measured Stokes vs RTE at defaults MAE 0.020 (near floor): at Faraday scale 0 the model switch is almost invisible |
| Faraday Ne Scale | `settings_window.cpp:220` | 0..5, 0 | `stokes.stokesNeScale` | GATED DEAD | default 0 disables the effect; Stokes only |

## 3. Settings > Physics (Advanced)

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| blackHoleMass | `settings_window.cpp:423` | 0.1..10, 1.0 | `physicsCore.blackHoleMass` -> `r_s = 2 * mass` scene units (`main.cpp:1028`), Hawking mass in solar masses | LABEL UNITS | raw identifier label, no units; camera distance stays absolute, so this rescales the apparent hole size; scaled for visualization per source comment. Not measured |
| kerrSpin(a/M) | `settings_window.cpp:427` | -0.998..0.998, 0 | `physicsCore.kerrSpin` -> `interop.kerrSpin`, LUT regeneration, ISCO | LABEL | Strong: record path vs 0.998: -0.998 0.276, -0.6 0.264, 0 0.226, 0.3 0.192, 0.6 0.140, 0.9 0.057 (monotone, flattening above 0.9). Identifier label; default 0 means the Kerr model shows no Kerr effect until moved. Export-path Schwarzschild vs Kerr geodesic model at spin 0: MAE 0.019 (floor) |
| Disk transfer | `settings_window.cpp:440` | Physical / Interstellar, Physical | `disk.diskTransferMode` -> `bhDiskEmission` g = 1 (`interop_trace.glsl:459`) | none | measured Interstellar vs Physical at spin 0: MAE 0.038 (3x floor); grows with spin and inclination (not measured) |
| Disk peak temperature (K) | `settings_window.cpp:448` | 2000..40000 log, 6500 | `diskPeakTemperature` -> blackbody chroma only (`interop_trace.glsl:458-460`) | none | changes hue, not luminance (luminance is the normalized flux); not measured |
| Disk brightness | `settings_window.cpp:451` | 0.01..100 log, 0.25 | `diskBrightness` multiplies emitted color | DUP RANGE | linear gain like Exposure and Bloom tone; a 10000x span, useful span about 0.05..2 with exposure 2.5 (exposure sweep below shows saturation above 10). Not measured |
| Disk clock (M per second) | `settings_window.cpp:454` | 0..100 log, 10 | `diskTimeScale` -> turbulence pattern clock only (`interop_trace.glsl:481`) | GATED | no effect when Disk turbulence is 0 or on the smooth disk; tooltip does not say so |
| Disk thickness (H/r) | `settings_window.cpp:460` | 0.01..0.4, 0.03 | `diskScaleHeight` -> `bhDiskScaleHeight` (`interop_trace.glsl:293`) | GATED DUP | RTE and Stokes only (tooltip says so; not disabled under Thin surface where it is inert) |
| Disk turbulence | `settings_window.cpp:466` | 0..1.2, 0.6 | `diskTurbulence` -> `disk_turbulence.glsl` | GATED | fragment and compute only (tooltip); reference scenes force 0; not measured |
| enablePhotonSphere | `settings_window.cpp:479` | bool, off | `enablePhotonSphere` -> legacy glow | DEAD LABEL | disabled on the Kerr contract; identifier label; its strength (`photonSphereGlowStrength`) has no control |
| enableRedshift | `settings_window.cpp:483` | bool, off | `enableRedshift` -> legacy `adiskColor` (`blackhole_main.frag:389`) | DEAD LABEL | greyed unless legacy; Kerr path always applies the g-factor |
| Enable Hawking Glow | `settings_window.cpp:489` | bool, off | `hawking.hawkingGlowEnabled` -> `bhHorizonShade` (`interop_trace.glsl:469`) | none | visible only at horizon-captured rays; physical scale is invisible by design |
| Hawking Preset | `settings_window.cpp:494` | Physical/Primordial/Extreme, Physical | overwrites Temp Scale and Glow Intensity on change | DUP | the two sliders below it are the same state; preset label is not updated when they move |
| Temp Scale | `settings_window.cpp:503` | 1..1e9 log, 1 | `hawkingTempScale` | UNITS | dimensionless multiplier; hint line explains 1 / 1e6 / 1e9 |
| Glow Intensity | `settings_window.cpp:506` | 0..5, 1.0 | `hawkingGlowIntensity` | none | |
| Use LUTs (Hawking) | `settings_window.cpp:507` | bool, on | `useHawkingLUTs` | none | status text shows LUT load |
| Use Spectral LUT | `settings_window.cpp:518` | bool, off | `useSpectralLut` -> `interop_trace.glsl:491` | DEAD | `assets/luts/rt_spectrum_lut.csv` is not shipped (`lut_manager.cpp:128`); the checkbox stays enabled and the status line reads "not loaded" |
| Use GRB Modulation | `settings_window.cpp:537` | bool, off | `useGrbModulation` -> `interop_trace.glsl:498` | none | LUT ships; live on the default path |
| Manual GRB Time / GRB Time | `settings_window.cpp:545,547` | LUT range, 0 | `grbTimeManual*` | UNITS | slider has no unit in its label (text above shows seconds) |
| Spectral Radius Min / Max (x2) | `settings_window.cpp:560,561` | 0..50, 0/0 | `spectralRadiusMin/Max` -> normalized by r_s (`interop_trace.glsl:493`) | DEAD UNITS | unusable without the missing spectral LUT; unit is r_s but unlabeled; not greyed |

## 4. Settings > Compute (Advanced)

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Backend | `settings_window.cpp:682` | Fragment / Compute (CUDA entry compiled out), Fragment | `dispatch.contract.backend` | none | text: "Backend selection controls compute dispatch" |
| Geodesic model | `settings_window.cpp:694` | Legacy / Schwarzschild / Kerr, Kerr | `contract.geodesic` | none | measured Legacy vs default MAE 0.119, Schwarzschild 0.019 (spin 0) |
| Radiative model | `settings_window.cpp:704` | Background / Thin / RTE / Stokes, RTE | `contract.radiative` | none | measured Background only 0.082, Thin surface 0.055, Stokes 0.020 |
| Quality tier | `settings_window.cpp:713` | Interactive / Balanced / Reference, Balanced | `contract.quality` | none | Reference overrides both step sliders (UI says so) |
| Terminal map | `settings_window.cpp:730` | bool, off | debug view | none | |
| Geodesic Steps | `settings_window.cpp:760` | 50..300 (Interactive) or 1000, 300 | `dispatch.computeMaxSteps` -> `rendererStepBudget` | RANGE | default equals the Interactive maximum; not measured (no setter) |
| Compute Step Size | `settings_window.cpp:762` | 0.1..1 (Interactive) or 0.01..1, 0.1 | `dispatch.computeStepSize` | LABEL UNITS | applies to the fragment path too; unit (affine step) not stated |
| Compute Tiled / Tile Size (x2) | `settings_window.cpp:770,772` | bool off; 64..1024, 256 | compute backend only | GATED | disabled unless Backend = Compute |

Compare harness (all hidden until "Compare Compute vs Fragment" is on, a developer tool): Compare Compute vs Fragment (off), Sample Size 4..64 (16), Frame Stride 1..60 (1), Write Snapshot PPMs / Diff PPM / Summary CSV (x3), Diff Scale 0.1..32 (8), Max Diff Threshold 0..0.5 (0.02), Allowed Outliers 0..50000 (10000), Allowed Outlier Frac 0..0.01 (0.006), Baseline, Overrides, Max Steps Override 0..1000, Step Size Override 0..2, Flag NaN/Range/Max-step (x3), Auto Capture, Auto Count 1..120, Auto Stride 1..600, Preset Settle Frames 1..10 (`settings_window.cpp:579-662`).

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Compare harness controls (x21) | `settings_window.cpp:579-662` | see list above | `rs.compare.*`, env overrides `BLACKHOLE_COMPARE_*` | GATED LABEL | developer test harness exposed in the user Compute tab; Step Size Override allows 0 while `compareOverridesEnabled` seeds it; no units on "Diff Scale" or "Threshold". Not measured |

## 5. Settings > GRMHD (Advanced)

`useGrmhd` is read only by the legacy fragment tracer (`blackhole_main.frag:283`) and the CUDA lane; `interop_trace.glsl`, `geodesic_trace.comp`, and `interop_raygen.glsl` contain no GRMHD sampling. On the default contract the GRMHD field, bounds, and time series do not change the black-hole image; only the Slice preview window (`grmhd_slice.frag`) shows the data.

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Use GRMHD Field | `settings_window.cpp:371` | bool, off | `grmhd.useGrmhd` -> legacy `useGrmhd` | DEAD | not disabled and no tooltip on the Kerr contract |
| GRMHD Meta (text), Load / Unload | `settings_window.cpp:372` | path | `loadGrmhdPacked` | none | |
| GRMHD Bounds Min / Max (x2, vec3) | `settings_window.cpp:389,390` | -50..50 each, (-10,-2,-10)/(10,2,10) | `grmhdBoundsMin/Max` | DEAD UNITS | overwritten to +/- rMax when a dataset loads (`settings_window.cpp:109-110`), so pre-load edits are lost; unit (scene units, r_s = 2) missing |
| Show GRMHD Slice | `settings_window.cpp:392` | bool, off | slice preview | GATED | disabled until loaded |
| Slice Axis | `settings_window.cpp:394` | X/Y/Z, Z | | GATED | |
| Slice Coord | `settings_window.cpp:395` | 0..1, 0.5 | normalized | GATED | |
| Slice Channel | `settings_window.cpp:396` | 0..3, 0 | | GATED RANGE | fixed at 3 instead of the dataset channel count; the name appears only in a line below |
| Slice Auto Range / Min / Max / Color Map (x4) | `settings_window.cpp:403-408` | bool on; floats 0/1; bool on | | GATED | Min and Max are InputFloat, shown only with auto range off |
| Slice Size | `settings_window.cpp:409` | 64..1024, 256 | texels | GATED UNITS | |
| Enable Time-Series Playback | `settings_window.cpp:284` | bool, off | `grmhdTimeSeriesEnabled` | DEAD | streams textures the default tracer never samples |
| JSON Metadata / Binary Data (x2) | `settings_window.cpp:289,291` | paths | | GATED | |
| Frame | `settings_window.cpp:300` | 0..maxFrame, 0 | seek | GATED | |
| Playback Speed | `settings_window.cpp:332` | 0.1..4, 1.0 | | GATED UNITS | "x" unit missing; time readout hard-codes 30 fps |

## 6. Post Processing window (Advanced or Diagnostics only)

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Bloom strength | `settings_window.cpp:906` | 0..1, 0.1 | `post.bloomStrength` -> `bloom_composite.frag` | RANGE | measured (export, floor 0.012): 0 -> MAE 0.035, 0.5 -> 0.042, 1.0 -> 0.065; even the maximum is a modest change; useful span about 0..0.5 |
| Bloom threshold | `settings_window.cpp:907` | 0..2, 0.4 | `bloomThreshold` -> `bloom_brightness_pass.frag` | none | not measured (no setter) |
| Bloom knee | `settings_window.cpp:908` | 0..0.5, 0.15 | smoothstep half-width | UNITS | not measured |
| Bloom tone | `settings_window.cpp:909` | 0..2, 1.0 | scales the SCENE term in `bloom_composite.frag`, not the bloom | LABEL DUP | acts as a second exposure applied before tone mapping |
| Tone mapping | `settings_window.cpp:911` | bool, on | `post.tonemappingEnabled` | GATED | off bypasses exposure, gamma, vignette, chromatic aberration, and grain (`tonemapping.frag:49-78`) with no UI note; measured off: MAE 0.177, mean luminance 0.198 -> 0.022 (image goes near black) |
| Exposure | `settings_window.cpp:914` | 0.01..50 log, 2.5 (settings) | `post.toneExposure` -> `tonemapping.frag:66` | RANGE GATED | measured MAE / mean luminance: 0.01 -> 0.179 / 0.020; 0.25 -> 0.142 / 0.057; 2.5 -> 0 / 0.198; 10 -> 0.195 / 0.392; 50 -> 0.478 / 0.676. Below 0.1 the frame is black; above 10 the ACES shoulder compresses (5x in exposure gives 1.7x in mean). Useful 0.3..12. `RenderState` default 1.0 is replaced at load by 2.5 |
| Gamma | `settings_window.cpp:916` | 1..4, 2.5 | `post.gamma` | UNITS GATED | measured 1 -> 0.151, 4 -> 0.141 (both large); display exponent, default 2.5 not 2.2; inert with tone mapping off |
| (no control) film grain 0.005, vignette 1.0, chromatic aberration 0.002 | `render_state.h` PostGroup | n/a | `tonemapping.frag` | none | fields exist with no UI; the default vignette is at its maximum and cannot be turned off |

## 7. Depth Effects window (Advanced or Diagnostics only)

Static finding, not measured (no setter). Depth comes from the alpha channel of the scene texture. The default RTE and Stokes interop paths write alpha 1.0 (`blackhole_main.frag:730,744`), so depth is the constant 1 on the default contract: Sobel edge strength is 0, Depth Curve is `pow(1, c) = 1`, fog, desaturation, chroma tint, and DoF blur apply uniformly. Only Thin surface and legacy paths write real depth. `depthCuesApply` is false for the tesseract and observer scenes (`post_pipeline.cpp:134`), and the window gives no notice.

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Enable Depth Effects | `settings_window.cpp:927` | bool, off | `depthFx.depthEffectsEnabled` | GATED | master; black-hole scene only |
| Depth Far | `settings_window.cpp:928` | 10..2000 log, 500 | `display.depthFar` -> tracer escape radius `max(depthFar, 1.01 * cameraDist)` (`interop_trace.glsl:301`) | LABEL RANGE | lives in the Depth Effects window but is the ray escape radius and works with effects off; below 1.01x camera distance (151 at default) the slider does nothing |
| Preset buttons (x4) | `settings_window.cpp:934-999` | Off / Subtle / Cinematic / Clarity | write many fields | GATED | inert where depth is 1 |
| Fog + Fog Density + Fog Start + Fog End + Fog Color (x5) | `settings_window.cpp:1009-1014` | bool off; 0..1 (0.08); 0..1 (0.6); 0..1 (0.98); rgb | `depth_cues.frag` | GATED UNITS | start/end are fractions of depth (unlabeled); sub-controls stay live when their checkbox is off; on RTE depth = 1 so fog is a uniform tint |
| Edge Outlines + Threshold + Width + Color (x4) | `settings_window.cpp:1017-1020` | bool off; 0..1 (0.5); 0.5..3 (1.0); rgb | Sobel on depth | DEAD | constant depth gives zero edges on the default contract |
| Depth Desaturation + Desaturation (x2) | `settings_window.cpp:1023,1024` | bool off; 0..1 (0.10) | | GATED | uniform on RTE |
| Chroma Depth | `settings_window.cpp:1025` | bool, off | | GATED | uniform tint on RTE |
| Motion Parallax Hint | `settings_window.cpp:1026` | bool, off | screen-edge sine pattern | GATED LABEL | "hint" is a decorative stripe pattern |
| Depth of Field + Focus Near + Focus Far + Max Radius (x4) | `settings_window.cpp:1029-1033` | bool off; 0..1 (0.3); 0..1 (0.9); 0..12 px (2.0) | 5-tap blur | GATED UNITS | uniform blur on RTE; radius unit px is not in the label |
| Depth Curve | `settings_window.cpp:1034` | 0.5..2, 1.0 | `pow(depth, c)` | DEAD | `pow(1, c) = 1` on the default contract |

## 8. Controls window (Simulator workspace, always visible)

Inputs act on the camera through `InputManager`; not measured (input, no setter).

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Mouse / Keyboard / Scroll Sensitivity (x3) | `panels.cpp:339,344,349` | 0.1..3, 1.0 | `InputManager` | none | presets Balanced/Precision/Fast set them |
| Invert Mouse X/Y, Keyboard X/Y (x4) | `panels.cpp:358-370` | bool, off | | none | |
| Camera Mode | `panels.cpp:379` | Input / Front / Top / Orbit, Input | `camera.cameraModeIndex` -> `camera_math.cpp:51` | LABEL | Front and Top are fixed poses at 14 and 21 scene units that ignore the camera distance |
| Orbit Radius | `panels.cpp:382` | 2..50, 15 | `camera.orbitRadius` | RANGE UNITS | scene units where r_s = 2: minimum 2 is the horizon radius; the default view sits at 150 units, so entering Orbit jumps to 15 (inside the 40-unit disk edge) |
| Orbit Speed (deg/s) | `panels.cpp:383` | 0..30, 6 | `orbitSpeed` | none | Orbit mode only |
| Hold-to-Toggle Camera | `panels.cpp:387` | bool, off | | none | |
| Time Scale | `panels.cpp:392` | 0..4, 1.0 | `getEffectiveDeltaTime` (orbit clock, tesseract motion) | DEAD LABEL | the black-hole disk and wiregrid read content time (`main.cpp:1933`), not this scale or Pause; effective only in Orbit mode and the tesseract |
| Enable Gamepad + 4 invert + Deadzone 0..0.5 (0.15) + Look 10..180 (90) + Roll 10..180 (90) + Zoom 1..20 (6) + Trigger Zoom 1..20 (8) (x10) | `panels.cpp:406-449` | see list | `InputManager` | GATED UNITS | matters only with a gamepad; sensitivities carry no unit (deg/s implied) |
| Gamepad axis mapping (x6) and button mapping (x3) | `panels.cpp:468-513` | SliderInt 0..5 and 0..14 | | LABEL RANGE | enumerations as integer sliders; a combo of named axes/buttons is the usable form |
| Key bindings (buttons) | `panels.cpp:558-600` | 21 actions | | none | |
| Save Settings / Reset Defaults (buttons) | `panels.cpp:596,605` | | | none | Reset Defaults saves immediately with no confirmation |

## 9. Display, Background, Wiregrid, Performance, Gizmo, RmlUi

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Fullscreen | `panels.cpp:696` | bool, off | | none | |
| Swap Interval | `panels.cpp:706` | "Off (0)", "VSync (1)", "Triple (2)", 1 | `glfwSwapInterval` | LABEL | interval 2 is every second vblank, not triple buffering |
| Render Scale | `panels.cpp:712` | 0.25..1.5, 1.0 | `display.renderScale`; read only inside a commented-out resize block (`main.cpp:2009-2016`) | DEAD | measured: `renderScale` 0.25 and 1.0 both produced 1324 x 1032 (targets follow the docked viewport, `main.cpp:1975-1990`) |
| Resolution Preset | `panels.cpp:719` | Native..UW 5120x2160, Native | writes `renderScale` | DEAD RANGE | inert like Render Scale; "4K" from a 1080p window computes 2.0, above the slider maximum; the "Render: WxH" readout reports a size that is never rendered |
| Enable Background | `panels.cpp:791` | bool, off | `Settings::backgroundEnabled` -> `interop_trace.glsl:556` | none | measured on: MAE 0.277 vs off (replaces the star cubemap) |
| Intensity | `panels.cpp:792` | 0..2, 0.5 | `Settings::backgroundIntensity` | GATED | measured: 2.0 with Enable off MAE 0.0106 (floor, no effect); with Enable on: 0 -> 0.075, 0.5 -> 0.277, 2.0 -> 0.545 vs off; slider not greyed when off |
| Background Asset | `panels.cpp:802` | manifest list, carina | `backgroundId` | GATED | no effect while Enable is off |
| Parallax Strength | `panels.cpp:815` | 0..0.01, 0 | `backgroundParallaxStrength` | RANGE GATED | offset = camera xy x strength x layer depth (`main.cpp:1263-1269`); at the default 150-unit camera the maximum shifts layers by tens of percent; maximum parallax plus maximum drift together: MAE 0.106 vs background on |
| Drift Strength | `panels.cpp:816` | 0..0.05, 0 | `backgroundDriftStrength` | RANGE GATED | same |
| Layer Depth / Scale / Weight / LOD Bias (x12) | `panels.cpp:821-824` | 0..2 (0.2/0.5/0.9), 0.5..2 (1/1.08/1.16), 0..2 (1/0.6/0.35), 0..6 (0/1/2) | `backgroundLayer*` | GATED UNITS | require Enable Background; Depth needs Parallax above 0 (default 0); same labels in three sections (id via PushID only) |
| Enable Wiregrid | `panels.cpp:845` | bool, off | `wiregrid.wiregridEnabled` | none | measured on (Beauty): MAE 0.056 |
| Wiregrid Mode | `panels.cpp:846` | Beauty / Diagnostic, Beauty | overwrites all wiregrid sliders and the color (`panels.cpp:50-69`) | DUP | Diagnostic vs Beauty: MAE 0.19 (mean luminance 0.24 -> 0.40); sliders below are the same state |
| Show Ergosphere | `panels.cpp:855` | bool, on | | GATED | spin 0 makes the ergosphere coincide with the horizon; measured MAE 0.012 (floor) at default spin |
| Grid Scale | `panels.cpp:856` | 0.25..4, 0.92 (Beauty) | | none | 4.0 vs 0.92: MAE 0.071 |
| Motion Scale / Infall Scale (x2) | `panels.cpp:857,858` | 0..4 (0.62); 0..2 (0.24) | time-driven advection | none | not measured (time-dependent) |
| Strength | `panels.cpp:859` | 0.1..2, 0.84 | | none | 2.0 vs default: MAE 0.036 |
| Scene Preserve | `panels.cpp:860` | 0..1, 1.0 | | RANGE | 0 vs 1: MAE 0.010 (floor): no visible effect in Beauty on the default scene |
| Wiregrid Color (RGBA) | `panels.cpp:862` | rgba | | none | |
| Enable RmlUi overlay | `panels.cpp:873` | bool, off | `overlays.rmluiEnabled` | DEAD | own text says "placeholder only"; `ENABLE_RMLUI=OFF` in this build |
| GPU Timing | `panels.cpp:891` | bool, off | timers | none | |
| HUD Overlay | `panels.cpp:892` | bool, on | `perfOverlayEnabled` | DEAD | only `BLACKHOLE_PERF_HUD` writes it; nothing reads it (`[[maybe_unused]]`) |
| HUD Scale | `panels.cpp:893` | 0.5..2, 1.0 | `perfOverlayScale` | DEAD | same |
| Depth Pre-pass | `panels.cpp:897` | bool, off, permanently disabled | | DEAD | disabled by design with a tooltip |
| Enable Gizmo Target | `panels.cpp:634` | bool, off | `gizmoTransform` translation -> focus target (`main.cpp:1231`) | none | black-hole scene only (UI says so) |
| Gizmo Operation / Mode (x2) | `panels.cpp:653,666` | Translate/Rotate/Scale; World/Local | | DEAD | the camera reads only the translation column, so Rotate, Scale, and Local do not change the render |

## 10. Tesseract window (scene = Tesseract)

Measurement limit: no settings key, CLI flag, or environment variable sets any tesseract field, and the record path replaces view distance and FOV with the record camera (`tesseract_renderer.cpp:315-336`). All slider effects below are static unless a MAE is quoted. Only time (start frame), record FOV, record distance, and record exposure were measurable. Tesseract default, record path, frame 360, 662 x 492: MAE floor 0 (two identical renders), mean luminance 0.106.

| Measured | MAE vs default | Mean luminance |
| --- | --- | --- |
| start frame 0 / 90 / 720 / 1440 (time) | 0.102 / 0.102 / 0.113 / 0.110 | 0.099 / 0.100 / 0.117 / 0.114 |
| `--record-fov` 20 / 100 (default record FOV) | 0.093 / 0.130 | 0.083 / 0.136 |
| `--record-distance` 5 | 0.0000025 (ignored) | 0.106 |
| `--record-exposure` 1.0 / 6.0 (default 2.6) | 0.044 / 0.063 | 0.062 / 0.169 |

Time decorrelates the frame to about 0.10 to 0.11 at any offset, so animation is strongly visible; the record distance flag confirms the fixed-fill framing.

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| Animate (rotation and pulse) | `panels.cpp:958` | bool, on | `tesseract.animate` -> `advanceTesseractMotion` | none | freezes rotation, pulse, and drift together |
| Speed ds/dt | `panels.cpp:959` | 0..3, 1.0 | `rotationSpeed` | UNITS | jargon label; scales rotation only, not drift or pulse |
| Reset phase s0 | `panels.cpp:960` | 0..12, 2.5 | `resetPhase` | UNITS LABEL | rotation parameter in "s", not seconds of wall time; applies on Reset only |
| qL rate / qR rate (x2, vec3) | `panels.cpp:965,966` | -1..1, (0.35,0,0.15)/(0,0.03,0) | `leftRate/rightRate` -> `rotation4` -> `buildSliceFrame` (`tesseract.frag:160`) | RANGE UNITS | rad per ds unstated; `rotation4` is blended toward identity by 0.10 x Scene scale (0.13 default), so the full 4D rotation appears attenuated |
| Preset buttons (Simple xw, Left isoclinic, SO(3)) | `panels.cpp:970-983` | | write rates | none | |
| Projection | `panels.cpp:992` | Perspective / Stereographic, Perspective | `projectionMode` uniform | DEAD | declared at `tesseract.frag:50`, never read; only changes the record-mode framing radius |
| Eye w distance | `panels.cpp:996` | 2.2..8, 3.0 | `perspectiveDistance` uniform | DEAD UNITS | declared at `tesseract.frag:51`, never read; only the record-mode framing radius reads it (R = 3.49 at 3.0, 2.69 at 8.0) |
| Scene scale | `panels.cpp:997` | 0.3..3, 1.3 | `sceneScale` -> slice tilt `blend = clamp(0.10 x scale, 0, 0.6)` | LABEL RANGE | does not scale the scene: sets a 0.03..0.30 tilt of the slice frame; the 0.6 clamp is unreachable (needs 6) |
| View distance | `panels.cpp:998` | 3..20, 8 | `viewDistance` -> eye offset | GATED UNITS | live interactively (also scroll zoom); overridden by the record camera (measured: `--record-distance` ignored); world units unstated |
| FOV (deg) | `panels.cpp:1000` | 20..100, 50 | `fovDeg` -> `fovScale` | GATED | live interactively; record captures use the record camera FOV instead (measured 20 -> 0.093, 100 -> 0.130) |
| Corridor density | `panels.cpp:1005` | 3..30, 12 | `cellSize` (lattice period, world units) | LABEL UNITS | inverted: a larger value is a SPARSER lattice; all geometry scales with it and fog distance scales with it |
| Corridor period | `panels.cpp:1006` | 1..30, 10 | `timeSpan` -> `corridorPeriod` | LABEL UNITS | depth period of the light bands; source comment also cites an SO(4) shear the shader does not use; also clamps Now depth and Pulse sliders |
| Drift speed | `panels.cpp:1007` | 0..4, 0.6 | `driftSpeed` | UNITS | world units per second, unlabeled |
| Strand glow | `panels.cpp:1008` | 0..4, 1.0 | `strandGlow` multiplies strands, beams, halo | none | not measured |
| Fog | `panels.cpp:1009` | 0..2, 0.35 | `fogDensity` -> `fogDistance = 3.5 cells x 0.35 / fog` (`tesseract.frag:339`) | RANGE LABEL | analytic: below 0.051 fog distance exceeds the 24-cell march (288 units) so 0..0.05 is a dead zone; at 0.35 the far field is fully fogged; a density labeled "Fog" reads as a toggle |
| Quality | `panels.cpp:1014` | Dense (GPU) / Sparse (software GL), Dense | `qualityTier` | LABEL | Sparse only cuts the march budget from 256 to 160 steps; the label names software GL |
| Now depth | `panels.cpp:1019` | 0..period, 6 | `litMoment` | UNITS | static highlight band on strands; depth units unstated |
| Now width | `panels.cpp:1020` | 0.05..3, 0.5 | `litWidth` | UNITS | |
| Gravity message pulse | `panels.cpp:1021` | bool, on | `pulseEnabled` | none | |
| Pulse t_now / t_past (x2) | `panels.cpp:1022,1023` | 0..period (10), 0..t_now (6) | pulse span | LABEL RANGE | default t_now equals the period maximum; t_past is bounded by t_now |
| Pulse speed | `panels.cpp:1025` | 0.1..10, 1.5 | `pulseSpeed` | RANGE | at 10 a 4-unit span repeats 2.5 times a second (strobe) |
| Pulse width | `panels.cpp:1026` | 0.05..2, 0.35 | `pulseWidth` | UNITS | |

## 11. Observer sky windows (scene = Observer sky)

Own scene, own ranges (`src/render/observer_sky_view.h:88-95`); env setters exist (`BLACKHOLE_OBSERVER_*`) but this scene was outside the measured set (not measured: scope). Static only.

| Control | file:line | Range / default | State field -> wiring | Flags | Note |
| --- | --- | --- | --- | --- | --- |
| 1 - a | `observer_panels.cpp:40` | 1e-15..1 log, 1.33e-14 | `epsilon` -> sky LUT rebuild | LABEL | jargon label; "Gargantua canon" button resets |
| Observer kind | `observer_panels.cpp:54` | 4 kinds, Prograde | | none | |
| At the ISCO | `observer_panels.cpp:57` | bool, on | | none | r - 1 slider appears only when off |
| r - 1 (M) | `observer_panels.cpp:61` | 1e-8..1e3 log, 5 | `x` | UNITS | shown only when not at ISCO |
| Mass (M_sun) | `observer_panels.cpp:68` | 1..1e11 log, 1e8 | `massSolar` | none | affects the clock model, not the traced sky |
| Sky time scale | `observer_panels.cpp:76` | 1e-6..10 log, 1e-3 | `skyTimeScale` | none | unit text below the slider |
| Paused / Motion blur (x2) | `observer_panels.cpp:88,89` | bool | | none | |
| Navigation radios (x3) | `observer_panels.cpp:101-108` | Manual / Orbit camera / Blueshift patch | | none | |
| Longitude / Latitude (x2) | `observer_panels.cpp:117,119` | +/-180 (135), +/-89 (0) deg | | none | shown for Manual only |
| Field of view (deg) | `observer_panels.cpp:128` | 0.01..170 log, 100 | | none | |
| CMB / Stars (x2) | `observer_panels.cpp:134,136` | bool, on | | none | |
| Starfield luminance | `observer_panels.cpp:139` | 1e-6..1 log, 1e-3 cd/m^2 | `starSkyLuminance` | RANGE | six decades; the header states the unit |
| log10 luminance range | `observer_panels.cpp:141` | -12..20, (-7, 13.5) | display mapping | UNITS | `displayPeak` (4.0) has no control |
| Viewer inclination (deg) | `observer_panels.cpp:290` | 5..90, 80 | `distantInclinationDeg` | GATED | drives the schematic window drawing only |
| Viewer radius (M) | `observer_panels.cpp:326` | 2..1e6 log, 400 | `distantRadius` | GATED | drives the light-delay text only |

## 12. Campaign and Proper Time panels (game UI)

Statically sampled; they drive the campaign simulation, not the renderer. Not measured (out of scope).

| Control | file:line | Range / default | Flags | Note |
| --- | --- | --- | --- | --- |
| task cost (proper hours) | `campaign_panels.cpp:441` | 1..500 log, 24 | none | unit in the value format |
| local s per wall s | `campaign_panels.cpp:645` | 1..3600 log, 1 | none | log slider, unit in the label |
| run in real time / inbox / pause-on categories | `campaign_panels.cpp:629,631,666` | bool | none | |
| target band combo, prograde/retrograde and orbit/hover radios | `campaign_panels.cpp:385,409-420` | | none | |
| map backdrop combo, focus radios, Singularity window toggle | `campaign_panels.cpp:808,621,906` | | none | |
| Target system / Target band (x2, InputInt) | `constellation_panels.cpp:172,173` | unbounded ints, 0/0 | RANGE | out-of-range ids are only rejected at order time; a combo of valid systems and bands is the usable form |
| Retrograde orbit / Hold position with thrust / Hide briefing (x3) | `constellation_panels.cpp:175,179,265` | bool | none | |
| Curve Overlay Enabled | `settings_window.cpp:882` | bool, on | GATED | window exists only with `--curve-tsv` |

## 13. Proposed cut / merge / re-range list

Cut or hide:
1. Render Scale and Resolution Preset: no consumer; delete, or wire `renderScale` into `renderTargetExtent` (`main.cpp:1649`).
2. HUD Overlay, HUD Scale, Depth Pre-pass, RmlUi checkbox, Gizmo Operation and Mode (Rotate, Scale, Local), Use Spectral LUT with its two radius sliders (asset missing): nothing reads them.
3. Tesseract Projection and Eye w distance: uniforms are never read; either implement projection in `tesseract.frag` or remove.
4. Legacy disk block (12 sliders plus Noise Texture): move under a "Legacy tracer" collapsible that appears only when `BLACKHOLE_PHYSICAL_TRACER=0` or Legacy geodesic is selected; the default Visuals tab then shows the Kerr controls.
5. GRMHD Use / Bounds / Time-Series on the Kerr contract: disable with a tooltip as the legacy sliders are; keep the Slice preview.
6. Compare harness (21 controls): move to a developer window.

Merge:
1. Bloom Iterations moves into Post Processing beside the other bloom sliders.
2. Bloom tone folds into Exposure (both linear scene gains); Disk brightness keeps the emitter scale.
3. Hawking Preset drives the two sliders; either grey the sliders or show "Custom" after a manual edit.
4. Depth Far leaves the Depth Effects window (rename "Ray escape radius", scene units).
5. Time controls: one "Simulation time scale" that also drives the disk clock, or label Time Scale "Orbit camera and tesseract only".

Re-range or re-label:
1. Exposure default range 0.3..12 (log); Disk brightness 0.05..2.
2. Parallax max 0.01 -> about 0.001; add distance normalization. Drift max 0.05 -> 0.01.
3. Fog (tesseract): floor 0.05 or invert the mapping; rename "Fog density"; rename "Corridor density" to "Cell size (world units)"; rename "Scene scale" to "Slice tilt".
4. Orbit Radius 2..50 -> 4..400 to match the default 150-unit camera; the minimum must clear the horizon.
5. Swap Interval "Triple (2)" -> "Every 2nd vblank".
6. Add units: Compute Step Size, GRMHD bounds, Spectral radius, Slice Size, Drift speed, Playback Speed, gamepad sensitivities.
7. Replace gamepad axis and button SliderInt with named combos; Slice Channel range from the dataset.
8. Make Depth Effects work on RTE (write real depth into alpha) or grey the window with a notice; grey Exposure and Gamma when Tone mapping is off.
9. Expose or delete vignette, film grain, chromatic aberration, photon sphere glow strength, `displayPeak`.
10. Copy the orphaned persisted keys (`adisk*`, `gravitationalLensing`, `renderBlackHole`) into `RenderState` on load or delete them from `Settings`.

Not measured, with reasons: all controls without a setter (see setter matrix), input-device controls (Controls window), game panels, and observer sky. Every not-measured row is marked in its Note column or its section header.
