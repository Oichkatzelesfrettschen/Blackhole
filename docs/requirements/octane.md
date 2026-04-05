# Octane Requirements

## Scope

Use this lane for the optional Octane-backed Blender environment. This is a
separate track from stock Blender support.

## Required

- Octane-enabled Blender installation
- NVIDIA GPU and CUDA-capable driver/runtime
- Matching Octane runtime setup for the local environment
- NumPy available in OctaneBlender's Python environment

## Current policy

- Octane is treated as an optional secondary rendering lane.
- Stock Blender and OctaneBlender should be documented and tested separately.
- Do not assume Octane availability when validating the primary Blender path.

## Suggested validation

- verify the Octane-enabled Blender binary is visible on `PATH`
- record the binary version in the generated repo-truth report
- keep Octane smoke tests separate from the stock Blender addon tests
- point OctaneBlender at the same canonical addon package built from `blender/addon/blackhole_physics/`
- set `BLACKHOLE_BRIDGE_LIB` explicitly when the bridge library is outside standard linker paths

## Headless smoke test

When `OctaneBlender` is available on `PATH`, validate the addon lane with:

```bash
./scripts/conan_install.sh RelWithDebInfo build/FullDev/RelWithDebInfo
cmake --preset full-dev
cmake --build --preset full-dev --target octane-addon-smoke verify-octane-smoke-report
ctest --preset full-dev -R "octane_addon_smoke|octane_smoke_report" --output-on-failure
```

Current local note:

- The Octane smoke test passes even when Octane prints server-connect warnings,
  so treat those messages as environment diagnostics unless the target exits
  non-zero.
- The generated machine-readable report lands under
  `build/<preset>/reports/octane_smoke.json`.
- The verified summary lands under
  `build/<preset>/reports/octane_smoke_verified.json`.
- The tier sweep lands under:
  - `build/<preset>/reports/octane_quality_sweep.json`
  - `build/<preset>/reports/octane_quality_sweep_verified.json`
  - `build/<preset>/reports/octane_quality_sweep_verified.md`

## Dream Textures

The Octane lane carries a separate Dream Textures runtime. This is staged into
the OctaneBlender 4.5 user addon tree and pinned to a Blackhole-managed Python
3.11 venv before verification.

```bash
cmake --build --preset release --target verify-dream-textures-octane
ctest --test-dir build/Release -R dream_textures_octane --output-on-failure
```

Generated evidence:

- `build/<preset>/reports/dream_textures_octane_install.json`
- `build/<preset>/reports/dream_textures_octane_verified.json`
- `build/<preset>/reports/dream_textures_octane_verified.md`

## Optimization workflow

Use the interactive benchmark lane for the default Octane policy:

```bash
cmake --build --preset release --target verify-octane-interactive-benchmark
```

Use the tier sweep when you want to tune quality vs performance deliberately:

```bash
cmake --build --preset release --target verify-octane-quality-sweep
```

The current repo-native tiers are:

- `interactive`: for lookdev and faster preview iteration
- `balanced`: the default benchmark policy
- `cinematic`: slower final-quality render settings

The detailed policy is documented in:

- `docs/developer-guide/octane-optimization.md`

Use the harsh-lighting benchmark when you want a second, more stressful scene:

```bash
cmake --build --preset release --target verify-octane-harsh-scene
```

Interactive setup still needs the packaged addon zip installed in OctaneBlender
or an explicit `BLENDER_USER_SCRIPTS` directory. If the bridge library is not
installed into a standard loader path, export:

```bash
export BLACKHOLE_BRIDGE_LIB=/absolute/path/to/libblackhole_bridge.so
OctaneBlender --python blender/addon/setup_octane.py
```
