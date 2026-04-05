# Product Matrix

This repository currently exposes one shared desktop UI plus adjacent integration
surfaces. The intended product split is:

| Product | Preset | Primary output | Notes |
|---------|--------|----------------|-------|
| Shared desktop app | `release` | `Blackhole` | Baseline desktop build. |
| Pure GLSL desktop | `glsl-only` | `BlackholeGLSL` | Dedicated desktop executable with the shared UI and no CUDA backend. |
| CUDA desktop | `cuda-only` | `BlackholeCUDA` | Dedicated desktop executable with the shared UI and CUDA forced on. |
| Blender bridge | `blender-bridge` | `libblackhole_bridge.so` | Bridge-focused build without desktop app, tools, or benchmarks. |
| Docs + verification | `docs` | `doxygen`, `repo-truth`, `verify-physics-claims`, `package-blender-addon`, `verify-blender-addon-package`, `verify-blender-bridge-abi`, `stage-blender-addon` | Documentation and evidence lane. |
| Full dev stack | `full-dev` | Desktop app + bridge + tools + tests | Main development preset for the unified stack. |

## Shared UI policy

The desktop application remains the canonical control surface. The current
foundation work keeps a single desktop UI and treats backend selection as a
product boundary rather than a separate frontend. The `BlackholeGLSL` and
`BlackholeCUDA` binaries are compiled from the same shared UI/runtime entrypoint
but expose different backend policy at compile time.

## Conan install directories

Each preset expects Conan output in the matching build tree:

```bash
./scripts/conan_install.sh Release build/GLSL-Only/Release
./scripts/conan_install.sh Release build/CUDA-Only/Release
./scripts/conan_install.sh Release build/BlenderBridge/Release
./scripts/conan_install.sh Release build/Docs/Release
./scripts/conan_install.sh RelWithDebInfo build/FullDev/RelWithDebInfo
```

## Workflow examples

Pure GLSL desktop:

```bash
./scripts/conan_install.sh Release build/GLSL-Only/Release
cmake --preset glsl-only
cmake --build --preset glsl-only
ctest --preset glsl-only
```

CUDA desktop:

```bash
./scripts/conan_install.sh Release build/CUDA-Only/Release
cmake --preset cuda-only
cmake --build --preset cuda-only
ctest --preset cuda-only
```

Docs and verification:

```bash
./scripts/conan_install.sh Release build/Docs/Release
cmake --preset docs
cmake --build --preset docs --target doxygen repo-truth verify-physics-claims package-blender-addon verify-blender-addon-package verify-blender-bridge-abi stage-blender-addon
ctest --preset docs -R "repo_truth_generation|physics_claims_matrix"
```

Microbenchmark lane:

```bash
./scripts/conan_install.sh --cmake-preset microbench
cmake --preset microbench
cmake --build --preset microbench --target physics_microbench
./build/Microbench/Release/physics_microbench --benchmark_format=json
```

This preset intentionally disables Highway so the benchmark lane stays buildable
on the current Clang toolchain while still exercising the xsimd/SLEEF path.

mimalloc allocator experiment lane:

```bash
./scripts/conan_install.sh --cmake-preset release-mimalloc
cmake --preset release-mimalloc
cmake --build --preset release-mimalloc
ctest --test-dir build/ReleaseMimalloc/Release --output-on-failure
```

Bridge-focused build:

```bash
./scripts/conan_install.sh Release build/BlenderBridge/Release
cmake --preset blender-bridge
cmake --build --preset blender-bridge --target blackhole_bridge package-blender-addon verify-blender-addon-package verify-blender-bridge-abi stage-blender-addon
```

Full development stack:

```bash
./scripts/conan_install.sh RelWithDebInfo build/FullDev/RelWithDebInfo
cmake --preset full-dev
cmake --build --preset full-dev
ctest --preset full-dev
```

Bridge smoke tests and smoke-report verification are only registered in a build tree that has both
`ENABLE_BLENDER_BRIDGE=ON` and `BUILD_TESTING=ON`. The `full-dev` preset is the
recommended default for `ctest`-driven Blender and Octane validation.
