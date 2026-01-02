# Dependency Matrix

**Last Updated:** 2026-01-01
**Conan Home:** `.conan/` (repo-local, reproducible)
**CMake Version:** 3.31+
**Compiler:** GCC/Clang C++23

---

## Core Dependencies (Conan 2.x)

### Graphics & UI

| Package | Version | Purpose | Override |
|---------|---------|---------|----------|
| glfw | 3.4 | Window, input, context | - |
| glbinding | 3.5.0 | OpenGL loader (pure C++) | - |
| glm | 1.0.1 | Math (shader path) | - |
| imgui | 1.92.5-docking | UI panels | override |
| imguizmo | cci.20231114 | Gizmo transforms | - |
| rmlui | 6.1 | HUD overlay (optional) | - |

### Math & Physics

| Package | Version | Purpose | Override |
|---------|---------|---------|----------|
| eigen | 3.4.0 | Math (physics path) | optional |
| xsimd | 13.2.0 | SIMD vectorization | override |
| gmp | 6.3.0 | Multiprecision (validation) | - |
| mpfr | 4.2.2 | Multiprecision (validation) | - |

### Data & Serialization

| Package | Version | Purpose | Override |
|---------|---------|---------|----------|
| flatbuffers | 25.9.23 | Binary serialization | - |
| hdf5 | 1.14.6 | GRMHD data files | override |
| highfive | 3.1.1 | HDF5 C++ wrapper | - |
| stb | cci.20240531 | Image loading | - |

### Concurrency & ECS

| Package | Version | Purpose | Override |
|---------|---------|---------|----------|
| entt | 3.15.0 | Entity-component system | - |
| pcg-cpp | cci.20220409 | Random number generation | - |
| taskflow | 3.10.0 | Task parallelism | - |

### Logging & CLI

| Package | Version | Purpose | Override |
|---------|---------|---------|----------|
| spdlog | 1.16.0 | Structured logging | shared |
| fmt | 12.1.0 | Format strings | override, shared |
| cli11 | 2.6.0 | Command-line parsing | - |
| boost | 1.90.0 | Utility libraries | - |

### Profiling & Debug

| Package | Version | Purpose | Override |
|---------|---------|---------|----------|
| tracy | 0.13.1 | CPU/GPU profiling | optional |
| z3 | 4.14.1 | Constraint solver | optional |

### SPIR-V Tooling (Optional)

| Package | Version | Purpose | Override |
|---------|---------|---------|----------|
| shaderc | 2025.3 | GLSL -> SPIR-V | optional |
| spirv-tools | 1.4.313.0 | SPIR-V optimizer | optional |
| spirv-cross | 1.4.321.0 | SPIR-V reflection | optional |
| spirv-headers | 1.4.313.0 | SPIR-V headers | optional |

### Optional Features

| Package | Version | Purpose | CMake Option |
|---------|---------|---------|--------------|
| ktx | 4.3.2 | KTX2 textures | ENABLE_KTX |
| openimageio | 3.1.8.0 | HDR images | ENABLE_OPENIMAGEIO |
| meshoptimizer | 0.25 | Mesh optimization | ENABLE_MESHOPTIMIZER |
| fastnoise2 | 0.10.0-alpha | Procedural noise | ENABLE_FASTNOISE2 |
| watcher | 0.14.1 | File watching | ENABLE_SHADER_WATCHER |

---

## CMake Options

```cmake
option(ENABLE_KTX "Enable KTX texture support" OFF)
option(ENABLE_OPENIMAGEIO "Enable OpenImageIO support" OFF)
option(ENABLE_SPIRV_TOOLING "Enable SPIR-V compile/optimize/reflect" ON)
option(ENABLE_MESHOPTIMIZER "Enable mesh optimization" ON)
option(ENABLE_SHADER_WATCHER "Enable shader hot-reload" OFF)
option(ENABLE_FASTNOISE2 "Enable FastNoise2" ON)
option(ENABLE_EIGEN "Enable Eigen math backend" ON)
option(ENABLE_RMLUI "Enable RmlUi overlay" OFF)
option(ENABLE_TRACY "Enable Tracy profiler" OFF)
option(ENABLE_Z3 "Enable Z3 solver" OFF)
option(ENABLE_PRECISION_TESTS "Enable GMP/MPFR tests" OFF)
```

---

## Build Presets

| Preset | Purpose | Flags |
|--------|---------|-------|
| release | Production | -O3 -DNDEBUG |
| debug | Development | -g -O0 |
| riced | Optimized debug | -O2 -g -march=native |
| riced-asan | Address sanitizer | -fsanitize=address |
| riced-tsan | Thread sanitizer | -fsanitize=thread |
| riced-coverage | Code coverage | --coverage |
| riced-profile | Profiling | -pg |

---

## Validation Status

| Test | Status | Command |
|------|--------|---------|
| physics_validation | Pass | `ctest -R physics` |
| grmhd_pack_fixture | Pass | `ctest -R grmhd` |
| precision_regression | Pass | `ctest -R precision` |
| math_types_parity | Pass | `ctest -R math_types` |
| shader validation | Pass | `cmake --build --target validate-shaders` |

---

## Version Update Procedure

1. Check available versions: `conan list -c "pkg/*"`
2. Update version in `conanfile.py`
3. Run `./scripts/conan_install.sh Release build`
4. Rebuild: `cmake --build --preset release`
5. Run tests: `ctest --test-dir build/Release`
6. Update this document with new version

---

## Known Issues

| Package | Issue | Workaround |
|---------|-------|------------|
| fastnoise2 | GCC overflow warnings | Suppress via system includes |
| spirv-cross | Deprecated lambda captures | Suppress via system includes |
| z3 | GCC 15 warnings | Keep non-fatal |
| hdf5 | Requires shared=True | Set in default_options |

---

## External Tools (Non-Conan)

| Tool | Version | Purpose |
|------|---------|---------|
| glslangValidator | System | Shader validation |
| perf | System | CPU profiling |
| gcovr | System | Coverage reports |
| clang-tidy | System | Static analysis |
| cppcheck | System | Static analysis |

---

## References

- Conan Center: https://conan.io/center
- conanfile.py: `/home/eirikr/Github/Blackhole/conanfile.py`
- requirements.md: `/home/eirikr/Github/Blackhole/requirements.md`
