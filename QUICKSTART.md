# Blackhole - Quick Start Guide

**Native Conan 2.x + CMake Build - No Scripts Required**

## One-Line Build

```bash
conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=17 && cmake --preset release && cmake --build --preset release
```

Then run: `./build/Release/Blackhole`

## Build Configurations

| Configuration | Command |
|--------------|---------|
| **Release** (Maximum Performance) | `cmake --preset release && cmake --build --preset release` |
| **Debug** | `cmake --preset debug && cmake --build --preset debug` |
| **Profiling** (perf/valgrind) | `cmake --preset profiling && cmake --build --preset profiling` |
| **PGO** (Profile-Guided) | See PGO section below |

## Prerequisites

```bash
# Install Conan 2.x
pip install conan

# Detect your profile
conan profile detect
```

## Step-by-Step

### 1. Install Dependencies

```bash
conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=17
```

### 2. Configure

```bash
cmake --preset release
```

### 3. Build

```bash
cmake --build --preset release
```

### 4. Run

```bash
./build/Release/Blackhole
```

## Profile-Guided Optimization (PGO)

**Phase 1: Generate profiles**

```bash
conan install . --output-folder=build/PGO-Gen --build=missing -s compiler.cppstd=17
cmake --preset pgo-gen && cmake --build --preset pgo-gen
cd build/PGO-Gen && ./Blackhole  # Run typical workload
# For Clang: llvm-profdata merge -output=pgo-profiles/default.profdata pgo-profiles/default.profraw
```

**Phase 2: Optimized build**

```bash
conan install . --output-folder=build/PGO-Use --build=missing -s compiler.cppstd=17
cmake --preset pgo-use && cmake --build --preset pgo-use
./build/PGO-Use/Blackhole  # 10-20% faster than -O3
```

## Optimizations Enabled by Default

- **-O3**: Maximum compiler optimization
- **-march=native**: CPU-specific SIMD instructions
- **Fat LTO**: Link Time Optimization (full cross-module)
- **fast-math**: Aggressive floating-point optimizations

## Clean Build

```bash
rm -rf build .conan/
```

## Documentation

- **NATIVE_BUILD_WORKFLOW.md**: Complete native workflow guide
- **CONAN2_FULL_MIGRATION.md**: Migration details and package versions
- **CMakePresets.json**: All build configurations

## Verification

```bash
./scripts/verify-conan2-migration.sh
```

Expected: All checks pass, C++17 verified, latest packages confirmed.

## Technology Stack

- **C++17** (GCC 7+, Clang 5+, MSVC 2017+)
- **Conan 2.x** (native, no deprecated features)
- **OpenGL** (glfw 3.4, glbinding 3.5.0, glm 1.0.1, imgui 1.92.5-docking)
- **SIMD** (xsimd 14.0.0, highway 1.3.0, sleef 3.9.0)

## Troubleshooting

**Q**: Conan toolchain not found?
**A**: Run `conan install` before `cmake`:
```bash
conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=17
```

**Q**: Wrong C++ standard (C++23 instead of C++17)?
**A**: Add `-s compiler.cppstd=17` to `conan install` or update your profile:
```bash
# Edit ~/.conan2/profiles/default
[settings]
compiler.cppstd=17
```

**Q**: Missing dependencies?
**A**: Use `--build=missing` in `conan install`:
```bash
conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=17
```

## IDE Support

**VS Code**: Install CMake Tools → Select preset → Build (F7)
**CLion**: Auto-detects CMakePresets.json → Select from dropdown → Build (Ctrl+F9)

---

**Pure native build system - no shell scripts required.**
