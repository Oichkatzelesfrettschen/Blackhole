# Native Conan 2.x + CMake Build Workflow

**Date**: 2026-02-11
**Status**: ✅ Production Ready - Pure Conan 2.x + CMake Integration

## Overview

This project uses **native Conan 2.x + CMake integration** via **CMakePresets.json**.
All build configurations are defined natively in CMake - **no shell scripts required**.

## Philosophy

- **Native over scripted**: Use CMakePresets.json instead of wrapper scripts
- **Transparent**: All build options visible in CMakePresets.json and CMakeLists.txt
- **Reproducible**: Same commands work on any platform with Conan + CMake
- **Secure**: No external script injection, pure build system configuration

## Quick Start

### 1. Install Dependencies with Conan

```bash
# Detect your system's default profile
conan profile detect

# Install dependencies for Release build
conan install . --output-folder=build/Release --build=missing -s build_type=Release -s compiler.cppstd=17

# Or for Debug build
conan install . --output-folder=build/Debug --build=missing -s build_type=Debug -s compiler.cppstd=17
```

### 2. Configure and Build

```bash
# Using CMake presets (recommended)
cmake --preset release
cmake --build --preset release

# Or manually
cmake -B build/Release --preset release
cmake --build build/Release --parallel
```

### 3. Run

```bash
./build/Release/Blackhole
```

## Build Configurations

All configurations are defined in `CMakePresets.json`. Use them directly without scripts.

### Maximum Performance (Release)

Flags: `-O3`, `-march=native`, Fat LTO, fast-math

```bash
conan install . --output-folder=build/Release --build=missing -s build_type=Release -s compiler.cppstd=17
cmake --preset release
cmake --build --preset release
```

**Optimization features:**
- `ENABLE_NATIVE_ARCH=ON` - CPU-specific SIMD instructions
- `ENABLE_LTO=ON` - Link Time Optimization
- `ENABLE_FAT_LTO=ON` - Parallel LTO with full optimization
- `ENABLE_FAST_MATH=ON` - Aggressive floating-point optimizations
- `ENABLE_WERROR=ON` - Warnings as errors

### Profiling Build (perf/valgrind)

Optimized with debug symbols for profiling tools.

```bash
conan install . --output-folder=build/Profiling --build=missing -s build_type=RelWithDebInfo -s compiler.cppstd=17
cmake --preset profiling
cmake --build --preset profiling
```

**Profiling features:**
- `ENABLE_PERF_PROFILING=ON` - Frame pointers for perf
- `ENABLE_VALGRIND_FRIENDLY=ON` - Valgrind compatibility
- `ENABLE_PROFILING=ON` - General profiling support
- LTO and fast-math **disabled** for accurate profiling

**Usage:**
```bash
# perf profiling
perf record -F 99 -g ./build/Profiling/Blackhole
perf report

# valgrind memory check
valgrind --leak-check=full ./build/Profiling/Blackhole

# Generate flamegraph
perf script | stackcollapse-perf.pl | flamegraph.pl > flame.svg
```

### Debug Build

Full debug symbols, no optimization.

```bash
conan install . --output-folder=build/Debug --build=missing -s build_type=Debug -s compiler.cppstd=17
cmake --preset debug
cmake --build --preset debug
```

### Profile-Guided Optimization (PGO)

Two-phase build for 10-20% performance improvement over standard -O3.

**Phase 1: Generate profile data**

```bash
# Install dependencies
conan install . --output-folder=build/PGO-Gen --build=missing -s build_type=Release -s compiler.cppstd=17

# Build with instrumentation
cmake --preset pgo-gen
cmake --build --preset pgo-gen

# Run executable to generate profile data
cd build/PGO-Gen
./Blackhole
# (Exercise typical workload: render scenes, adjust settings)
cd ../..

# For Clang, merge profile data
llvm-profdata merge -output=build/PGO-Gen/pgo-profiles/default.profdata build/PGO-Gen/pgo-profiles/default.profraw
```

**Phase 2: Build with profile optimization**

```bash
# Install dependencies
conan install . --output-folder=build/PGO-Use --build=missing -s build_type=Release -s compiler.cppstd=17

# Build optimized binary
cmake --preset pgo-use
cmake --build --preset pgo-use

# Run optimized executable
./build/PGO-Use/Blackhole
```

## Conan 2.x Workflow

### Profile Configuration

Create or edit `~/.conan2/profiles/default`:

```ini
[settings]
arch=x86_64
build_type=Release
compiler=clang
compiler.cppstd=17
compiler.libcxx=libstdc++11
compiler.version=21
os=Linux

[conf]
tools.build:compiler_executables={'c': 'clang', 'cpp': 'clang++'}

[buildenv]
CC=clang
CXX=clang++
```

### Install Dependencies for All Build Types

```bash
# Release
conan install . --output-folder=build/Release --build=missing -s build_type=Release -s compiler.cppstd=17

# Debug
conan install . --output-folder=build/Debug --build=missing -s build_type=Debug -s compiler.cppstd=17

# Profiling
conan install . --output-folder=build/Profiling --build=missing -s build_type=RelWithDebInfo -s compiler.cppstd=17
```

### Using Conan Lockfiles (Reproducible Builds)

```bash
# Generate lockfile
conan lock create . --lockfile=conan.lock -s compiler.cppstd=17

# Install using lockfile
conan install . --lockfile=conan.lock --output-folder=build/Release --build=missing
```

## CMake Build Options

All options are in `CMakeLists.txt` and configurable via CMakePresets.json or command line.

### Performance Options

| Option | Default | Description |
|--------|---------|-------------|
| `ENABLE_NATIVE_ARCH` | ON | CPU-specific optimizations (-march=native) |
| `ENABLE_LTO` | ON | Link Time Optimization |
| `ENABLE_FAT_LTO` | ON | Parallel LTO with full optimization |
| `ENABLE_FAST_MATH` | ON | Aggressive floating-point optimizations |

### Profiling Options

| Option | Default | Description |
|--------|---------|-------------|
| `ENABLE_PERF_PROFILING` | OFF | Frame pointers for perf |
| `ENABLE_VALGRIND_FRIENDLY` | OFF | Valgrind compatibility |
| `ENABLE_PROFILING` | OFF | General profiling support |

### Code Quality Options

| Option | Default | Description |
|--------|---------|-------------|
| `ENABLE_WERROR` | ON | Treat warnings as errors |
| `WARNING_LEVEL` | 5 | Warning level (1-5) |
| `ENABLE_CLANG_TIDY` | OFF | Static analysis |
| `ENABLE_CPPCHECK` | OFF | Static analysis |

### Override Options at Configure Time

```bash
cmake --preset release -DENABLE_FAST_MATH=OFF -DWARNING_LEVEL=3
```

## Package Version Upgrades (2026-02-11)

Latest Conan 2.x native versions:

| Package | Version | Notes |
|---------|---------|-------|
| xsimd | 14.0.0 | SIMD abstraction (upgraded from 13.2.0) |
| highway | 1.3.0 | Portable SIMD (upgraded from 1.2.0) |
| entt | 3.16.0 | ECS framework (upgraded from 3.15.0) |
| spdlog | 1.17.0 | Logging (upgraded from 1.16.0) |
| gtest | 1.17.0 | Testing (upgraded from 1.14.0) |
| z3 | 4.15.4 | Theorem proving (upgraded from 4.14.1) |
| meshoptimizer | 1.0 | Mesh optimization (upgraded from 0.25) |
| eigen | 3.4.1 | Linear algebra (upgraded from 3.4.0) |

All packages verified in ConanCenter as Conan 2.x native.

## C++ Standard: C++17

Project uses **C++17** for maximum compatibility:

- **Compiler support**: GCC 7+, Clang 5+, MSVC 2017+
- **Conan 2.x recommended**: Standard for broad compatibility
- **OpenGL ecosystem**: Most libraries target C++17

Configured in `conanfile.py` and enforced in CMake.

## OpenGL Stack

Native OpenGL bindings:

- **glfw 3.4**: Window & input management
- **glbinding 3.5.0**: Type-safe OpenGL API binding
- **glm 1.0.1**: OpenGL Mathematics
- **imgui 1.92.5-docking**: Immediate mode GUI

## Verification

Run the migration verification script:

```bash
./scripts/verify-conan2-migration.sh
```

Expected output:
```
✓ Conan 2.x installed
✓ conanfile.py exists
✓ C++17 configured
✓ All packages at latest versions
✓ No deprecated Conan 1.x features
```

## Clean Build

```bash
# Clean all build artifacts
rm -rf build build-* .conan/

# Clean Conan cache (optional)
conan remove "*" -c

# Fresh build
conan install . --output-folder=build/Release --build=missing -s build_type=Release -s compiler.cppstd=17
cmake --preset release
cmake --build --preset release
```

## IDE Integration

### Visual Studio Code

Install CMake Tools extension, then:

1. Open Command Palette (Ctrl+Shift+P)
2. Select: "CMake: Select a Configure Preset"
3. Choose: `release`, `debug`, `profiling`, etc.
4. Build: "CMake: Build" (F7)

### CLion

CLion automatically detects CMakePresets.json:

1. Open project
2. Select preset from dropdown (top-right)
3. Build normally (Ctrl+F9)

## Troubleshooting

### Conan toolchain not found

**Problem**: CMake can't find `conan_toolchain.cmake`

**Solution**: Run `conan install` before `cmake`:

```bash
conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=17
```

### Wrong C++ standard (compiler.cppstd=23)

**Problem**: Build uses C++23 instead of C++17

**Solution**: Add `-s compiler.cppstd=17` to conan install:

```bash
conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=17
```

Or update your default profile:

```bash
conan profile show default
# Edit ~/.conan2/profiles/default and set: compiler.cppstd=17
```

### Missing dependencies

**Problem**: CMake can't find packages

**Solution**: Run `conan install` with `--build=missing`:

```bash
conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=17
```

## Migration from Shell Scripts

If you previously used shell scripts, here's the mapping:

| Old Script | New Native Command |
|------------|-------------------|
| `./scripts/build-optimized.sh Release` | `conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=17 && cmake --preset release && cmake --build --preset release` |
| `./scripts/build-profiling.sh` | `conan install . --output-folder=build/Profiling --build=missing -s compiler.cppstd=17 -s build_type=RelWithDebInfo && cmake --preset profiling && cmake --build --preset profiling` |
| `./scripts/build-master.sh` | Use presets directly: `cmake --preset <name>` |

**Note**: Shell scripts are kept for backwards compatibility but are no longer required.

## References

- [Conan 2.0 Documentation](https://docs.conan.io/2.0/)
- [CMakePresets.json Spec](https://cmake.org/cmake/help/latest/manual/cmake-presets.7.html)
- [Conan CMake Integration](https://docs.conan.io/2.0/reference/tools/cmake.html)
- [CMake Build Type](https://cmake.org/cmake/help/latest/variable/CMAKE_BUILD_TYPE.html)

## Summary

✅ **Pure Conan 2.x + CMake workflow**
✅ **No shell script dependency**
✅ **All options in CMakePresets.json**
✅ **Transparent and reproducible**
✅ **C++17 standard**
✅ **Latest package versions**
✅ **OpenGL-native stack**

**Workflow**:
```bash
conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=17
cmake --preset release
cmake --build --preset release
./build/Release/Blackhole
```
