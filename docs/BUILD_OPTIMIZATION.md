# Blackhole Build Optimization Guide

**Ground-Up Optimization Infrastructure**

This document describes the comprehensive build optimization system for maximum performance, profiling, and debugging capabilities.

## Overview

The Blackhole build system supports multiple optimization configurations:

1. **Release Build**: Maximum performance (-O3, -march=native, Fat LTO)
2. **Profiling Build**: Optimized with profiling support (perf, valgrind, flamegraph)
3. **PGO Build**: Profile-Guided Optimization (10-20% faster than -O3)
4. **Debug Build**: Full debugging with sanitizers

## Quick Start

### Interactive Menu

```bash
./scripts/build-master.sh
```

Provides an interactive menu for selecting build configurations, viewing system information, and more.

### Direct Build Commands

```bash
# Maximum performance build
./scripts/build-optimized.sh Release

# Profiling-ready build
./scripts/build-profiling.sh

# PGO workflow (guided)
./scripts/build-master.sh pgo

# Debug build
./scripts/build-optimized.sh Debug
```

## Build Configurations

### 1. Release Build (Maximum Performance)

**Optimizations Applied:**
- **-O3**: Maximum compiler optimization
- **-march=native**: CPU-specific instructions (AVX2, AVX-512, FMA, etc.)
- **Fat LTO**: Link-Time Optimization across all modules
- **Fast Math**: Aggressive floating-point optimizations

**Expected Performance:**
- 4-6x faster than -O0
- ~20% faster than -O2
- Uses all available CPU features (SIMD)

**Usage:**
```bash
./scripts/build-optimized.sh Release
cd build && ./Blackhole
```

**Verification:**
The build script automatically checks for:
- CPU-specific instructions in binary
- Optimization flags applied
- Binary size and format

### 2. Profiling Build

**Configuration:**
- **-O3**: Full optimization maintained for realistic profiling
- **-g**: Debug symbols for accurate stack traces
- **-fno-omit-frame-pointer**: Frame pointers preserved for perf
- **LTO disabled**: Faster iteration, better debuggability

**Supported Tools:**
- **perf**: Linux performance profiler
- **valgrind**: Memory and cache profiler
- **flamegraph**: Visual stack trace analysis
- **hotspot**: GUI performance analyzer
- **heaptrack**: Memory allocation profiler

**Usage:**
```bash
./scripts/build-profiling.sh
cd build-profiling

# CPU profiling with perf
perf record -F 99 -g ./Blackhole
perf report

# Generate flamegraph
perf script | stackcollapse-perf.pl | flamegraph.pl > flame.svg

# Memory profiling with valgrind
valgrind --tool=callgrind --cache-sim=yes ./Blackhole
kcachegrind callgrind.out.*

# Heap profiling
heaptrack ./Blackhole
heaptrack_gui heaptrack.*.gz

# GUI profiler
hotspot ./Blackhole
```

### 3. Profile-Guided Optimization (PGO)

**Two-Phase Build Process:**

#### Phase 1: Generate Profile Data
```bash
./scripts/build-optimized.sh PGO-Gen
cd build && ./Blackhole

# Exercise typical workload:
# - Render various scenes
# - Adjust settings (resolution, ray steps, etc.)
# - Navigate different views
# Let it run for 30-60 seconds
```

#### Phase 2: Build with Profile Optimization

For **GCC** (automatic):
```bash
./scripts/build-optimized.sh PGO-Use
```

For **Clang** (merge profiles first):
```bash
llvm-profdata merge -output=build/pgo-profiles/default.profdata \
                     build/pgo-profiles/default.profraw
./scripts/build-optimized.sh PGO-Use
```

#### Guided Workflow
```bash
./scripts/build-master.sh pgo
# Follow interactive prompts
```

**Expected Performance:**
- 10-20% faster than standard -O3 build
- Optimizes hot paths based on actual runtime behavior
- Most effective for workloads similar to profiling run

**How It Works:**
1. First build instruments code to collect runtime statistics
2. You run the program with typical workload
3. Profiling data captures branch frequencies, hot paths, cache usage
4. Second build uses this data to optimize:
   - Function inlining decisions
   - Branch prediction hints
   - Code layout for cache efficiency
   - Virtual call devirtualization

### 4. Debug Build

**Configuration:**
- **-O0**: No optimization
- **-g3**: Maximum debug information
- **Sanitizers available**: ASan, UBSan, TSan
- **-Og** (optional): Debug-friendly optimization

**Usage:**
```bash
./scripts/build-optimized.sh Debug

# With AddressSanitizer
cmake -B build-debug -DCMAKE_BUILD_TYPE=Debug -DENABLE_ASAN=ON
cmake --build build-debug
./build-debug/Blackhole

# With UndefinedBehaviorSanitizer
cmake -B build-debug -DCMAKE_BUILD_TYPE=Debug -DENABLE_UBSAN=ON
cmake --build build-debug
./build-debug/Blackhole
```

## Optimization Technologies Explained

### Link Time Optimization (LTO)

**What is LTO?**
- Performs optimization across entire program at link time
- Sees full call graph, can inline across translation units
- Eliminates dead code globally
- Optimizes virtual calls, devirtualizes when possible

**Fat LTO vs Standard:**
- **Standard LTO**: Sequential optimization at link time
- **Fat LTO** (GCC -flto=auto): Parallel optimization using all CPU cores
- **ThinLTO** (Clang): Fast parallel LTO, good balance

**Performance Impact:**
- 5-15% performance improvement
- Increased link time (1-3 minutes for Blackhole)
- Larger memory usage during linking

**Enable/Disable:**
```bash
# Enabled by default in Release
cmake -DENABLE_LTO=ON -DENABLE_FAT_LTO=ON

# Disable for faster iteration
cmake -DENABLE_LTO=OFF
```

### -march=native

**What it does:**
- Enables all CPU instructions supported by build machine
- Includes: AVX, AVX2, AVX-512, FMA, SSE4.2, etc.
- Optimizes for specific cache sizes and pipeline characteristics

**Trade-off:**
- ✅ Maximum performance on build machine
- ❌ Binary won't run on CPUs without same features
- ❌ Not suitable for distribution

**For your CPU:**
```bash
# Check your CPU features
cat /proc/cpuinfo | grep flags | head -1

# See what -march=native enables
gcc -march=native -Q --help=target | grep enabled
```

**Override:**
```bash
# Target specific architecture
cmake -DENABLE_NATIVE_ARCH=OFF -DSIMD_TIER=AVX2

# For distribution builds
cmake -DENABLE_NATIVE_ARCH=OFF -DSIMD_TIER=SSE4
```

### Fast Math

**What it does:**
- `-ffast-math`: Aggressive floating-point optimizations
- Assumes no NaN/Inf handling needed
- Allows associative math transformations
- Enables vectorization of FP operations

**Trade-offs:**
- ✅ 5-10% performance in FP-heavy code
- ❌ Non-IEEE 754 compliant
- ❌ Can cause issues with infinity/NaN checking

**Safe in Blackhole because:**
- Physics code uses `safe_limits.h` with compiler builtins
- Shader math benefits from fast FP operations
- No critical NaN/Inf checks in hot paths

## Performance Measurement

### Benchmarking

```bash
# Build optimized
./scripts/build-optimized.sh Release
cd build

# Run with FPS counter
./Blackhole

# Note baseline FPS
# Then compare with different optimizations
```

### Profiling Hot Paths

```bash
# Build for profiling
./scripts/build-profiling.sh
cd build-profiling

# Profile CPU usage
perf record -F 99 -g --call-graph dwarf ./Blackhole

# Analyze
perf report --stdio

# Find hottest functions
perf report --sort=dso,symbol --stdio | head -50
```

### Flame Graphs

```bash
# After perf record above
perf script > out.perf
stackcollapse-perf.pl out.perf > out.folded
flamegraph.pl out.folded > flame.svg

# Open flame.svg in browser
firefox flame.svg
```

**Reading Flame Graphs:**
- X-axis: Alphabetical order (NOT time)
- Y-axis: Stack depth
- Width: Time spent in function + children
- Color: Random (for differentiation)
- Click: Zoom to function

### Cache Analysis

```bash
# Valgrind cache profiling
valgrind --tool=cachegrind \
         --cachegrind-out-file=cachegrind.out \
         ./Blackhole

# Annotate source
cg_annotate --auto=yes cachegrind.out

# Look for:
# - High D1 cache misses (L1 data)
# - High LL cache misses (last level)
# - Branch mispredictions
```

## System Requirements

### Minimum
- CMake 3.21+
- Conan 2.x
- GCC 11+ or Clang 14+
- 8 GB RAM
- 4 cores

### Recommended for Optimization
- GCC 13+ or Clang 16+
- 16 GB RAM (for LTO)
- 8+ cores (for parallel builds)
- CPU with AVX2+ support

### Profiling Tools

**Essential:**
```bash
# Arch Linux
sudo pacman -S perf valgrind

# Ubuntu/Debian
sudo apt install linux-tools-generic valgrind
```

**Optional but Recommended:**
```bash
# Arch Linux
sudo pacman -S hotspot heaptrack

# Flame graph tools
git clone https://github.com/brendangregg/FlameGraph
sudo cp FlameGraph/*.pl /usr/local/bin/
```

## Troubleshooting

### Build Failures

**Out of memory during LTO:**
```bash
# Reduce parallelism
cmake --build build --parallel 2

# Or disable LTO
cmake -DENABLE_LTO=OFF ..
```

**Undefined references with LTO:**
```bash
# Try without fat LTO
cmake -DENABLE_FAT_LTO=OFF ..

# Or use ThinLTO (Clang)
# Automatically used on Clang
```

**"Illegal instruction" at runtime:**
```bash
# CPU doesn't support -march=native instructions
# Rebuild for older CPU:
cmake -DENABLE_NATIVE_ARCH=OFF -DSIMD_TIER=SSE4 ..
```

### Profiling Issues

**perf permission denied:**
```bash
# Temporarily allow perf for non-root
sudo sysctl kernel.perf_event_paranoid=-1

# Or run as root (not recommended)
sudo perf record -F 99 -g ./Blackhole
```

**No debug symbols in perf:**
```bash
# Rebuild with profiling configuration
./scripts/build-profiling.sh

# Verify symbols
file build-profiling/Blackhole | grep "not stripped"
```

**Valgrind too slow:**
```bash
# Use cachegrind instead of memcheck
valgrind --tool=cachegrind ./Blackhole

# Or use heaptrack for memory profiling
heaptrack ./Blackhole
```

## Build System Architecture

### CMake Configuration Hierarchy

```
CMakeLists.txt
├── Conan Integration (dependencies)
├── C++23 Standard Setup
├── SIMD Detection & Configuration
│   ├── CPU feature detection (CPUID)
│   ├── Compiler flag selection
│   └── -march=native (if enabled)
├── Optimization Configuration ← NEW
│   ├── Build type defaults
│   ├── -O3 enforcement
│   ├── LTO/IPO setup
│   ├── PGO configuration
│   └── Profiling tool support
├── Warning System (5 levels)
├── Hardening Flags (FORTIFY, stack protection)
├── Sanitizers (ASan, UBSan, TSan)
├── Source Files Organization
└── Target Configuration
```

### Build Scripts

```
scripts/
├── build-master.sh          ← Master orchestration (interactive)
├── build-optimized.sh       ← Release/Debug/PGO builds
├── build-profiling.sh       ← Profiling-ready builds
├── build-quick.sh           ← Legacy quick build
└── conan_install.sh         ← Dependency management
```

## Advanced Usage

### Custom Optimization Flags

```bash
# Add custom flags
cmake -DCMAKE_CXX_FLAGS="-O3 -march=znver3 -mtune=znver3" ..

# Disable specific optimizations
cmake -DENABLE_FAST_MATH=OFF ..
```

### Hybrid Optimization

```bash
# O3 with LTO but no march=native
cmake -DENABLE_NATIVE_ARCH=OFF -DENABLE_LTO=ON ..

# O3 with march=native but no LTO
cmake -DENABLE_NATIVE_ARCH=ON -DENABLE_LTO=OFF ..
```

### Comparing Builds

```bash
# Build all variants
./scripts/build-master.sh release
./scripts/build-optimized.sh PGO-Use

# Compare binary sizes
ls -lh build*/Blackhole

# Benchmark each
# (manually record FPS)
```

## Performance Expectations

### Typical Improvements (vs -O0)

| Optimization | Speedup | Build Time |
|--------------|---------|------------|
| -O2          | 3-4x    | +20%       |
| -O3          | 4-5x    | +30%       |
| -O3 -march   | 5-6x    | +30%       |
| + LTO        | 6-7x    | +100%      |
| + PGO        | 7-8x    | +150%      |

### Blackhole-Specific

Based on the ray tracing workload:

- **Baseline** (-O0): ~0.5 FPS
- **-O2**: ~2 FPS
- **-O3**: ~2.5-3 FPS
- **-O3 -march=native**: ~3-4 FPS
- **+ LTO**: ~4-5 FPS
- **+ PGO**: ~5-6 FPS
- **+ 48 ray steps** (balanced): ~10-15 FPS (from earlier optimization)

**Total expected:** ~10-15 FPS with full optimization stack

## Continuous Integration

For CI/CD pipelines:

```bash
# Reproducible builds (no -march=native)
cmake -B build \
      -DCMAKE_BUILD_TYPE=Release \
      -DENABLE_NATIVE_ARCH=OFF \
      -DSIMD_TIER=SSE4 \
      -DENABLE_LTO=ON \
      -DENABLE_WERROR=ON

cmake --build build --parallel $(nproc)
```

## References

- [GCC Optimization Options](https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html)
- [Clang Optimization Flags](https://clang.llvm.org/docs/CommandGuide/clang.html#code-generation-options)
- [CMake IPO](https://cmake.org/cmake/help/latest/prop_tgt/INTERPROCEDURAL_OPTIMIZATION.html)
- [Linux perf](https://perf.wiki.kernel.org/index.php/Main_Page)
- [Brendan Gregg's Flame Graphs](https://www.brendangregg.com/flamegraphs.html)
- [Valgrind Manual](https://valgrind.org/docs/manual/manual.html)
