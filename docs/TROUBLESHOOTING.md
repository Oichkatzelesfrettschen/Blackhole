# Troubleshooting Guide

**WHY:** Solve common build/runtime issues quickly
**WHAT:** Known issues, error messages, and solutions
**HOW:** Search for error message, follow solution steps

---

## Quick Diagnostics

**Build failing?**
```bash
# Clean and rebuild
rm -rf build .conan/p
./scripts/conan_install.sh Release build
cmake --preset release
cmake --build --preset release
```

**Runtime crash?**
```bash
# Run with debug symbols
cmake --preset debug
cmake --build --preset debug
gdb ./build/Debug/Blackhole
```

**Performance issues?**
```bash
# Check SIMD tier
BLACKHOLE_LOG_LEVEL=DEBUG ./build/Release/Blackhole

# Run benchmark
./build/Release/physics_bench --rays 4000 --steps 2000
```

---

## Build Issues

### Conan Package Resolution Failures

**Error:**
```
ERROR: Missing prebuilt package for 'glfw/3.4'
```

**Causes:**
1. Conan cache corruption
2. Network timeout
3. Incompatible compiler version

**Solutions:**
```bash
# Solution 1: Clean Conan cache
rm -rf ~/.conan2/p
./scripts/conan_install.sh Release build

# Solution 2: Build missing packages
conan install . --build=missing --output-folder=build/Release

# Solution 3: Update Conan
pip install --upgrade conan

# Solution 4: Check remote
conan remote list
conan remote update conancenter https://center.conan.io
```

---

### CMake Configuration Failures

**Error:**
```
CMake Error: Could NOT find OpenGL (missing: OPENGL_opengl_LIBRARY OPENGL_glx_LIBRARY)
```

**Cause:** Missing system OpenGL development libraries

**Solution (Arch Linux):**
```bash
sudo pacman -S mesa libglvnd
```

**Solution (Ubuntu/Debian):**
```bash
sudo apt install libgl1-mesa-dev libglu1-mesa-dev
```

---

**Error:**
```
CMake Error: The source directory ".../Blackhole" does not appear to contain CMakeLists.txt
```

**Cause:** Wrong directory or corrupted checkout

**Solution:**
```bash
# Verify you're in project root
ls -l CMakeLists.txt

# If missing, re-clone
cd ..
rm -rf Blackhole
git clone <repo-url> Blackhole
```

---

### Compilation Errors

**Error:**
```
error: 'std::format' is not a member of 'std'
```

**Cause:** Compiler doesn't support C++23 `<format>`

**Solution:**
```bash
# Check compiler version (need GCC 14+ or Clang 18+)
g++ --version
clang++ --version

# Upgrade compiler (Arch Linux)
sudo pacman -S gcc clang

# Or use libfmt fallback
cmake --preset release -DUSE_STD_FORMAT=OFF
```

---

**Error:**
```
error: #error "AVX-512 support required but not available"
```

**Cause:** Building AVX-512 code on CPU without support

**Solution:**
```bash
# Disable AVX-512 at build time
cmake --preset release -DBLACKHOLE_DISABLE_AVX512=ON
cmake --build --preset release
```

---

### Linker Errors

**Error:**
```
undefined reference to `glfwCreateWindow'
```

**Cause:** GLFW not linked or library path incorrect

**Solution:**
```bash
# Reinstall Conan dependencies
rm -rf build .conan/p
./scripts/conan_install.sh Release build
cmake --preset release
cmake --build --preset release
```

---

**Error:**
```
/usr/bin/ld: cannot find -lGL
```

**Cause:** Missing OpenGL libraries

**Solution (Arch Linux):**
```bash
sudo pacman -S mesa libglvnd
```

**Solution (Ubuntu):**
```bash
sudo apt install libgl1-mesa-dev
```

---

## Runtime Issues

### Shader Compilation Failures

**Error:**
```
ERROR: Shader compilation failed: shader/blackhole_main.frag
0:125: error: 'invalid syntax' : syntax error
```

**Causes:**
1. GLSL syntax error
2. Missing #include
3. OpenGL version mismatch

**Solutions:**
```bash
# Solution 1: Validate shader manually
glslangValidator -V shader/blackhole_main.frag

# Solution 2: Check OpenGL version
glxinfo | grep "OpenGL version"
# Need OpenGL 4.6+

# Solution 3: Check shader logs
BLACKHOLE_LOG_LEVEL=DEBUG ./build/Release/Blackhole 2>&1 | grep -A 10 "Shader"
```

---

### OpenGL Context Creation Failures

**Error:**
```
ERROR: Failed to create OpenGL 4.6 context
```

**Causes:**
1. GPU doesn't support OpenGL 4.6
2. Driver issue
3. Running in SSH/headless environment

**Solutions:**
```bash
# Solution 1: Check GPU support
glxinfo | grep "OpenGL version"

# Solution 2: Update graphics drivers (Arch Linux)
sudo pacman -S mesa vulkan-radeon # AMD
sudo pacman -S nvidia nvidia-utils  # NVIDIA

# Solution 3: Force software rendering (slow)
LIBGL_ALWAYS_SOFTWARE=1 ./build/Release/Blackhole

# Solution 4: Check X11 display
echo $DISPLAY  # Should be `:0` or similar
```

---

### Segmentation Faults

**Error:**
```
Segmentation fault (core dumped)
```

**Diagnosis:**
```bash
# Run with debugger
cmake --preset debug
cmake --build --preset debug
gdb ./build/Debug/Blackhole

# In GDB:
(gdb) run
(gdb) backtrace  # Shows crash location
(gdb) frame 0    # Inspect variables
```

**Common Causes:**
1. Null pointer dereference
2. Out-of-bounds array access
3. Unaligned SIMD load/store

**Solutions:**
```bash
# Solution 1: Run with AddressSanitizer
cmake --preset asan
cmake --build --preset asan
./build/ASan/Blackhole

# Solution 2: Run with Valgrind
valgrind --leak-check=full ./build/Debug/Blackhole

# Solution 3: Check memory limits
ulimit -v  # Virtual memory limit
```

---

### Performance Issues

**Issue:** Low FPS (< 30 fps)

**Diagnosis:**
```bash
# Check SIMD tier
BLACKHOLE_LOG_LEVEL=DEBUG ./build/Release/Blackhole 2>&1 | grep SIMD

# Run benchmark
./build/Release/physics_bench --rays 4000 --steps 2000

# Check GPU usage
nvidia-smi  # NVIDIA
radeontop   # AMD
```

**Solutions:**
```bash
# Solution 1: Force AVX2 (if AVX-512 throttling)
BLACKHOLE_SIMD_TIER=avx2 ./build/Release/Blackhole

# Solution 2: Reduce resolution
./build/Release/Blackhole --width 1280 --height 720

# Solution 3: Reduce raytracing quality
./build/Release/Blackhole --max-steps 1000

# Solution 4: Profile hotspots
perf record -g ./build/Release/Blackhole
perf report
```

---

**Issue:** High CPU usage (> 100%)

**Cause:** Rendering loop not vsync'd

**Solution:**
```bash
# Enable vsync
./build/Release/Blackhole --vsync

# Or in config:
# Edit imgui.ini, set VSync=true
```

---

### SIMD Issues

**Error:**
```
Illegal instruction (core dumped)
```

**Cause:** CPU doesn't support selected SIMD tier

**Solution:**
```bash
# Check CPU support
lscpu | grep -E "sse2|avx2|avx512"

# Force lower tier
BLACKHOLE_SIMD_TIER=avx2 ./build/Release/Blackhole

# Or build without AVX-512
cmake --preset release -DBLACKHOLE_DISABLE_AVX512=ON
```

---

**Issue:** AVX-512 slower than AVX2

**Cause:** CPU frequency throttling

**Diagnosis:**
```bash
# Monitor frequency during execution
watch -n 0.1 'cat /proc/cpuinfo | grep MHz | head -4'
```

**Solution:**
```bash
# Solution 1: Use AVX2 instead
BLACKHOLE_SIMD_TIER=avx2 ./build/Release/Blackhole

# Solution 2: Disable turbo boost
echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo
```

---

## Data Issues

### GRMHD Data Loading Failures

**Error:**
```
ERROR: Failed to load GRMHD dump: dump_000100.h5
```

**Causes:**
1. File not found
2. HDF5 library mismatch
3. Corrupt dump file

**Solutions:**
```bash
# Solution 1: Verify file exists
ls -lh dump_000100.h5

# Solution 2: Inspect dump structure
./build/Release/nubhlight_inspect dump_000100.h5

# Solution 3: Re-pack dump
./build/Release/nubhlight_pack dump_000100.h5 dump_000100.bin --metadata

# Solution 4: Check HDF5 version
h5dump --version
# Need HDF5 1.14+
```

---

### LUT Loading Failures

**Error:**
```
WARNING: LUT file not found, using runtime computation
```

**Cause:** Lookup tables not generated

**Solution:**
```bash
# Generate Novikov-Thorne LUT
python3 scripts/generate_nt_lut.py --output data/novikov_thorne_lut.bin

# Verify generated
ls -lh data/*.bin
```

---

## Test Failures

### CTest Failures

**Error:**
```
Test #12: physics_validation ......................***Failed
```

**Diagnosis:**
```bash
# Run test with verbose output
ctest --test-dir build/Release -R physics_validation --output-on-failure

# Run test binary directly
./build/Release/tests/physics_validation

# Check for floating-point tolerance issues
```

**Solutions:**
```bash
# Solution 1: Rebuild with debug symbols
cmake --preset debug
cmake --build --preset debug
ctest --test-dir build/Debug -R physics_validation

# Solution 2: Check for platform-specific issues
uname -a  # Report to maintainers if x86-64 Linux

# Solution 3: Disable failing test temporarily
ctest --test-dir build/Release -E physics_validation
```

---

### Benchmark Regressions

**Issue:** physics_bench shows >5% slowdown

**Diagnosis:**
```bash
# Compare against baseline
./build/Release/physics_bench --rays 4000 --steps 2000 --json current.json
python3 scripts/check_bench_regression.py bench_baseline.json current.json
```

**Causes:**
1. CPU frequency throttling
2. Background processes
3. Compiler optimization regression

**Solutions:**
```bash
# Solution 1: Pin CPU frequency
sudo cpupower frequency-set -g performance

# Solution 2: Kill background processes
pkill -STOP chrome firefox  # Pause browsers

# Solution 3: Rebuild with aggressive optimizations
cmake --preset riced
cmake --build --preset riced
```

---

## Platform-Specific Issues

### Arch Linux

**Issue:** Missing packages after system update

**Solution:**
```bash
# Reinstall all dependencies
sudo pacman -S --needed base-devel cmake conan mesa libglvnd hdf5 python

# Rebuild Conan packages
rm -rf ~/.conan2/p
./scripts/conan_install.sh Release build
```

---

### WSL2 (Windows Subsystem for Linux)

**Issue:** OpenGL not available

**Cause:** WSL2 doesn't support GPU acceleration by default

**Solution:**
```bash
# Use WSLg (Windows 11 22H2+)
# Ensure WSLg is enabled
wsl --update

# Or use software rendering (slow)
LIBGL_ALWAYS_SOFTWARE=1 ./build/Release/Blackhole
```

---

### macOS (Apple Silicon)

**Issue:** Build failures on M1/M2/M3

**Status:** Not officially supported yet (planned 2026 Q2)

**Workaround:**
```bash
# Use Rosetta 2 for x86-64 build
arch -x86_64 /bin/bash
cmake --preset release
cmake --build --preset release
```

---

## Getting Help

**Before reporting issues:**
1. Check this troubleshooting guide
2. Search existing issues on GitHub
3. Verify you're on latest commit: `git pull`

**When reporting issues, include:**
```bash
# System info
uname -a
lscpu
glxinfo | grep "OpenGL version"

# Build info
cmake --version
conan --version
g++ --version

# Error logs
cmake --preset release 2>&1 | tee cmake_error.log
./build/Release/Blackhole 2>&1 | tee runtime_error.log
```

**Contact:**
- GitHub Issues: <repo-url>/issues
- See AGENTS.md for contributor contacts

---

**Last Updated:** 2026-01-29
**Maintainer:** See AGENTS.md for contributors
