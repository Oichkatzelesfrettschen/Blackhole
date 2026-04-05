# Building Blackhole

This document covers the complete build process including bootstrapping dependencies.

## System Requirements

### Required Tools

| Tool | Minimum Version | Purpose |
|------|-----------------|---------|
| CMake | 3.26+ | Build system generator |
| Conan | **2.0+** | Package manager (see Bootstrap section) |
| C++ Compiler | C++23 support | GCC 13+, Clang 17+, or MSVC 19.36+ |
| Python | 3.10+ | Required for Conan and build scripts |
| OpenGL | 4.6 | GPU driver with compute shader support |

### Platform-Specific Dependencies

**Ubuntu/Debian:**
```bash
sudo apt-get install -y \
    cmake \
    python3 python3-pip pipx \
    libgl1-mesa-dev libxrandr-dev libxinerama-dev \
    libxcursor-dev libxi-dev libxkbcommon-dev \
    git-lfs
```

**Fedora/RHEL:**
```bash
sudo dnf install -y \
    cmake \
    python3 python3-pip pipx \
    mesa-libGL-devel libXrandr-devel libXinerama-devel \
    libXcursor-devel libXi-devel libxkbcommon-devel \
    git-lfs
```

**Arch Linux:**
```bash
sudo pacman -S cmake python python-pip conan mesa libxrandr libxinerama libxcursor libxi libxkbcommon git-lfs
```

## Bootstrap: Conan 2.x

This project **requires Conan 2.x**. The build scripts use Conan 2.x-specific commands (`conan profile detect`, updated `conan install` syntax).

### Check Your Conan Version

```bash
conan --version
```

If this shows version 1.x (e.g., `Conan version 1.64.0`), you must upgrade.

### Installing/Upgrading Conan

**Recommended: Using pipx (isolated environment)**
```bash
# Install pipx if not present
python3 -m pip install --user pipx
python3 -m pipx ensurepath

# Install Conan 2.x (or upgrade from 1.x)
pipx install conan
# OR if already installed:
pipx upgrade conan

# Verify
conan --version  # Should show 2.x
```

**Alternative: Using pip (system/user install)**
```bash
# May require --break-system-packages on newer distros
pip install --user conan>=2.0

# Or in a virtual environment
python3 -m venv ~/.venv/conan
source ~/.venv/conan/bin/activate
pip install conan>=2.0
```

**Why Conan 2.x is Required:**
- `conan profile detect` command (used in `scripts/conan_init.sh`)
- Updated `conan install` and `conan export` syntax
- CMake toolchain generation changes
- The scripts explicitly detect and adapt to Conan version, but 2.x is the primary target

## Build Process

### Quick Start

```bash
# 1. Clone with LFS support
git lfs install
git clone https://github.com/Oichkatzelesfrettschen/Blackhole.git
cd Blackhole

# 2. Install dependencies (uses repo-local Conan cache)
./scripts/conan_install.sh Release build

# 3. Configure and build
cmake --preset release
cmake --build --preset release

# 4. Generate the measured repo inventory for this build tree
cmake --build --preset release --target repo-truth

# 5. Run
./build/Release/Blackhole
```

### One-Command Build

```bash
./scripts/build-quick.sh
```

Or with clean rebuild:

```bash
./scripts/build-quick.sh --clean
```

### One-Line Build (No Scripts)

```bash
conan install . --output-folder=build/Release --build=missing -s compiler.cppstd=23 && cmake --preset release && cmake --build --preset release
```

### Step-by-Step

#### 1. Initialize Conan (repo-local)

The project uses a repo-local Conan home (`$REPO/.conan/`) to isolate from system Conan state:

```bash
# This creates .conan/ folder with profiles and cache
./scripts/conan_init.sh
```

#### 2. Export Local Recipes

Custom Conan recipes for specific versions:

```bash
./scripts/conan_export_local_recipes.sh
```

#### 3. Install Dependencies

```bash
# Release build (recommended)
./scripts/conan_install.sh Release build

# Debug build
./scripts/conan_install.sh Debug build-debug
```

#### 4. Configure CMake

```bash
# Using presets (recommended)
cmake --preset release

# Or manually
cmake -DCMAKE_BUILD_TYPE=Release -S . -B build/Release \
    -DCMAKE_TOOLCHAIN_FILE=build/Release/generators/conan_toolchain.cmake
```

#### 5. Build

```bash
cmake --build --preset release
# Or: cmake --build build/Release
```

## Build Directory Structure

```
Blackhole/
  .conan/              # Conan package cache (persists across clean builds)
    p/                 # Compiled packages (reused)
    profiles/          # Build profiles
  build/               # CMake build directory (can be deleted for clean builds)
    Release/
      generators/      # Conan CMake toolchain files
      Blackhole        # Built executable
```

**Key point:** Deleting `build/` does NOT delete `.conan/`. The compiled packages in `.conan/p/`
are reused across builds. Only the CMake toolchain files need regeneration.

### Clean Build Process

```bash
# Clean build (regenerate toolchain, reuse cached packages)
rm -rf build
./scripts/conan_install.sh Release build
cmake --preset release
cmake --build --preset release

# Full rebuild (recompile ALL dependencies - rarely needed)
./scripts/conan_install.sh Release build --force-reinstall
cmake --preset release
cmake --build --preset release

# Nuclear option (delete everything)
rm -rf build .conan/
./scripts/conan_install.sh Release build
```

## Build Configurations

| Configuration | Command |
|--------------|---------|
| **Release** (Maximum Performance) | `cmake --preset release && cmake --build --preset release` |
| **Debug** | `cmake --preset debug && cmake --build --preset debug` |
| **Profiling** (perf/valgrind) | `cmake --preset profiling && cmake --build --preset profiling` |
| **PGO** (Profile-Guided) | See PGO section below |

## Product Presets

The repo now exposes product-oriented presets so the desktop and bridge tracks
can be built independently without relying on undocumented target assumptions.

| Preset | Purpose | Conan install directory |
|--------|---------|-------------------------|
| `glsl-only` | Shared desktop UI with GLSL path only | `build/GLSL-Only/Release` |
| `cuda-only` | Shared desktop UI with CUDA enabled | `build/CUDA-Only/Release` |
| `blender-bridge` | Blender bridge without desktop app or benchmarks | `build/BlenderBridge/Release` |
| `full-dev` | Shared desktop UI, CUDA, Blender bridge, tools, tests | `build/FullDev/RelWithDebInfo` |

Example:

```bash
./scripts/conan_install.sh Release build/CUDA-Only/Release
cmake --preset cuda-only
cmake --build --preset cuda-only
ctest --preset cuda-only
```

## Build Options

| CMake Option | Default | Description |
|--------------|---------|-------------|
| `ENABLE_TRACY` | OFF | Enable Tracy profiler integration |
| `ENABLE_RMLUI` | OFF | Enable RmlUi HUD overlay |
| `ENABLE_WERROR` | ON | Treat warnings as errors |
| `ENABLE_CUDA` | OFF | Enable CUDA compute backend (SM80+) |
| `ENABLE_EIGEN` | OFF | Enable Eigen for sparse ODE solvers |
| `ENABLE_DESKTOP_APP` | ON | Build the shared desktop application |
| `ENABLE_BENCHMARKS` | ON | Build benchmark executables |
| `ENABLE_TOOLS` | ON | Build CLI/helper tools |

Example:
```bash
cmake --preset release -DENABLE_TRACY=ON -DENABLE_RMLUI=ON
```

## Measured repo truth

Use the generated repo-truth report whenever you need the authoritative local
inventory for the configured build tree:

```bash
cmake --build --preset release --target repo-truth
```

This writes:

- `build/<preset>/reports/repo_truth.json`
- `build/<preset>/reports/repo_truth.md`

The report captures the configured build options, `ctest -N` inventory, visible
configure presets, key local tools, and selected system packages.

It also folds in generated Blender/Octane evidence when those targets have
been run:

- `build/<preset>/reports/blender_addon_manifest.json`
- `build/<preset>/reports/blender_bridge_abi.json`
- `build/<preset>/reports/blender_addon_package.json`
- `build/<preset>/reports/blender_addon_stage.json`
- `build/<preset>/reports/blender_smoke.json`
- `build/<preset>/reports/blender_smoke_verified.json`
- `build/<preset>/reports/blender_interactive_benchmark.json`
- `build/<preset>/reports/blender_interactive_benchmark_verified.json`
- `build/<preset>/reports/octane_readiness.json`
- `build/<preset>/reports/octane_smoke.json`
- `build/<preset>/reports/octane_smoke_verified.json`

## Blender and Octane lanes

Use two different presets depending on what you are trying to validate:

- `blender-bridge`: fastest way to build `libblackhole_bridge.so` and the
  packaged addon artifact.
- `full-dev`: simplest preset that guarantees both `ENABLE_BLENDER_BRIDGE=ON`
  and `BUILD_TESTING=ON`, so the `ctest`-registered smoke tests exist.

Bridge packaging only:

```bash
./scripts/conan_install.sh Release build/BlenderBridge/Release
cmake --preset blender-bridge
cmake --build --preset blender-bridge --target blackhole_bridge package-blender-addon verify-blender-addon-package verify-blender-bridge-abi stage-blender-addon
```

Smoke-tested Blender or Octane lane:

```bash
./scripts/conan_install.sh RelWithDebInfo build/FullDev/RelWithDebInfo
cmake --preset full-dev
cmake --build --preset full-dev --target blender-addon-smoke verify-blender-smoke-report
ctest --preset full-dev -R "blender_bridge_abi|blender_addon_package|blender_addon_stage|blender_addon_smoke|blender_smoke_report"
```

Blender interactive benchmark lane:

```bash
cmake --build --preset full-dev --target benchmark-blender-interactive verify-blender-interactive-benchmark
ctest --preset full-dev -R "blender_interactive_benchmark|blender_interactive_benchmark_report" --output-on-failure
```

That benchmark lane now uses the repo's isolated BlenderMCP bootstrap first,
so the timed run starts from a saved studio scene generated through MCP rather
than from an ad hoc factory-startup scene.

For Octane:

```bash
cmake --build --preset full-dev --target probe-octane-readiness octane-addon-smoke verify-octane-smoke-report benchmark-octane-interactive verify-octane-interactive-benchmark
ctest --preset full-dev -R "octane_readiness|octane_addon_smoke|octane_smoke_report|octane_interactive_benchmark|octane_interactive_benchmark_report" --output-on-failure
```

For the Octane tier sweep:

```bash
cmake --build --preset full-dev --target verify-octane-quality-sweep
ctest --preset full-dev -R "octane_quality_sweep_report" --output-on-failure
```

For the harsher multi-light Octane scene:

```bash
cmake --build --preset full-dev --target verify-octane-harsh-scene
ctest --preset full-dev -R "octane_harsh_scene_report" --output-on-failure
```

The Octane readiness probe exists because "OctaneBlender launches" and
"headless Octane final rendering is automation-ready" are not the same state.
If Octane still needs interactive sign-in, activation, cuDNN setup, or a live
`OctaneServer`, the probe records that explicitly and the benchmark lane skips
the final render with the same recorded reason.

The smoke runner installs the packaged addon into an isolated temporary Blender
user-scripts directory automatically. Interactive Blender sessions do not get
that isolation for free; use the packaged addon zip from
`build/<preset>/dist/blackhole_physics-addon.zip` or set
`BLACKHOLE_BRIDGE_LIB=/absolute/path/to/libblackhole_bridge.so`.

## Profile-Guided Optimization (PGO)

**Phase 1: Generate profiles**

```bash
conan install . --output-folder=build/PGO-Gen --build=missing -s compiler.cppstd=23
cmake --preset pgo-gen && cmake --build --preset pgo-gen
cd build/PGO-Gen && ./Blackhole  # Run typical workload
# For Clang: llvm-profdata merge -output=pgo-profiles/default.profdata pgo-profiles/default.profraw
```

**Phase 2: Optimized build**

```bash
conan install . --output-folder=build/PGO-Use --build=missing -s compiler.cppstd=23
cmake --preset pgo-use && cmake --build --preset pgo-use
./build/PGO-Use/Blackhole  # 10-20% faster than -O3
```

## Optimizations Enabled by Default

- **-O3**: Maximum compiler optimization
- **-march=native**: CPU-specific SIMD instructions
- **Fat LTO**: Link Time Optimization (full cross-module)
- **fast-math**: Aggressive floating-point optimizations

## Wayland Support

To enable native Wayland rendering (better performance):

1. Modify `conanfile.py` to build GLFW with Wayland
2. Or use system GLFW: `paru -S glfw` (provides both X11 and Wayland)
3. Rebuild

**Note:** Current Conan GLFW uses X11/XWayland compatibility layer.

## Troubleshooting

### "Conan toolchain not found"

Run the dependency installation script first:
```bash
./scripts/conan_install.sh Release build
```

### "Could not find toolchain file"

Wrong path to `conan_toolchain.cmake`. Use absolute path or correct relative path:
```bash
cmake .. -DCMAKE_TOOLCHAIN_FILE=$PWD/Release/generators/conan_toolchain.cmake
```

### Double-nested `build/Release/Release/`

Pass only `build` (not `build/Release`) to `conan_install.sh`:
```bash
./scripts/conan_install.sh Release build  # Correct
```

### Dependency Corruption or Version Mismatch

If packages seem corrupted or you need to rebuild all dependencies:
```bash
# Force rebuild all packages
./scripts/conan_install.sh Release build --force-reinstall

# Or completely reset Conan cache (nuclear option)
rm -rf .conan build
./scripts/conan_install.sh Release build
```

### Conan 1.x vs 2.x Errors

If you see errors like:
- `error: argument subcommand: invalid choice: 'detect'`
- `conan profile detect: command not found`

Upgrade to Conan 2.x:
```bash
pipx upgrade conan
# or
pip install --user --upgrade conan>=2.0
```

### Git LFS Errors

If you see `git-lfs filter-process: not found`:
```bash
sudo apt-get install git-lfs  # or equivalent
git lfs install
git lfs pull
```

### Missing OpenGL Headers

Install OpenGL development packages:
```bash
# Ubuntu/Debian
sudo apt-get install libgl1-mesa-dev

# Fedora
sudo dnf install mesa-libGL-devel
```

## API Documentation (Doxygen)

Generate HTML API docs from source comments:

```bash
# Install tools (Arch)
sudo pacman -S doxygen graphviz

# Or on Ubuntu/Debian
# sudo apt install doxygen graphviz

# Configure with Doxygen enabled
cmake --preset release -DENABLE_DOXYGEN=ON

# Build documentation
cmake --build --preset release --target doxygen
```

Output: `build/Release/docs/api/html/index.html`

The Doxygen target is independent of the main build -- it only processes source
comments and generates HTML. Graphviz (`dot`) is optional but enables call graphs.

## IDE Support

**VS Code**: Install CMake Tools, select preset, build (F7).
**CLion**: Auto-detects CMakePresets.json, select from dropdown, build (Ctrl+F9).

## Dependencies

All managed via Conan (see `conanfile.py`):
- GLFW (graphics), GLM (math), ImGui (UI), Eigen3 (linear algebra)
- See `conanfile.py` for the full list (20+ packages)

## CI/CD

The GitHub Actions workflow (`.github/workflows/ci.yml`) automates:
- Conan 2.x installation via pip
- Dependency resolution and caching
- Release build verification

See the workflow file for the canonical CI build process.

## Verification

```bash
./scripts/verify-conan2-migration.sh
```

Expected: All checks pass, C++23 verified, latest packages confirmed.

## Technology Stack

- **C++23** (GCC 13+, Clang 17+, MSVC 2022+)
- **Conan 2.x** (native, no deprecated features)
- **OpenGL** (glfw 3.4, glbinding 3.5.0, glm 1.0.1, imgui 1.92.5-docking)
- **SIMD** (xsimd 14.0.0, highway 1.3.0, sleef 3.9.0)
