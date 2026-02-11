# Build System Documentation

## Overview

This project uses **Conan 2.x** for dependency management and **CMake** for building.

## Quick Start (Recommended)

```bash
# 1. Clean build
./scripts/build-quick.sh

# 2. Run
./build/Blackhole
```

## Manual Build (Standard Workflow)

```bash
# 1. Install dependencies with Conan
./scripts/conan_install.sh Release

# 2. Configure CMake
cd build
cmake .. -DCMAKE_BUILD_TYPE=Release \
         -DCMAKE_TOOLCHAIN_FILE=Release/generators/conan_toolchain.cmake

# 3. Build
make -j$(nproc) Blackhole

# 4. Run
./Blackhole
```

## Build Directory Structure

```
Blackhole/
├── build/                      # Build artifacts
│   ├── Blackhole              # Final executable
│   ├── Release/               # Conan output
│   │   └── generators/        # Conan-generated files
│   │       └── conan_toolchain.cmake
│   └── CMakeFiles/            # CMake artifacts
├── .conan/                    # Conan cache (repo-local)
└── scripts/                   # Build scripts
    ├── conan_install.sh       # Install Conan dependencies
    └── build-quick.sh         # One-command build (NEW)
```

## Common Issues

### Issue: "Could not find toolchain file"

**Cause:** Wrong path to `conan_toolchain.cmake`

**Fix:** Use absolute path or correct relative path:
```bash
cmake .. -DCMAKE_TOOLCHAIN_FILE=$PWD/Release/generators/conan_toolchain.cmake
```

### Issue: "Conan toolchain not found"

**Cause:** Skipped `conan_install.sh` step

**Fix:** Always run Conan install first:
```bash
./scripts/conan_install.sh Release
```

### Issue: Double-nested `build/Release/Release/`

**Cause:** Passing `build/Release` to `conan_install.sh` instead of just `build`

**Fix:** Use default or pass only `build`:
```bash
./scripts/conan_install.sh Release build  # Correct
```

## Build Types

- `Release` - Optimized, no debug symbols (default)
- `Debug` - Debug symbols, no optimization
- `RelWithDebInfo` - Optimized with debug symbols

## Rebuilding

```bash
# Full clean rebuild
rm -rf build .conan
./scripts/conan_install.sh Release --force-reinstall
cd build && cmake .. [options] && make -j$(nproc)

# Or use quick script:
./scripts/build-quick.sh --clean
```

## Dependencies

All managed via Conan (see `conanfile.py`):
- GLFW (graphics)
- GLM (math)
- ImGui (UI)
- Eigen3 (linear algebra)
- And 20+ more...

## Advanced: Wayland Support

To enable native Wayland rendering (better performance):

1. Modify `conanfile.py` to build GLFW with Wayland
2. Or use system GLFW: `paru -S glfw` (provides both X11 and Wayland)
3. Rebuild

**Note:** Current Conan GLFW uses X11/XWayland compatibility layer.
