# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Real-time black hole rendering simulation using OpenGL. Implements Schwarzschild geodesics for gravitational lensing, accretion disk rendering with procedural noise, and a multi-pass post-processing pipeline (bloom, tone mapping).

**Language:** C++17
**Graphics API:** OpenGL 3.0+ (GLSL 330 core)
**Resolution:** 1920x1080 (borderless window)
**License:** GPL-3.0

## Code Metrics

| Category | Count |
|----------|-------|
| Source Lines (SLOC) | 2,518 |
| Project Files | 41 |
| Functions | 15 (project sources) |
| Avg Cyclomatic Complexity | 3.5 |

### Lines by Component
- `src/` (C++): 591 SLOC in project files, 1,481 SLOC including third-party (imgui)
- `shader/` (GLSL): 385 SLOC
- Assets: 18MB (textures), 3MB (docs)

## Build Commands

### Prerequisites
- CMake 3.5+
- Conan package manager (1.x recommended, 2.x may have compatibility issues)
- OpenGL development libraries

### Ubuntu/Debian Dependencies
```bash
sudo apt-get install -y libgl1-mesa-dev libxrandr-dev libxinerama-dev libxcursor-dev libxi-dev
```

### Build
```bash
# Configure and build (Release)
cmake -DCMAKE_BUILD_TYPE=Release -S . -B build
cmake --build build

# Run the executable
./build/Blackhole

# Generate compile_commands.json for IDE/linter support
cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -S . -B build
```

### Static Analysis Commands
```bash
# cppcheck - C++ static analysis (exclude third-party imgui files)
cppcheck --enable=all --std=c++17 --suppress=missingIncludeSystem --quiet \
  src/main.cpp src/render.cpp src/shader.cpp src/texture.cpp src/GLDebugMessageCallback.cc

# cpplint - Google style checker
cpplint --filter=-whitespace,-legal,-build/include_subdir,-build/header_guard \
  src/main.cpp src/render.cpp src/shader.cpp src/texture.cpp

# flawfinder - Security analysis
flawfinder --minlevel=1 src/main.cpp src/render.cpp src/shader.cpp src/texture.cpp

# lizard - Cyclomatic complexity
lizard src/main.cpp src/render.cpp src/shader.cpp src/texture.cpp

# clang-format - Check formatting (dry run)
clang-format --dry-run -Werror src/main.cpp

# glslangValidator - GLSL shader validation
glslangValidator shader/*.frag shader/*.vert
```

## Architecture

### Rendering Pipeline

The application implements a multi-pass GPU rendering pipeline:

```
1. Black Hole Ray Tracing (blackhole_main.frag)
   └── Schwarzschild geodesic simulation, accretion disk, gravitational lensing

2. Bloom Effect (8-level pyramid)
   ├── Brightness extraction (bloom_brightness_pass.frag)
   ├── Pyramid downsampling (bloom_downsample.frag) x8
   ├── Pyramid upsampling (bloom_upsample.frag) x8
   └── Composite blend (bloom_composite.frag)

3. Tone Mapping (tonemapping.frag)
   └── ACES filmic + gamma correction

4. Display (passthrough.frag)
```

### Key Source Files

| File | Purpose | NLOC | CCN |
|------|---------|------|-----|
| `src/main.cpp` | Entry point, GLFW window, ImGui controls, pipeline orchestration | 228 | 15 (main) |
| `src/render.cpp` | Framebuffer/texture creation, render-to-texture with lazy caching | 135 | 7 (renderToTexture) |
| `src/shader.cpp` | Shader compilation and linking | 67 | 3 |
| `src/texture.cpp` | 2D texture and cubemap loading via stb_image | 68 | 7 (loadTexture2D) |
| `src/GLDebugMessageCallback.cc` | OpenGL debug output callback | 82 | - |

### Third-Party Files (vendored in src/)
- `imgui_impl_glfw.cpp/h` - ImGui GLFW bindings
- `imgui_impl_opengl3.cpp/h` - ImGui OpenGL3 bindings
- `imgui_impl_opengl3_loader.h` - OpenGL function loader
- `stb_image.cpp` - STB image wrapper

### Core Data Structures

**RenderToTextureInfo** (`render.h:35-44`): Central struct for configuring render passes
- `fragShader`: Fragment shader path
- `floatUniforms`: Dynamic float uniforms (camera, effects)
- `textureUniforms` / `cubemapUniforms`: Texture bindings
- `targetTexture`, `width`, `height`: Output target

**PostProcessPass** (`main.cpp:62-98`): Simple post-processing wrapper class

### Shader Architecture

**blackhole_main.frag** (287 SLOC) is the physics core:
- Simplex 3D noise (procedural accretion disk texture)
- Quaternion rotations for camera control
- Schwarzschild metric geodesic integration (300 iterations)
- Accretion disk with configurable density, height, lighting

Key uniforms exposed to ImGui:
- Camera: `cameraRoll`, `frontView`, `topView`, `mouseControl`, `fovScale`
- Black hole: `gravatationalLensing`, `renderBlackHole`
- Accretion disk: `adiskEnabled`, `adiskParticle`, `adiskHeight`, `adiskDensityV/H`, `adiskLit`, `adiskNoiseLOD`, `adiskNoiseScale`, `adiskSpeed`
- Post-processing: `bloomStrength`, `tonemappingEnabled`, `gamma`

### Design Patterns

1. **Lazy Initialization**: Shaders and framebuffers cached via static maps in `renderToTexture()`
2. **Macro-based ImGui**: `IMGUI_TOGGLE` and `IMGUI_SLIDER` macros for rapid UI prototyping
3. **Uniform Mapping**: Dynamic uniform passing via STL maps avoids hardcoded bindings

### Dependencies (via Conan)

| Package | Version | Purpose |
|---------|---------|---------|
| imgui | 1.86 | Immediate mode GUI |
| glfw | 3.3.6 | Window/input management |
| glew | 2.2.0 | OpenGL extension loading |
| glm | 0.9.9.8 | Math library (vectors, matrices, quaternions) |
| stb | cci.20210713 | Image loading |

## Static Analysis Results

### cppcheck Findings (project sources only)

| File | Issue | Severity | Line |
|------|-------|----------|------|
| main.cpp | `firstMouse` assigned bool to float | style | 56 |
| main.cpp | `PostProcessPass` constructor not explicit | style | 67 |
| main.cpp | `texBlackhole` shadows outer variable | style | 216 |
| main.cpp | Unused: `lastX`, `lastY`, `yaw`, `pitch`, `firstMouse` | style | 52-56 |
| main.cpp | Unused: `show_demo_window`, `show_another_window` | style | 177-178 |
| main.cpp | `io` should be const reference | style | 165 |
| shader.cpp | Unused variable: `VertexShaderCode` | style | 12 |
| GLDebugMessageCallback.cc | String literal compared with `!=` instead of `strcmp()` | warning | 146 |

### cpplint Findings

| Category | Count |
|----------|-------|
| build/include_order | 8 |
| readability/casting (C-style casts) | 7 |
| runtime/explicit | 1 |

### Cyclomatic Complexity (lizard)

| Function | CCN | NLOC | Risk |
|----------|-----|------|------|
| `main()` | 15 | 170 | At threshold |
| `renderToTexture()` | 7 | 52 | OK |
| `loadTexture2D()` | 7 | 36 | OK |
| All others | ≤3 | - | OK |

### Security Analysis (flawfinder)

**No security vulnerabilities found** in project sources.

### GLSL Shader Validation (glslangValidator)

**All 8 shaders pass validation** without errors or warnings.

## Recommended Tooling Configuration

This project lacks `.clang-format` and `.clang-tidy` configuration. Recommended additions:

**.clang-format**
```yaml
BasedOnStyle: LLVM
IndentWidth: 2
ColumnLimit: 100
BreakBeforeBraces: Attach
```

**.clang-tidy**
```yaml
Checks: >
  clang-analyzer-*,
  bugprone-*,
  modernize-*,
  performance-*,
  -modernize-use-trailing-return-type
WarningsAsErrors: ''
```

## File Structure

```
Blackhole/
├── src/                          # C++ source (156KB)
│   ├── main.cpp                  # Entry point, render loop
│   ├── render.cpp/h              # Framebuffer utilities
│   ├── shader.cpp/h              # Shader compilation
│   ├── texture.cpp/h             # Texture loading
│   ├── GLDebugMessageCallback.*  # Debug callbacks
│   ├── stb_image.cpp             # STB wrapper
│   └── imgui_impl_*              # Third-party ImGui bindings
├── shader/                       # GLSL shaders (44KB)
│   ├── simple.vert               # Fullscreen quad vertex
│   ├── blackhole_main.frag       # Core ray tracing (287 LOC)
│   ├── bloom_*.frag              # Bloom pipeline (4 shaders)
│   ├── tonemapping.frag          # ACES tone mapping
│   └── passthrough.frag          # Final display
├── assets/                       # Textures (18MB)
│   ├── color_map.png             # Accretion disk gradient
│   ├── skybox_nebula_dark/       # 6-face cubemap
│   ├── skybox_test/              # Test cubemap
│   └── uv_checker.png            # UV test pattern
├── docs/                         # Documentation (3MB)
│   └── blackhole-screenrecord.gif
├── .github/workflows/ci.yml      # GitHub Actions CI
├── CMakeLists.txt                # Build configuration
├── README.md                     # Project documentation
└── LICENSE                       # GPL-3.0
```

## CI/CD

GitHub Actions workflow (`.github/workflows/ci.yml`):
- Triggers on push and pull requests
- Ubuntu latest runner
- Installs Conan via pip, OpenGL dev libraries
- CMake Release build

## Controls

- **Mouse movement**: Camera orbit control (when `mouseControl` enabled)
- **ImGui panel**: Real-time parameter adjustment for all effects
- **Window close**: Exit application
