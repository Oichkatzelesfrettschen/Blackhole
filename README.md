# Real-time Black Hole Rendering in OpenGL

![Screenshot](docs/blackhole-screenrecord.gif)

## Highlights
- Schwarzschild/Kerr geodesic tracing (fragment + compute paths).
- LUT-driven emissivity/redshift and validation assets in `assets/`.
- C++23 + OpenGL 4.6 with tunable post-processing and controls.

## Prerequisite

- [cmake](https://cmake.org/)
- [conan](https://conan.io/) package manager (repo-local home; see `scripts/conan_env.sh`)
- C++23-capable compiler
- OpenGL 4.6-capable GPU/driver

## Build the code

```bash
# Install dependencies with repo-local Conan (output folder must match your CMake build dir).

Preferred invocation (Conan 2.x):

```bash
# repo-local cache
./scripts/conan_install.sh Release build
# then configure
cmake --preset profile
```

If you must use raw conan commands, prefer the 2.x syntax:

```bash
conan install . --output-folder=build --build=missing -s build_type=Release -s compiler.cppstd=23
```

./scripts/conan_install.sh Release build
./scripts/fetch_implot.sh

# Configure the project and generate a native build system.
cmake --preset release
cmake --build --preset release

# Optional RmlUi overlay (MangoHUD port groundwork).
cmake --preset release -DENABLE_RMLUI=ON

# Optional Tracy profiling.
cmake --preset release -DENABLE_TRACY=ON

# Or explicit configure/build.
cmake -DCMAKE_BUILD_TYPE=Release -S . -B build/Release \
  -DCMAKE_TOOLCHAIN_FILE=build/Release/generators/conan_toolchain.cmake

# Compile / build the project.
cmake --build build/Release
```

## OpenGL 4.6 scope

See `docs/opengl-4-6-scope.md` for validation and platform notes.

## Status and validation

- Roadmap + issue tracking: `STATUS.md` and `TODO_FIXES.md`.
- GLSL validation (warnings treated as errors only when `ENABLE_WERROR=ON`):
  `cmake --build --preset release --target validate-shaders`
- Physics validation tables:
  `python3 scripts/generate_validation_tables.py`

## Acknowledgements

**Papers**

- Gravitational Lensing by Spinning Black Holes in Astrophysics, and in the Movie Interstellar
- Trajectory Around A Spherically Symmetric Non-Rotating Black Hole - Sumanta
- Approximating Light Rays In The Schwarzschild Field - O. Semerak
- Implementing a Rasterization Framework for a Black Hole Spacetime - Yoshiyuki Yamashita

<!-- https://arxiv.org/pdf/1502.03808.pdf -->
<!-- https://arxiv.org/pdf/1109.0676.pdf -->
<!-- https://arxiv.org/pdf/1412.5650.pdf -->
<!-- https://pdfs.semanticscholar.org/56ff/9c575c29ae8ed6042e23075ff0ca00031ccc.pdfhttps://pdfs.semanticscholar.org/56ff/9c575c29ae8ed6042e23075ff0ca00031ccc.pdf -->

**Articles**

- Physics of oseiskar.github.io/black-hole - https://oseiskar.github.io/black-hole/docs/physics.html
- Schwarzschild geodesics - https://en.wikipedia.org/wiki/Schwarzschild_geodesics
- Photons and black holes - https://flannelhead.github.io/posts/2016-03-06-photons-and-black-holes.html
- A real-time simulation of the visual appearance of a Schwarzschild Black Hole - http://spiro.fisica.unipd.it/~antonell/schwarzschild/
- Ray Tracing a Black Hole in C# by Mikolaj Barwicki - https://www.codeproject.com/Articles/994466/Ray-Tracing-a-Black-Hole-in-Csharp
- Ray Marching and Signed Distance Functions - http://jamie-wong.com/2016/07/15/ray-marching-signed-distance-functions/
- Einstein's Rings and the Fabric of Space - https://www.youtube.com/watch?v=Rl8H4XEs0hw)
- Opus 2, GLSL ray tracing tutorial - http://fhtr.blogspot.com/2013/12/opus-2-glsl-ray-tracing-tutorial.html
- Ray Tracing in One Weekend - https://raytracing.github.io/
- On ray casting, ray tracing, ray marching and the like - http://hugi.scene.org/online/hugi37/- hugi%2037%20-%20coding%20adok%20on%20ray%20casting,%20ray%20tracing,%20ray%20marching%20and%20the%20like.htm

**Other GitHub Projects**

- https://github.com/sirxemic/Interstellar
- https://github.com/ssloy/tinyraytracer
- https://github.com/RayTracing/raytracing.github.io
- https://awesomeopensource.com/projects/raytracing
- Ray-traced simulation of a black hole - https://github.com/oseiskar/black-hole
- Raytracing a blackhole - https://rantonels.github.io/starless/
- https://github.com/rantonels/schwarzschild
