# Blackhole Requirements

## Build prerequisites
- CMake 3.21+
- Conan 2.x
- C++23-capable compiler (GCC 13+/Clang 16+)
- OpenGL 4.6-capable GPU + driver
- Python 3 (for LUT generation scripts)
- Git

## Linux system packages (Ubuntu/Debian)
```bash
sudo apt-get install -y \
  libgl1-mesa-dev \
  libx11-dev \
  libxrandr-dev \
  libxinerama-dev \
  libxcursor-dev \
  libxi-dev \
  libxext-dev \
  libxrender-dev \
  libxfixes-dev
```

## Optional system packages (shader validation)
```bash
sudo apt-get install -y \
  glslang-tools \
  shaderc \
  spirv-tools
```

## Optional system packages (GRMHD ingestion tooling)
```bash
sudo apt-get install -y \
  libhdf5-dev \
  hdf5-tools
```

## Linux system packages (Arch/CachyOS)
```bash
sudo pacman -S --needed \
  mesa \
  libx11 \
  libxrandr \
  libxinerama \
  libxcursor \
  libxi \
  libxext \
  libxrender \
  libxfixes
```

## Optional system packages (shader validation) (Arch/CachyOS)
```bash
sudo pacman -S --needed \
  glslang \
  shaderc \
  spirv-tools
```

## Optional system packages (GRMHD ingestion tooling) (Arch/CachyOS)
```bash
sudo pacman -S --needed \
  hdf5
```

## Conan packages
- glfw/3.4
- glbinding/3.5.0
- glm/cci.20230113
- xsimd/13.2.0
- entt/3.15.0
- pcg-cpp/cci.20220409
- taskflow/3.10.0
- imgui/1.92.5-docking
- imguizmo/cci.20231114
- rmlui/4.4 (optional; enable with `-DENABLE_RMLUI=ON`)
- flatbuffers/25.9.23
- hdf5/1.14.6
- highfive/3.1.1
- spdlog/1.16.0
- fmt/12.1.0
- tracy/0.12.2
- cli11/2.6.0
- z3/4.14.1 (optional; enable with `-DENABLE_Z3=ON`)
- gmp/6.3.0 (optional; precision ground-truth via Boost.Multiprecision MPFR backend)
- mpfr/4.2.2 (optional; precision ground-truth via Boost.Multiprecision MPFR backend)
- boost/1.90.0
- stb/cci.20240531

Note: `conanfile.py` sets shared builds for hdf5/spdlog/fmt and disables
`boost` cobalt to keep the dependency graph stable.

## Vendored sources
- ImPlot (upstream master, 0.18 WIP): `external/implot` (fetch with
  `scripts/fetch_implot.sh`). Conan's `implot/0.16` does not yet support
  ImGui 1.92+ (FontBaked/ImTextureRef API changes).

## Conan update candidates (center2, 2025-12-30)
Latest recipes on conancenter (current pins in parentheses):
- imgui: 1.92.5-docking (current 1.92.5-docking)
- implot: 0.16 (Conan recipe; project vendors master until 1.92+ support lands)
- glfw: 3.4 (current 3.4)
- glbinding: 3.5.0 (current 3.5.0)
- glm: cci.20230113 (current cci.20230113; 1.0.1 also available)
- xsimd: 13.2.0 (current 13.2.0)
- entt: 3.15.0 (current 3.15.0)
- taskflow: 3.10.0 (current 3.10.0)
- highfive: 3.1.1 (current 3.1.1)
- flatbuffers: 25.9.23 (current 25.9.23)
- spdlog: 1.16.0 (current 1.16.0)
- fmt: 12.1.0 (current 12.1.0)
- tracy: 0.12.2 (current 0.12.2; cci.20220130 also available)
- cli11: 2.6.0 (current 2.6.0)
- boost: 1.90.0 (current 1.90.0)
- hdf5: 1.14.6 (current 1.14.6)
- z3: 4.14.1 (current 4.14.1)
- gmp: 6.3.0 (current 6.3.0)
- mpfr: 4.2.2 (current 4.2.2)
- eigen: 5.0.1 (optional/deferred; current 3.4.0)
- pcg-cpp: cci.20220409 (current cci.20220409)
- stb: cci.20240531 (current cci.20240531)

Optional additions for the cleanroom pipeline (on conancenter):
- benchmark/1.9.4 (microbench harness)
- mimalloc/2.2.4 (allocator experiments)
- glad/2.0.8 (fallback OpenGL loader)
- bgfx/1.129.8930-495 or cci.20230216 (renderer reference; optional)

Missing on conancenter (needs custom Conan recipe or vendoring):
- amrex (AMR grid solver)
- autodiff (automatic differentiation)
- enzyme (LLVM plugin autodiff)
- halide (scheduling DSL)
- tbb (task scheduler)
- magnum (graphics toolkit)
- imnodes (node editor for ImGui)
- imgui-color-text-edit (code editor widget)
- imgui-markdown (Markdown renderer)

## Upgrade guidance (current)
- Core deps are pinned to the latest center2 recipes (see list above).
- Eigen is deferred pending a coordinated API refactor.
- GL loader path: glbinding/3.5.0; glad remains fallback only.

## Build (Release)
```bash
conan profile detect --force
conan remote update conancenter --url="https://center2.conan.io"
conan install . --output-folder=build --build=missing -s build_type=Release -s compiler.cppstd=23
./scripts/fetch_implot.sh

# If system CMake >=4.x breaks glbinding's configure step, rerun with CMake 3.x:
# conan install . --output-folder=build --build=missing -s build_type=Release -s compiler.cppstd=23 \
#   -c tools.cmake:cmake_program=/path/to/cmake-3.31

cmake --preset release
cmake --preset release -DENABLE_Z3=ON  # enable z3_sanity tool
cmake --build --preset release

# Or explicit configure/build
cmake -S . -B build/build/Release -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_TOOLCHAIN_FILE=build/build/Release/generators/conan_toolchain.cmake
cmake --build build/build/Release
```

## Validation assets (offline)
```bash
python3 scripts/generate_validation_tables.py
```
- Outputs `assets/validation/metrics.json`, `assets/validation/redshift_curve.csv`,
  and `assets/validation/spin_radii_curve.csv`.
- Uses `compact-common` if available; otherwise falls back to internal CGS formulas.

## LUT generation (offline)
```bash
python3 scripts/generate_luts.py --size 256 --spin 0.0 --mass-solar 4.0e6 --mdot 0.1 --spin-points 64
```
- Outputs emissivity/redshift LUTs and optional `spin_radii_lut.csv`.
- Embeds `isco_source` and `compact_common_version` in `assets/luts/lut_meta.json` when available.

## Radiative transfer LUTs (stub)
```bash
python3 scripts/generate_tardis_lut_stub.py --output-dir assets/luts
```
- Emits `rt_spectrum_lut.csv` + `rt_spectrum_meta.json` as placeholders.

## Optional tools
- glslangValidator (validate-shaders target)
- glslc (SPIR-V compile target)
- spirv-val (SPIR-V validation target if enabled)
- clang-format
- clang-tidy
- cppcheck
- compact-common (Python module for higher-fidelity ISCO in LUT generation)
- grb-common (Python module for cosmology/extinction LUT generation)
- tardis (Python >=3.13, for radiative transfer LUT calibration)
- JetFit/boxfit/PyGRB (GRB LUT references; offline only)
- numpy/scipy/astropy/h5py/extinction (Python deps for offline LUT + validation scripts)

## Runtime notes
- macOS is not supported (no OpenGL 4.6).
- The app writes settings.json in the launch directory.
- Swap interval (vsync) and render scale are user settings (see Display panel).

## Unit system
- C++ physics uses CGS by default (cm, g, s) in `src/physics/constants.h`.
- Geometric units (G=c=1) are used only where explicitly noted.
- LUTs in `src/physics/lut.h` are normalized in r/r_s and sampled in shaders.
