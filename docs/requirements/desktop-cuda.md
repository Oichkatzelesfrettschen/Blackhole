# Desktop CUDA Requirements

## Scope

Use this lane when you want the shared desktop UI with the CUDA backend enabled.
The dedicated executable for this product is `BlackholeCUDA`.

## Required

- NVIDIA GPU with supported driver
- CUDA toolkit visible to CMake and the runtime
- CMake 3.21+
- Conan 2.x
- C++23-capable compiler
- Python 3

## Useful local tooling

- `nvcc`
- `nvidia-smi`
- `ncu`
- `nsys`
- `cuobjdump`
- `nvdisasm`
- `compute-sanitizer`
- `doxygen` and `dot` if you also want the docs/evidence lane

## Recommended Arch packages

```bash
sudo pacman -S --needed \
  cuda \
  cudnn \
  cutensor \
  nccl \
  nsight-compute \
  nsight-systems \
  optix-dev-headers
```

## Configure/build

```bash
./scripts/conan_install.sh Release build/CUDA-Only/Release
cmake --preset cuda-only
cmake --build --preset cuda-only
ctest --preset cuda-only
```

## Optional Conan-backed extras

- `benchmark/1.9.4` via `enable_google_benchmark=True` for the `physics_microbench` target
- `mimalloc/2.2.4` via `enable_mimalloc=True` for allocator experiments on desktop/runtime binaries

The helper script understands the matching build presets:

```bash
./scripts/conan_install.sh --cmake-preset microbench
./scripts/conan_install.sh --cmake-preset release-mimalloc
```

`microbench` currently disables Highway at install/configure time to avoid the
current Clang + Highway source-build failure while keeping the benchmark lane
useful for xsimd/SLEEF measurements.

For manual Conan installs, keep the Conan and CMake toggles aligned:

```bash
./scripts/conan_install.sh Release build/CUDA-Only/Release \
  -o blackhole/*:enable_google_benchmark=True \
  -o blackhole/*:enable_mimalloc=True

cmake --preset cuda-only \
  -DENABLE_GOOGLE_BENCHMARK=ON \
  -DENABLE_MIMALLOC=ON
```

## Notes

- This preset keeps the shared desktop UI and disables the Blender bridge.
- CUDA-specific benchmark and SASS research inputs should be documented with
  provenance before they are treated as canonical optimization guidance.
