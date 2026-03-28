# Desktop GLSL Requirements

## Scope

Use this lane when you want the shared desktop UI with GLSL/OpenGL rendering and
no CUDA dependency.

## Required

- OpenGL 4.6-capable GPU and driver
- CMake 3.21+
- Conan 2.x
- C++23-capable compiler
- Python 3
- System shader validation tools for `validate-shaders`:
  - `glslangValidator`
  - optional: `glslc`, `spirv-tools`, `spirv-cross`

## Recommended Arch packages

```bash
sudo pacman -S --needed \
  mesa \
  glslang \
  xorg-server-xvfb \
  tmux \
  shaderc \
  spirv-tools \
  spirv-cross
```

## Configure/build

```bash
./scripts/conan_install.sh Release build/GLSL-Only/Release
cmake --preset glsl-only
cmake --build --preset glsl-only
ctest --preset glsl-only
cmake --build --preset glsl-only --target validate-shaders
```

## Headless capture

Use the repo-owned headless runner when you want many GLSL shots without a
desktop window stealing focus. The default backend uses a hidden GLFW window on
your real display, which is the most reliable GPU path on this machine.

Single quiet capture:

```bash
python3 scripts/run_glsl_headless.py \
  --backend hidden \
  --record-dir .cache/headless_one \
  --record-frames 1 \
  --record-profile showcase-orbit \
  --record-composition wide-right \
  --width 2560 \
  --height 1004
```

Detached tmux-backed run:

```bash
python3 scripts/run_glsl_headless.py \
  --detach-tmux \
  --backend hidden \
  --tmux-session blackhole-glsl-headless \
  --record-dir .cache/headless_batch \
  --record-frames 120 \
  --record-profile showcase-orbit \
  --record-composition wide-right
```

Notes:

- The runner always writes renderer output to `headless_run.log`.
- `--backend hidden` keeps the GLFW window invisible and unfocused.
- `--backend xvfb` is available as an experimental fallback, but on this
  machine the hidden-window path is more reliable than GLX under `Xvfb`.
- It sets `BLACKHOLE_RECORD_WIDTH` and `BLACKHOLE_RECORD_HEIGHT` from the
  requested headless resolution.
- `showcase-orbit` now supports named framing presets:
  - `centered`
  - `left-third`
  - `right-third`
  - `wide-left`
  - `wide-right`
- You can also override the framing directly with:
  - `--record-frame-x`
  - `--record-frame-y`
  These are measured in half-frame units in camera space. Positive `x` pushes
  the black hole left in frame. Positive `y` pushes it down in frame.
- No `sudo`, `yay`, or askpass helper is needed if the required tools are
  already installed.
