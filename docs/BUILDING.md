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

# 4. Run
./build/Release/Blackhole
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

## Build Options

| CMake Option | Default | Description |
|--------------|---------|-------------|
| `ENABLE_TRACY` | OFF | Enable Tracy profiler integration |
| `ENABLE_RMLUI` | OFF | Enable RmlUi HUD overlay |
| `ENABLE_WERROR` | OFF | Treat warnings as errors |

Example:
```bash
cmake --preset release -DENABLE_TRACY=ON -DENABLE_RMLUI=ON
```

## Troubleshooting

### "Conan toolchain not found"

Run the dependency installation script first:
```bash
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

## CI/CD

The GitHub Actions workflow (`.github/workflows/ci.yml`) automates:
- Conan 2.x installation via pip
- Dependency resolution and caching
- Release build verification

See the workflow file for the canonical CI build process.
