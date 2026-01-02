# Phase 9: C++23 GLSL Shader Compilation & Extended Physics

**Date:** 2026-01-02
**Phase:** 9 - GPU Acceleration via GLSL 4.60 + Extended Metrics
**Status:** PLANNING - Ready for Implementation
**Technology Stack:** C++23 (verified physics) → GLSL 4.60 (GPU acceleration)

---

## Executive Summary

Phase 9 pivots to **pure C++23 + GLSL 4.60** architecture (no CUDA dependency). Consumer GPU optimization happens through GLSL shader compilation targeting Lovelace/Ada architecture (SM_89). Simultaneously, we implement extended physics metrics (Kerr-Newman for charged black holes, Kerr-de Sitter for cosmological constant). WASM deployment is deferred to wishlist indefinitely.

**Key Decision:** Compile **C++23 verified kernels to GLSL 4.60** for shader-based GPU acceleration rather than using CUDA. This approach:
- ✓ No CUDA SDK dependency
- ✓ Vendor-agnostic (works on any GPU)
- ✓ Builds on proven Phase 3 transpiler (`cpp_to_glsl.py`)
- ✓ Seamless integration with existing graphics pipeline
- ✓ Same performance characteristics as CUDA with simpler workflow

**Target Hardware:**
- NVIDIA RTX 4090 (Lovelace SM_89, GLSL 4.60)
- NVIDIA RTX 4080 (Lovelace SM_89, GLSL 4.60)
- NVIDIA RTX 5000 Ada (Ada SM_89, GLSL 4.60)
- AMD RDNA / AMD Radeon (GLSL 4.60)
- Intel Arc (GLSL 4.60)
- User's card: SM_89 (RTX 4090/4080/5000 class)

---

## Part 1: Phase 9.0 - GLSL Shader Compilation (C++23 → GPU)

### 1.1 Architecture Overview: C++23 → GLSL Pipeline

```
Verified Physics Kernels (C++23)
  ├─ src/physics/verified/kerr.hpp
  ├─ src/physics/verified/rk4.hpp
  ├─ src/physics/verified/energy_conserving_geodesic.hpp
  └─ src/physics/verified/schwarzschild.hpp
              ↓
   C++ to GLSL Transpiler (enhanced)
  └─ scripts/cpp_to_glsl.py (Phase 3, already functional)
              ↓
   Generated GLSL Headers (4.60)
  ├─ shader/generated/kerr.glsl
  ├─ shader/generated/rk4.glsl
  ├─ shader/generated/christoffel.glsl
  └─ shader/generated/energy_conserving.glsl
              ↓
   Shader Modules (Consumer GPU Optimized)
  ├─ shader/raytracer.frag (main ray-tracing shader)
  ├─ shader/integrator.glsl (RK4 integration)
  └─ shader/metrics.glsl (metric computations)
              ↓
   GPU Execution (OpenGL/Vulkan)
  └─ Real-time ray-traced imagery
```

### 1.2 Phase 9.0 Tasks: GLSL Shader Compilation

#### 1.2.1 Enhance C++ to GLSL Transpiler

**File:** `scripts/cpp_to_glsl.py` (Phase 3, currently functional but needs enhancements)

**Current Capabilities (from Phase 3):**
- ✓ Parse C++ template functions
- ✓ Generate GLSL equivalents
- ✓ Handle float32/float64 conversions
- ✓ Generate shader includes

**Phase 9.0 Enhancements Needed:**

```python
# 1. Optimize for SM_89 (Lovelace/Ada specific optimizations)
class GLSL460Optimizer:
    def optimize_for_lovelace(shader_code):
        # Target: Maximize L2 cache utilization (5 TB/s on RTX 4090)
        # Technique: Loop blocking and data reuse within shared memory bounds
        # Optimization: Unroll short loops, privatize loop variables

    def reduce_register_pressure(shader_code):
        # Reduce from ~32 regs/thread to ~24 regs
        # Technique: Inline temporary variables, reduce vector operations

    def insert_occupancy_pragmas(shader_code):
        # Add GLSL hints for occupancy (GL_ARB_shading_language_include)
        return shader_code  # Already optimal for GLSL

# 2. Add precision annotations
def add_precision_qualifiers(shader_code):
    # Insert: layout(std140) for uniform blocks
    # Insert: highp/mediump for critical calculations
    # Preserve: Original C++ type semantics

# 3. Generate validated shader includes
def generate_verified_headers(cpp_files):
    # Output: shader/generated/verified_kerr.glsl
    #         shader/generated/verified_rk4.glsl
    # Verify: Each function has input/output contracts
    # Comment: Reference back to Rocq proofs
```

**Implementation Plan:**
- [ ] Add Lovelace-specific optimization passes
- [ ] Insert precision qualifiers (std140 layouts)
- [ ] Generate verified shader headers with proof references
- [ ] Create shader include guard system
- [ ] Test transpiler on all verified:: kernels

#### 1.2.2 Generate GLSL Shader Modules

**File Structure:**
```
shader/
├─ generated/               (auto-generated from C++)
│  ├─ verified_kerr.glsl
│  ├─ verified_rk4.glsl
│  ├─ verified_christoffel.glsl
│  └─ verified_energy_conserving.glsl
├─ raytracer.frag           (main fragment shader - Phase 9.0 NEW)
├─ integrator.glsl          (RK4 integration module - Phase 9.0 NEW)
└─ metrics.glsl             (metric helper functions - Phase 9.0 NEW)
```

**Main Shader: `shader/raytracer.frag` (300-400 lines)**

```glsl
#version 460 core

// Generated verified headers (from C++23)
#include "generated/verified_kerr.glsl"
#include "generated/verified_rk4.glsl"
#include "generated/verified_energy_conserving.glsl"

// Input from host
uniform mat4 camera_matrix;
uniform dvec2 uv_pixel;
uniform double M;
uniform double a;
uniform int max_steps;

// Output
layout(location = 0) out vec4 frag_color;

// Per-thread working memory
shared GPUGeodesicState[128] thread_rays;  // One ray per thread
shared float[128] ray_energy;

void main() {
    // 1. Initialize ray from camera parameters
    GPUGeodesicState ray = initialize_ray(uv_pixel, camera_matrix);

    // 2. Integrate geodesic using verified RK4
    double energy = compute_energy(ray, M, a);

    for (int step = 0; step < max_steps; step++) {
        ray = verified_rk4_step(ray, M, a, 0.1);

        // Energy conservation check
        double new_energy = compute_energy(ray, M, a);
        ray = apply_hamiltonian_correction(ray, energy);

        // Termination checks
        if (ray.x1 > 1000.0) break;  // Escape to infinity
        if (ray.x1 < horizon(M, a) + 0.1) break;  // Into black hole
    }

    // 3. Compute pixel color based on final ray position
    frag_color = compute_pixel_color(ray, M, a);
}
```

**Integration Module: `shader/integrator.glsl`**

```glsl
// RK4 stepping with energy conservation
// Uses verified:: kernels from C++23

void main_integrator_loop(inout GPUGeodesicState ray, double M, double a) {
    double energy = compute_energy(ray, M, a);

    for (int i = 0; i < NUM_STEPS; i++) {
        // Step via verified RK4
        ray = verified_rk4_step(ray, M, a, DT);

        // Restore energy conservation
        double norm_sq = compute_metric_norm(ray, M, a);
        double correction = sqrt(1.0 / norm_sq);
        ray.v1 *= correction;
        ray.v2 *= correction;
        ray.v3 *= correction;
    }
}
```

#### 1.2.3 Compilation Infrastructure

**CMake Enhancement: `CMakeLists.txt`**

```cmake
# ============================================================================
# Phase 9.0: GLSL Shader Compilation from C++23 Verified Kernels
# ============================================================================

option(BLACKHOLE_GENERATE_GLSL "Generate GLSL from C++23 kernels" ON)

if(BLACKHOLE_GENERATE_GLSL)
    # Run C++ to GLSL transpiler
    add_custom_target(generate_glsl ALL
        COMMAND python3 ${CMAKE_SOURCE_DIR}/scripts/cpp_to_glsl.py
            --input src/physics/verified/kerr.hpp
            --input src/physics/verified/rk4.hpp
            --input src/physics/verified/energy_conserving_geodesic.hpp
            --output shader/generated/
            --target glsl460
            --optimize-for-lovelace
        DEPENDS
            src/physics/verified/kerr.hpp
            src/physics/verified/rk4.hpp
            scripts/cpp_to_glsl.py
        COMMENT "Generating GLSL 4.60 from verified C++23 kernels"
    )

    # Validate generated shaders with glslangValidator
    add_custom_target(validate_glsl ALL
        COMMAND glslangValidator -S frag shader/raytracer.frag
        DEPENDS generate_glsl
        COMMENT "Validating GLSL shader syntax"
    )

    message(STATUS "GLSL shader generation: ENABLED")
else()
    message(STATUS "GLSL shader generation: DISABLED")
endif()
```

**Build Commands:**
```bash
# Generate and validate GLSL shaders
cmake -B build -DBLACKHOLE_GENERATE_GLSL=ON
cmake --build build

# Just generate (skip validation)
cmake -B build -DBLACKHOLE_GENERATE_GLSL=ON -DBLACKHOLE_VALIDATE_GLSL=OFF
cmake --build build

# Compile with optimizations for SM_89
cmake -B build -DBLACKHOLE_GENERATE_GLSL=ON \
  -DGLSL_OPTIMIZATION_TARGET=Lovelace
cmake --build build
```

#### 1.2.4 Shader Testing & Validation

**GPU Rendering Tests: `tests/shader_raytracer_test.cpp`**

```cpp
// Test verified physics in GLSL by rendering test scenes

TEST(GLSLShaderTests, RayInitialization) {
    // Initialize OpenGL context
    GLFWwindow* window = glfwCreateWindow(512, 512, "Shader Test", NULL, NULL);

    // Compile shader
    GLuint shader_program = compile_shader_program("shader/raytracer.frag");

    // Test ray initialization matches C++ version
    glUseProgram(shader_program);
    glUniform2d(glGetUniformLocation(shader_program, "uv_pixel"), 0.5, 0.5);

    // Render to texture
    GLuint framebuffer = create_test_framebuffer(512, 512);
    glBindFramebuffer(GL_FRAMEBUFFER, framebuffer);
    glDrawArrays(GL_TRIANGLE_STRIP, 0, 4);

    // Read back and validate
    std::vector<float> gpu_result(512*512*4);
    glReadPixels(0, 0, 512, 512, GL_RGBA, GL_FLOAT, gpu_result.data());

    // Compare to CPU reference implementation
    std::vector<float> cpu_result = compute_reference_image_cpu(512, 512);

    EXPECT_NEAR(gpu_result, cpu_result, 1e-5);  // Float32 tolerance
}

TEST(GLSLShaderTests, EnergyConservation) {
    // Render many rays, check energy is conserved
    // Over 1000 test rays, energy should vary <0.1%
}

TEST(GLSLShaderTests, ISCOValidation) {
    // Render ray starting at ISCO
    // Should remain stable on circular orbit
}
```

**Benchmark Suite:**

```cpp
struct ShaderBenchmark {
    double render_time_ms;      // Time to render 512×512 image
    double rays_per_ms;         // Throughput
    double gflops;              // Floating point operations
    double sm_occupancy;        // Estimated SM utilization
};

BenchmarkResults benchmark_shader_pipeline() {
    // Test various resolutions
    // Test various max_steps (10, 50, 100, 500)
    // Measure: render time, memory bandwidth, utilization
    // Compare: GPU vs CPU baseline
}
```

#### 1.2.5 Performance Targets for Consumer GPU (SM_89)

| Metric | Target | RTX 4090 | RTX 4080 | RTX 5000 Ada |
|--------|--------|----------|----------|-------------|
| 1080p 60fps | Yes | 512×512/ray | 512×512/ray | 512×512/ray |
| 4K 30fps | Yes | 256×256/ray | 128×128/ray | 256×256/ray |
| Ray throughput | 100+ Mray/s | 180 Mray/s | 120 Mray/s | 150 Mray/s |
| Memory bandwidth | 700+ GB/s | 1008 GB/s | 716.8 GB/s | 900+ GB/s |
| SM occupancy | 60-75% | 70% | 65% | 70% |

**Strategy for consumer GPUs:**
1. Use smaller tiles (4×4 or 8×8 rays per workgroup)
2. Leverage L2 cache (5 TB/s on RTX 4090)
3. Minimize register pressure (<24 registers/thread)
4. Use shared memory only for ray state buffering

#### 1.2.6 GLSL Shader Features

**Feature: Verified Metric Computation**
```glsl
// From verified_kerr.glsl (transpiled from C++23)
dvec2 kerr_horizons(double M, double a) {
    double discriminant = M*M - a*a;
    if (discriminant < 0.0) return dvec2(0.0);  // No horizons

    double sqrt_disc = sqrt(discriminant);
    double r_plus = M + sqrt_disc;
    double r_minus = M - sqrt_disc;

    return dvec2(r_plus, r_minus);
}

// From verified_christoffel.glsl
dmat3 kerr_christoffel_acceleration(dvec4 position, dvec4 velocity, double M, double a) {
    // Compute Christoffel symbols and acceleration
    // 100% verified from Rocq proofs
}
```

**Feature: Real-Time Ray Tracing**
```glsl
// Fragment shader traces one ray per pixel
// Energy-conserving integration
// Termination on escape or capture
// Interactive camera control
```

---

## Part 2: Phase 9.2 & 9.3 - Extended Physics

### 2.1 Kerr-Newman Metric (Charged Rotating Black Holes)

**Approach:** Same as outlined in original plan, but C++23 only (no CUDA)

#### 2.1.1 Implementation Tasks

```
□ Rocq Formalization
  ├─ rocq/theories/Kerr-Newman/metric.v
  ├─ Prove horizon existence
  └─ Prove Kerr limit (Q=0 → Kerr)

□ C++23 Implementation
  ├─ src/physics/verified/kerr_newman.hpp
  ├─ Implement: Sigma, Delta, horizons
  ├─ Implement: ISCO numerical solver
  └─ Implement: Christoffel symbols with charge

□ GLSL Transpilation
  ├─ Auto-generate shader/generated/kerr_newman.glsl
  ├─ Validate shader compilation
  └─ Benchmark shader performance

□ Testing
  ├─ Unit tests (C++): 10+ test cases
  ├─ Shader tests (GLSL): GPU vs CPU parity
  └─ Literature validation: Compare to published ISCO values
```

**Key Physics:**
- **Parameters:** M (mass), a (spin), Q (charge)
- **Metric:** Delta = r² - 2Mr + a² + Q²
- **Horizons:** r₊ = M + √(M² - a² - Q²), r₋ = M - √(M² - a² - Q²)
- **ISCO:** Transcendental equation (numerical solution required)
- **Continuity:** lim Q→0 → Kerr (verified in tests)

#### 2.1.2 Lacuna: Charged Particle Dynamics

**Gap Identified:** Currently only neutral geodesics

**Options:**
- **Phase 9.2 Scope:** Neutral particles only (focus on metric geometry)
- **Phase 10+ Scope:** Add Lorentz force for charged particles

**Recommendation:** Stay neutral for Phase 9, add charged particles in Phase 10.

### 2.2 Kerr-de Sitter Metric (With Cosmological Constant)

**Approach:** Same structure as Kerr-Newman

#### 2.2.1 Implementation Tasks

```
□ Rocq Formalization
  ├─ rocq/theories/Kerr-de-Sitter/metric.v
  ├─ Prove triple horizon existence
  └─ Prove Kerr limit (Λ=0 → Kerr)

□ C++23 Implementation
  ├─ src/physics/verified/kerr_de_sitter.hpp
  ├─ Implement: Delta with Λ term
  ├─ Implement: Three horizons (event, Cauchy, cosmological)
  ├─ Implement: ISCO existence check
  └─ Implement: Geodesic equations

□ GLSL Transpilation
  ├─ Auto-generate shader/generated/kerr_de_sitter.glsl
  ├─ Optimize for numerical stability (small Λ)
  └─ Benchmark multi-horizon computations

□ Testing
  ├─ Unit tests: 12+ test cases
  ├─ Shader tests: GPU parity validation
  └─ Literature: Compare horizon calculations
```

**Key Physics:**
- **Parameter:** Λ (cosmological constant)
- **Metric:** Delta = r² - 2Mr + a² - (Λ/3)r⁴
- **Horizons:** Three roots (event, Cauchy, cosmological)
- **ISCO:** May not exist for large Λ (return std::optional)
- **Scaling:** Handle very small Λ (~10⁻⁵² in natural units)

---

## Part 3: Identified Lacunae & Gaps (Revised for C++23/GLSL)

### 3.1 GPU/Rendering Layer Gaps

**Gap 1.1: Shader Optimization for SM_89**
- **Issue:** Generic GLSL may not leverage Lovelace-specific features
- **Impact:** Suboptimal performance on consumer GPUs
- **Solution:** Insert Lovelace-specific optimizations in transpiler
- **Effort:** 200 LOC transpiler enhancement
- **Blocks:** Phase 9.0 performance targets

**Gap 1.2: Precision and Accuracy in GLSL**
- **Issue:** Float32 in GLSL vs double precision in C++
- **Impact:** Numerical accuracy differences, energy conservation drift
- **Solution:** Use float64 (GL_ARB_gpu_shader_fp64) where available
- **Effort:** 150 LOC shader modifications
- **Blocks:** GPU validation tests

**Gap 1.3: Interactive Camera Control**
- **Issue:** No camera system for real-time exploration
- **Impact:** Static visualization, can't move through scene
- **Solution:** Add camera matrix uniforms and input handling
- **Effort:** 300 LOC (camera system + input)
- **Blocks:** Phase 10 visualization

### 3.2 Physics Computation Gaps (Same as Original)

**Gap 2.1: Photon Orbit Stability Analysis**
- **Missing:** Lyapunov exponent calculations
- **Solution:** Implement geodesic deviation equations
- **Effort:** 300-400 LOC

**Gap 2.2: Numerical Integration Accuracy Spec**
- **Missing:** Formal tolerance requirements
- **Solution:** Document accuracy budget
- **Effort:** 100 LOC documentation

**Gap 2.3: Extremal Limit Handling**
- **Missing:** Explicit validation near a² + Q² = M²
- **Solution:** Add parameter range checking
- **Effort:** 100 LOC

### 3.3 Visualization Gaps

**Gap 3.1: Accretion Disk Model**
- **Missing:** Thin disk rendering
- **Solution:** Implement Novikov-Thorne model
- **Effort:** 300+ LOC shader code
- **Priority:** Medium (Phase 10)

**Gap 3.2: Gravitational Lensing Visualization**
- **Missing:** Show light deflection on background
- **Solution:** Render grid of rays showing distortion
- **Effort:** 200 LOC shader enhancement
- **Priority:** Medium (Phase 10)

### 3.4 Testing & Validation Gaps

**Gap 4.1: GPU vs CPU Parity Tests**
- **Missing:** Systematic comparison of GLSL vs C++23 results
- **Solution:** Render reference CPU image, compare pixel-by-pixel
- **Effort:** 300 LOC test code
- **Blocks:** Phase 9.0 validation (HIGH PRIORITY)

**Gap 4.2: Literature Validation**
- **Missing:** Systematic comparison with published values
- **Solution:** Create validation test suite with known results
- **Effort:** 200 LOC tests

**Gap 4.3: Benchmark Suite**
- **Missing:** Systematic performance measurement
- **Solution:** Create render time benchmarks for various parameters
- **Effort:** 150 LOC

### 3.5 Build & Infrastructure Gaps

**Gap 5.1: Shader Generation CMake Integration**
- **Missing:** Automated shader generation from C++
- **Solution:** Add CMake custom target for transpiler
- **Effort:** 100 LOC CMakeLists.txt
- **Blocks:** Phase 9.0 (CRITICAL)

**Gap 5.2: Shader Compilation & Validation**
- **Missing:** glslangValidator integration
- **Solution:** Add CMake validation step
- **Effort:** 50 LOC
- **Priority:** HIGH (catch shader errors early)

### 3.6 Documentation Gaps

**Gap 6.1: GLSL Shader Guide**
- **Missing:** Documentation on generated shaders
- **Solution:** Create docs/GLSL_SHADER_GUIDE.md
- **Effort:** 300 LOC documentation

**Gap 6.2: C++ to GLSL Transpilation Guide**
- **Missing:** How transpiler works, extending it
- **Solution:** Document transpiler architecture
- **Effort:** 200 LOC documentation

---

## Part 4: Phase 9 Team Execution Plan

### 4.1 GLSL Shader Compilation (Phase 9.0) - Priority 1

**Team Member: Rendering/GPU Developer**

```
□ P1: Enhance C++ to GLSL Transpiler (scripts/cpp_to_glsl.py)
  ├─ Add Lovelace optimization passes
  ├─ Insert precision qualifiers (std140 layouts)
  ├─ Generate verified shader headers with proof references
  ├─ Test on all verified:: kernels (kerr.hpp, rk4.hpp, etc.)
  └─ Validate output GLSL syntax

□ P1: CMake GLSL Generation Integration
  ├─ Create custom target for shader generation
  ├─ Add glslangValidator validation step
  ├─ Test build with and without shader generation
  └─ Document build configuration

□ P1: Main Fragment Shader (shader/raytracer.frag)
  ├─ Include verified shader headers
  ├─ Implement ray initialization from camera
  ├─ Implement geodesic integration loop
  ├─ Implement energy conservation checking
  ├─ Implement pixel color computation
  └─ Compile without warnings

□ P1: Integration Module (shader/integrator.glsl)
  ├─ Implement verified RK4 stepping
  ├─ Implement Hamiltonian correction
  ├─ Implement termination checks
  └─ Verify matches C++ behavior

□ P1: GPU Shader Tests (tests/shader_raytracer_test.cpp)
  ├─ Initialize OpenGL context
  ├─ Compile and link shaders
  ├─ Test ray initialization parity
  ├─ Test energy conservation on GPU
  ├─ Test against CPU reference
  └─ Benchmark rendering throughput

□ P1: GPU vs CPU Parity Validation
  ├─ Render reference CPU image (512×512)
  ├─ Render same image with GLSL shader
  ├─ Compare pixel-by-pixel (tolerance: <1e-4 for float32)
  ├─ Test across full spin range (0 ≤ a ≤ 0.99)
  └─ Document divergences (if any)

□ P1: Performance Benchmarking
  ├─ Measure render time for 1080p, 4K, 8K
  ├─ Measure ray throughput (Mray/s)
  ├─ Estimate GFLOP/s
  ├─ Profile memory bandwidth utilization
  ├─ Compare to Phase 8 targets (250+ GFLOP minimum)
  └─ Create performance comparison table

Total Effort: ~2000 LOC (transpiler + shaders + tests)
Estimated Time: 2-3 weeks
```

### 4.2 Kerr-Newman Metric (Phase 9.2) - Priority 2

**Team Member: Physics/Verification Developer**

```
□ P2: Rocq Formalization (rocq/theories/Kerr-Newman/metric.v)
  ├─ Define metric components (Sigma, Delta with Q)
  ├─ Prove horizon existence and ordering
  ├─ Prove Kerr limit: Q=0 → Kerr
  ├─ Prove Reissner-Nordström limit: a=0
  └─ All proofs verified by Rocq checker

□ P2: C++23 Implementation (src/physics/verified/kerr_newman.hpp)
  ├─ Implement metric functions (Sigma, Delta, g_tt, g_rr, etc.)
  ├─ Implement horizon calculations
  ├─ Implement Christoffel symbol computation
  ├─ Implement geodesic RHS equations
  ├─ Implement ISCO numerical solver (Brent's method)
  ├─ All functions in verified:: namespace
  └─ Zero warnings, compile with -Werror

□ P2: Numerical ISCO Solver
  ├─ Implement bracketing algorithm
  ├─ Use Newton's method for refinement
  ├─ Handle extremal limit (a²+Q²→M²)
  └─ Test against any available literature values

□ P2: GLSL Transpilation
  ├─ Auto-generate shader/generated/kerr_newman.glsl
  ├─ Insert precision qualifiers
  ├─ Validate GLSL syntax with glslangValidator
  └─ Benchmark shader performance

□ P2: Unit Tests (tests/kerr_newman_test.cpp)
  ├─ Test horizons for various Q values
  ├─ Test Kerr limit (Q=0 → original)
  ├─ Test Reissner-Nordström (a=0)
  ├─ Test geodesic equations
  ├─ Test ISCO solver
  └─ 10+ tests all passing

□ P2: Shader Tests (tests/shader_kerr_newman_test.cpp)
  ├─ Compare GLSL results vs C++ reference
  ├─ Validate horizon calculations on GPU
  ├─ Test energy conservation
  └─ <1e-4 relative error tolerance

Total Effort: ~1000 LOC
Estimated Time: 2-3 weeks
```

### 4.3 Kerr-de Sitter Metric (Phase 9.3) - Priority 2

**Team Member: Physics/Verification Developer**

```
□ P2: Rocq Formalization (rocq/theories/Kerr-de-Sitter/metric.v)
  ├─ Define Delta with Λ term: r² - 2Mr + a² - (Λ/3)r⁴
  ├─ Prove three horizons exist for physical parameters
  ├─ Prove Kerr limit: Λ=0 → Kerr
  └─ All proofs verified

□ P2: C++23 Implementation (src/physics/verified/kerr_de_sitter.hpp)
  ├─ Implement metric functions
  ├─ Implement three horizon solvers (event, Cauchy, cosmological)
  ├─ Implement ISCO existence check (returns std::optional)
  ├─ Implement geodesic equations
  └─ Handle small Λ numerically

□ P2: Multi-Scale Numerical Approach
  ├─ Design dimensionless variable transformation
  ├─ Implement robust polynomial root finding
  ├─ Test with astrophysically realistic Λ
  └─ Document numerical precision limits

□ P2: GLSL Transpilation
  ├─ Auto-generate shader/generated/kerr_de_sitter.glsl
  ├─ Optimize for numerical stability
  ├─ Handle small Λ in shader precision
  └─ Validate shader compilation

□ P2: Unit Tests (tests/kerr_de_sitter_test.cpp)
  ├─ Test three horizons exist in valid range
  ├─ Test Kerr limit: Λ=0 → Kerr
  ├─ Test Schwarzschild-de Sitter: a=0
  ├─ Test ISCO existence/non-existence
  ├─ Test geodesic equations
  └─ 12+ tests all passing

□ P2: Shader Tests (tests/shader_kerr_de_sitter_test.cpp)
  ├─ GPU vs CPU parity
  ├─ Horizon position validation
  ├─ Geodesic integration on GPU
  └─ <1e-4 relative error

Total Effort: ~1200 LOC
Estimated Time: 2.5-3 weeks
```

### 4.4 Testing & Validation Infrastructure (Phase 9.T) - Priority 1.5

**Team Member: QA/Testing Developer**

```
□ P1.5: GPU vs CPU Parity Tests
  ├─ Create test framework comparing GLSL vs C++23
  ├─ Render reference images (various sizes)
  ├─ Compare pixel-by-pixel with float32 tolerance
  ├─ Test across parameter ranges
  └─ Document acceptable divergences

□ P1.5: Shader Compilation & Validation
  ├─ Integrate glslangValidator into CMake
  ├─ Test shader compilation on various drivers
  ├─ Verify -Werror equivalence (no warnings)
  └─ Document shader prerequisites

□ P2: Benchmark Infrastructure
  ├─ Create render time measurement suite
  ├─ Measure rays/ms, GB/s bandwidth, GFLOP/s
  ├─ Track performance across phases
  ├─ Create visualization of benchmarks
  └─ Compare CPU vs GPU performance

□ P2: Literature Validation Suite
  ├─ Kerr-Newman: Gather published ISCO values
  ├─ Kerr-de Sitter: Gather horizon calculations
  ├─ Create automated test cases
  └─ Document all reference sources

Total Effort: ~600 LOC tests
Estimated Time: 1-2 weeks
```

### 4.5 Documentation & Infrastructure (Phase 9.D) - Priority 3

**Team Member: Documentation Developer**

```
□ P3: GLSL Shader Build Guide (docs/GLSL_SHADER_BUILD_GUIDE.md)
  ├─ Prerequisites (OpenGL 4.6, glslang)
  ├─ Build instructions for shader generation
  ├─ Troubleshooting common issues
  ├─ Optimization tips for various GPUs
  └─ Examples for RTX 4090/4080/5000

□ P3: C++ to GLSL Transpiler Guide
  ├─ How transpiler works
  ├─ Extending transpiler for new patterns
  ├─ Optimization passes explanation
  ├─ Precision handling in shaders
  └─ Limitations and workarounds

□ P3: Extended Physics Reference
  ├─ Kerr-Newman physics explanation
  ├─ Kerr-de Sitter physics explanation
  ├─ Parameter constraints
  ├─ Links to Rocq formalizations
  └─ Example calculations

□ P3: API Documentation
  ├─ Add Doxygen comments to verified:: functions
  ├─ Generate HTML documentation
  ├─ Add examples for each function
  └─ Link to theoretical background

Total Effort: ~1000 LOC documentation
Estimated Time: 1 week
```

---

## Part 5: Wishlist (Deferred Items)

### 5.1 WASM Deployment (DEFERRED INDEFINITELY)

**Rationale:**
- Lower priority than consumer GPU optimization
- Browser-based visualization can wait
- Current focus: correct GPU acceleration on desktop
- Can revisit if web deployment becomes priority

### 5.2 Other Deferred Items

**Nice-to-Have (Phase 10+):**
- Charged particle dynamics (Lorentz force)
- Radiation reaction (Lorentz-Dirac)
- Accretion disk models (Novikov-Thorne)
- Gravitational wave generation
- Advanced visualization (reflections, refractions)

---

## Phase 9 Success Criteria

### Phase 9.0 (GLSL Shader Compilation) Success Criteria

✓ C++ to GLSL transpiler generates valid GLSL 4.60 from verified kernels
✓ All generated shaders compile without errors/warnings
✓ GPU vs CPU parity tests pass with <1e-4 relative error (float32)
✓ Render throughput: 100+ Mray/s on RTX 4090
✓ 1080p real-time rendering (60+ fps) achievable
✓ CMake integration works seamlessly
✓ Documentation complete

### Phase 9.2 (Kerr-Newman) Success Criteria

✓ Rocq formalization type-checks and proves key theorems
✓ C++23 passes 10+ unit tests
✓ GLSL shader generates and validates
✓ GPU parity validation passes
✓ Kerr limit (Q=0) matches original Kerr exactly
✓ Reissner-Nordström limit (a=0) correct

### Phase 9.3 (Kerr-de Sitter) Success Criteria

✓ Rocq formalization complete with proofs
✓ C++23 handles triple horizons correctly
✓ GLSL shader generates and validates
✓ GPU parity validation passes
✓ Kerr limit (Λ=0) matches Kerr exactly
✓ All 12+ tests passing

---

## Phase 9 Technology Stack

```
Development Layer
  C++23 (verified physics kernels)
    ↓
Transpilation Layer
  Python (cpp_to_glsl.py)
    ↓
GPU Acceleration Layer
  GLSL 4.60 (shader code)
    ↓
Execution Layer
  OpenGL 4.6 (on any modern GPU)
```

**Advantages of C++23 → GLSL approach:**
- ✓ No external GPU SDK dependencies (vs CUDA)
- ✓ Vendor-agnostic (NVIDIA, AMD, Intel)
- ✓ Proven transpiler from Phase 3
- ✓ Simpler development workflow
- ✓ Easier debugging (CPU and GPU versions both available)
- ✓ Same mathematical correctness (extracted from Rocq)

---

## Timeline & Resource Allocation

**Estimated Total Effort:** 4500-5000 LOC

| Phase | Tasks | Time | Priority |
|-------|-------|------|----------|
| 9.0 | GLSL shaders + transpiler enhancement | 2-3 weeks | P1 |
| 9.2 | Kerr-Newman (Rocq + C++ + GLSL) | 2-3 weeks | P2 |
| 9.3 | Kerr-de Sitter (Rocq + C++ + GLSL) | 2.5-3 weeks | P2 |
| 9.T | Testing & validation | 1-2 weeks | P1.5 |
| 9.D | Documentation | 1 week | P3 |

**Total: 8-11 weeks with 1-2 parallel developers**

---

## References

**GLSL/OpenGL:**
- [GLSL 4.60 Specification](https://www.khronos.org/registry/OpenGL/specs/gl/GLSLangSpec.4.60.pdf)
- [OpenGL ARB Extensions](https://www.khronos.org/opengl/wiki/OpenGL_Extension#ARB_extensions)

**Extended Physics:**
- [Kerr-Newman - Wikipedia](https://en.wikipedia.org/wiki/Kerr–Newman_metric)
- [Kerr-de Sitter - arXiv](https://arxiv.org/abs/1011.0479)

---

**Status:** Phase 9 Scoping Complete (C++23/GLSL Only)
**Ready for:** Team assignment and implementation
**Next Step:** Begin Phase 9.0 GLSL shader compilation

Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Haiku 4.5 <noreply@anthropic.com>
