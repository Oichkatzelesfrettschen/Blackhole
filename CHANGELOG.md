# Changelog

All notable changes to the Blackhole black hole visualization engine are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- Comprehensive `shader/README.md` documenting C++23 to GLSL transpilation patterns
- Complete shader validation infrastructure (21 shaders: 14 fragment, 5 vertex, 2 compute)
- Documentation of reserved keyword issues (`lambda` → `affine_param`)
- Include order dependency guidelines for verified physics modules

### Fixed
- **CRITICAL**: All 21 shaders now compile without errors (2026-01-15)
  - `kerr.glsl`: Added missing `PI` constant include
  - `blackhole_main.frag`: Defined inline `sch_photonSphereRadius()` and `sch_iscoRadius()`
  - `rk4.glsl`: Fixed corrupted StateVector struct, replaced C++ aggregate initialization
  - `geodesic.glsl`: Fixed MetricComponents and ChristoffelAccel structs
  - `energy_conserving_geodesic.glsl`: Fixed ConservedQuantities struct, removed `std::max`
  - `null_constraint.glsl`: Fixed ConstraintStats struct, commented out lambda-dependent functions
  - `integrator.glsl`: Replaced reserved `lambda` keyword with `affine_param`
  - `raytracer.frag`: Moved `integrator.glsl` include after RayState definition
  - `geodesic_trace.comp`: Corrected include order (rk4.glsl before geodesic.glsl)
- Fast-math NaN/infinity handling: Use `physics::safe_isnan()`/`safe_isinf()` from `safe_limits.h`
- Unused variable/field warnings: Added `[[maybe_unused]]` attributes to preserve future scaffolding
- Double-promotion warnings: Added explicit `static_cast<double>()` at type boundaries
- Clang -Werror compatibility: All compilation warnings resolved

### Changed
- Consolidated shader validation todos (11 items → 2 final items)
- Updated todo list structure for Phase 10.1+ work

### Known Issues
- `z3_verification_test` has googletest linking issue (tracked in TODO_FIXES.md)
- Some lambda-dependent functions in `null_constraint.glsl` require architectural refactoring

---

## [Phase 10.1] - 2026-01-02 - Hawking Radiation Thermal Glow

### Added
- GPU-accelerated Hawking radiation thermal glow visualization
- **New Files**: 10 source files (1,673 lines total)
  - `scripts/generate_hawking_lut.py` - LUT generation (200 lines)
  - `shader/include/hawking_luts.glsl` - GLSL sampling utilities (200+ lines)
  - `shader/hawking_glow.glsl` - Thermal glow shader (234 lines)
  - `src/physics/hawking_renderer.{h,cpp}` - C++ GPU interface (599 lines)
  - `tests/hawking_glow_test.cpp` - Physics validation (170 lines)
  - `tests/hawking_spectrum_test.cpp` - Spectrum validation (270 lines)
- **LUT Data**: 768 precomputed samples (512 temperature + 256 spectrum)
- **Visualization Presets**:
  1. Physical (T_scale=1.0) - Realistic (invisible for solar mass BH)
  2. Primordial (T_scale=1e6) - Blue-white X-ray glow
  3. Extreme (T_scale=1e9) - Maximum visibility for education
- **UI Integration**: ImGui controls
  - Enable/disable checkbox
  - Preset selector (Physical/Primordial/Extreme)
  - Temperature scale slider (logarithmic, 1.0–1×10⁹)
  - Intensity slider (0.0–5.0)
  - LUT toggle (precomputed vs direct calculation)

### Fixed
- Phase 10.1 shader compilation errors (commit 7a4c49b)

### Validated
- **Physics Accuracy**:
  - Solar mass temperature: 6.17×10⁻⁸ K (±0.4% accuracy) ✓
  - Inverse mass law: T_H ∝ 1/M (exact) ✓
  - Wien's displacement: λ_peak × T = 0.2898 cm·K (exact) ✓
  - Stefan-Boltzmann: L ∝ T⁴ (0.001% accuracy) ✓
- **Test Coverage**: 13 unit tests (100% pass rate)
  - `hawking_glow_test`: 5/5 tests PASSED
  - `hawking_spectrum_test`: 8/8 tests PASSED

### Documentation
- `docs/PHASE10_TESTING_GUIDE.md` - Manual testing procedures
- `docs/PHASE10.1_COMPLETE.md` - Implementation completion summary

---

## [Phase 8.2] - 2025-12 - GPU Shader Optimizations

### Added
- Disk density profile LUT (commit f6f387f)
- Conditional texture batching with `mix()` (commit f2c2426)
- Cached Cartesian radius computation in disk rendering (commit 035d33c)

### Optimized
- **Priority 1**: GPU shader optimizations (commit dec8f09)
  - Inline acceleration computation
  - Photon glow LUT integration
- **Priority 2**: Disk density LUT integration into accretion disk shader (commit f5ed012)
- **Priority 3**: Distance computation optimization (commit a06b404)

### Documentation
- Priority 3 Optimization #8: Distance computation documentation (commit a06b404)

---

## [Phase 7] - 2025-11 - TLA+ Verification & Z3 Constraints

### Added
- TLA+ formal verification of geodesic integration
- Z3 SMT solver constraints for physics validation
- GLSL physics kernel integration
- Performance benchmarking infrastructure

### Completed
- Phase 7 verification suite (commit acebd05)

---

## [Phase 6] - 2025-11 - C++23 Verified Physics Extraction

### Added
- **Rocq Pipeline**: Rocq 9.1+ → OCaml → C++23 → GLSL 4.60
- Verified physics modules in `src/physics/verified/`:
  - `rk4.hpp` - 4th-order Runge-Kutta integration
  - `geodesic.hpp` - Geodesic equation RHS from Christoffel symbols
  - `schwarzschild.hpp` - Schwarzschild metric
  - `kerr.hpp` - Kerr metric (24 functions)
  - `energy_conserving_geodesic.hpp` - Hamiltonian constraint preservation
  - `null_constraint.hpp` - Null geodesic verification
- SPIRV infrastructure removal (commit 3365577)
- Comprehensive warnings cleanup (commit 3365577)
- `-Werror` compilation mode enabled (commit 7b40e2a)

### Fixed
- BPT (Bardeen-Petterson-Thorne) ISCO formula (commit 7b40e2a)

### Completed
- Phase 6 extraction and integration (commit 2f73738)

---

## [Phase 5] - 2025-10 - SIMD Integration & Legacy Fallbacks

### Added
- SLEEF integration for vectorized transcendental functions (commit 57d97df)
- Tiered SIMD dispatch (AVX512 → AVX2 → SSE4.2 → scalar fallback)
- Physics benchmarking with SIMD variants

### Features
- `physics_bench` executable for performance baseline capture
- SIMD detection and runtime dispatch

---

## [Phase 4] - 2025-09 - Visual Enhancements

### Added
- Curve overlay for spacetime visualization (commit b0636ef)
- Doppler beaming effects (commit b0636ef)
- Wiregrid curvature overlay shader (`wiregrid.frag`, `wiregrid.vert`)

### Changed
- Replaced hardcoded radius uniforms with derived physics functions (commit 92e522a)

---

## [Phase 3] - 2025-08 - Asset Pipeline

### Added
- Background asset manifest (`IMAGE_SOURCES.md`)
- Procedural noise integration (fastnoise2 evaluation)
- Optional LUT-backed emissivity/redshift shading

### Infrastructure
- Runtime vs precomputed LUT toggle
- `assets/luts/` directory for precomputed lookup tables

---

## [Phase 2] - 2025-07 - Rendering Pipeline

### Added
- 8-level bloom post-processing pyramid
  - `bloom_brightness_pass.frag` - HDR brightness extraction
  - `bloom_downsample.frag` / `bloom_upsample.frag` - Gaussian pyramid
  - `bloom_composite.frag` - Final composition
- ACES filmic tonemapping (`tonemapping.frag`)
- Depth cues shader (`depth_cues.frag`)
- GRMHD slice visualization (`grmhd_slice.frag`)

### Features
- RGBA16F HDR framebuffer
- Gamma correction
- Tonemapping intensity control

---

## [Phase 1] - 2025-06 - Core Geodesic Ray Tracing

### Added
- Schwarzschild geodesic ray tracer (`raytracer.frag`)
- Black hole main shader with accretion disk (`blackhole_main.frag`)
- Compute shader path (experimental) (`geodesic_trace.comp`)
- GPU timing panel with fragment/compute split
- ImGui controls panel

### Infrastructure
- OpenGL 4.6 rendering backend
- CMake build system with Conan 2.x dependencies
- Shader validation target (`validate-shaders`)
- Unit test suite with googletest

### Features
- Real-time geodesic integration (RK4)
- Accretion disk with procedural noise
- Camera controls (position, orientation, FOV)
- Runtime shader compilation with hot-reload (debug builds)

### Dependencies
- GLFW 3.3.8
- GLM 0.9.9.8
- ImGui 1.90.0 (docking branch)
- stb_image, stb_easy_font
- googletest 1.14.0

---

## [Phase 0] - 2025-05 - Project Bootstrap

### Added
- Initial project structure
- Git repository initialization
- License (MIT)
- Basic documentation (`README.md`, `BUILDING.md`)

### Infrastructure
- Conan profile setup for C++23
- CMake presets (debug, release, relwithdebinfo)
- GitHub repository structure

---

## Version History Summary

| Phase | Date | Description | Status |
|-------|------|-------------|--------|
| **Unreleased** | 2026-01-15 | Shader validation + transpilation docs | ✅ Complete |
| **Phase 10.1** | 2026-01-02 | Hawking radiation thermal glow | ✅ Complete |
| **Phase 8.2** | 2025-12 | GPU shader optimizations | ✅ Complete |
| **Phase 7** | 2025-11 | TLA+/Z3 verification | ✅ Complete |
| **Phase 6** | 2025-11 | Verified physics extraction (Rocq) | ✅ Complete |
| **Phase 5** | 2025-10 | SIMD integration (SLEEF) | ✅ Complete |
| **Phase 4** | 2025-09 | Visual enhancements | ✅ Complete |
| **Phase 3** | 2025-08 | Asset pipeline | ✅ Complete |
| **Phase 2** | 2025-07 | Rendering pipeline (bloom, tonemapping) | ✅ Complete |
| **Phase 1** | 2025-06 | Core geodesic ray tracing | ✅ Complete |
| **Phase 0** | 2025-05 | Project bootstrap | ✅ Complete |

---

## Roadmap Forward

See `docs/MASTER_ROADMAP.md` for detailed future phases:

### Phase 11: SPIR-V Backend (Q2 2026)
- Vulkan 1.3 compute shader integration
- Direct SPIR-V generation from Rocq via MLIR
- Performance validation vs OpenGL backend

### Phase 12: Adaptive Stepping (Q2 2026)
- Dynamic step size control based on Hamiltonian drift
- Maintain O(h⁴) accuracy with fewer steps in flat regions

### Phase 13: Kerr-Newman (Q3 2026)
- Charged rotating black hole visualization
- Electromagnetic field effect rendering
- Already scaffolded: `shader/include/verified/kerr_newman.glsl`

### Phase 14: Kerr-de Sitter (Q3 2026)
- Rotating black hole with cosmological constant
- Accelerated expansion visualization
- Already scaffolded: `shader/include/verified/kerr_de_sitter.glsl`

### Phase 15: Multi-Black Hole Systems (Q4 2026)
- N-body geodesic integration
- Gravitational lensing from multiple sources
- Merger event simulation

---

## Contributors

- **Eirikr** - Primary developer, verification pipeline, shader optimization
- **Claude** (Anthropic) - Code review, documentation, build system assistance
- **Codex** (OpenAI) - Feature implementation, testing infrastructure
- **Gemini** (Google) - Architecture planning, performance analysis

---

## License

MIT License - See `LICENSE` file for details

---

## Citations

### Theoretical Foundations
- Misner, Thorne, Wheeler (1973) - "Gravitation"
- Carter (1968) - "Global Structure of the Kerr Family of Gravitational Fields"
- Teukolsky (1973) - "Perturbations of a Rotating Black Hole"

### Numerical Methods
- Runge-Kutta (1901) - 4th-order integration method
- Gray et al. (2021) - "GRay: A Massively Parallel GPU-Based Code for Ray Tracing in Relativistic Spacetimes"

### Verification
- Rocq Prover (Coq 9.1+) - Formal verification framework
- SMT-LIB (Z3) - Constraint solving for physics validation

---

**Last Updated**: 2026-01-15
**Current Phase**: 10.1 (Hawking Radiation) Complete
**Next Milestone**: Phase 11 (SPIR-V Backend)
**Shader Validation**: 21/21 shaders passing
**Verification Status**: All geodesic kernels Rocq-proven to 1e-6 precision
