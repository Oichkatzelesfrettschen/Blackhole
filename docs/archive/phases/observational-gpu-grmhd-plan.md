# Implementation Plan: Phases 5-6 Complete Recursive TODO

Date: 2026-01-29
Status: Fully Scoped and Ready for Implementation
Total Tasks: 110 atomic tasks (Phase 5: 40, Phase 6: 70)
Estimated Duration: 11-12 weeks
Estimated LOC: 8,000-10,000 lines

---

## PHASE 5: MULTI-WAVELENGTH OBSERVATIONAL FEATURES (5-6 weeks)

Goal: Synthetic spectra generation, EHT/LIGO comparison, radiative transfer

### PHASE 5.1: SYNCHROTRON GPU INTEGRATION (1-2 weeks)

High-Level Task #52: Create synchrotron_emission.glsl shader

Granular Tasks:
1. Create shader/include/synchrotron_emission.glsl header (~300 LOC)
2. Port synchrotron_F(x) to GLSL (low/mid/high freq approximations)
3. Port synchrotron_G(x) for polarization degree
4. Implement power_law_spectrum() in GLSL
5. Implement self_absorption_coefficient() calculation
6. Test F(x) and G(x) against analytical values
7. Test power-law spectrum shape (α = -(p-1)/2)
8. Validate absorption coefficient vs theory

Total: 8 tasks, ~300 LOC, 2-3 days

### PHASE 5.2: RADIATIVE TRANSFER SHADER (3-4 days)

High-Level Task #53: Create radiative_transfer.glsl shader

Granular Tasks:
9. Create shader/include/radiative_transfer.glsl (~400 LOC)
10. Implement optical depth integration (tau = integral of alpha * ds)
11. Implement emission-weighted ray marching
12. Add multi-frequency spectral sampling
13. Implement color blending from multiple frequencies
14. Test optical depth convergence
15. Validate energy conservation in ray marching
16. Profile shader performance (target <1ms per pixel)

Total: 8 tasks, ~400 LOC, 3-4 days

### PHASE 5.3: SPECTRAL CHANNELS (2-3 days)

High-Level Task #54: Implement spectral channels and color mapping

Granular Tasks:
17. Create src/physics/spectral_channels.h (~200 LOC)
18. Define radio band (230 GHz EHT)
19. Define optical band (400-800 nm)
20. Define X-ray band (0.5-10 keV Chandra)
21. Implement band-to-RGB mapping
22. Implement wavelength-to-RGB conversion
23. Create band filter functions
24. Validate color accuracy vs standard filters

Total: 8 tasks, ~200 LOC, 2-3 days

### PHASE 5.4: EHT SYNTHETIC IMAGING (4-5 days)

High-Level Task #55: Create EHT synthetic image generator

Granular Tasks:
25. Create tools/eht_synthetic_image.cpp (~500 LOC)
26. Implement 230 GHz raytracer (frequency-specific)
27. Implement Gaussian beam convolution
28. Implement shadow diameter measurement algorithm
29. Implement FITS export (using cfitsio)
30. Create scripts/eht_shadow_metrics.py (~300 LOC)
31. Implement M87* vs Sgr A* comparison logic
32. Validate shadow diameter within +/- 5% of observations

Total: 8 tasks, ~800 LOC, 4-5 days

### PHASE 5.5: LIGO WAVEFORM EXPORT (3-4 days)

High-Level Task #56: Implement LIGO waveform export

Granular Tasks:
33. Create tools/ligo_waveform_export.cpp (~400 LOC)
34. Implement HDF5 export with LIGO schema
35. Add merger phase (NR fits or phenomenological)
36. Add ringdown phase (QNM from gravitational_waves.h)
37. Create scripts/ligo_comparison.py (~300 LOC)
38. Implement matched filtering
39. Implement SNR computation
40. Validate GW150914 parameters match observations

Total: 8 tasks, ~700 LOC, 3-4 days

### PHASE 5.6: VALIDATION TESTS (3-4 days)

High-Level Task #57: Create Phase 5 validation test suite

Granular Tasks:
41. Create tests/synchrotron_spectrum_test.cpp (~200 LOC)
42. Test synchrotron_F(x) against Rybicki & Lightman
43. Test synchrotron_G(x) polarization degree
44. Test power-law spectrum index derivation
45. Create tests/eht_shadow_test.cpp (~200 LOC)
46. Test M87* shadow diameter (42 +/- 3 microarcsec)
47. Test Sgr A* shadow diameter (~52 microarcsec)
48. Create tests/gw_waveform_test.cpp (~250 LOC)
49. Test chirp mass extraction
50. Test frequency evolution (df/dt)
51. Test strain amplitude scaling
52. Test polarization computation

Total: 12 tasks, ~650 LOC, 3-4 days

---

## PHASE 6: GPU ACCELERATION & FULL GRMHD (9-12 weeks)

Goal: 1000x GPU raytracer speedup + production GRMHD streaming

### PHASE 6.1a: GPU RAYTRACER PROFILING (1 week)

High-Level Task #58: GPU raytracer profiling and analysis

Granular Tasks:
1. Profile geodesic_trace.comp with nsight-systems
2. Measure baseline occupancy (target >60%)
3. Identify register spilling (reduce from peak to <64)
4. Measure memory bandwidth utilization
5. Compute thread divergence percentage
6. Identify latency bottlenecks
7. Create optimization roadmap with priorities
8. Document current performance baseline
9. Set per-component performance targets
10. Design benchmark framework for validation

Total: 10 tasks, 1 week

### PHASE 6.1b: REGISTER & MEMORY OPTIMIZATION (1 week)

High-Level Task #59: Register and memory optimization

Granular Tasks:
11. Refactor StateVector for tighter packing
12. Replace separate floats with vec2/vec4 where possible
13. Move rarely-used variables to shared memory
14. Implement register spill analysis tool
15. Reduce intermediate calculations
16. Inline critical functions
17. Implement coalesced memory access patterns
18. Add shared memory for frequent reads (LUT cache)
19. Optimize stride patterns (avoid bank conflicts)
20. Test occupancy impact of changes
21. Measure performance delta per optimization
22. Document optimization tradeoffs
23. Finalize memory-optimized version

Total: 13 tasks, 1 week

### PHASE 6.1c: CONTROL FLOW & ASYNC PIPELINE (1 week)

High-Level Task #60: Control flow and async pipeline

Granular Tasks:
24. Analyze branch divergence patterns
25. Reduce conditional branches via ballot/vote functions
26. Implement uniform code paths
27. Optimize hot loops (RK4 integration)
28. Reduce function call overhead
29. Flatten nested conditionals
30. Design async compute + graphics sync strategy
31. Implement command buffer management
32. Add fence/event synchronization primitives
33. Implement work stealing scheduler
34. Add GPU-GPU synchronization
35. Test zero-copy techniques
36. Finalize async pipeline integration

Total: 13 tasks, 1 week

### PHASE 6.1d: PERFORMANCE VALIDATION (1 week)

High-Level Task #61: GPU raytracer performance validation

Granular Tasks:
37. Benchmark baseline geodesic_trace.comp
38. Benchmark register-optimized version
39. Benchmark memory-optimized version
40. Benchmark control-flow optimized version
41. Benchmark with async pipeline enabled
42. Compare CPU vs GPU performance (1000x target)
43. Measure actual occupancy achieved
44. Measure actual memory bandwidth utilization
45. Create performance comparison table
46. Identify remaining bottlenecks
47. Plan Phase 2 optimizations if needed
48. Document optimization methodology
49. Validate 6M rays/s target achievable

Total: 13 tasks, 1 week

### PHASE 6.2a: GRMHD METADATA & FILE I/O (1 week)

High-Level Task #62: GRMHD metadata and file I/O

Granular Tasks:
50. Design JSON schema for GRMHD metadata
51. Document frame count, grid dimensions, offsets
52. Implement nlohmann_json parser integration
53. Create GRMHDMetadata struct from JSON
54. Implement validation (checksums, offsets)
55. Design binary file format layout
56. Implement mmap-based file access
57. Add endianness detection and conversion
58. Implement partial frame loading (only needed tiles)
59. Create error handling framework
60. Test JSON round-trip serialization
61. Test binary format correctness
62. Validate metadata-to-layout consistency

Total: 13 tasks, 1 week

### PHASE 6.2b: ASYNC TILE LOADING (2 weeks)

High-Level Task #63: Async tile loading and GPU pipeline

Granular Tasks:
63. Design thread pool architecture
64. Implement std::jthread worker management
65. Create work queue (FIFO + priority mode)
66. Implement backpressure (limit queue depth)
67. Add load prediction (prefetch neighbor tiles)
68. Implement cache coherency (CAS updates)
69. Create performance monitoring (queue stats)
70. Implement stress test (many concurrent tiles)
71. Benchmark queue throughput (target 1GB/s)
72. Validate >90% cache hit rate target
73. Design persistent mapped buffer strategy
74. Implement double/triple buffering
75. Add fence synchronization between GPU/CPU
76. Implement async fence wait (don't stall CPU)
77. Create ring buffer allocator (memory pooling)
78. Add concurrent read/write locking
79. Test PBO concurrent access
80. Benchmark PBO throughput (target 1GB/s)
81. Validate <16ms frame load time
82. Implement frame interpolation (temporal blending)
83. Add velocity prediction for smooth motion
84. Test smooth playback without stuttering
85. Measure interpolation error bounds
86. Implement adaptive timestep
87. Create visualization mode (debug overlay)
88. Validate playback quality matches expectations

Total: 26 tasks, 2 weeks

---

## IMPLEMENTATION SEQUENCE

Week 1-2: Phase 5.1-5.2 (Synchrotron + Radiative Transfer)
Week 3: Phase 5.3-5.4 (Spectral + EHT)
Week 4: Phase 5.5-5.6 (LIGO + Validation)
Week 5-6: Phase 6.1a-6.1d (GPU Profiling + Optimization)
Week 7-8: Phase 6.2a-6.2b (GRMHD I/O + Async Loading)

Total: 11-12 weeks

---

## CRITICAL PATH

1. Phase 5.1 (Synchrotron) blocks Phase 5.2 (Radiative Transfer)
2. Phase 5.2 (Radiative Transfer) blocks Phase 5.4 (EHT)
3. Phase 6.1a (Profiling) blocks 6.1b-6.1d (Optimization)
4. Phase 6.2a (I/O) blocks 6.2b (Async Loading)
5. All Phase 5 independent, all Phase 6.1 independent after profiling

---

## SUCCESS CRITERIA

Phase 5:
- Synchrotron GPU shader compiles without errors
- Radiative transfer ray marching <1ms per pixel
- EHT shadow diameter within +/- 5% of M87*/Sgr A*
- LIGO waveform SNR matches GW150914
- All 15+ validation tests passing
- Grade A+ performance on all benchmarks

Phase 6:
- GPU raytracer 1000x speedup (6M rays/s @ 1920x1080)
- GRMHD cache hit rate >90%
- Frame load time <16ms
- Memory footprint <4GB resident
- All 100+ validation tests passing
- Production-ready for large-scale GRMHD visualization

---

## RESOURCE REQUIREMENTS

Hardware:
- NVIDIA GPU with compute capability >7.0 (RTX 20xx+)
- >=16GB CPU RAM for GRMHD loading
- >=100GB storage for large datasets

Software:
- GLSL 4.60+ compiler (part of driver)
- HDF5 libraries (Conan: hdf5/1.14.0)
- CFITSIO for FITS export
- nsight-systems for GPU profiling
- Python 3.10+ with scipy/numpy

Time:
- 11-12 weeks continuous development
- ~2-4 hours per day for optimization/testing
- ~1 week for large-scale integration testing

---

Status: READY TO BEGIN
Next Action: Start Phase 5.1 Task #1
