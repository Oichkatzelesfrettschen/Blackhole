# Phase 6: GPU Acceleration & Full GRMHD - Research Synthesis

Date: 2026-01-29
Status: Research Complete - Ready for Implementation
Scope: 1000x GPU raytracer + full GRMHD streaming (800-1200 LOC)

---

## Existing Infrastructure

### 1. Compute Shader Foundation (shader/geodesic_trace.comp)
Status: COMPLETE (verified RK4 integration)

Components:
- RK4 integration for null geodesics
- Schwarzschild and Kerr metric support
- Redshift calculations
- LUT-based disk emissivity
- Work group config: 16x16 local threads
- Output to RGBA32F texture
- Full feature integration (spectral, GRB modulation)

Verified includes:
- include/verified/schwarzschild.glsl
- include/verified/rk4.glsl
- include/verified/geodesic.glsl
- include/verified/kerr.glsl
- include/verified/null_constraint.glsl

Current Performance:
- Schwarzschild raytracer: 6,317 rays/s (CPU baseline for 2000x2000 rays)
- GPU potential: 1000x speedup → 6M rays/s @ 1920x1080

### 2. GRMHD Streaming Stub (Phase 4 Output)
Status: COMPLETE Architecture, Stub Implementation

Components:
- TileCache: LRU eviction, thread-safe
- GRMHDStreamer: Async loader architecture
- Octree spatial indexing (8 levels)
- Texture array integration (3D RGBA32F)

Missing Implementation:
1. JSON metadata parsing (nlohmann/json ready in Conan)
2. Binary file memory mapping (mmap or fstream)
3. Thread pool for async loading
4. OpenGL PBO async GPU upload

---

## Phase 6.1: GPU Compute Raytracer (1000x speedup)

Goal: Achieve 6M rays/s @ 1920x1080 via compute shader RK4

Tasks:
1. Analyze geodesic_trace.comp bottlenecks
2. Profile current implementation
3. Optimize register usage (target <64 per thread)
4. Implement tiled dispatch strategy
5. Add async compute + graphics sync
6. Benchmark baseline vs optimized
7. Document GPU optimization patterns

Expected Speedup Breakdown:
- CPU serial: 6.3K rays/s (baseline)
- GPU parallel: 6M rays/s target
- Speedup factor: ~1000x
- Per-warp utilization: >90%
- Memory bandwidth: ~100GB/s (PCIe 3.0 cap)

Optimization Techniques:
- Reduce register pressure (spill → local memory)
- Coalesce memory accesses (tile-friendly reads)
- Minimize thread divergence (shared branching)
- Use fast math (--use_fast_math equivalent)
- Pipeline optimization (hide latency)

Key Metrics:
- Occupancy: target >60% (compute intensity allows lower)
- Memory efficiency: >70% bandwidth utilization
- Divergence: <10% thread divergence penalty
- Warp efficiency: >90% active lanes

---

## Phase 6.2: Full GRMHD Streaming (800-1200 LOC)

Goal: Production-ready streaming pipeline for multi-GB GRMHD datasets

Components to Implement:

1. JSON Metadata Parsing (120-150 LOC)
   - Frame count, grid dimensions
   - Byte offsets for each frame
   - Channel names (rho, u, v^r, v^phi)
   - Time stamps for interpolation

2. Binary File I/O (150-200 LOC)
   - Memory mapping with mmap or fstream
   - Byte-order handling (endianness)
   - Partial frame loading (only needed tiles)
   - Error handling and validation

3. Async Tile Loader (200-250 LOC)
   - Thread pool (std::jthread or Taskflow)
   - Work queue management
   - Priority queue (load current/neighbor tiles first)
   - Backpressure handling (don't overload queue)

4. GPU PBO Upload (100-150 LOC)
   - Persistent mapped buffer objects
   - Async transfer with fences
   - Double/triple buffering
   - Synchronization primitives

5. Frame Interpolation (100-150 LOC)
   - Temporal blending between frames
   - Velocity prediction
   - Caching prev/current/next frames

Expected Performance:
- Cache hit rate: >90% during smooth playback
- Load time: <16ms per frame (60fps budget)
- Memory: <4GB resident (for 50GB+ datasets)
- Throughput: 1GB/s tile bandwidth

---

## Phase 6.3: Radiative Transfer Integration (1-2 weeks)

Goal: Full spectral synthesis pipeline

Components:
1. Synchrotron GPU integration
2. Comptonization effects
3. Iron line profile (Laor 1991)
4. Multi-frequency ray marching
5. Optical depth tracking
6. Polarization output

---

## Complete Phase 6 TODO List (70 Tasks)

### Phase 6.1: GPU Raytracer Analysis (Tasks 1-10)

1. [ ] Profile geodesic_trace.comp with nsight-systems
2. [ ] Identify register spilling locations
3. [ ] Measure occupancy (target >60%)
4. [ ] Analyze memory access patterns
5. [ ] Measure divergence via warp statistics
6. [ ] Identify latency bottlenecks
7. [ ] Document baseline performance metrics
8. [ ] Create optimization roadmap
9. [ ] Set performance targets per component
10. [ ] Design benchmark framework

### Phase 6.1: Register Optimization (Tasks 11-20)

11. [ ] Refactor StateVector to pack tighter
12. [ ] Use vec2/vec4 instead of separate floats where possible
13. [ ] Move rarely-used variables to shared memory
14. [ ] Implement register spill analysis
15. [ ] Reduce intermediate calculations
16. [ ] Inline critical functions
17. [ ] Test occupancy impact
18. [ ] Measure performance delta
19. [ ] Document optimization tradeoffs
20. [ ] Finalize register-optimized version

### Phase 6.1: Memory Optimization (Tasks 21-30)

21. [ ] Implement coalesced memory access
22. [ ] Add shared memory for frequent reads
23. [ ] Optimize LUT cache lines
24. [ ] Use local memory for register spills
25. [ ] Implement prefetching (if supported)
26. [ ] Test memory bandwidth utilization
27. [ ] Profile cache hit rates
28. [ ] Measure latency hiding
29. [ ] Optimize stride patterns
30. [ ] Finalize memory-optimized version

### Phase 6.1: Control Flow Optimization (Tasks 31-40)

31. [ ] Analyze branch divergence
32. [ ] Reduce conditional branches
33. [ ] Use ballot/vote functions for divergence
34. [ ] Implement uniform code paths
35. [ ] Test warp efficiency
36. [ ] Profile divergence penalty
37. [ ] Optimize hot loops
38. [ ] Reduce function call overhead
39. [ ] Flatten nested conditionals
40. [ ] Finalize control-optimized version

### Phase 6.1: Async Compute Pipeline (Tasks 41-50)

41. [ ] Design async compute + graphics sync
42. [ ] Implement command buffer management
43. [ ] Add fence/event synchronization
44. [ ] Implement work stealing scheduler
45. [ ] Add task prioritization
46. [ ] Benchmark async overhead
47. [ ] Implement GPU-GPU sync
48. [ ] Test zero-copy techniques
49. [ ] Profile memory bandwidth
50. [ ] Finalize async pipeline

### Phase 6.1: Performance Validation (Tasks 51-60)

51. [ ] Create synthetic ray trace test
52. [ ] Benchmark baseline (geodesic_trace.comp as-is)
53. [ ] Benchmark after register optimization
54. [ ] Benchmark after memory optimization
55. [ ] Benchmark after control flow optimization
56. [ ] Benchmark with async pipeline
57. [ ] Compare CPU vs GPU performance
58. [ ] Measure actual occupancy achieved
59. [ ] Measure actual memory bandwidth
60. [ ] Validate 1000x speedup target

### Phase 6.2: JSON Metadata Parsing (Tasks 61-65)

61. [ ] Design JSON schema for GRMHD metadata
62. [ ] Implement nlohmann_json integration
63. [ ] Create frame metadata structure
64. [ ] Implement parser with validation
65. [ ] Test round-trip JSON serialization

### Phase 6.2: Binary File I/O (Tasks 66-70)

66. [ ] Design binary format layout
67. [ ] Implement mmap-based file access
68. [ ] Add endianness detection/conversion
69. [ ] Implement partial frame loading
70. [ ] Create error handling framework

### Phase 6.2: Async Tile Loading (Tasks 71-80)

71. [ ] Design thread pool architecture
72. [ ] Implement worker thread management
73. [ ] Create work queue (FIFO + priority)
74. [ ] Implement backpressure (limit queue depth)
75. [ ] Add load prediction (prefetch neighbors)
76. [ ] Implement cache coherency
77. [ ] Add performance monitoring
78. [ ] Create stress test (many tiles)
79. [ ] Benchmark queue throughput
80. [ ] Validate >90% cache hit rate target

### Phase 6.2: GPU PBO Upload (Tasks 81-90)

81. [ ] Design persistent mapped buffer strategy
82. [ ] Implement double buffering
83. [ ] Add fence synchronization
84. [ ] Implement async fence wait
85. [ ] Create ring buffer allocator
86. [ ] Add memory pooling
87. [ ] Implement error detection
88. [ ] Test concurrent reads/writes
89. [ ] Benchmark PBO throughput
90. [ ] Validate <16ms load time

### Phase 6.2: Frame Interpolation (Tasks 91-100)

91. [ ] Design temporal blending scheme
92. [ ] Implement frame cache (prev/curr/next)
93. [ ] Create interpolation kernel
94. [ ] Add velocity prediction
95. [ ] Implement extrapolation (forward predict)
96. [ ] Test smooth playback
97. [ ] Measure interpolation error
98. [ ] Add adaptive timestep
99. [ ] Create visualization mode
100. [ ] Validate playback quality

---

## Critical Implementation Sequence

Phase 6.1 (GPU Raytracer):
Week 1-2: Profiling + register optimization
Week 3: Memory + control flow optimization
Week 4: Async pipeline integration
Week 5: Performance validation + tuning

Phase 6.2 (GRMHD Streaming):
Week 6: JSON + I/O implementation
Week 7: Async loader (thread pool)
Week 8: PBO upload pipeline
Week 9: Frame interpolation
Week 10: Integration testing + optimization

---

## Performance Targets

GPU Raytracer:
- Throughput: 6M rays/s @ 1920x1080
- Latency: <16ms per frame
- Occupancy: >60%
- Memory bandwidth: >70%
- Power efficiency: <10W GPU power

GRMHD Streaming:
- Cache hit rate: >90%
- Frame load time: <16ms
- Memory footprint: <4GB resident
- Tile throughput: 1GB/s
- Concurrent frames: 3 (prev/curr/next)

---

## Estimated Effort

Phase 6.1 GPU Raytracer: 3-4 weeks, 500-800 LOC
Phase 6.2 GRMHD Streaming: 4-5 weeks, 800-1200 LOC
Phase 6.3 Radiative Transfer: 2-3 weeks, 600-800 LOC

Total Phase 6: 9-12 weeks, 1900-2800 LOC

---

Research Status: COMPLETE
Implementation Status: Ready to begin
Blockers: None (all dependencies available)

Next Action: Begin Task #1 (Profile geodesic_trace.comp)
