/**
 * @file interop_uniform_registry.h
 * @brief Single-source table for the float uniforms shared by the fragment
 *        and compute render paths.
 *
 * One row here IS the uniform: the X-macro expands into the
 * InteropUniforms struct field, the fragment-path rtti map write, and
 * the compute-path glUniform1f call. Before this table, adding one
 * uniform meant hand-editing those three sites plus the CUDA launch
 * struct, and a typo in a string key failed silently at runtime
 * (debt-ledger.md STRUCT-2 / generator fanned-facts).
 *
 * Row shape: X(field, glslName, defaultValue)
 *   field        C++ member name in InteropUniforms
 *   glslName     uniform name in both GLSL paths (string literal)
 *   defaultValue member initializer
 *
 * Deliberately NOT in this table:
 *   - cameraPos (vec3), cameraBasis (mat3), maxSteps (int): typed
 *     specials whose two paths differ in call shape; they stay explicit
 *     beside the expansions.
 *   - iscoRadius: carried in the struct for the compare-CSV and CUDA
 *     fill, never uploaded as a GL uniform.
 *   - The CUDA BH_LaunchParams fill: it applies semantic transforms
 *     (thresholds, bool packing), not mechanical copies, and its ABI is
 *     guarded separately by bh_device_launch_params_abi().
 */

#ifndef BLACKHOLE_RENDER_INTEROP_UNIFORM_REGISTRY_H
#define BLACKHOLE_RENDER_INTEROP_UNIFORM_REGISTRY_H

// NOLINTBEGIN(cppcoreguidelines-macro-usage)
// WHY: the table must expand into a struct definition, map writes, and
// GL calls; only the preprocessor can stamp all three from one row.

#define BH_INTEROP_UNIFORM_FLOATS(X)                                         \
  X(fovScale, "fovScale", 1.0f)                                              \
  X(timeSec, "time", 0.0f)                                                   \
  X(schwarzschildRadius, "schwarzschildRadius", 0.0f)                        \
  X(kerrSpin, "kerrSpin", 0.0f)                                              \
  X(depthFar, "depthFar", 0.0f)                                              \
  X(stepSize, "interopStepSize", 0.0f)                                       \
  X(adiskEnabled, "adiskEnabled", 0.0f)                                      \
  X(enableRedshift, "enableRedshift", 0.0f)                                  \
  X(useLUTs, "useLUTs", 0.0f)                                                \
  X(useSpectralLUT, "useSpectralLUT", 0.0f)                                  \
  X(useGrbModulation, "useGrbModulation", 0.0f)                              \
  X(lutRadiusMin, "lutRadiusMin", 0.0f)                                      \
  X(lutRadiusMax, "lutRadiusMax", 1.0f)                                      \
  X(redshiftRadiusMin, "redshiftRadiusMin", 0.0f)                            \
  X(redshiftRadiusMax, "redshiftRadiusMax", 1.0f)                            \
  X(spectralRadiusMin, "spectralRadiusMin", 0.0f)                            \
  X(spectralRadiusMax, "spectralRadiusMax", 1.0f)                            \
  X(grbTime, "grbTime", 0.0f)                                                \
  X(grbTimeMin, "grbTimeMin", 0.0f)                                          \
  X(grbTimeMax, "grbTimeMax", 1.0f)                                          \
  X(rteEnabled, "rteEnabled", 0.0f)                                          \
  X(rteOpacityScale, "rteOpacityScale", 0.5f)                                \
  X(debugPreRedshiftBackground, "debugPreRedshiftBackground", 0.0f)          \
  X(debugPreShapingBackground, "debugPreShapingBackground", 0.0f)            \
  X(debugPostShapingBackground, "debugPostShapingBackground", 0.0f)          \
  X(debugShaperInputs, "debugShaperInputs", 0.0f)                            \
  X(debugClosestApproachState, "debugClosestApproachState", 0.0f)            \
  X(debugClosestApproachTimeline, "debugClosestApproachTimeline", 0.0f)      \
  X(debugClosestApproachDirection, "debugClosestApproachDirection", 0.0f)    \
  X(debugEscapedDirection, "debugEscapedDirection", 0.0f)                    \
  X(diskPeakTemperature, "diskPeakTemperature", 6500.0f)                     \
  X(diskBrightness, "diskBrightness", 1.0f)                                  \
  X(diskFluxPeak, "diskFluxPeak", 1.1458947e-4f)

// NOLINTEND(cppcoreguidelines-macro-usage)

#endif // BLACKHOLE_RENDER_INTEROP_UNIFORM_REGISTRY_H
