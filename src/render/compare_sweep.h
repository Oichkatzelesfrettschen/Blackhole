/**
 * @file compare_sweep.h
 * @brief Compute-vs-fragment parity sweep state machine for the render loop.
 *
 * The sweep walks the K_COMPARE_PRESETS table: it saves the live camera once,
 * drives each preset's camera/spin, waits comparePresetSettleFrames for the
 * scene to settle, then flags a snapshot capture; when the presets are
 * exhausted (or compute shaders are unavailable) it stops and requests a
 * restore. advanceComparePresetSweep runs before the scene render (it sets the
 * camera the render consumes); restoreCompareSweepState runs after, once the
 * final snapshot has been taken, to put the live camera back. The snapshot
 * capture and CSV writing themselves live at the dispatch site and use the
 * compare_harness primitives.
 */

#ifndef BLACKHOLE_RENDER_COMPARE_SWEEP_H
#define BLACKHOLE_RENDER_COMPARE_SWEEP_H

#include <glbinding/gl/types.h>

#include "render/interop_uniforms.h"

class InputManager;

namespace blackhole {

struct RenderState;

/**
 * @brief Per-frame inputs the parity snapshot needs beyond RenderState: the two
 *        parity render targets, the effective feature flags the frame rendered
 *        with, the interop uniform values both paths received, and the frame's
 *        wall-clock time. Populated at the dispatch site from the same locals
 *        the render used, so the CSV records exactly what was drawn.
 */
struct CompareParityInputs {
  gl::GLuint fragmentTarget = 0;           ///< Fragment-path parity target (texBlackholeCompare or texBlackhole).
  gl::GLuint computeTarget = 0;            ///< Compute-path parity target (the other of the two).
  bool compareActive = false;             ///< Compute/fragment parity capture active this frame.
  bool compareBaselineActive = false;     ///< Baseline-suppression frame (features forced off).
  bool backgroundEnabledEffective = false;///< Background layer enabled this frame.
  bool noiseReady = false;                ///< Disk noise volume selected AND present this frame.
  bool grmhdEnabled = false;              ///< GRMHD volume selected AND ready this frame.
  bool spectralEnabled = false;           ///< Spectral LUT selected AND ready this frame.
  bool grbModulationEnabled = false;      ///< GRB modulation LUT selected AND ready this frame.
  bool enablePhotonSphereEffective = false;///< Photon-sphere accent enabled this frame.
  float grbTimeSeconds = 0.0f;            ///< GRB modulation phase time this frame.
  double timeSec = 0.0;                   ///< Wall-clock time stamped into the summary CSV row.
  InteropUniforms interop;                ///< Uniform values both render paths received this frame.
};

/** @brief Advances the compare-preset sweep for the current frame: saves the
 *         live camera on entry, applies the active preset, counts settle frames,
 *         and flags captureCompareSnapshot at the settle boundary. Disables the
 *         sweep (requesting a restore) when compute shaders are unavailable or
 *         the presets are exhausted. */
void advanceComparePresetSweep(RenderState &rs, InputManager &input, bool computeShadersAvailable);

/** @brief Restores the camera/spin saved at the start of the sweep, once the
 *         sweep has ended and its final snapshot has been captured. No-op until
 *         then. */
void restoreCompareSweepState(RenderState &rs, InputManager &input);

/**
 * @brief Ends any compare sweep at once and puts the saved camera back.
 *
 * The sweep drives the black-hole integrator only; main calls this on every
 * frame another scene renders, so a sweep armed or running when the scene
 * changes stops, its preset camera and spin give way to the saved live ones,
 * and no pending restore or snapshot survives into a later black-hole frame.
 * No-op when no sweep is armed and nothing is saved.
 */
void cancelComparePresetSweep(RenderState &rs, InputManager &input);

/**
 * @brief The frame's sweep step for the active scene: advanceComparePresetSweep
 *        in the black-hole scene, cancelComparePresetSweep in any other.
 */
void updateComparePresetSweep(RenderState &rs, InputManager &input, bool computeShadersAvailable);

/** @brief Runs the compute-vs-fragment parity diff for the current frame: on the
 *         auto-capture stride it flags a snapshot, samples the strided texture
 *         diff, and on a flagged snapshot reads both parity targets, computes
 *         full DiffStats and the outlier gate, and writes the PPM/summary/uniform
 *         artifacts. When parity capture is inactive it clears the compare stats
 *         so the UI reads clean. */
void captureCompareParity(RenderState &rs, const CompareParityInputs &in);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_COMPARE_SWEEP_H
