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

class InputManager;

namespace blackhole {

struct RenderState;

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

} // namespace blackhole

#endif // BLACKHOLE_RENDER_COMPARE_SWEEP_H
