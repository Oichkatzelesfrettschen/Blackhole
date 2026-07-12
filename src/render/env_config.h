/**
 * @file env_config.h
 * @brief One-time startup configuration from environment variables.
 *
 * applyEnvironmentConfig reads the BLACKHOLE_* environment variables that select
 * the compare/parity sweep, forced interop-fragment mode, CUDA kernel variant,
 * GPU-timing log, draw-id/multi-draw probes, LUT asset-only mode, the control
 * and performance HUD overlays, and integrator debug flags, writing the results
 * into the matching RenderState config groups. Each block is guarded by its own
 * init flag so it applies once.
 */

#ifndef BLACKHOLE_RENDER_ENV_CONFIG_H
#define BLACKHOLE_RENDER_ENV_CONFIG_H

namespace blackhole {

struct RenderState;

/** @brief Applies BLACKHOLE_* environment-variable overrides to rs at startup. */
void applyEnvironmentConfig(RenderState &rs);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_ENV_CONFIG_H
