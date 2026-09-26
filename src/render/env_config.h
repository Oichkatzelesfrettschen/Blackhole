/**
 * @file env_config.h
 * @brief One-time startup configuration from environment variables.
 *
 * applyEnvironmentConfig reads the BLACKHOLE_* environment variables that select
 * the scene (BLACKHOLE_SCENE=blackhole|tesseract), the compare/parity sweep,
 * forced interop-fragment mode, CUDA kernel variant, GPU-timing log,
 * draw-id/multi-draw probes, LUT asset-only mode, the control and performance
 * HUD overlays, and integrator debug flags, writing the results into the
 * matching RenderState config groups. Each block is guarded by its own init
 * flag so it applies once.
 */

#ifndef BLACKHOLE_RENDER_ENV_CONFIG_H
#define BLACKHOLE_RENDER_ENV_CONFIG_H

#include <optional>
#include <string_view>

#include "render/render_state.h"

namespace blackhole {

/** @brief Scene named by a BLACKHOLE_SCENE value: "blackhole" or "tesseract". */
std::optional<RenderState::SceneMode> parseSceneName(std::string_view name);

/**
 * @brief Scene the process starts in: BLACKHOLE_SCENE when it names a scene,
 *        Blackhole otherwise. applyEnvironmentConfig and main's option
 *        validation both read the scene through this function.
 */
RenderState::SceneMode startupSceneMode();

/** @brief Applies BLACKHOLE_* environment-variable overrides to rs at startup. */
void applyEnvironmentConfig(RenderState &rs);

/**
 * @brief Parses one BLACKHOLE_* float value.
 *
 * Accepts a decimal fixed or scientific number with optional surrounding
 * whitespace and one optional leading sign ('+' or '-'). Hexadecimal floats,
 * trailing characters, a repeated sign, "inf", "nan", and magnitudes beyond
 * float range are rejected.
 *
 * @param value environment string, or nullptr
 * @return the parsed value, or 0 when the input is rejected
 */
float parseEnvironmentFloat(const char *value);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_ENV_CONFIG_H
