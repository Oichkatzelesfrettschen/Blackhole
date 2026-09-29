/**
 * @file env_config.h
 * @brief One-time startup configuration from environment variables.
 *
 * applyEnvironmentConfig reads the BLACKHOLE_* environment variables that select
 * the scene (BLACKHOLE_SCENE=blackhole|observer-sky|tesseract), the
 * observer-sky view (BLACKHOLE_OBSERVER_*), the compare/parity sweep, forced
 * interop-fragment mode, CUDA kernel variant, GPU-timing log, draw-id/multi-draw
 * probes, LUT asset-only mode, the control and performance HUD overlays, and
 * integrator debug flags, writing the results into the matching RenderState
 * config groups. Each block is guarded by its own init flag so it applies once.
 */

#ifndef BLACKHOLE_RENDER_ENV_CONFIG_H
#define BLACKHOLE_RENDER_ENV_CONFIG_H

#include <optional>
#include <string_view>
#include <utility>

#include "render/render_state.h"

namespace blackhole {

/** @brief Scene named by a CLI or BLACKHOLE_SCENE value. */
std::optional<RenderState::SceneMode> parseSceneName(std::string_view name);

/**
 * @brief Scene the process starts in: an explicit capture scene, then
 *        BLACKHOLE_SCENE, then Blackhole. Startup and option validation share
 *        this selector.
 */
RenderState::SceneMode startupSceneMode(std::string_view sceneName = {});

/** @brief Applies BLACKHOLE_* overrides with an optional capture scene. */
void applyEnvironmentConfig(RenderState &rs, std::string_view sceneName = {});

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

/**
 * @brief Two finite doubles from "<a>,<b>", or nothing.
 *
 * Feeds BLACKHOLE_OBSERVER_LOOK's explicit "<longitude>,<latitude>" form and
 * BLACKHOLE_OBSERVER_LUMINANCE_RANGE's "<log10 min>,<log10 max>": strtod
 * reads "nan" and "inf" without an error, so both components are checked
 * finite here rather than left to the caller's range comparison, which a
 * non-finite value can pass or fail unpredictably.
 *
 * @param text environment string, or nullptr
 * @return the pair, or nothing when either component is missing, trails
 *         extra characters, or is not finite
 */
std::optional<std::pair<double, double>> parseFinitePair(const char *text);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_ENV_CONFIG_H
