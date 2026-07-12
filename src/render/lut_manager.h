/**
 * @file lut_manager.h
 * @brief Radiative-transfer LUT lifecycle owned outside the frame loop.
 *        updateLuts reconciles the emissivity/redshift/photon-glow/disk-density
 *        GL textures against the current spin and disk density, preferring
 *        pre-baked CSV assets and falling back to generated LUTs. The spectral
 *        and GRB-modulation loaders read their CSV + JSON-meta asset pairs on
 *        demand; both resolve paths through platform::resourcePath.
 */

#ifndef BLACKHOLE_RENDER_LUT_MANAGER_H
#define BLACKHOLE_RENDER_LUT_MANAGER_H

#include <string>
#include <vector>

namespace blackhole {

struct RenderState;

/**
 * @brief Rebuilds the emissivity/redshift/photon-glow/disk-density LUT textures
 *        when spin or disk density has changed, or on first use. Prefers baked
 *        asset LUTs when their spin matches; honours asset-only mode; otherwise
 *        generates them. Writes all texture handles and radius/spin metadata
 *        into rs.luts (and shares emissivity/redshift with the CUDA backend).
 */
void updateLuts(RenderState &rs, float spin, float densityV);

/** @brief Loads the ray-tracing spectral LUT (rt_spectrum) and its wavelength
 *         bounds; returns false if the CSV or JSON-meta asset is missing. */
[[nodiscard]] bool loadSpectralLutAssets(std::vector<float> &values, float &wavelengthMin,
                                         float &wavelengthMax);

/** @brief Loads the GRB modulation LUT and its time bounds; returns false if the
 *         CSV or JSON-meta asset is missing. */
[[nodiscard]] bool loadGrbModulationLutAssets(std::vector<float> &values, float &timeMin,
                                              float &timeMax);

/** @brief First-use GRB-modulation texture upload: on the try latch, loads the
 *         GRB modulation LUT assets and, on success, uploads the modulation
 *         texture and seeds the manual-time value. */
void loadGrbModulationLut(RenderState &rs);

/** @brief First-use uploads for the spectral ray-tracing LUT, the synchrotron
 *         G(x) LUT, and the Hawking LUTs, each guarded by its own latch and
 *         sharing the spectral/synchG textures with the CUDA backend. */
void loadSpectralSynchHawkingLuts(RenderState &rs);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_LUT_MANAGER_H
