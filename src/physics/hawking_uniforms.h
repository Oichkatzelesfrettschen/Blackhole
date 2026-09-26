/**
 * @file hawking_uniforms.h
 * @brief Values a shader program receives for the Hawking thermal glow.
 *
 * The scalar uniforms do not depend on the LUT textures: with useHawkingLUTs
 * off the shader evaluates T_H and the Planck spectrum directly
 * (hawking_luts.glsl hawkingTemperatureDirect / planckBlackbodyRGB). The LUT
 * path is taken only when both LUT textures are loaded, so a program never
 * samples an unbound or fallback texture as a LUT. HawkingRenderer and the
 * fragment binder both derive their uniforms here, which keeps the fragment
 * and compute paths in parity whether or not the LUTs loaded.
 */

#ifndef PHYSICS_HAWKING_UNIFORMS_H
#define PHYSICS_HAWKING_UNIFORMS_H

namespace physics {

struct HawkingUniformValues {
  float enabled = 0.0f;        ///< hawkingGlowEnabled
  float tempScale = 1.0f;      ///< hawkingTempScale
  float intensity = 1.0f;      ///< hawkingGlowIntensity
  float useLUTs = 0.0f;        ///< useHawkingLUTs, 1 only with both LUTs loaded
  float blackHoleMass = 0.0f;  ///< blackHoleMass [g]
  bool bindLUTTextures = false; ///< bind hawkingTempLUT / hawkingSpectrumLUT
};

[[nodiscard]] constexpr HawkingUniformValues
hawkingUniformValues(bool enabled, float tempScale, float intensity, bool useLUTs,
                     double blackHoleMass, bool lutsReady) {
  HawkingUniformValues v;
  v.enabled = enabled ? 1.0f : 0.0f;
  v.tempScale = tempScale;
  v.intensity = intensity;
  v.useLUTs = (useLUTs && lutsReady) ? 1.0f : 0.0f;
  v.blackHoleMass = static_cast<float>(blackHoleMass);
  v.bindLUTTextures = lutsReady;
  return v;
}

} // namespace physics

#endif // PHYSICS_HAWKING_UNIFORMS_H
