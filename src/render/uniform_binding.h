/**
 * @file uniform_binding.h
 * @brief Shared raytracer uniform binders. Both interop binders expand the
 *        BH_INTEROP_UNIFORM_FLOATS registry so the fragment (RenderToTextureInfo)
 *        and compute (glUniform) GPU paths cannot drift on which float uniforms
 *        exist; the Hawking binder forwards glow parameters to a program.
 */

#ifndef BLACKHOLE_RENDER_UNIFORM_BINDING_H
#define BLACKHOLE_RENDER_UNIFORM_BINDING_H

#include <glbinding/gl/types.h>

#include "physics/hawking_renderer.h"
#include "render.h"
#include "render/interop_uniforms.h"
#include "render/render_state.h"

namespace blackhole {

/**
 * @brief Per-frame derived render inputs the uniform binders read alongside the
 *        persistent RenderState. These are transients recomputed every frame
 *        (compare-baseline gating, LUT readiness); they are deliberately not
 *        stored in RenderState.
 */
struct FrameBindingInputs {
  bool adiskEnabledEffective = false;      ///< adiskEnabled AND not compare-baseline frame.
  bool enableRedshiftEffective = false;    ///< enableRedshift AND not compare-baseline frame.
  bool backgroundEnabledEffective = false; ///< backgroundEnabled AND not compare-baseline frame.
  bool enablePhotonSphereEffective = false;///< enablePhotonSphere AND not compare-baseline frame.
  float backgroundIntensity = 0.0f;        ///< settings.backgroundIntensity for this frame.
  bool lutReady = false;                   ///< Emissivity + redshift LUT textures both present.
  bool spectralEnabled = false;            ///< Spectral LUT selected AND ready this frame.
  bool grbModulationEnabled = false;       ///< GRB modulation LUT selected AND ready this frame.
  bool noiseReady = false;                 ///< Disk noise volume selected AND present this frame.
  bool grmhdEnabled = false;               ///< GRMHD volume selected AND ready this frame.
  bool adiskParticleEffective = false;     ///< adiskParticle AND not compare-baseline frame.
  bool compareActive = false;              ///< Compute/fragment parity capture active (interop parity mode).
  gl::GLuint grmhdTexId = 0;               ///< GRMHD 3D texture to bind (streaming or packed).
};

/**
 * @brief Fills the fragment-path float and typed uniforms on @p rtti from the
 *        interop registry, plus the parity-mode and Hawking-glow extras.
 */
void applyInteropUniforms(RenderToTextureInfo &rtti, const InteropUniforms &interop,
                          bool parityMode, bool hawkingEnabled, float hawkingTempScale,
                          float hawkingIntensity, bool hawkingUseLUTs, double blackHoleMass);

/**
 * @brief Sets the same registry float uniforms plus typed specials (resolution,
 *        camera basis/position, max steps) on the bound compute @p program.
 */
void applyInteropComputeUniforms(gl::GLuint program, const InteropUniforms &interop, int width,
                                 int height);

/**
 * @brief Binds the compute-path wiregrid, Stokes, LUT/cubemap/background-layer
 *        textures and background scalars on @p program, in parity with the
 *        fragment path. Texture units are assigned sequentially from 0.
 */
void bindComputeUniforms(gl::GLuint program, const RenderState &rs, const FrameBindingInputs &in);

/**
 * @brief Fills the load-order-independent fragment-path uniforms on @p rtti:
 *        the post-derivation texture/scalar re-writes, the registry+Hawking
 *        floats via applyInteropUniforms, and the wiregrid/Stokes/disk floats.
 *        The emissivity-family LUT bindings stay at the caller's first-pass
 *        site because they are coupled to the between-passes updateLuts handle
 *        reassignment.
 */
void bindFragmentUniforms(RenderToTextureInfo &rtti, const RenderState &rs,
                          const InteropUniforms &interop, const FrameBindingInputs &in);

/**
 * @brief Forwards Hawking-glow parameters to @p program via
 *        HawkingRenderer::setShaderUniforms; a no-op when the renderer is not ready.
 */
void applyHawkingUniforms(gl::GLuint program, const physics::HawkingRenderer &renderer, bool enabled,
                          float tempScale, float intensity, bool useLUTs, double blackHoleMass);

#if BLACKHOLE_HAS_CUDA
/**
 * @brief Fills a BH_LaunchParams for the CUDA raytracer lane from @p interop,
 *        persistent @p rs, and the per-frame @p in transients. The caller owns
 *        the dispatch seam (ensureInit/registration/renderFrame).
 */
void bindCudaLaunchParams(BH_LaunchParams &cp, const RenderState &rs,
                          const InteropUniforms &interop, const FrameBindingInputs &in);
#endif

} // namespace blackhole

#endif // BLACKHOLE_RENDER_UNIFORM_BINDING_H
