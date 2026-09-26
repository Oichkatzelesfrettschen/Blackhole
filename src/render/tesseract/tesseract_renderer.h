/**
 * @file tesseract_renderer.h
 * @brief GL pass for the speculative tesseract scene mode.
 *
 * Draws the segments of buildSceneSegments as instanced camera-facing ribbons
 * (shader/tesseract.vert + shader/tesseract.frag) into the scene HDR target,
 * so the bloom and ACES tonemap passes treat the scene like the black-hole
 * frame. The pass owns its program, vertex array, instance buffer, and
 * framebuffer; its uniforms bind directly and stay outside the interop
 * uniform registry, which describes the geodesic integrator alone.
 */

#ifndef BLACKHOLE_RENDER_TESSERACT_TESSERACT_RENDERER_H
#define BLACKHOLE_RENDER_TESSERACT_TESSERACT_RENDERER_H

#include <array>
#include <string_view>

#include <glbinding/gl/types.h>

#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/matrix_float4x4.hpp>

namespace blackhole {

struct RenderState;

/**
 * @brief Provenance label the tesseract scene shows on screen at all times.
 *
 * The scene illustrates a speculative idea from popular science. The label is
 * drawn into the presented texture, so the viewport, --record-frames, and
 * --export-frame outputs carry it; --export-raw-frame reads the unlabeled HDR
 * target and exportFrameOnce refuses it in this scene.
 */
inline constexpr std::string_view TESSERACT_SPECULATIVE_LABEL =
    "SPECULATIVE (Thorne, The Science of Interstellar ch. 29-31): not physics";

/** @brief Per-frame parameters of one tesseract pass. */
struct TesseractFrameInputs {
  gl::GLuint targetTexture = 0;
  int width = 0;
  int height = 0;
  glm::mat4 viewProjection{1.0f};
  std::array<float, 16> rotation{}; ///< Column-major SO(4) matrix (toColumnMajor).
  int projectionMode = 0;           ///< 0 perspective along w, 1 stereographic.
  float perspectiveDistance = 3.0f; ///< Eye position d on the w axis.
  float sceneScale = 1.0f;          ///< World units per projected unit.
  float timeSpan = 10.0f;           ///< Library time extent T.
  float litMoment = 0.0f;           ///< Library time of the lit moment.
  float litWidth = 0.5f;            ///< Gaussian width of the lit moment.
  float pulseTime = 0.0f;           ///< Library time of the gravity-message pulse.
  float pulseWidth = 0.35f;         ///< Gaussian width of the pulse.
  bool pulseEnabled = false;        ///< Draw the pulse.
  int pulseStrand = 0;              ///< Strand (feature index) carrying the pulse.
  float lineWidthPx = 2.5f;         ///< Ribbon width in pixels.
  float edgeIntensity = 1.0f;       ///< Tesseract edge radiance scale.
  float strandIntensity = 1.0f;     ///< World-tube radiance scale.
  float sliceIntensity = 1.0f;      ///< Lit-moment room outline radiance scale.
};

/**
 * @brief Owner of the tesseract pass GL objects.
 *
 * GL objects are created on the first render() and released by shutdown(),
 * which must run while the context is current; the destructor calls it for
 * handles still live.
 */
class TesseractRenderer {
public:
  TesseractRenderer() = default;
  ~TesseractRenderer();
  TesseractRenderer(const TesseractRenderer &) = delete;
  TesseractRenderer &operator=(const TesseractRenderer &) = delete;
  TesseractRenderer(TesseractRenderer &&) = delete;
  TesseractRenderer &operator=(TesseractRenderer &&) = delete;

  /** @brief Clear the target and draw every scene segment into it. */
  void render(const TesseractFrameInputs &inputs);

  /** @brief Release all GL objects; safe to call repeatedly. */
  void shutdown();

private:
  void ensureResources(float timeSpan);

  gl::GLuint program_ = 0;
  gl::GLuint vao_ = 0;
  gl::GLuint vbo_ = 0;
  gl::GLuint fbo_ = 0;
  gl::GLsizei instanceCount_ = 0;
  float builtTimeSpan_ = -1.0f;
};

/**
 * @brief View-projection for the tesseract scene from the frame camera basis.
 *
 * Looks at the origin along the camera's forward axis (cameraBasis[2]) with
 * its up axis (cameraBasis[1]) from @p viewDistance, so the unit-scale scene
 * frames the same way whatever orbit radius the black-hole camera holds.
 */
glm::mat4 tesseractViewProjection(const glm::mat3 &cameraBasis, float viewDistance, float fovDeg,
                                  float aspect);

/**
 * @brief Render the tesseract scene for this frame into rs.targets.texBlackhole.
 *
 * While rs.tesseract.animate holds, the stored orientation advances by
 * advanceOrientation over ds = rotationSpeed * deltaSeconds and the pulse by
 * advancePulseTravel over pulseSpeed * deltaSeconds; with it off both hold
 * still. deltaSeconds is clamped to 0.25 s per frame. The view comes from
 * tesseractViewProjection.
 */
void renderTesseractScene(RenderState &rs, const glm::mat3 &cameraBasis, float deltaSeconds);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_TESSERACT_TESSERACT_RENDERER_H
