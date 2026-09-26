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
#include <optional>
#include <string>
#include <string_view>
#include <vector>

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

/** @brief Lines and HUD glyph scale that fit the label into one render width. */
struct SpeculativeLabelLayout {
  std::vector<std::string> lines;
  float scale = 1.0f;
};

/// Largest HUD scale the label uses; wide targets draw one line at this scale.
inline constexpr float SPECULATIVE_LABEL_MAX_SCALE = 2.0f;
/// Smallest scale the layout prefers before wrapping to more lines.
inline constexpr float SPECULATIVE_LABEL_WRAP_SCALE = 1.0f;
/// Pixel margin between the label background and each side of the target.
inline constexpr float SPECULATIVE_LABEL_MARGIN = 14.0f;
/// HudOverlay clamps its scale to this floor, so narrower targets wrap instead.
inline constexpr float SPECULATIVE_LABEL_MIN_SCALE = 0.25f;

/**
 * @brief Fit TESSERACT_SPECULATIVE_LABEL into @p renderWidth pixels.
 *
 * Tries one line, then two (break after the citation), then three (label,
 * citation, verdict), taking the first whose widest line, plus the 2*scale
 * background pad on each side and SPECULATIVE_LABEL_MARGIN on each side,
 * fits at scale >= SPECULATIVE_LABEL_WRAP_SCALE; the scale is the largest
 * that fits, capped at SPECULATIVE_LABEL_MAX_SCALE. Narrower targets keep
 * three lines and shrink the scale to fit, down to HudOverlay's 0.25 floor;
 * below that they wrap word by word at the floor scale.
 * The lines joined with spaces always equal the label.
 */
SpeculativeLabelLayout layoutSpeculativeLabel(int renderWidth);

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

  /**
   * @brief Recompile shader/tesseract.{vert,frag} for shader hot reload.
   *
   * On success the new program replaces the old one and the call returns
   * true. On a read, compile, or link failure the last working program stays
   * in use and the call returns false. A pass that has not drawn yet has no
   * program and compiles on its first render(), so the call returns true.
   */
  bool reloadShaders();

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
 * Interactive frames (@p outputClockSeconds empty) advance the stored
 * orientation by advanceOrientation over ds = rotationSpeed * deltaSeconds and
 * the pulse by advancePulseTravel over pulseSpeed * deltaSeconds while
 * rs.tesseract.animate holds; deltaSeconds is clamped to 0.25 s per frame.
 * Recorded frames pass the output frame time and take the state from
 * tesseractMotionAt at that time (time 0 while animation is off), so render
 * throughput and warm-up never reach the frames. The view comes from
 * tesseractViewProjection.
 */
void renderTesseractScene(RenderState &rs, const glm::mat3 &cameraBasis, float deltaSeconds,
                          std::optional<double> outputClockSeconds);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_TESSERACT_TESSERACT_RENDERER_H
