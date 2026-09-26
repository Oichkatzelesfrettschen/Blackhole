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
#include <glm/ext/vector_float3.hpp>

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

/** @brief Lines and HUD glyph scale that fit the label into one render target. */
struct SpeculativeLabelLayout {
  std::vector<std::string> lines;
  float scale = 1.0f;
};

/// Largest HUD scale the label uses; wide targets draw one line at this scale.
inline constexpr float SPECULATIVE_LABEL_MAX_SCALE = 2.0f;
/// Smallest scale the layout prefers before wrapping to more lines.
inline constexpr float SPECULATIVE_LABEL_WRAP_SCALE = 1.0f;
/// Pixel margin between the label background and each edge of the target.
inline constexpr float SPECULATIVE_LABEL_MARGIN = 14.0f;
/// HudOverlay clamps its scale to this floor, so smaller targets wrap instead.
inline constexpr float SPECULATIVE_LABEL_MIN_SCALE = 0.25f;
/// Smallest target width that holds every line: the widest word,
/// "SPECULATIVE", at SPECULATIVE_LABEL_MIN_SCALE with pad (19.75 px) plus
/// both margins.
inline constexpr int SPECULATIVE_LABEL_MIN_TARGET_WIDTH = 48;
/// Smallest target height that holds the block at
/// SPECULATIVE_LABEL_MIN_TARGET_WIDTH: seven word-wrapped lines at
/// SPECULATIVE_LABEL_MIN_SCALE with pad (25.5 px) plus both margins.
inline constexpr int SPECULATIVE_LABEL_MIN_TARGET_HEIGHT = 54;

/**
 * @brief Fit TESSERACT_SPECULATIVE_LABEL into a @p renderWidth x
 *        @p renderHeight target.
 *
 * The label draws top-center with SPECULATIVE_LABEL_MARGIN on every side. At
 * scale s a line of unit-scale width w occupies (w + 4) * s across and n lines
 * occupy n * HudOverlay::lineHeight(s) + 4 * s down, the 4 * s being the
 * 2 * s background pad on each side; the layout keeps both inside the target
 * minus two margins.
 *
 * Tries one line, then two (break after the citation), then three (label,
 * citation, verdict), taking the first that fits at scale >=
 * SPECULATIVE_LABEL_WRAP_SCALE, at the largest scale that fits, capped at
 * SPECULATIVE_LABEL_MAX_SCALE. Otherwise it takes the phrase break that fits
 * at the largest scale, down to HudOverlay's SPECULATIVE_LABEL_MIN_SCALE
 * floor; below that it wraps word by word at the floor scale. Every target
 * at least SPECULATIVE_LABEL_MIN_TARGET_WIDTH x
 * SPECULATIVE_LABEL_MIN_TARGET_HEIGHT holds the whole block; a smaller one
 * clips it. The lines joined with spaces always equal the label.
 */
SpeculativeLabelLayout layoutSpeculativeLabel(int renderWidth, int renderHeight);

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

/// Near clip plane of the tesseract view, in world units from the eye.
inline constexpr float TESSERACT_NEAR_PLANE = 0.05f;
/// Closest tesseract view distance; the View distance slider shares it.
inline constexpr float TESSERACT_MIN_VIEW_DISTANCE = 3.0f;
/// Black-hole camera distance at which a recorded tesseract frame uses the UI
/// view distance unchanged: the CameraState default orbit radius.
inline constexpr float TESSERACT_RECORD_REFERENCE_DISTANCE = 15.0f;
/// Widest tesseract field of view; glm::perspective needs fovy below 180 deg.
inline constexpr float TESSERACT_MAX_FOV_DEG = 179.0f;
/// Narrowest tesseract field of view, which keeps the projection finite.
inline constexpr float TESSERACT_MIN_FOV_DEG = 1.0f;

/** @brief Pose of the record camera that frames a recorded tesseract frame. */
struct TesseractRecordCamera {
  float distance = TESSERACT_RECORD_REFERENCE_DISTANCE; ///< CameraState::distance.
  float fovDeg = 45.0f;                                 ///< CameraState::fov.
};

/** @brief Output clock and camera of one recorded tesseract frame. */
struct TesseractRecordFrame {
  double outputClockSeconds = 0.0; ///< frameIndex / fps of the frame being written.
  TesseractRecordCamera camera;
};

/** @brief Distance and field of view of the tesseract view camera. */
struct TesseractFraming {
  float viewDistance = 8.0f;
  float fovDeg = 50.0f;
};

/**
 * @brief Framing of the tesseract view for one frame.
 *
 * Without @p record the UI viewDistance and fovDeg frame the scene. A recorded
 * frame follows the record camera, which the record profile path,
 * --record-distance, and --record-fov set: its field of view passes through,
 * clamped to [TESSERACT_MIN_FOV_DEG, TESSERACT_MAX_FOV_DEG], and its
 * black-hole distance d maps to viewDistance * d /
 * TESSERACT_RECORD_REFERENCE_DISTANCE. The two scenes share no length unit,
 * so the map is a ratio: the black-hole camera's default distance frames the
 * tesseract as the UI does and a profile dolly scales the tesseract view by
 * the same factor. The distance never falls below
 * TESSERACT_MIN_VIEW_DISTANCE.
 */
TesseractFraming tesseractFraming(float viewDistance, float fovDeg,
                                  const std::optional<TesseractRecordCamera> &record);

/**
 * @brief View-projection for the tesseract scene from the black-hole camera.
 *
 * The eye sits @p viewDistance from the origin along -@p focusDirection, the
 * unit direction from the black-hole camera to its focus, and keeps that
 * camera's orientation: forward cameraBasis[2], up cameraBasis[1]. The
 * unit-scale scene then frames the same way whatever orbit radius the
 * black-hole camera holds, and a showcase-orbit frame offset, which turns the
 * camera toward an aim point beside the focus, moves the tesseract to the
 * screen position the black hole takes at the same field of view. Without an
 * offset the forward axis is the focus direction and the eye looks at the
 * origin.
 *
 * The projection has its near plane at TESSERACT_NEAR_PLANE and an infinite
 * far plane. The pass draws without a depth test, so a far plane would only
 * clip, and the projected scene reaches far: a rotated 4-cube corner has
 * norm 2, so perspective along w reaches |p| of about 6.5 * sceneScale at
 * the 2.1 eye distance, and the stereographic image reaches
 * sqrt((2 - STEREOGRAPHIC_MIN_DENOM) / STEREOGRAPHIC_MIN_DENOM), about
 * 9.95 * sceneScale, both beyond any fixed multiple of the view distance.
 */
glm::mat4 tesseractViewProjection(const glm::mat3 &cameraBasis, const glm::vec3 &focusDirection,
                                  float viewDistance, float fovDeg, float aspect);

/** @brief The view half of tesseractViewProjection: eye placement and orientation. */
glm::mat4 tesseractView(const glm::mat3 &cameraBasis, const glm::vec3 &focusDirection,
                        float viewDistance);

/**
 * @brief Advance the tesseract orientation and pulse for this frame.
 *
 * Interactive frames (@p record empty) advance the stored orientation by
 * advanceOrientation over ds = rotationSpeed * deltaSeconds and the pulse by
 * advancePulseTravel over pulseSpeed * deltaSeconds while
 * rs.tesseract.animate holds. @p deltaSeconds is the simulation step, the
 * caller's InputManager::getEffectiveDeltaTime, so pause holds the scene and
 * the time scale speeds or slows it; it is clamped to 0.25 s per frame.
 * Recorded frames take the state from tesseractMotionAt at the output frame
 * time (time 0 while animation is off), so render throughput and warm-up
 * never reach the frames. Also clamps the library-time sliders into range.
 */
void advanceTesseractMotion(RenderState &rs, float deltaSeconds,
                            const std::optional<TesseractRecordFrame> &record);

/**
 * @brief Render the tesseract scene for this frame into rs.targets.texBlackhole.
 *
 * Advances the motion by advanceTesseractMotion, then draws with the view of
 * tesseractViewProjection and the tesseractFraming of @p record's camera.
 */
void renderTesseractScene(RenderState &rs, const glm::mat3 &cameraBasis,
                          const glm::vec3 &focusDirection, float deltaSeconds,
                          const std::optional<TesseractRecordFrame> &record);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_TESSERACT_TESSERACT_RENDERER_H
