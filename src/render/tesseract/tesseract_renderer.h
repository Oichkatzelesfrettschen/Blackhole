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
#include <glm/ext/vector_float2.hpp>
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
/// Farthest interactive tesseract view distance; the View distance slider shares it.
inline constexpr float TESSERACT_MAX_VIEW_DISTANCE = 20.0f;
/// Smallest eye distance on the w axis the perspective projection uses; the
/// "Eye w distance" slider stops at 2.2.
inline constexpr float TESSERACT_MIN_PERSPECTIVE_DISTANCE = 2.1f;
/**
 * @brief Tone exposure of every tesseract recording, whatever the profile.
 *
 * The record exposure rule (record_mode.h) with the tesseract's own target.
 * The profiles' exposures place the disk's luminance L99 at display 0.9,
 * which the emissive ribbons do not share, so applyRecordProfileSetup
 * replaces them in the tesseract scene. The ribbons are saturated colors
 * that ACES clips per channel, so the statistic is the 99th percentile of the
 * per-pixel max channel over ribbon pixels of the raw frame
 * (tesseract_exposure_gl_test): 1.97 to 2.68 across the default animation,
 * median 2.4. ACES^-1(0.9^2.35) = 0.900 over 2.4 maps the brightest ribbons
 * to display 0.875-0.912 at the showcase-orbit gamma and the 0.012 clear
 * color to 0.059; cinematic's gamma 2.25 maps both slightly higher.
 */
inline constexpr float TESSERACT_RECORD_EXPOSURE = 0.375f;
/// Fraction of a recorded frame's room between the tesseract's center and the
/// nearer frame edge that the bounding sphere fills on the tighter axis, below
/// 1 so the sphere, a conservative bound, stays in frame (tesseractFraming).
inline constexpr float TESSERACT_RECORD_FILL = 0.85f;
/// Widest tesseract field of view; glm::perspective needs fovy below 180 deg.
inline constexpr float TESSERACT_MAX_FOV_DEG = 179.0f;
/// Narrowest tesseract field of view, which keeps the projection finite.
inline constexpr float TESSERACT_MIN_FOV_DEG = 1.0f;
/// Smallest forward cosine tesseractFocusTangent divides by.
inline constexpr float TESSERACT_MIN_FOCUS_COSINE = 1e-3f;

/** @brief Record camera lens and focus position that frame a recorded tesseract frame. */
struct TesseractRecordCamera {
  float fovDeg = 45.0f; ///< CameraState::fov.
  /// Tangents of the angles from the view axis to the tesseract's center,
  /// across and up (tesseractFocusTangent); zero on a centered frame.
  glm::vec2 focusTangent{0.0f};
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
 * @brief Radius of a sphere about the origin that holds the projected scene.
 *
 * Every scene point lies in the norm-2 ball of R^4, and rotations keep it
 * there. Perspective along w maps that ball inside radius
 * 2 d / sqrt(d^2 - 4) (reached at w = 4 / d) for the eye distance
 * d = max(@p perspectiveDistance, TESSERACT_MIN_PERSPECTIVE_DISTANCE).
 * Stereographic projection has no useful bound (sqrt((2 - m) / m) for the
 * clamp m = STEREOGRAPHIC_MIN_DENOM is about 9.95), so it uses the radius of
 * the fully lit image, sqrt((2 - f) / f) = 3 for f = STEREOGRAPHIC_FADE_END;
 * only tails fading toward the pole reach past it. Both scale by
 * @p sceneScale.
 */
float tesseractBoundingRadius(bool stereographic, float sceneScale, float perspectiveDistance);

/**
 * @brief Framing of the tesseract view for one frame.
 *
 * Without @p record the UI viewDistance and fovDeg frame the scene. A recorded
 * frame takes the record camera's field of view, clamped to
 * [TESSERACT_MIN_FOV_DEG, TESSERACT_MAX_FOV_DEG], and places the eye so the
 * sphere of @p boundingRadius R fills TESSERACT_RECORD_FILL k of the room
 * between its center and the nearer frame edge on the tighter axis. The field
 * of view is vertical, so the half-extents subtend T_y = tan(fov / 2) up and
 * T_x = @p aspect T_y across. The record camera's focusTangent c places the
 * center off the view axis when a showcase-orbit frame offset turns the
 * camera (tesseractView); its magnitude is clamped to k T per axis, so a
 * center past the frame edge frames as if it sat at k T. Per axis the
 * silhouette's outer edge must reach no farther than the tangent
 * E = |c| + k (T - |c|): the planes through the eye that hold the other image
 * axis and touch the sphere lie asin(R / rho) either side of the center's
 * angle atan(|c|), where rho = D sqrt(1 + c_axis^2) / sqrt(1 + |c|^2) is the
 * center's distance from that axis, so
 * D = R / sin(atan(E) - atan(|c|)) * sqrt(1 + |c|^2) / sqrt(1 + c_axis^2),
 * and the eye takes the larger of the two axes' distances. A centered sphere
 * reduces to D = R sqrt(1 + 1 / (k t)^2) with t the narrower half-extent
 * min(1, aspect) T_y. Every profile, composition, and landscape or portrait
 * target then frames the whole tesseract; the record camera's black-hole
 * distance, including --record-distance, sets no tesseract size. The distance
 * never falls below TESSERACT_MIN_VIEW_DISTANCE.
 */
TesseractFraming tesseractFraming(float viewDistance, float fovDeg, float boundingRadius,
                                  float aspect, const std::optional<TesseractRecordCamera> &record);

/**
 * @brief Tesseract view distance after interactive zoom.
 *
 * While the tesseract scene is active, InputManager redirects zoom input
 * (setZoomRedirect) so the black-hole camera distance stays put, and this
 * applies the redirected @p zoomDelta, in zoom-rate units (the input before
 * zoomRateScale), at the black-hole camera's distance-proportional rate: the
 * view moves by zoomDelta * viewDistance / K_ZOOM_RATE_REFERENCE_DISTANCE,
 * so one scroll step changes the view by the same fraction it changes the
 * black-hole camera distance. The result stays in
 * [TESSERACT_MIN_VIEW_DISTANCE, TESSERACT_MAX_VIEW_DISTANCE].
 */
float tesseractZoom(float viewDistance, float zoomDelta);

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
 * @brief Tangents of the angles from the tesseract view axis to its center.
 *
 * tesseractView looks along cameraBasis[2] from an eye on the line through
 * the origin along @p focusDirection, so the center sits at
 * (dot(f, right), dot(f, up)) / dot(f, forward) in view tangents, with right
 * cameraBasis[0] and up cameraBasis[1]. Zero when the camera looks at its
 * focus; a showcase-orbit frame offset makes it about the offset times the
 * half-extent tangents. The forward component is floored at
 * TESSERACT_MIN_FOCUS_COSINE, so a focus at or behind the eye plane maps to
 * a large finite tangent.
 */
glm::vec2 tesseractFocusTangent(const glm::mat3 &cameraBasis, const glm::vec3 &focusDirection);

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
