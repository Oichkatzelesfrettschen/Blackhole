/**
 * @file tesseract_geometry.h
 * @brief Speculative tesseract scene geometry: the 4-cube, its 4D->3D
 *        projections, and the "library of time" world-tubes.
 *
 * Render-only content for the Tesseract scene mode, after Thorne, The Science
 * of Interstellar ch. 29-31; none of it is physics. Points of R^4 are
 * glm::vec4 ordered (x, y, z, w), the layout so4.h uses, so a rotation from
 * so4FromPair applies to them directly.
 *
 * The library of time extrudes a few bedroom feature points (shelf, window,
 * desk) along w = t for t in [0, T]: each point becomes a 4D polyline, its
 * world-tube. The renderer maps [0, T] onto the tesseract's w extent [-1, 1]
 * with libraryToTesseract, lights one moment with a Gaussian in t, and runs a
 * "gravity message" pulse backward along one strand.
 */

#ifndef BLACKHOLE_RENDER_TESSERACT_TESSERACT_GEOMETRY_H
#define BLACKHOLE_RENDER_TESSERACT_TESSERACT_GEOMETRY_H

#include <array>
#include <cstddef>
#include <vector>

#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>

#include "render/tesseract/so4.h"

namespace blackhole::tesseract {

/** @brief Vertex count of the 4-cube, 2^4. */
inline constexpr std::size_t TESSERACT_VERTEX_COUNT = 16;

/** @brief Edge between two vertices whose indices differ in bit @c axis. */
struct TesseractEdge {
  std::size_t a = 0;
  std::size_t b = 0;
  std::size_t axis = 0;
};

/** @brief Square face spanning two axes; vertices listed in cyclic order. */
struct TesseractFace {
  std::array<std::size_t, 4> vertices{};
  std::size_t axisA = 0;
  std::size_t axisB = 0;
};

/** @brief Cubic cell on the hyperplane coordinate[axis] = sign. */
struct TesseractCell {
  std::array<std::size_t, 8> vertices{};
  std::size_t axis = 0;
  float sign = 1.0f;
};

/**
 * @brief The 4-cube [-1, 1]^4 as a cell complex.
 *
 * Vertex i has coordinate k equal to +1 when bit k of i is set and -1
 * otherwise, so an edge joins indices that differ in exactly one bit.
 * Counts: 16 vertices, 32 edges, 24 faces, 8 cells. The boundary is a
 * 3-sphere, a closed odd-dimensional manifold, so V - E + F - C = 0.
 */
struct TesseractMesh {
  std::array<glm::vec4, TESSERACT_VERTEX_COUNT> vertices{};
  std::vector<TesseractEdge> edges;
  std::vector<TesseractFace> faces;
  std::vector<TesseractCell> cells;
};

/** @brief Vertex @p index of [-1, 1]^4 under the bit encoding of TesseractMesh. */
glm::vec4 tesseractVertex(std::size_t index);

/** @brief Build the full vertex/edge/face/cell complex of the 4-cube. */
TesseractMesh buildTesseract();

/// Smallest eye distance d - w the perspective projection divides by.
inline constexpr float PERSPECTIVE_MIN_DEPTH = 0.05f;
/// Smallest 1 - w the stereographic projection divides by.
inline constexpr float STEREOGRAPHIC_MIN_DENOM = 0.02f;
/// 1 - w at which the stereographic pole fade reaches full brightness.
inline constexpr float STEREOGRAPHIC_FADE_END = 0.2f;
/// |p| below which the stereographic projection sends p to the south pole.
inline constexpr float STEREOGRAPHIC_MIN_NORM = 1e-4f;
/// Smallest Gaussian width litMomentEmission divides by.
inline constexpr float EMISSION_MIN_WIDTH = 1e-4f;

/**
 * @brief Perspective projection along w from an eye at w = d.
 *
 * p = xyz * d / max(d - w, PERSPECTIVE_MIN_DEPTH). Points nearer the eye
 * (larger w) project larger, so the w = +1 cell of the 4-cube appears as the
 * outer cube; the clamp bounds points at or behind the eye. Mirrors
 * projectPerspective in shader/tesseract.vert operation for operation.
 */
glm::vec3 projectPerspective(const glm::vec4 &p, float eyeDistance);

/** @brief Stereographic image and pole fade of one point. */
struct StereographicPoint {
  glm::vec3 position{0.0f};
  float fade = 1.0f; ///< 0 at the pole w = 1, 1 once 1 - w >= STEREOGRAPHIC_FADE_END.
};

/**
 * @brief Stereographic projection of S^3 from the pole w = 1.
 *
 * The input is first normalized onto S^3 (a point with |p| below
 * STEREOGRAPHIC_MIN_NORM goes to the south pole), then
 * p = xyz / max(1 - w, STEREOGRAPHIC_MIN_DENOM) and
 * fade = smoothstep(STEREOGRAPHIC_MIN_DENOM, STEREOGRAPHIC_FADE_END, 1 - w).
 * Away from the clamp the south pole maps to the origin, the equator w = 0 to
 * the unit sphere, and |p|^2 = (1 + w) / (1 - w). Mirrors
 * projectStereographic in shader/tesseract.vert operation for operation.
 */
StereographicPoint projectStereographic(const glm::vec4 &p);

/** @brief Bedroom furniture a library strand belongs to. */
enum class FeatureKind { Shelf, Window, Desk };

/** @brief One bedroom feature point in the unit room [-1, 1]^3. */
struct LibraryFeature {
  FeatureKind kind = FeatureKind::Shelf;
  glm::vec3 position{0.0f};
};

/** @brief Procedural bedroom: five shelf books, four window and four desk corners. */
std::vector<LibraryFeature> bedroomFeatures();

/** @brief Feature-index pairs that sketch the shelf line, window frame, and desk top. */
std::vector<std::array<std::size_t, 2>> bedroomOutline();

/**
 * @brief World-tube of a fixed point: samples (xyz, t_k), t_k = T k / (n - 1).
 *
 * The polyline runs from w = 0 to w = T with @p samples points (at least 2).
 */
std::vector<glm::vec4> extrudeWorldTube(const glm::vec3 &point, float timeSpan,
                                        std::size_t samples);

/** @brief Map library time w in [0, T] onto the tesseract's w extent [-1, 1]. */
glm::vec4 libraryToTesseract(const glm::vec4 &p, float timeSpan);

/**
 * @brief Emissive weight of library time @p t for the lit moment.
 *
 * exp(-u^2 / 2) with u = (t - litMoment) / max(width, EMISSION_MIN_WIDTH): 1 at
 * the lit moment, exp(-1/2) one width away. Mirrors gaussian in
 * shader/tesseract.frag operation for operation.
 */
float litMomentEmission(float t, float litMoment, float width);

/**
 * @brief Advance the gravity-message pulse by @p distance library units.
 *
 * @p travel is how far the pulse has run back from t_now; the pulse sits at
 * library time t_now - travel and repeats after reaching t_past, so the
 * result is (travel + distance) wrapped into [0, span), span = t_now - t_past.
 * Callers accumulate travel per frame (distance = pulse speed * frame time),
 * so a speed change alters only the motion that follows it. A span <= 0
 * returns 0; distance 0 re-wraps travel after a span change.
 */
float advancePulseTravel(float travel, float distance, float span);

/**
 * @brief One animation step of the SO(4) orientation.
 *
 * qL <- exp(ds leftRate) qL and qR <- exp(ds rightRate) qR, renormalized.
 * Constant rates compose to exp(s leftRate), exp(s rightRate) at s = sum ds;
 * per-step accumulation keeps a rate change from rescaling the rotation
 * already travelled, which a closed form in total time s would do.
 */
So4Pair<double> advanceOrientation(const So4Pair<double> &orientation,
                                   const std::array<float, 3> &leftRate,
                                   const std::array<float, 3> &rightRate, double ds);

/** @brief Orientation and pulse travel of the tesseract animation at one instant. */
struct TesseractMotion {
  So4Pair<double> orientation{};
  float pulseTravel = 0.0f;
};

/**
 * @brief Animation state at output time @p seconds for constant rates, in closed form.
 *
 * Orientation (exp(s leftRate), exp(s rightRate)) at s = resetPhase +
 * rotationSpeed * seconds and pulse travel pulseSpeed * seconds wrapped into
 * [0, pulseSpan): what per-frame advanceOrientation / advancePulseTravel reach
 * from the reset state after @p seconds. A recording evaluates this at
 * frameIndex / fps, so every output frame depends on its index alone and a
 * capture resumed at a later start frame reproduces the full capture's frames.
 */
TesseractMotion tesseractMotionAt(const std::array<float, 3> &leftRate,
                                  const std::array<float, 3> &rightRate, double resetPhase,
                                  double rotationSpeed, float pulseSpeed, float pulseSpan,
                                  double seconds);

/** @brief Kind tag stored in SegmentInstance::meta.z. */
enum class SegmentKind { TesseractEdge = 0, WorldTube = 1, LitSlice = 2 };

/**
 * @brief One instanced line segment for shader/tesseract.vert.
 *
 * a and b are tesseract-space endpoints; meta = (tA, tB, kind, strand). A
 * LitSlice segment carries w = 0 in a and b and the vertex shader substitutes
 * the lit moment for both w and t, so the room outline follows the slider
 * without a buffer upload. Three vec4 attributes, 48 bytes per instance.
 */
struct SegmentInstance {
  glm::vec4 a{0.0f};
  glm::vec4 b{0.0f};
  glm::vec4 meta{0.0f};
};

/** @brief Tessellation parameters for buildSceneSegments. */
struct SceneSegmentOptions {
  float timeSpan = 10.0f;       ///< Library time extent T.
  std::size_t tubeSamples = 48; ///< Points per world-tube polyline.
  std::size_t edgeSubdivisions =
      16; ///< Pieces per edge and outline link (curves under stereographic).
};

/**
 * @brief Every segment of the scene: subdivided tesseract edges, the world-tube
 *        strands (strand index = feature index), and the lit-moment room outline.
 */
std::vector<SegmentInstance> buildSceneSegments(const SceneSegmentOptions &options);

} // namespace blackhole::tesseract

#endif // BLACKHOLE_RENDER_TESSERACT_TESSERACT_GEOMETRY_H
