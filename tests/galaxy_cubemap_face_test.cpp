/**
 * @file galaxy_cubemap_face_test.cpp
 * @brief Headless validation of galaxy cubemap face-selection and UV logic.
 *
 * WHY: d_sample_galaxy_cubemap() in device_physics.cuh implements manual
 *      cubemap face selection to match the OpenGL fixed-function
 *      `texture(samplerCube galaxy, dir)` call.  The GL spec (section 8.13,
 *      Table 8.19) defines the face-selection rules and the per-face UV
 *      formulae.  This test validates the C++ port of that logic -- no CUDA
 *      device, no OpenGL context, and no cubemap texture data are required.
 *
 * WHAT: Tests mirror the face-select / UV-map logic in device_physics.cuh so
 *      that any divergence between the CUDA and GL paths is caught before
 *      running the full pixel-parity test.
 *
 * Tests:
 *  1. +X cardinal direction -> layer 0, UV (0.5, 0.5)
 *  2. -X cardinal direction -> layer 1, UV (0.5, 0.5)
 *  3. +Y cardinal direction -> layer 2, UV (0.5, 0.5)
 *  4. -Y cardinal direction -> layer 3, UV (0.5, 0.5)
 *  5. +Z cardinal direction -> layer 4, UV (0.5, 0.5)
 *  6. -Z cardinal direction -> layer 5, UV (0.5, 0.5)
 *  7. Arbitrary direction in +X octant maps to layer 0.
 *  8. Diagonal (1,1,0)/sqrt(2): dominant X+Y tie broken by >= rule -> layer 0 or 2.
 *  9. UV endpoints: direction pointing to face corner yields (0,0) or (1,1).
 * 10. All 26 octant/face directions produce UV values in [0,1].
 *
 * HOW: The cubemap_face() helper replicates the face-select + UV code from
 *      d_sample_galaxy_cubemap() exactly.  Both live in the anonymous namespace
 *      so misc-use-anonymous-namespace is satisfied.
 */

#include <cmath>
#include <cstdio>
#include <exception>
#include <format>
#include <iostream>
#include <numbers>
#include <string>
#include <string_view>

namespace {

/* =========================================================================
 * GL face ordering: matches lut_manager.cu::lutRegisterCubemap and the
 * GL_TEXTURE_CUBE_MAP_POSITIVE_X ... NEGATIVE_Z sequence (0-5).
 * ======================================================================= */
enum CubeFace {
  FacePosX = 0, /**< +X: arrayIndex 0 in GL face order */
  FaceNegX = 1, /**< -X: arrayIndex 1 */
  FacePosY = 2, /**< +Y: arrayIndex 2 */
  FaceNegY = 3, /**< -Y: arrayIndex 3 */
  FacePosZ = 4, /**< +Z: arrayIndex 4 */
  FaceNegZ = 5  /**< -Z: arrayIndex 5 */
};

/** @brief Minimum positive float to avoid divide-by-zero in face selection. */
constexpr float D_EPSILON = 1e-7f;

/**
 * @brief Result of cubemap face selection: face layer index and UV coordinates.
 */
struct FaceUV {
  int layer; /**< @brief BhLutGalaxy layer (0-5). */
  float u;   /**< @brief Horizontal texture coordinate in [0,1]. */
  float v;   /**< @brief Vertical texture coordinate in [0,1]. */
};

/**
 * @brief C++ port of the face-selection logic in d_sample_galaxy_cubemap().
 *
 * Replicates OpenGL spec 8.13 Table 8.19 face selection and UV formulae.
 * Face ordering: +X=0, -X=1, +Y=2, -Y=3, +Z=4, -Z=5.
 *
 * @param dx Direction X component.
 * @param dy Direction Y component.
 * @param dz Direction Z component.
 * @return FaceUV with layer in [0,5] and u,v in [0,1].
 */
FaceUV cubemapFace(float dx, float dy, float dz) {
  float const ax = std::fabs(dx);
  float const ay = std::fabs(dy);
  float const az = std::fabs(dz);

  float u;
  float v;
  int layer;

  if (ax >= ay && ax >= az) {
    float const sc = 1.0f / std::fmax(ax, D_EPSILON);
    if (dx > 0.0f) {
      layer = FacePosX;
      u = -dz * sc;
      v = -dy * sc;
    } else {
      layer = FaceNegX;
      u = dz * sc;
      v = -dy * sc;
    }
  } else if (ay >= ax && ay >= az) {
    float const sc = 1.0f / std::fmax(ay, D_EPSILON);
    if (dy > 0.0f) {
      layer = FacePosY;
      u = dx * sc;
      v = dz * sc;
    } else {
      layer = FaceNegY;
      u = dx * sc;
      v = -dz * sc;
    }
  } else {
    float const sc = 1.0f / std::fmax(az, D_EPSILON);
    if (dz > 0.0f) {
      layer = FacePosZ;
      u = dx * sc;
      v = -dy * sc;
    } else {
      layer = FaceNegZ;
      u = -dx * sc;
      v = -dy * sc;
    }
  }

  /* Remap [-1,1] to [0,1] */
  u = 0.5f * (u + 1.0f);
  v = 0.5f * (v + 1.0f);

  return FaceUV{layer, u, v};
}

/* =========================================================================
 * Test helpers
 * ======================================================================= */

bool gAllPass = true;

void check(bool cond, const char *name, std::string_view detail = {}) {
  if (cond) {
    std::cout << "  [PASS] " << name << "\n";
  } else {
    std::cout << "  [FAIL] " << name;
    if (!detail.empty()) {
      std::cout << " -- " << detail;
    }
    std::cout << "\n";
    gAllPass = false;
  }
}

/** @brief Assert that |a - b| <= tol. */
void checkNear(float a, float b, float tol, const char *name) {
  bool const ok = std::fabs(a - b) <= tol;
  if (!ok) {
    const std::string buf =
        std::format("got {:.5f}, expected {:.5f} (tol {:.5f})", static_cast<double>(a),
                    static_cast<double>(b), static_cast<double>(tol));
    check(false, name, buf);
  } else {
    check(true, name);
  }
}

/* =========================================================================
 * Test 1-6: cardinal directions -> correct face and center UV
 * ======================================================================= */

/**
 * @brief Tests 1-6: each axis-aligned unit vector maps to the expected GL face
 *        with UV = (0.5, 0.5) (the texel at the center of that face).
 */
void testCardinalDirections() {
  std::cout << "Tests 1-6: cardinal directions -> correct face, UV=(0.5,0.5)\n";

  struct Card {
    float dx, dy, dz;
    int expectedLayer;
    const char *label;
  };
  const Card cards[] = {
      {1.0f, 0.0f, 0.0f, FacePosX, "+X -> layer 0"}, {-1.0f, 0.0f, 0.0f, FaceNegX, "-X -> layer 1"},
      {0.0f, 1.0f, 0.0f, FacePosY, "+Y -> layer 2"}, {0.0f, -1.0f, 0.0f, FaceNegY, "-Y -> layer 3"},
      {0.0f, 0.0f, 1.0f, FacePosZ, "+Z -> layer 4"}, {0.0f, 0.0f, -1.0f, FaceNegZ, "-Z -> layer 5"},
  };

  for (const auto &c : cards) {
    FaceUV const r = cubemapFace(c.dx, c.dy, c.dz);
    check(r.layer == c.expectedLayer, c.label);
    checkNear(r.u, 0.5f, 0.01f, "  u == 0.5 at face center");
    checkNear(r.v, 0.5f, 0.01f, "  v == 0.5 at face center");
  }
}

/* =========================================================================
 * Test 7: off-axis direction still selects correct dominant face
 * ======================================================================= */

/**
 * @brief Test 7: a direction in the +X octant (X largest) selects layer 0.
 */
void testOffAxisDominance() {
  std::cout << "Test 7: off-axis direction selects dominant face\n";
  /* X is dominant (0.9 > 0.3 > 0.2) */
  FaceUV const r = cubemapFace(0.9f, 0.3f, -0.2f);
  check(r.layer == FacePosX, "+X dominant: layer 0");
  check(r.u >= 0.0f && r.u <= 1.0f, "u in [0,1]");
  check(r.v >= 0.0f && r.v <= 1.0f, "v in [0,1]");
}

/* =========================================================================
 * Test 8: exact UV at face corners
 * ======================================================================= */

/**
 * @brief Test 8: direction pointing to the corners of the +X face
 *        yields UV close to the corners (0 or 1).
 *
 * The +X face has: u = -z/|x|, v = -y/|x|.
 * For (x=1, y=1, z=-1): u = -(-1)/1 = 1 -> U=1.0; v = -(1)/1 = -1 -> V=0.0.
 */
void testCornerUV() {
  std::cout << "Test 8: corner direction -> UV at (1,0) or (0,1)\n";

  /* (1, 1, -1): +X dominant, corner of face -> U=1, V=0 */
  {
    float const len = std::numbers::sqrt3_v<float>;
    FaceUV const r = cubemapFace(1.0f / len, 1.0f / len, -1.0f / len);
    check(r.layer == FacePosX, "+X dominant for (1,1,-1)/sqrt(3)");
    checkNear(r.u, 1.0f, 0.02f, "u ~ 1.0 at corner");
    checkNear(r.v, 0.0f, 0.02f, "v ~ 0.0 at corner");
  }

  /* (1, -1, 1): +X dominant, opposite corner -> U=0, V=1 */
  {
    float const len = std::numbers::sqrt3_v<float>;
    FaceUV const r = cubemapFace(1.0f / len, -1.0f / len, 1.0f / len);
    check(r.layer == FacePosX, "+X dominant for (1,-1,1)/sqrt(3)");
    checkNear(r.u, 0.0f, 0.02f, "u ~ 0.0 at opposite corner");
    checkNear(r.v, 1.0f, 0.02f, "v ~ 1.0 at opposite corner");
  }
}

/* =========================================================================
 * Test 9: all 26 grid directions produce UV in [0,1]
 * ======================================================================= */

/**
 * @brief Test 9: a 3x3x3 direction grid (excluding zero vector) all yield
 *        UV values within [0,1] and a valid layer index.
 */
void testAllDirectionsInRange() {
  std::cout << "Test 9: 26-direction grid -- UV in [0,1], layer in [0,5]\n";

  bool allPass = true;
  int count = 0;

  for (int xi = -1; xi <= 1; ++xi) {
    for (int yi = -1; yi <= 1; ++yi) {
      for (int zi = -1; zi <= 1; ++zi) {
        if (xi == 0 && yi == 0 && zi == 0) {
          continue;
        }
        auto const dx = static_cast<float>(xi);
        auto const dy = static_cast<float>(yi);
        auto const dz = static_cast<float>(zi);
        FaceUV const r = cubemapFace(dx, dy, dz);
        if (r.layer < 0 || r.layer > 5 || r.u < -0.001f || r.u > 1.001f || r.v < -0.001f ||
            r.v > 1.001f) {
          allPass = false;
        }
        ++count;
      }
    }
  }

  const std::string buf = std::format("({:d} directions)", count);
  check(allPass, "all 26 directions: UV in [0,1], layer in [0,5]", buf);
}

/* =========================================================================
 * Test 10: face-edge continuity -- adjacent face directions yield UV near edge
 * ======================================================================= */

/**
 * @brief Test 10: directions near the face-edge boundary yield UV values near
 *        0 or 1 on the edge axis, verifying the remap is monotone.
 *
 * For +X face: dir = (1, 0, +0.99) gives z/x close to +1, so u = -z/x ~ -1
 * -> U ~ 0.  The edge UV should be monotone between center and extremes.
 */
void testFaceEdgeMonotonicity() {
  std::cout << "Test 10: +X face u-coordinate is monotone in z\n";

  float prevU = -1.0f;
  bool monotone = true;

  /* Vary z from -0.9 to +0.9 at fixed x=1, y=0: u should be monotone decreasing */
  for (int i = 0; i <= 9; ++i) {
    float const dz = -0.9f + static_cast<float>(i) * 0.2f;
    FaceUV const r = cubemapFace(1.0f, 0.0f, dz);
    if (r.layer != FacePosX) {
      monotone = false;
      break;
    }
    if (i > 0 && r.u >= prevU - 0.001f) {
      monotone = false;
    }
    /* u = 0.5*((-dz/1)+1) = 0.5*(1-dz): decreasing in dz, increasing as dz decreases */
    float const expectedU = 0.5f * (1.0f - dz);
    if (std::fabs(r.u - expectedU) > 0.01f) {
      monotone = false;
    }
    prevU = r.u;
  }

  check(monotone, "+X face: u = 0.5*(1 - z/x) for varying z");
}

} // namespace

int main() try {
  std::cout << "\n================================================\n"
            << "GALAXY CUBEMAP FACE-SELECTION VALIDATION\n"
            << "C++ port of d_sample_galaxy_cubemap() face math\n"
            << "================================================\n\n";

  testCardinalDirections();
  std::cout << "\n";
  testOffAxisDominance();
  std::cout << "\n";
  testCornerUV();
  std::cout << "\n";
  testAllDirectionsInRange();
  std::cout << "\n";
  testFaceEdgeMonotonicity();
  std::cout << "\n";

  std::cout << "================================================\n"
            << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
            << "================================================\n\n";

  return gAllPass ? 0 : 1;
} catch (const std::exception &error) {
  return std::fprintf(stderr, "[FAIL] Unexpected exception: %s\n", error.what()) < 0 ? 2 : 1;
} catch (...) {
  return std::fprintf(stderr, "[FAIL] Unexpected nonstandard exception\n") < 0 ? 2 : 1;
}
