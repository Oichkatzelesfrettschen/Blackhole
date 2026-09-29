#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <ios>
#include <numbers>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <gtest/gtest.h>
#include <stdlib.h> // NOLINT(modernize-deprecated-headers) -- POSIX setenv declaration.
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include "../shader/include/ray_terminal.h"
#include "physics/analytic_kerr_geodesic.h"
#include "physics/disk_transfer.h"
#include "physics/novikov_thorne.h"
#include "render/render_output_metrics.h"
#include "support/gl_compute_harness.h"

#ifdef BH_RENDER_HAS_CUDA
#include <cuda_runtime_api.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#endif

namespace {

struct CapturedFrame {
  int width = 0;
  int height = 0;
  std::vector<float> raw;
  std::vector<float> display;
  std::vector<std::uint8_t> terminals;
  blackhole::ImageMetrics rawMetrics;
  blackhole::ImageMetrics displayMetrics;
  blackhole::DiskImageMetrics diskMetrics;
};

double criticalEdgeColumnError(const CapturedFrame &frame);

std::filesystem::path artifactRoot() {
  const char *configured = std::getenv("BLACKHOLE_RENDER_ARTIFACTS");
  return configured != nullptr ? std::filesystem::path(configured)
                               : std::filesystem::path(BH_RENDER_ARTIFACT_DIR);
}

std::vector<float> loadPfm(const std::filesystem::path &path, int &width, int &height) {
  std::ifstream input(path, std::ios::binary);
  std::string magic;
  float scale = 0.0f;
  input >> magic >> width >> height >> scale;
  if (!input || magic != "PF" || width <= 0 || height <= 0 || scale != -1.0f) {
    throw std::runtime_error("invalid HDR capture: " + path.string());
  }
  input.get();
  const auto pixels = static_cast<std::size_t>(width) * static_cast<std::size_t>(height);
  std::vector<float> rgb(pixels * 3U);
  input.read(reinterpret_cast<char *>(rgb.data()),
             static_cast<std::streamsize>(rgb.size() * sizeof(float)));
  if (!input) {
    throw std::runtime_error("truncated HDR capture: " + path.string());
  }
  std::vector<float> luminance(pixels);
  for (std::size_t index = 0; index < luminance.size(); ++index) {
    const auto channel = 3 * index;
    luminance[index] =
        (0.2126f * rgb[channel]) + (0.7152f * rgb[channel + 1]) + (0.0722f * rgb[channel + 2]);
  }
  return luminance;
}

std::vector<float> loadDisplayBytes(const std::filesystem::path &path, int width, int height) {
  std::ifstream input(path, std::ios::binary);
  std::string magic;
  int imageWidth = 0;
  int imageHeight = 0;
  int maximum = 0;
  input >> magic >> imageWidth >> imageHeight >> maximum;
  if (!input || magic != "P6" || imageWidth != width || imageHeight != height || maximum != 255) {
    throw std::runtime_error("invalid display capture: " + path.string());
  }
  input.get();
  std::vector<std::uint8_t> pixels(static_cast<std::size_t>(width) *
                                   static_cast<std::size_t>(height) * 3U);
  input.read(reinterpret_cast<char *>(pixels.data()), static_cast<std::streamsize>(pixels.size()));
  if (!input) {
    throw std::runtime_error("truncated display capture: " + path.string());
  }
  std::vector<float> luminance(static_cast<std::size_t>(width) * static_cast<std::size_t>(height));
  for (std::size_t index = 0; index < luminance.size(); ++index) {
    const auto channel = 3 * index;
    luminance[index] = ((0.2126f * static_cast<float>(pixels.at(channel))) +
                        (0.7152f * static_cast<float>(pixels.at(channel + 1))) +
                        (0.0722f * static_cast<float>(pixels.at(channel + 2)))) /
                       255.0f;
  }
  return luminance;
}

std::vector<std::uint8_t> loadTerminals(const std::filesystem::path &path, int width, int height) {
  std::ifstream input(path, std::ios::binary);
  std::string magic;
  int mapWidth = 0;
  int mapHeight = 0;
  int maximum = 0;
  input >> magic >> mapWidth >> mapHeight >> maximum;
  if (!input || magic != "P5" || mapWidth != width || mapHeight != height || maximum != 255) {
    throw std::runtime_error("invalid terminal capture: " + path.string());
  }
  input.get();
  std::vector<std::uint8_t> terminals(static_cast<std::size_t>(width) *
                                      static_cast<std::size_t>(height));
  input.read(reinterpret_cast<char *>(terminals.data()),
             static_cast<std::streamsize>(terminals.size()));
  if (!input) {
    throw std::runtime_error("truncated terminal capture: " + path.string());
  }
  return terminals;
}

void writeMetrics(const std::filesystem::path &path, const CapturedFrame &frame,
                  std::string_view scene, std::string_view backend, std::string_view quality) {
  std::ofstream output(path);
  const auto &raw = frame.rawMetrics;
  const auto &display = frame.displayMetrics;
  output << "{\n  \"scene\": \"" << scene << "\",\n  \"backend\": \"" << backend
         << "\",\n  \"quality\": \"" << quality << "\",\n"
         << "  \"width\": " << frame.width << ",\n  \"height\": " << frame.height
         << ",\n  \"critical_radius_px\": " << raw.boundaryRadius
         << ",\n  \"critical_diameter_px\": " << raw.boundaryDiameter
         << ",\n  \"vertical_diameter_px\": " << raw.verticalDiameter
         << ",\n  \"bounding_box_px\": [" << raw.boundingCenterX << ", " << raw.boundingCenterY
         << ", " << raw.boundingWidth << ", " << raw.boundingHeight << "]"
         << ",\n  \"luminance_boundary_radius_px\": " << raw.luminanceBoundaryRadius
         << ",\n  \"luminance_boundary_diameter_px\": " << raw.luminanceBoundaryDiameter
         << ",\n  \"center_offset_px\": [" << raw.centerOffsetX << ", " << raw.centerOffsetY
         << "],\n  \"circularity\": " << raw.circularity
         << ",\n  \"limb_radius_px\": " << raw.limbRadius
         << ",\n  \"limb_contrast\": " << raw.limbContrast
         << ",\n  \"limb_width_px\": " << raw.limbWidth
         << ",\n  \"central_to_ring\": " << raw.centralToRing
         << ",\n  \"captured_fraction\": " << raw.capturedFraction
         << ",\n  \"escaped_fraction\": " << raw.escapedFraction
         << ",\n  \"exhausted_fraction\": " << raw.exhaustedFraction
         << ",\n  \"invalid_fraction\": " << raw.invalidFraction
         << ",\n  \"raw_finite_fraction\": " << raw.finiteFraction
         << ",\n  \"display_finite_fraction\": " << display.finiteFraction
         << ",\n  \"raw_range\": [" << raw.minimum << ", " << raw.maximum
         << "],\n  \"display_range\": [" << display.minimum << ", " << display.maximum
         << "],\n  \"raw_hash\": " << raw.luminanceHash
         << ",\n  \"display_hash\": " << display.luminanceHash
         << ",\n  \"terminal_hash\": " << raw.terminalHash
         << ",\n  \"disk_left_mean_luminance\": " << frame.diskMetrics.leftMeanLuminance
         << ",\n  \"disk_right_mean_luminance\": " << frame.diskMetrics.rightMeanLuminance
         << ",\n  \"disk_near_side_inner_edge_px\": "
         << frame.diskMetrics.nearSideInnerEdgePixels
         << ",\n  \"critical_edge_column_error_px\": "
         << (scene == "D" ? criticalEdgeColumnError(frame) : 0.0) << ",\n"
         << "  \"radial_luminance\": [";
  for (std::size_t index = 0; index < raw.radialLuminance.size(); ++index) {
    output << (index == 0 ? "" : ", ") << raw.radialLuminance[index];
  }
  output << "]\n}\n";
  if (!output) {
    throw std::runtime_error("metrics write failed: " + path.string());
  }
}

CapturedFrame capture(std::string_view scene, std::string_view backend = "fragment",
                      std::string_view quality = "balanced",
                      std::optional<blackhole::ProfileAnchor> anchor = std::nullopt) {
  const auto directory = artifactRoot();
  std::filesystem::create_directories(directory);
  const std::string stem =
      std::string(scene) + "-" + std::string(backend) + "-" + std::string(quality);
  const auto png = directory / (stem + ".png");
  const auto pfm = directory / (stem + ".pfm");
  const pid_t child = fork();
  if (child < 0) {
    throw std::runtime_error("fork failed");
  }
  if (child == 0) {
    setenv("BLACKHOLE_WINDOW_HIDDEN", "1", 1);
    const std::string sceneArg(scene);
    const std::string backendArg(backend);
    const std::string qualityArg(quality);
    execl(BH_RENDER_APP_EXECUTABLE, BH_RENDER_APP_EXECUTABLE, "--reference-scene", sceneArg.c_str(),
          "--reference-backend", backendArg.c_str(), "--reference-quality", qualityArg.c_str(),
          "--export-frame", png.c_str(), "--export-raw-frame", pfm.c_str(),
          static_cast<char *>(nullptr));
    _exit(127);
  }
  int status = 0;
  if (waitpid(child, &status, 0) != child || !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
    throw std::runtime_error("desktop reference render failed: " + stem);
  }
  CapturedFrame frame;
  frame.raw = loadPfm(pfm, frame.width, frame.height);
  frame.display = loadDisplayBytes(png.string() + ".rgb.ppm", frame.width, frame.height);
  if (backend == "cuda") {
    frame.terminals.assign(static_cast<std::size_t>(frame.width) *
                               static_cast<std::size_t>(frame.height),
                           BH_TERMINAL_OUTSIDE_DOMAIN);
  } else {
    frame.terminals = loadTerminals(png.string() + ".terminals.pgm", frame.width, frame.height);
  }
  frame.rawMetrics =
      blackhole::measureImage(frame.raw, frame.terminals, frame.width, frame.height, anchor);
  frame.displayMetrics =
      blackhole::measureImage(frame.display, frame.terminals, frame.width, frame.height, anchor);
  frame.diskMetrics = blackhole::measureDiskImage(frame.raw, frame.terminals,
                                                  frame.width, frame.height);
  writeMetrics(directory / (stem + ".metrics.json"), frame, scene, backend, quality);
  return frame;
}

void writeDifference(const CapturedFrame &reference, const CapturedFrame &candidate,
                     const std::filesystem::path &path) {
  std::ofstream output(path, std::ios::binary);
  output << "P5\n" << reference.width << ' ' << reference.height << "\n255\n";
  for (std::size_t index = 0; index < reference.raw.size(); ++index) {
    const double error = std::abs(static_cast<double>(reference.raw[index]) -
                                  static_cast<double>(candidate.raw[index]));
    output.put(static_cast<char>(std::clamp(error * 255.0, 0.0, 255.0)));
  }
}

void writeComparison(const CapturedFrame &reference, const CapturedFrame &candidate,
                     const std::filesystem::path &path) {
  const auto metrics = blackhole::compareImages(reference.raw, candidate.raw);
  std::ofstream output(path);
  output << "{\"mae\": " << metrics.mae << ", \"psnr\": " << metrics.psnr
         << ", \"structure\": " << metrics.structure << "}\n";
}

bool fullSweep() {
  const char *enabled = std::getenv("BLACKHOLE_RENDER_FULL");
  return enabled != nullptr && std::string_view(enabled) == "1";
}

// Reference camera: distance 30 M, vertical field of view 30 degrees, and
// yaw -90 degrees. buildCameraBasis then puts screen right along world +z,
// which bhWorldToPhysics maps to physics -y. For a camera at azimuth 180
// degrees that is the sky direction of photons with L_z < 0, so Bardeen's
// alpha = -xi / sin(i) increases to the right on screen.
constexpr double K_CAMERA_DISTANCE = 30.0;
constexpr double K_CAMERA_FOV_DEGREES = 30.0;
// K_REFERENCE_SCENE_EXTENT in render/record_mode.h; the scene B test asserts
// the captured height against it.
constexpr int K_IMAGE_EXTENT = 160;

// Screen offset in pixels of a ray with impact vector (alpha, beta), through
// the coordinate-direction camera model of blackhole::criticalRadiusPixels.
double screenPixels(double component, double impact, int imageHeight) {
  const double lapseSquared = 1.0 - (2.0 / K_CAMERA_DISTANCE);
  const double sineSquared =
      (impact * impact) /
      ((K_CAMERA_DISTANCE * K_CAMERA_DISTANCE) + ((1.0 - lapseSquared) * impact * impact));
  const double tangent = std::sqrt(sineSquared / (1.0 - sineSquared));
  return (component / impact) * tangent * static_cast<double>(imageHeight) /
         (2.0 * std::tan(K_CAMERA_FOV_DEGREES * std::numbers::pi / 360.0));
}

struct KerrScreenGeometry {
  double centerX = 0.0; ///< Signed; + is screen right.
  double width = 0.0;
  double height = 0.0;
};

// Bardeen critical curve (M = 1) for a camera at inclination 60 degrees from
// the spin axis, the reference pitch of 30 degrees above the disk plane.
KerrScreenGeometry kerrScreenGeometry(double spin, int imageHeight) {
  const double magnitude = std::abs(spin);
  const double prograde = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(-magnitude)));
  const double retrograde = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(magnitude)));
  const double inner = std::min(prograde, retrograde);
  const double outer = std::max(prograde, retrograde);
  const double inclination = std::numbers::pi / 3.0;
  const double sine = std::sin(inclination);
  const double cosine = std::cos(inclination);
  const double cotangent = cosine / sine;
  double left = 1.0e6;
  double right = -1.0e6;
  double top = 0.0;
  for (int index = 0; index <= 4096; ++index) {
    const double radius = inner + ((outer - inner) * static_cast<double>(index) / 4096.0);
    const auto impact = physics::criticalImpactParams(radius, spin);
    const double alpha = -impact.xi / sine;
    const double betaSquared = impact.eta + (spin * spin * cosine * cosine) -
                               (impact.xi * impact.xi * cotangent * cotangent);
    if (betaSquared < 0.0) {
      continue;
    }
    const double beta = std::sqrt(betaSquared);
    const double magnitudeImpact = std::hypot(alpha, beta);
    left = std::min(left, screenPixels(alpha, magnitudeImpact, imageHeight));
    right = std::max(right, screenPixels(alpha, magnitudeImpact, imageHeight));
    top = std::max(top, screenPixels(beta, magnitudeImpact, imageHeight));
  }
  return {.centerX = (left + right) / 2.0, .width = right - left, .height = 2.0 * top};
}

// Display luminance spread over escaped pixels. A backlit scene has one sky
// color, so any spread is overlay text or post-processing in the display bytes.
double escapedDisplaySpread(const CapturedFrame &frame) {
  double low = 1.0;
  double high = 0.0;
  for (std::size_t index = 0; index < frame.display.size(); ++index) {
    if (frame.terminals[index] == BH_TERMINAL_ESCAPE) {
      low = std::min(low, static_cast<double>(frame.display[index]));
      high = std::max(high, static_cast<double>(frame.display[index]));
    }
  }
  return high >= low ? high - low : 0.0;
}

// Integer value of a top-level numeric field in the exported renderer
// metadata, which records the effective configuration the frame rendered with.
int metadataInteger(const std::filesystem::path &path, std::string_view key) {
  std::ifstream input(path);
  const std::string needle = "\"" + std::string(key) + "\": ";
  std::string line;
  while (std::getline(input, line)) {
    const auto position = line.find(needle);
    if (position != std::string::npos) {
      return std::stoi(line.substr(position + needle.size()));
    }
  }
  throw std::runtime_error("metadata field missing: " + std::string(key));
}

// The oracle critical edge falls at the image center of scene D. A captured
// run ends at the right edge of its rightmost horizon pixel; one pixel is the
// quantization unit of this column measurement.
double criticalEdgeColumnError(const CapturedFrame &frame) {
  const int row = frame.height / 2;
  int rightmostHorizon = -1;
  for (int column = 0; column < frame.width; ++column) {
    const auto index = (static_cast<std::size_t>(row) * static_cast<std::size_t>(frame.width)) +
                       static_cast<std::size_t>(column);
    if (frame.terminals[index] == BH_TERMINAL_HORIZON) {
      rightmostHorizon = column;
    }
  }
  if (rightmostHorizon < 0) {
    return static_cast<double>(frame.width);
  }
  return std::abs(static_cast<double>(rightmostHorizon + 1) -
                  (static_cast<double>(frame.width) / 2.0));
}

bool contextAvailable() {
  const bhtest::HiddenGlContext context;
  return context.available();
}

#ifdef BH_RENDER_HAS_CUDA
std::string glVendor() {
  const bhtest::HiddenGlContext context;
  if (!context.available()) {
    return {};
  }
  const auto *vendor = reinterpret_cast<const char *>(gl::glGetString(gl::GL_VENDOR));
  return vendor != nullptr ? std::string(vendor) : std::string();
}
#endif

// Renders the desktop's first frame from an empty working directory, so the
// app starts from fresh Settings: the default camera, sky, and exposure.
CapturedFrame captureDefaultScene() {
  const auto directory = artifactRoot() / "default-scene";
  std::filesystem::remove_all(directory);
  std::filesystem::create_directories(directory);
  const auto png = directory / "default.png";
  const auto pfm = directory / "default.pfm";
  const pid_t child = fork();
  if (child < 0) {
    throw std::runtime_error("fork failed");
  }
  if (child == 0) {
    setenv("BLACKHOLE_WINDOW_HIDDEN", "1", 1);
    if (chdir(directory.c_str()) != 0) {
      _exit(126);
    }
    execl(BH_RENDER_APP_EXECUTABLE, BH_RENDER_APP_EXECUTABLE, "--export-frame", png.c_str(),
          "--export-raw-frame", pfm.c_str(), "--export-size", "320", "180",
          static_cast<char *>(nullptr));
    _exit(127);
  }
  int status = 0;
  if (waitpid(child, &status, 0) != child || !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
    throw std::runtime_error("desktop default-scene render failed");
  }
  CapturedFrame frame;
  frame.raw = loadPfm(pfm, frame.width, frame.height);
  frame.terminals = loadTerminals(png.string() + ".terminals.pgm", frame.width, frame.height);
  return frame;
}

} // namespace

// The capture verifies geometry, terminal classes, and image range together.
// NOLINTNEXTLINE(readability-function-cognitive-complexity)
TEST(RenderedOutput, SchwarzschildCriticalCurve) {
  if (!contextAvailable()) {
    GTEST_SKIP() << "GL 4.6 context unavailable";
  }
  const auto fragment = capture("A");
  const double predicted = blackhole::criticalRadiusPixels(1.0, K_CAMERA_DISTANCE,
                                                           K_CAMERA_FOV_DEGREES, fragment.height);
  EXPECT_GT(fragment.rawMetrics.capturedFraction, 0.01);
  EXPECT_GT(fragment.rawMetrics.escapedFraction, 0.01);
  EXPECT_LE(fragment.rawMetrics.invalidFraction, 0.001);
  EXPECT_EQ(fragment.rawMetrics.finiteFraction, 1.0);
  EXPECT_EQ(fragment.displayMetrics.finiteFraction, 1.0);
  EXPECT_GT(fragment.rawMetrics.maximum - fragment.rawMetrics.minimum, 0.1);
  EXPECT_LT(fragment.rawMetrics.maximum, 1.0e6);
  EXPECT_GE(fragment.displayMetrics.minimum, 0.0);
  EXPECT_LE(fragment.displayMetrics.maximum, 1.0);
  // Pixel-edge quantization bounds each extent to +-1 pixel about the curve,
  // so the mean radius of two diameters lies within 1 pixel of the oracle.
  EXPECT_NEAR(fragment.rawMetrics.boundaryRadius, predicted, 1.0);
  // Radial bins are 1 pixel wide and centered half a pixel off the edge.
  EXPECT_NEAR(fragment.rawMetrics.luminanceBoundaryRadius, predicted, 1.5);
  EXPECT_LE(fragment.rawMetrics.circularity, 0.02);
  EXPECT_NEAR(fragment.rawMetrics.centerOffsetX, 0.0, 0.5);
  EXPECT_NEAR(fragment.rawMetrics.centerOffsetY, 0.0, 0.5);
  EXPECT_LE(escapedDisplaySpread(fragment), 2.0 / 255.0) << "display bytes carry non-scene pixels";
  EXPECT_GT(fragment.displayMetrics.maximum - fragment.displayMetrics.minimum, 0.1);
  if (!::testing::Test::HasFailure()) {
    std::ofstream receipt(artifactRoot() / "rendered_output_validation.pass", std::ios::trunc);
    receipt << "PASS\n";
    ASSERT_TRUE(static_cast<bool>(receipt));
  }
  if (fullSweep()) {
    const auto compute = capture("A", "compute");
    const auto comparison = blackhole::compareImages(fragment.raw, compute.raw);
    writeDifference(fragment, compute, artifactRoot() / "A-fragment-compute-diff.pgm");
    writeComparison(fragment, compute, artifactRoot() / "A-fragment-compute-comparison.json");
    // Scene A's raw frame is 0 or 1 per pixel, so MAE is the fraction of
    // pixels whose capture classification differs.
    EXPECT_LT(comparison.mae, 0.01) << "shared GLSL plumbing parity";
  }
}

// CUDA writes the frame through CUDA-GL interop, which needs the GL context on
// an NVIDIA device; under Mesa the desktop refuses a CUDA reference export.
TEST(RenderedOutput, CudaMatchesFragment) {
  if (!fullSweep()) {
    GTEST_SKIP() << "set BLACKHOLE_RENDER_FULL=1 for backend comparisons";
  }
#ifdef BH_RENDER_HAS_CUDA
  int devices = 0;
  if (cudaGetDeviceCount(&devices) != cudaSuccess || devices == 0) {
    GTEST_SKIP() << "no CUDA device";
  }
  const std::string vendor = glVendor();
  if (vendor.find("NVIDIA") == std::string::npos) {
    GTEST_SKIP() << "GL vendor '" << vendor << "' has no CUDA interop";
  }
  const auto fragment = capture("A");
  const auto cuda = capture("A", "cuda");
  const auto comparison = blackhole::compareImages(fragment.raw, cuda.raw);
  writeDifference(fragment, cuda, artifactRoot() / "A-fragment-cuda-diff.pgm");
  writeComparison(fragment, cuda, artifactRoot() / "A-fragment-cuda-comparison.json");
  EXPECT_LT(comparison.mae, 0.01) << "CUDA pixel plumbing parity";
#else
  GTEST_SKIP() << "built without CUDA";
#endif
}

TEST(RenderedOutput, EmittingDiskLimbAndEdge) {
  if (!fullSweep()) {
    GTEST_SKIP() << "set BLACKHOLE_RENDER_FULL=1 for disk and spin sweeps";
  }
  if (!contextAvailable()) {
    GTEST_SKIP() << "GL 4.6 context unavailable";
  }
  // At a = 0 the critical curve is the image-centered circle of scene A for
  // any inclination, so the oracle anchors the profile the disk would bias.
  const double critical = blackhole::criticalRadiusPixels(1.0, K_CAMERA_DISTANCE,
                                                          K_CAMERA_FOV_DEGREES, K_IMAGE_EXTENT);
  const auto frame =
      capture("B", "fragment", "balanced", blackhole::ProfileAnchor{.radius = critical});
  ASSERT_EQ(frame.height, K_IMAGE_EXTENT);
  // The lensed disk images of order n >= 1 approach the critical curve from
  // outside and narrow by e^-pi per order, so at this scale the first one is
  // a ring about a pixel wide within a few pixels outside the curve. A hard
  // matte steps from dark to disk with no local maximum and fails the
  // contrast check.
  EXPECT_GE(frame.rawMetrics.limbRadius, std::floor(critical));
  EXPECT_LE(frame.rawMetrics.limbRadius, critical + 3.0);
  EXPECT_GT(frame.rawMetrics.limbContrast,
            0.1 * frame.rawMetrics.radialLuminance.at(
                      static_cast<std::size_t>(frame.rawMetrics.limbRadius)));
  EXPECT_GE(frame.rawMetrics.limbWidth, 1.0);
  EXPECT_LE(frame.rawMetrics.limbWidth, 4.0);
  EXPECT_LT(frame.rawMetrics.centralToRing, 0.8);
  EXPECT_EQ(frame.rawMetrics.finiteFraction, 1.0);
}

TEST(RenderedOutput, KerrSpinOrientation) {
  if (!fullSweep()) {
    GTEST_SKIP() << "set BLACKHOLE_RENDER_FULL=1 for disk and spin sweeps";
  }
  if (!contextAvailable()) {
    GTEST_SKIP() << "GL 4.6 context unavailable";
  }
  const auto positive = capture("C+");
  const auto negative = capture("C-");
  const auto predictedPositive = kerrScreenGeometry(0.6, positive.height);
  const auto predictedNegative = kerrScreenGeometry(-0.6, negative.height);
  ASSERT_GT(predictedPositive.centerX, 1.0) << "oracle: a > 0 shifts the shadow toward +alpha";
  // Signed comparisons: a mirrored spin moves the shadow to the wrong side and
  // fails here, where an absolute-value comparison would pass it.
  for (const auto &[frame, predicted] :
       {std::pair{&positive, predictedPositive}, std::pair{&negative, predictedNegative}}) {
    EXPECT_GT(frame->rawMetrics.capturedFraction, 0.0);
    EXPECT_NEAR(frame->rawMetrics.boundingCenterX, predicted.centerX, 1.0);
    EXPECT_NEAR(frame->rawMetrics.boundingCenterY, 0.0, 1.0);
    EXPECT_NEAR(frame->rawMetrics.boundingWidth, predicted.width, 1.5);
    EXPECT_NEAR(frame->rawMetrics.boundingHeight, predicted.height, 1.5);
    EXPECT_LE(frame->rawMetrics.invalidFraction, 0.001);
  }
}

TEST(RenderedOutput, DiskRotationConvention) {
  const double progradeIsco = blackhole::physics::NovikovThorneDisk::iscoRadius(0.6);
  const double retrogradeIsco = blackhole::physics::NovikovThorneDisk::iscoRadius(-0.6);
  ASSERT_GT(retrogradeIsco, progradeIsco);
  ASSERT_GT(physics::keplerianOmega(progradeIsco, 0.6), 0.0);
  ASSERT_GT(physics::keplerianOmega(retrogradeIsco, -0.6), 0.0);
}

TEST(RenderedOutput, DiskRotationAndRetrogradeInnerEdge) {
  if (!fullSweep()) {
    GTEST_SKIP() << "set BLACKHOLE_RENDER_FULL=1 for disk and spin sweeps";
  }
  if (!contextAvailable()) {
    GTEST_SKIP() << "GL 4.6 context unavailable";
  }
  const auto positive = capture("Cd+");
  const auto negative = capture("Cd-");
  // The camera views physics x = -30. Screen right points to physics -y,
  // where +phi motion recedes; the approaching disk occupies screen left.
  for (const CapturedFrame *frame : {&positive, &negative}) {
    ASSERT_GT(frame->diskMetrics.leftDiskPixels, 0u);
    ASSERT_GT(frame->diskMetrics.rightDiskPixels, 0u);
    EXPECT_GT(frame->diskMetrics.leftMeanLuminance,
              frame->diskMetrics.rightMeanLuminance);
    EXPECT_EQ(frame->rawMetrics.invalidFraction, 0.0);
  }
  ASSERT_GT(positive.diskMetrics.nearSideInnerEdgePixels, 0.0);
  ASSERT_GT(negative.diskMetrics.nearSideInnerEdgePixels, 0.0);
  EXPECT_GT(negative.diskMetrics.nearSideInnerEdgePixels,
            positive.diskMetrics.nearSideInnerEdgePixels);
}

TEST(RenderedOutput, CriticalRegionExhaustion) {
  if (!fullSweep()) {
    GTEST_SKIP() << "set BLACKHOLE_RENDER_FULL=1 for disk and spin sweeps";
  }
  if (!contextAvailable()) {
    GTEST_SKIP() << "GL 4.6 context unavailable";
  }
  const auto balanced = capture("D");
  const auto reference = capture("D", "fragment", "reference");
  const double balancedEdgeError = criticalEdgeColumnError(balanced);
  const double referenceEdgeError = criticalEdgeColumnError(reference);
  EXPECT_GT(metadataInteger(artifactRoot() / "D-fragment-reference.png.json", "max_steps"),
            metadataInteger(artifactRoot() / "D-fragment-balanced.png.json", "max_steps"))
      << "the reference tier must change the effective step budget";
  EXPECT_LE(reference.rawMetrics.exhaustedFraction, balanced.rawMetrics.exhaustedFraction);
  EXPECT_LE(referenceEdgeError, balancedEdgeError);
  EXPECT_TRUE(reference.rawMetrics.exhaustedFraction < balanced.rawMetrics.exhaustedFraction ||
              referenceEdgeError < balancedEdgeError)
      << "the reference tier must reduce max-step pixels or the center-row edge error: "
      << "balanced=" << balancedEdgeError << " px, reference=" << referenceEdgeError << " px";
  EXPECT_TRUE(reference.rawMetrics.terminalHash != balanced.rawMetrics.terminalHash ||
              reference.rawMetrics.luminanceHash != balanced.rawMetrics.luminanceHash)
      << "the zoomed critical region must distinguish the quality tiers";
  EXPECT_EQ(reference.rawMetrics.invalidFraction, 0.0);
}

// The fresh desktop frame shows the disk as a lit band rather than a dark
// surface over the sky. Under the record exposure rule (render/record_mode.h)
// a disk pixel below 1% of the disk's 99th-percentile raw luminance displays
// as black, so such pixels mark disk area that hides the sky while showing no
// emission; a disk edge far beyond the emitting radii makes them the majority.
// The disk also leaves most of the frame to the sky and the shadow.
TEST(RenderedOutput, DefaultSceneDiskStaysLit) {
  if (!contextAvailable()) {
    GTEST_SKIP() << "GL 4.6 context unavailable";
  }
  const CapturedFrame frame = captureDefaultScene();
  std::vector<float> disk;
  std::size_t captured = 0;
  for (std::size_t index = 0; index < frame.terminals.size(); ++index) {
    if (frame.terminals.at(index) == BH_TERMINAL_DISK_HIT) {
      disk.push_back(frame.raw.at(index));
    } else if (frame.terminals.at(index) == BH_TERMINAL_HORIZON) {
      ++captured;
    }
  }
  ASSERT_FALSE(disk.empty());
  EXPECT_GT(captured, 0U) << "the default camera must show the shadow";
  const double diskFraction =
      static_cast<double>(disk.size()) / static_cast<double>(frame.terminals.size());
  EXPECT_LE(diskFraction, 0.35) << "the disk must leave most of the frame to sky and shadow";
  std::vector<float> sorted = disk;
  const auto rank = static_cast<std::ptrdiff_t>((sorted.size() * 99U) / 100U);
  std::nth_element(sorted.begin(), sorted.begin() + rank, sorted.end());
  const float bright = sorted.at(static_cast<std::size_t>(rank));
  const auto dark =
      std::ranges::count_if(disk, [bright](float value) { return value < (0.01f * bright); });
  const double darkFraction = static_cast<double>(dark) / static_cast<double>(disk.size());
  EXPECT_LE(darkFraction, 0.05) << "disk pixels below 1% of L99 display as an unlit surface";
}
