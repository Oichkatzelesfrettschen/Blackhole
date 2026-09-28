#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <ios>
#include <numbers>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

#include <gtest/gtest.h>
#include <stdlib.h> // NOLINT(modernize-deprecated-headers) -- POSIX setenv declaration.
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include "../shader/include/ray_terminal.h"
#include "physics/analytic_kerr_geodesic.h"
#include "render/render_output_metrics.h"
#include "support/gl_compute_harness.h"

#ifdef BH_RENDER_HAS_CUDA
#include <cuda_runtime_api.h>
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
};

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
         << ",\n  \"terminal_hash\": " << raw.terminalHash << ",\n"
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
                      std::string_view quality = "balanced") {
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
  frame.rawMetrics = blackhole::measureImage(frame.raw, frame.terminals, frame.width, frame.height);
  frame.displayMetrics =
      blackhole::measureImage(frame.display, frame.terminals, frame.width, frame.height);
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

struct KerrScreenGeometry {
  double center = 0.0;
  double horizontalDiameter = 0.0;
  double verticalDiameter = 0.0;
};

KerrScreenGeometry kerrScreenGeometry(double spin, int imageHeight) {
  const double magnitude = std::abs(spin);
  const double innerOrbit = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(-magnitude)));
  const double outerOrbit = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(magnitude)));
  double minimum = 1.0e6;
  double maximum = -1.0e6;
  double maximumBeta = 0.0;
  const double inclination = std::numbers::pi / 3.0;
  const double sine = std::sin(inclination);
  const double cosine = std::cos(inclination);
  const double cotangent = cosine / sine;
  for (int index = 0; index <= 1024; ++index) {
    const double radius =
        innerOrbit + ((outerOrbit - innerOrbit) * static_cast<double>(index) / 1024.0);
    const auto impact = physics::criticalImpactParams(radius, spin);
    const double alpha = -impact.xi / sine;
    const double betaSquared = impact.eta + (spin * spin * cosine * cosine) -
                               (impact.xi * impact.xi * cotangent * cotangent);
    if (betaSquared < 0.0) {
      continue;
    }
    minimum = std::min(minimum, alpha);
    maximum = std::max(maximum, alpha);
    maximumBeta = std::max(maximumBeta, std::sqrt(betaSquared));
  }
  const double scale =
      static_cast<double>(imageHeight) / (60.0 * std::tan(std::numbers::pi / 12.0));
  return {.center = ((minimum + maximum) / 2.0) * scale,
          .horizontalDiameter = (maximum - minimum) * scale,
          .verticalDiameter = 2.0 * maximumBeta * scale};
}

bool contextAvailable() {
  const bhtest::HiddenGlContext context;
  return context.available();
}

} // namespace

// The capture verifies geometry, terminal classes, and image range together.
// NOLINTNEXTLINE(readability-function-cognitive-complexity)
TEST(RenderedOutput, SchwarzschildCriticalCurve) {
  if (!contextAvailable()) {
    GTEST_SKIP() << "GL 4.6 context unavailable";
  }
  const auto fragment = capture("A");
  const double predicted = blackhole::criticalRadiusPixels(1.0, 30.0, 30.0, fragment.height);
  EXPECT_GT(fragment.rawMetrics.capturedFraction, 0.01);
  EXPECT_GT(fragment.rawMetrics.escapedFraction, 0.01);
  EXPECT_LE(fragment.rawMetrics.invalidFraction, 0.001);
  EXPECT_EQ(fragment.rawMetrics.finiteFraction, 1.0);
  EXPECT_EQ(fragment.displayMetrics.finiteFraction, 1.0);
  EXPECT_GT(fragment.rawMetrics.maximum - fragment.rawMetrics.minimum, 0.1);
  EXPECT_LT(fragment.rawMetrics.maximum, 1.0e6);
  EXPECT_GE(fragment.displayMetrics.minimum, 0.0);
  EXPECT_LE(fragment.displayMetrics.maximum, 1.0);
  EXPECT_NEAR(fragment.rawMetrics.boundaryRadius, predicted, 8.0);
  EXPECT_NEAR(fragment.rawMetrics.luminanceBoundaryRadius, predicted, 8.0);
  EXPECT_LE(fragment.rawMetrics.circularity, 0.1);
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
    EXPECT_LT(comparison.mae, 0.1) << "shared GLSL plumbing parity";
#ifdef BH_RENDER_HAS_CUDA
    int devices = 0;
    if (cudaGetDeviceCount(&devices) == cudaSuccess && devices > 0) {
      const auto cuda = capture("A", "cuda");
      const auto cudaComparison = blackhole::compareImages(fragment.raw, cuda.raw);
      writeDifference(fragment, cuda, artifactRoot() / "A-fragment-cuda-diff.pgm");
      writeComparison(fragment, cuda, artifactRoot() / "A-fragment-cuda-comparison.json");
      EXPECT_LT(cudaComparison.mae, 0.2) << "CUDA pixel plumbing parity";
    }
#endif
  }
}

TEST(RenderedOutput, EmittingDiskLimbAndEdge) {
  if (!fullSweep()) {
    GTEST_SKIP() << "set BLACKHOLE_RENDER_FULL=1 for disk and spin sweeps";
  }
  if (!contextAvailable()) {
    GTEST_SKIP() << "GL 4.6 context unavailable";
  }
  const auto frame = capture("B");
  EXPECT_GT(frame.rawMetrics.limbContrast, 0.01);
  EXPECT_GE(frame.rawMetrics.limbWidth, 2.0);
  EXPECT_LT(frame.rawMetrics.limbWidth, 20.0);
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
  EXPECT_GT(positive.rawMetrics.capturedFraction, 0.0);
  EXPECT_GT(negative.rawMetrics.capturedFraction, 0.0);
  EXPECT_LT(positive.rawMetrics.centerOffsetX * negative.rawMetrics.centerOffsetX, 0.0);
  const auto predictedPositive = kerrScreenGeometry(0.6, positive.height);
  const auto predictedNegative = kerrScreenGeometry(-0.6, negative.height);
  EXPECT_LT(predictedPositive.center * predictedNegative.center, 0.0);
  EXPECT_NEAR(std::abs(positive.rawMetrics.centerOffsetX), std::abs(predictedPositive.center), 8.0);
  EXPECT_NEAR(std::abs(negative.rawMetrics.centerOffsetX), std::abs(predictedNegative.center), 8.0);
  EXPECT_NEAR(positive.rawMetrics.boundaryDiameter, predictedPositive.horizontalDiameter, 15.0);
  EXPECT_NEAR(negative.rawMetrics.boundaryDiameter, predictedNegative.horizontalDiameter, 15.0);
  EXPECT_NEAR(positive.rawMetrics.verticalDiameter, predictedPositive.verticalDiameter, 15.0);
  EXPECT_NEAR(negative.rawMetrics.verticalDiameter, predictedNegative.verticalDiameter, 15.0);
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
  EXPECT_LE(reference.rawMetrics.exhaustedFraction, balanced.rawMetrics.exhaustedFraction);
  EXPECT_EQ(reference.rawMetrics.invalidFraction, 0.0);
}
