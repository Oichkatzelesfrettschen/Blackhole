/**
 * @file cli_options.cpp
 * @brief Usage banner and argv sweep for the record/export command-line options.
 */

#include "cli_options.h"

#include <charconv>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <system_error>

#include "cinematic.h" // K_CINEMATIC_FRAMES
#include "physics/safe_limits.h"

namespace platform {

void printCliUsage(const char *argv0) {
  std::printf("Usage: %s [--curve-tsv <path>] [--export-frame <path.png>]"
              " [--export-raw-frame <path.pfm>]"
              " [--record-frames <dir> <N>] [--record-profile <name>]\n", argv0);
  std::printf("  --curve-tsv <path>       Load a 2-column TSV and plot it in ImGui.\n");
  std::printf("  --workspace-screenshot <prefix>  Capture whole-window PNG and layout JSON.\n");
  std::printf("  --workspace <simulator|gororoba|diagnostics>  Select a fresh workspace.\n");
  std::printf("  --window-size <WxH>      Capture framebuffer size.\n");
  std::printf("  --ui-scale <S>           Capture UI scale (default: 1).\n");
  std::printf("  --export-frame <path>    Render one frame, save as PNG, then exit.\n");
  std::printf("  --export-raw-frame <path> Export raw texBlackhole HDR RGB as PFM, then exit.\n");
  std::printf("  --reference-scene <A|B|C+|C-|Cd+|Cd-|D>  Fixed camera and source model for rendered validation.\n");
  std::printf("  --reference-backend <fragment|compute|cuda>  Reference render backend.\n");
  std::printf("  --reference-quality <balanced|reference>  Numerical tier.\n");
  std::printf("  --renderer-geodesic <legacy-beauty|schwarzschild-reference|kerr-reference>  Startup geodesic.\n");
  std::printf("  --renderer-backend <fragment|compute|cuda>  Startup backend.\n");
  std::printf("  --export-frames N       Export on settled frame N, then exit (default: frame 5, exit 6).\n");
  std::printf("  --export-size W H       Set export render dimensions.\n");
  std::printf("  --export-exposure X     Set export exposure without changing saved settings.\n");
  std::printf("  --export-bloom X        Set export bloom strength without changing saved settings.\n");
  std::printf("  --export-tone-mapping on|off  Set export tone mapping.\n");
  std::printf("  --record-frames <dir> N  Record N profile-driven frames as PNG into <dir>.\n");
  std::printf("                           N defaults to %d (3 min @ 60 fps).\n",
              K_CINEMATIC_FRAMES);
  std::printf("  --record-profile <name>  Recording profile: cinematic | compare-orbit-near | showcase-orbit.\n");
  std::printf("  --start-frame N          Start recording from frame N (default: 0).\n");
  std::printf("  --record-yaw <deg>       Showcase-orbit base yaw.\n");
  std::printf("  --record-pitch <deg>     Showcase-orbit pitch.\n");
  std::printf("  --record-distance <r>    Override the black-hole record camera distance (every profile);\n"
              "                           the tesseract scene keeps its fixed fill.\n");
  std::printf("  --record-fov <deg>       Override record camera field of view (every profile).\n");
  std::printf("  --record-exposure <x>    Override record tone-map exposure.\n");
  std::printf("  --record-spin <a>        Override the Kerr spin a/M every recorded frame.\n");
  std::printf("  --record-sweep-deg <x>   Showcase-orbit sweep degrees across frames.\n");
  std::printf("  --record-composition <n> Showcase framing: above-disk (default) | inside-disk (= wide-right) | centered | left-third | right-third | wide-left | wide-right.\n");
  std::printf("  --record-frame-x <n>     Override horizontal framing offset in half-frame units.\n");
  std::printf("  --record-frame-y <n>     Override vertical framing offset in half-frame units.\n");
  std::printf("  --record-background-id <id>  Override showcase background asset id.\n");
  std::printf("  --record-bg-yaw <deg>    Override showcase background yaw.\n");
  std::printf("  --record-bg-pitch <deg>  Override showcase background pitch.\n");
}

// Flat argv dispatch: one branch per option flag, so the cognitive-complexity
// score reflects the option count, not nesting depth.
// NOLINTNEXTLINE(readability-function-cognitive-complexity)
CliParseOutcome parseCliOptions(int argc, char **argv, CliOptions &out) {
  out.recordFramesTotal = K_CINEMATIC_FRAMES;
  for (int i = 1; i < argc; ++i) {
    std::string const arg = argv[i];
    if (arg == "--help" || arg == "-h") {
      printCliUsage(argv[0]);
      return CliParseOutcome::ExitSuccess;
    }
    if (arg == "--curve-tsv" && i + 1 < argc) {
      out.curveTsvPath = argv[++i];
      continue;
    }
    if (arg == "--workspace-screenshot" && i + 1 < argc) {
      out.workspaceScreenshotPath = argv[++i];
      continue;
    }
    if (arg == "--workspace" && i + 1 < argc) {
      out.workspaceName = argv[++i];
      continue;
    }
    if (arg == "--window-size" && i + 1 < argc) {
      const std::string value = argv[++i];
      const size_t separator = value.find('x');
      if (separator != std::string::npos) {
        const char *const begin = value.data();
        const char *const end = begin + value.size();
        const auto widthResult = std::from_chars(begin, begin + separator, out.windowWidth);
        const auto heightResult = std::from_chars(begin + separator + 1, end, out.windowHeight);
        if (widthResult.ec == std::errc{} && widthResult.ptr == begin + separator &&
            heightResult.ec == std::errc{} && heightResult.ptr == end &&
            out.windowWidth >= 640 && out.windowWidth <= 8192 && out.windowHeight >= 480 &&
            out.windowHeight <= 4320) {
          continue;
        }
      }
    }
    if (arg == "--ui-scale" && i + 1 < argc) {
      const std::string value = argv[++i];
      const auto result = std::from_chars(value.data(), value.data() + value.size(), out.uiScale);
      if (result.ec == std::errc{} && result.ptr == value.data() + value.size() &&
          physics::safeIsfinite(out.uiScale) && out.uiScale >= 0.5f && out.uiScale <= 3.0f) {
        continue;
      }
    }
    if (arg == "--export-frame" && i + 1 < argc) {
      out.exportFramePath = argv[++i];
      continue;
    }
    if (arg == "--export-raw-frame" && i + 1 < argc) {
      out.exportRawFramePath = argv[++i];
      continue;
    }
    if (arg == "--reference-scene" && i + 1 < argc) {
      out.referenceScene = argv[++i];
      continue;
    }
    if (arg == "--reference-backend" && i + 1 < argc) {
      out.referenceBackend = argv[++i];
      continue;
    }
    if (arg == "--reference-quality" && i + 1 < argc) {
      out.referenceQuality = argv[++i];
      continue;
    }
    if (arg == "--renderer-geodesic" && i + 1 < argc) {
      out.rendererGeodesic = argv[++i];
      if (out.rendererGeodesic == "legacy-beauty" ||
          out.rendererGeodesic == "schwarzschild-reference" ||
          out.rendererGeodesic == "kerr-reference") {
        continue;
      }
    }
    if (arg == "--renderer-backend" && i + 1 < argc) {
      out.rendererBackend = argv[++i];
      if (out.rendererBackend == "fragment" || out.rendererBackend == "compute" ||
          out.rendererBackend == "cuda") {
        continue;
      }
    }
    if (arg == "--export-frames" && i + 1 < argc) {
      const std::string value = argv[++i];
      const auto [end, error] = std::from_chars(value.data(), value.data() + value.size(),
                                                out.exportFrames);
      if (error == std::errc{} && end == value.data() + value.size() &&
          out.exportFrames >= 5) {
        continue;
      }
    }
    if (arg == "--export-size" && i + 2 < argc) {
      const std::string width = argv[++i];
      const std::string height = argv[++i];
      const auto [widthEnd, widthError] = std::from_chars(
          width.data(), width.data() + width.size(), out.exportWidth);
      const auto [heightEnd, heightError] = std::from_chars(
          height.data(), height.data() + height.size(), out.exportHeight);
      if (widthError == std::errc{} && heightError == std::errc{} &&
          widthEnd == width.data() + width.size() &&
          heightEnd == height.data() + height.size() &&
          out.exportWidth > 0 && out.exportHeight > 0) {
        continue;
      }
    }
    if (arg == "--export-exposure" && i + 1 < argc) {
      const std::string value = argv[++i];
      const auto [end, error] = std::from_chars(value.data(), value.data() + value.size(),
                                                out.exportExposure);
      if (error == std::errc{} && end == value.data() + value.size() &&
          physics::safeIsfinite(out.exportExposure) && out.exportExposure > 0.0f) {
        out.hasExportExposure = true;
        continue;
      }
    }
    if (arg == "--export-bloom" && i + 1 < argc) {
      const std::string value = argv[++i];
      const auto [end, error] = std::from_chars(value.data(), value.data() + value.size(),
                                                out.exportBloomStrength);
      if (error == std::errc{} && end == value.data() + value.size() &&
          physics::safeIsfinite(out.exportBloomStrength) && out.exportBloomStrength >= 0.0f) {
        out.hasExportBloomStrength = true;
        continue;
      }
    }
    if (arg == "--export-tone-mapping" && i + 1 < argc) {
      const std::string value = argv[++i];
      if (value == "on" || value == "off") {
        out.hasExportToneMapping = true;
        out.exportToneMapping = value == "on";
        continue;
      }
    }
    if (arg == "--record-frames" && i + 1 < argc) {
      out.recordFramesDir = argv[++i];
      if (i + 1 < argc && argv[i + 1][0] != '-') {
        out.recordFramesTotal = std::atoi(argv[++i]); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c) -- CLI count, invalid input defaults to 0
      }
      continue;
    }
    if (arg == "--start-frame" && i + 1 < argc) {
      out.recordStartFrame = std::atoi(argv[++i]); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c) -- CLI frame index, invalid input defaults to 0
      continue;
    }
    if (arg == "--record-profile" && i + 1 < argc) {
      out.recordProfile = argv[++i];
      continue;
    }
    if (arg == "--record-composition" && i + 1 < argc) {
      out.recordComposition = argv[++i];
      continue;
    }
    if (arg == "--record-yaw" && i + 1 < argc) {
      out.recordYawDeg = std::strtof(argv[++i], nullptr);
      out.hasRecordYaw = true;
      continue;
    }
    if (arg == "--record-pitch" && i + 1 < argc) {
      out.recordPitchDeg = std::strtof(argv[++i], nullptr);
      out.hasRecordPitch = true;
      continue;
    }
    if (arg == "--record-distance" && i + 1 < argc) {
      out.recordDistance = std::strtof(argv[++i], nullptr);
      out.hasRecordDistance = true;
      continue;
    }
    if (arg == "--record-fov" && i + 1 < argc) {
      out.recordFovDeg = std::strtof(argv[++i], nullptr);
      out.hasRecordFov = true;
      continue;
    }
    if (arg == "--record-exposure" && i + 1 < argc) {
      out.recordExposure = std::strtof(argv[++i], nullptr);
      out.hasRecordExposure = true;
      continue;
    }
    if (arg == "--record-spin" && i + 1 < argc) {
      out.recordSpin = std::strtof(argv[++i], nullptr);
      out.hasRecordSpin = true;
      continue;
    }
    if (arg == "--record-sweep-deg" && i + 1 < argc) {
      out.recordSweepDeg = std::strtof(argv[++i], nullptr);
      out.hasRecordSweep = true;
      continue;
    }
    if (arg == "--record-frame-x" && i + 1 < argc) {
      out.recordFrameX = std::strtof(argv[++i], nullptr);
      out.hasRecordFrameX = true;
      continue;
    }
    if (arg == "--record-frame-y" && i + 1 < argc) {
      out.recordFrameY = std::strtof(argv[++i], nullptr);
      out.hasRecordFrameY = true;
      continue;
    }
    if (arg == "--record-background-id" && i + 1 < argc) {
      out.recordBackgroundId = argv[++i];
      out.hasRecordBackgroundId = true;
      continue;
    }
    if (arg == "--record-bg-yaw" && i + 1 < argc) {
      out.recordBackgroundYawDeg = std::strtof(argv[++i], nullptr);
      out.hasRecordBackgroundYaw = true;
      continue;
    }
    if (arg == "--record-bg-pitch" && i + 1 < argc) {
      out.recordBackgroundPitchDeg = std::strtof(argv[++i], nullptr);
      out.hasRecordBackgroundPitch = true;
      continue;
    }
    std::printf("Unknown argument: %s\n", arg.c_str());
    printCliUsage(argv[0]);
    return CliParseOutcome::ExitFailure;
  }
  return CliParseOutcome::Run;
}

} // namespace platform
