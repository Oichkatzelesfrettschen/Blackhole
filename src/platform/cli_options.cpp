/**
 * @file cli_options.cpp
 * @brief Usage banner and argv sweep for the record/export command-line options.
 */

#include "cli_options.h"

#include <cstdio>
#include <cstdlib>
#include <string>

#include "cinematic.h" // K_CINEMATIC_FRAMES

namespace platform {

void printCliUsage(const char *argv0) {
  std::printf("Usage: %s [--curve-tsv <path>] [--export-frame <path.png>]"
              " [--export-raw-frame <path.pfm>]"
              " [--record-frames <dir> <N>] [--record-profile <name>]\n", argv0);
  std::printf("  --curve-tsv <path>       Load a 2-column TSV and plot it in ImGui.\n");
  std::printf("  --export-frame <path>    Render one frame, save as PNG, then exit.\n");
  std::printf("  --export-raw-frame <path> Export raw texBlackhole HDR RGB as PFM, then exit.\n");
  std::printf("  --record-frames <dir> N  Record N profile-driven frames as PNG into <dir>.\n");
  std::printf("                           N defaults to %d (3 min @ 60 fps).\n",
              K_CINEMATIC_FRAMES);
  std::printf("  --record-profile <name>  Recording profile: cinematic | compare-orbit-near | showcase-orbit.\n");
  std::printf("  --start-frame N          Start recording from frame N (default: 0).\n");
  std::printf("  --record-yaw <deg>       Override record camera yaw.\n");
  std::printf("  --record-pitch <deg>     Override record camera pitch.\n");
  std::printf("  --record-distance <r>    Override record camera distance.\n");
  std::printf("  --record-fov <deg>       Override record camera field of view.\n");
  std::printf("  --record-exposure <x>    Override record tone-map exposure.\n");
  std::printf("  --record-spin <a>        Override the Kerr spin a/M every recorded frame.\n");
  std::printf("  --record-sweep-deg <x>   Override orbit sweep degrees across frames.\n");
  std::printf("  --record-composition <n> Showcase framing: centered | left-third | right-third | wide-left | wide-right.\n");
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
    if (arg == "--export-frame" && i + 1 < argc) {
      out.exportFramePath = argv[++i];
      continue;
    }
    if (arg == "--export-raw-frame" && i + 1 < argc) {
      out.exportRawFramePath = argv[++i];
      continue;
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
