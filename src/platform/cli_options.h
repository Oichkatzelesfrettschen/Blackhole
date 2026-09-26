/**
 * @file cli_options.h
 * @brief Command-line record/export options and their argv parser.
 *
 * CliOptions holds every value the argv sweep can set: the export and
 * record-frame paths, the record profile and showcase composition, and the
 * per-axis camera/framing/background overrides (each paired with a has-flag so
 * the render loop can tell an explicit override from a default). parseCliOptions
 * fills one from argv and reports whether main should run or exit; the semantic
 * profile/composition validation stays with main, where the showcase-orbit
 * table lives.
 */

#ifndef BLACKHOLE_PLATFORM_CLI_OPTIONS_H
#define BLACKHOLE_PLATFORM_CLI_OPTIONS_H

#include <string>

namespace platform {

struct CliOptions {
  std::string curveTsvPath;
  std::string exportFramePath;
  std::string exportRawFramePath;
  std::string recordFramesDir;
  std::string recordProfile = "cinematic";
  std::string recordComposition = "wide-right";
  std::string recordBackgroundId;
  int         recordFramesTotal = 0; ///< Seeded to K_CINEMATIC_FRAMES by parseCliOptions.
  int         recordStartFrame  = 0;
  float       recordYawDeg = 0.0f;
  float       recordPitchDeg = 0.0f;
  float       recordDistance = 0.0f;
  float       recordFovDeg = 0.0f;
  float       recordExposure = 0.0f;
  float       recordSpin = 0.0f;
  float       recordSweepDeg = 0.0f;
  float       recordFrameX = 0.0f;
  float       recordFrameY = 0.0f;
  float       recordBackgroundYawDeg = 0.0f;
  float       recordBackgroundPitchDeg = 0.0f;
  // The has-flags pack together after the floats; a float followed by its
  // flag pads each pair to 8 bytes (clang-analyzer-optin.performance.Padding).
  bool        hasRecordYaw = false;
  bool        hasRecordPitch = false;
  bool        hasRecordDistance = false;
  bool        hasRecordFov = false;
  bool        hasRecordExposure = false;
  bool        hasRecordSpin = false;
  bool        hasRecordSweep = false;
  bool        hasRecordFrameX = false;
  bool        hasRecordFrameY = false;
  bool        hasRecordBackgroundId = false;
  bool        hasRecordBackgroundYaw = false;
  bool        hasRecordBackgroundPitch = false;
};

/** @brief Whether main should proceed or exit after argv parsing. */
enum class CliParseOutcome {
  Run,         ///< Options parsed; continue startup.
  ExitSuccess, ///< --help was handled; exit 0.
  ExitFailure, ///< Unknown or malformed argument; exit non-zero.
};

/** @brief Prints the usage banner (options, defaults, record profiles) to stdout. */
void printCliUsage(const char *argv0);

/** @brief Parses argv into out, printing usage on --help and on bad arguments.
 *         Returns Run when startup should continue. */
CliParseOutcome parseCliOptions(int argc, char **argv, CliOptions &out);

} // namespace platform

#endif // BLACKHOLE_PLATFORM_CLI_OPTIONS_H
