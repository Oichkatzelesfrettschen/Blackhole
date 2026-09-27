/**
 * @file observer_sky_lut_options_test.cpp
 * @brief Unit tests for observer_sky_lut's argument parsing and observer
 *        resolution (src/tools/observer_sky_lut_options.h), exercised
 *        without spawning the tool's process.
 */

#include <algorithm>
#include <optional>
#include <span>
#include <vector>

#include <gtest/gtest.h>

#include "physics/kerr_observer.h"
#include "tools/observer_sky_lut_options.h"

using blackhole::observer_sky_lut_cli::Options;
using blackhole::observer_sky_lut_cli::parseOptions;
using blackhole::observer_sky_lut_cli::resolveObserver;
namespace ko = physics::kerr_observer;

namespace {

/** @brief parseOptions over a fixed argv built from string literals. */
std::optional<Options> parse(const std::vector<const char *> &args) {
  std::vector<char *> argv(args.size());
  std::transform(args.begin(), args.end(), argv.begin(), [](const char *arg) {
    return const_cast<char *>(arg); // NOLINT(cppcoreguidelines-pro-type-const-cast)
                                    // -- parseOptions never writes through argv
  });
  return parseOptions(std::span<char *>(argv.data(), argv.size()));
}

} // namespace

/**
 * Falsifier: an explicit --height given before --width is overwritten by
 * width / 2, so argument order changes the output. --height sets
 * heightExplicit, and a later --width leaves it alone.
 */
TEST(ObserverSkyLutOptions, WidthAfterHeightKeepsExplicitHeight) {
  const auto options = parse({"observer_sky_lut", "--height", "300", "--width", "800"});
  if (!options.has_value()) {
    GTEST_FAIL() << "options is empty";
  }
  EXPECT_EQ(options->dimensions.width, 800U);
  EXPECT_EQ(options->dimensions.height, 300U);
}

TEST(ObserverSkyLutOptions, WidthAloneDerivesDefaultHeight) {
  const auto options = parse({"observer_sky_lut", "--width", "800"});
  if (!options.has_value()) {
    GTEST_FAIL() << "options is empty";
  }
  EXPECT_EQ(options->dimensions.width, 800U);
  EXPECT_EQ(options->dimensions.height, 400U);
}

TEST(ObserverSkyLutOptions, HeightAfterWidthOverridesDefault) {
  const auto options = parse({"observer_sky_lut", "--width", "800", "--height", "300"});
  if (!options.has_value()) {
    GTEST_FAIL() << "options is empty";
  }
  EXPECT_EQ(options->dimensions.width, 800U);
  EXPECT_EQ(options->dimensions.height, 300U);
}

/**
 * Falsifier: "--velocity 0.9 --canon" keeps velocity 0.9 instead of the
 * canon preset's orbiting observer, because --canon resets x, epsilon, and
 * observer but not an earlier --velocity.
 */
TEST(ObserverSkyLutOptions, CanonResetsEarlierVelocity) {
  const auto options = parse({"observer_sky_lut", "--velocity", "0.9", "--canon"});
  if (!options.has_value()) {
    GTEST_FAIL() << "options is empty";
  }
  EXPECT_FALSE(options->velocity.has_value());
}

TEST(ObserverSkyLutOptions, IscoDoesNotResetVelocity) {
  const auto options = parse({"observer_sky_lut", "--velocity", "0.9", "--isco"});
  if (!options.has_value()) {
    GTEST_FAIL() << "options is empty";
  }
  const std::optional<double> velocity = options->velocity;
  if (!velocity.has_value()) {
    GTEST_FAIL() << "velocity is empty";
  }
  EXPECT_DOUBLE_EQ(*velocity, 0.9);
}

/**
 * Falsifier: resolveObserver builds an ObserverKey for an explicit
 * --velocity or --observer zamo without checking x, so
 * "--epsilon 1 --x 0.5 --observer zamo" (x = 0.5 inside the Schwarzschild
 * horizon at offset 1.0) publishes a nonphysical bundle instead of being
 * refused.
 */
TEST(ObserverSkyLutOptions, RejectsZamoAtOrInsideHorizon) {
  Options options;
  options.epsilon = 1.0;
  options.x = 0.5;
  options.observer = "zamo";
  EXPECT_FALSE(resolveObserver(options).has_value());
}

TEST(ObserverSkyLutOptions, RejectsExplicitVelocityAtOrInsideHorizon) {
  Options options;
  options.epsilon = 1.0;
  options.x = ko::horizonOffset(1.0); // exactly at the horizon
  options.velocity = 0.1;
  EXPECT_FALSE(resolveObserver(options).has_value());
}

TEST(ObserverSkyLutOptions, AcceptsZamoOutsideHorizon) {
  Options options;
  options.epsilon = 1.0;
  options.x = 2.0;
  options.observer = "zamo";
  const auto key = resolveObserver(options);
  if (!key.has_value()) {
    GTEST_FAIL() << "key is empty";
  }
  EXPECT_DOUBLE_EQ(key->velocity, 0.0);
}

TEST(ObserverSkyLutOptions, AcceptsExplicitVelocityOutsideHorizon) {
  Options options;
  options.epsilon = 1.0;
  options.x = 2.0;
  options.velocity = 0.3;
  const auto key = resolveObserver(options);
  if (!key.has_value()) {
    GTEST_FAIL() << "key is empty";
  }
  EXPECT_DOUBLE_EQ(key->velocity, 0.3);
}
