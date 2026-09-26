/**
 * @file observer_sky_lut_options_test.cpp
 * @brief Unit tests for observer_sky_lut's argument parsing and observer
 *        resolution (src/tools/observer_sky_lut_options.h), exercised
 *        without spawning the tool's process.
 */

#include <algorithm>
#include <cstddef>
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
 * Falsifier: before the fix, --width always set height = width / 2
 * unconditionally, so an explicit --height given before --width was
 * silently overwritten and argument order changed the output. With the
 * fix, --height sets heightExplicit and a later --width no longer touches
 * it.
 */
TEST(ObserverSkyLutOptions, WidthAfterHeightKeepsExplicitHeight) {
  const auto options = parse({"observer_sky_lut", "--height", "300", "--width", "800"});
  ASSERT_TRUE(options.has_value());
  EXPECT_EQ(options->dimensions.width, 800U);
  EXPECT_EQ(options->dimensions.height, 300U);
}

TEST(ObserverSkyLutOptions, WidthAloneDerivesDefaultHeight) {
  const auto options = parse({"observer_sky_lut", "--width", "800"});
  ASSERT_TRUE(options.has_value());
  EXPECT_EQ(options->dimensions.width, 800U);
  EXPECT_EQ(options->dimensions.height, 400U);
}

TEST(ObserverSkyLutOptions, HeightAfterWidthOverridesDefault) {
  const auto options = parse({"observer_sky_lut", "--width", "800", "--height", "300"});
  ASSERT_TRUE(options.has_value());
  EXPECT_EQ(options->dimensions.width, 800U);
  EXPECT_EQ(options->dimensions.height, 300U);
}

/**
 * Falsifier: before the fix, --canon reset x and epsilon/observer but left
 * an earlier --velocity in place, so "--velocity 0.9 --canon" produced a
 * key with velocity 0.9 instead of the canon preset's orbiting observer.
 */
TEST(ObserverSkyLutOptions, CanonResetsEarlierVelocity) {
  const auto options = parse({"observer_sky_lut", "--velocity", "0.9", "--canon"});
  ASSERT_TRUE(options.has_value());
  EXPECT_FALSE(options->velocity.has_value());
}

TEST(ObserverSkyLutOptions, IscoDoesNotResetVelocity) {
  const auto options = parse({"observer_sky_lut", "--velocity", "0.9", "--isco"});
  ASSERT_TRUE(options.has_value());
  ASSERT_TRUE(options->velocity.has_value());
  EXPECT_DOUBLE_EQ(*options->velocity, 0.9);
}

/**
 * Falsifier: before the fix, resolveObserver built an ObserverKey for any
 * explicit --velocity or --observer zamo regardless of x, so
 * "--epsilon 1 --x 0.5 --observer zamo" (x = 0.5 inside the Schwarzschild
 * horizon at offset 1.0) published a nonphysical bundle instead of being
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
  ASSERT_TRUE(key.has_value());
  EXPECT_DOUBLE_EQ(key->velocity, 0.0);
}

TEST(ObserverSkyLutOptions, AcceptsExplicitVelocityOutsideHorizon) {
  Options options;
  options.epsilon = 1.0;
  options.x = 2.0;
  options.velocity = 0.3;
  const auto key = resolveObserver(options);
  ASSERT_TRUE(key.has_value());
  EXPECT_DOUBLE_EQ(key->velocity, 0.3);
}
