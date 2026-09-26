/**
 * @file env_config_test.cpp
 * @brief Unit tests for parseEnvironmentFloat, the BLACKHOLE_* float parser.
 *
 * The parser feeds render overrides such as the compare step size and the
 * outlier fraction; a rejected input must read as 0 rather than as a partial
 * or non-finite value. The target links blackhole_testcore, which compiles
 * env_config.cpp with the project's math flags, so under ENABLE_FAST_MATH the
 * "inf" and "nan" cases exercise the bit-level classification the parser uses.
 */

#include <gtest/gtest.h>

#include "render/env_config.h"

using blackhole::parseEnvironmentFloat;

TEST(ParseEnvironmentFloat, AcceptsDecimalForms) {
  EXPECT_FLOAT_EQ(parseEnvironmentFloat("1.5"), 1.5F);
  EXPECT_FLOAT_EQ(parseEnvironmentFloat("-2.25"), -2.25F);
  EXPECT_FLOAT_EQ(parseEnvironmentFloat("+0.125"), 0.125F);
  EXPECT_FLOAT_EQ(parseEnvironmentFloat("3e-2"), 0.03F);
  EXPECT_FLOAT_EQ(parseEnvironmentFloat("  7 "), 7.0F);
  EXPECT_FLOAT_EQ(parseEnvironmentFloat("4\n"), 4.0F);
}

TEST(ParseEnvironmentFloat, RejectsRepeatedSigns) {
  EXPECT_EQ(parseEnvironmentFloat("+-1"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("++1"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("--1"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("-+1"), 0.0F);
}

TEST(ParseEnvironmentFloat, RejectsTrailingCharacters) {
  EXPECT_EQ(parseEnvironmentFloat("1.5x"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("2 3"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("0.5f"), 0.0F);
}

TEST(ParseEnvironmentFloat, RejectsHexNonFiniteAndOutOfRange) {
  EXPECT_EQ(parseEnvironmentFloat("0x1p3"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("inf"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("-infinity"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("nan"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("1e39"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("1e400"), 0.0F);
}

TEST(ParseEnvironmentFloat, RejectsEmptyAndNull) {
  EXPECT_EQ(parseEnvironmentFloat(""), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("   "), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat("+"), 0.0F);
  EXPECT_EQ(parseEnvironmentFloat(nullptr), 0.0F);
}
