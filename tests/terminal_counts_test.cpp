#include <array>
#include <cstdint>

#include <gtest/gtest.h>

#include "render/terminal_counts.h"
#include "../shader/include/ray_terminal.h"

TEST(TerminalCounts, FoldKeepsExhaustionDistinctFromEscape) {
  constexpr std::array<std::uint32_t, 10> codes = {
      BH_TERMINAL_HORIZON, BH_TERMINAL_ESCAPE, BH_TERMINAL_DISK_HIT,
      BH_TERMINAL_MAX_STEPS, BH_TERMINAL_MAX_STEPS, BH_TERMINAL_NON_FINITE,
      BH_TERMINAL_INVARIANT_FAILURE, BH_TERMINAL_OPAQUE_MEDIUM,
      BH_TERMINAL_OUTSIDE_DOMAIN, 99};
  const blackhole::TerminalCounts counts = blackhole::foldTerminalCodes(codes);
  EXPECT_EQ(counts[BH_TERMINAL_HORIZON], 1U);
  EXPECT_EQ(counts[BH_TERMINAL_ESCAPE], 1U);
  EXPECT_EQ(counts[BH_TERMINAL_DISK_HIT], 1U);
  EXPECT_EQ(counts[BH_TERMINAL_MAX_STEPS], 2U);
  EXPECT_EQ(counts[BH_TERMINAL_NON_FINITE], 1U);
  EXPECT_EQ(counts[BH_TERMINAL_INVARIANT_FAILURE], 2U);
  EXPECT_EQ(counts[BH_TERMINAL_OPAQUE_MEDIUM], 1U);
  EXPECT_EQ(counts[BH_TERMINAL_OUTSIDE_DOMAIN], 1U);
}
