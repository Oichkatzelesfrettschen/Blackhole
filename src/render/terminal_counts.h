#ifndef BLACKHOLE_RENDER_TERMINAL_COUNTS_H
#define BLACKHOLE_RENDER_TERMINAL_COUNTS_H

#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

#include "../../shader/include/ray_terminal.h"

namespace blackhole {

inline constexpr std::size_t K_TERMINAL_CLASS_COUNT = BH_TERMINAL_INVARIANT_FAILURE + 1;

struct TerminalCounts {
  std::array<std::uint64_t, K_TERMINAL_CLASS_COUNT> values{};

  [[nodiscard]] std::uint64_t operator[](std::size_t terminal) const {
    return values.at(terminal);
  }
};

[[nodiscard]] inline TerminalCounts foldTerminalCodes(std::span<const std::uint32_t> codes) {
  TerminalCounts counts;
  for (const std::uint32_t code : codes) {
    const std::size_t index = code < K_TERMINAL_CLASS_COUNT
                                  ? static_cast<std::size_t>(code)
                                  : static_cast<std::size_t>(BH_TERMINAL_INVARIANT_FAILURE);
    ++counts.values.at(index);
  }
  return counts;
}

} // namespace blackhole

#endif
