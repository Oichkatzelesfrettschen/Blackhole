#ifndef BLACKHOLE_GAME_FIRST_PLAY_BRIEFING_H
#define BLACKHOLE_GAME_FIRST_PLAY_BRIEFING_H

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

namespace game {

class DesktopGame;

struct BriefingStep {
  std::string_view title;
  std::string body;
  bool complete = false;
};

struct Briefing {
  std::vector<BriefingStep> steps;
  std::size_t currentIndex = 0;
};

[[nodiscard]] Briefing evaluateBriefing(const DesktopGame &session);

} // namespace game

#endif
