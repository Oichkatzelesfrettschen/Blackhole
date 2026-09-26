#include <cstdio>
#include "game/campaign_sim_lines.h"
int main() {
  using namespace campaign_sim;
  for (Commit c : {Commit::Outer, Commit::Solo, Commit::Pod, Commit::Stabilize}) {
    const auto r = runLine(42, 1200, c);
    std::printf("%-5s energy=%9.1f stab=%6.3f integrity=%.3f cleared=%lld status=%d\n", commitLabel(c),
                r.view.energyUnits, r.view.stabilization, r.view.fleetIntegrity,
                static_cast<long long>(r.view.clearedTurn), static_cast<int>(r.view.status));
  }
}
