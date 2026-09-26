#include <cstdio>
#include "physics/iron_kline.h"
#include "physics/verified/energy_conserving_geodesic.hpp"
int main() {
  for (auto [a, r] : {std::pair{0.0, 6.0}, {0.9, 2.320883041761887}, {0.998, 1.2369706551751845}})
    std::printf("kerrDiskGFactor(r=%.6f, phi=0, a=%.3f, i=0) = %.6f\n", r, a, physics::kerrDiskGFactor(r, 0.0, a, 0.0));
  return 0;
}
