#ifndef PHYSICS_NOISE_H
#define PHYSICS_NOISE_H

#include <cstdint>
#include <vector>

namespace physics {

struct NoiseVolume {
  int size = 0;
  std::vector<float> values;
};

NoiseVolume generate_noise_volume(int size, std::uint32_t seed);

} // namespace physics

#endif
