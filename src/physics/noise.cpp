#include "noise.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>

namespace physics {
namespace {

std::uint32_t mix(std::uint32_t x) {
  x ^= x >> 16;
  x *= 0x7feb352du;
  x ^= x >> 15;
  x *= 0x846ca68bu;
  x ^= x >> 16;
  return x;
}

float toUnitFloat(std::uint32_t x) {
  constexpr float kInv = 1.0f / 16777215.0f;
  return static_cast<float>(x & 0x00ffffffu) * kInv;
}

} // namespace

NoiseVolume generateNoiseVolume(int size, std::uint32_t seed) {
  NoiseVolume volume;
  size = std::clamp(size, 4, 128);
  volume.size = size;
  const std::size_t count = static_cast<std::size_t>(size) *
                            static_cast<std::size_t>(size) *
                            static_cast<std::size_t>(size);
  volume.values.resize(count);

  for (int z = 0; z < size; ++z) {
    for (int y = 0; y < size; ++y) {
      for (int x = 0; x < size; ++x) {
        std::uint32_t h = seed;
        h ^= static_cast<std::uint32_t>(x) * 0x9e3779b1u;
        h ^= static_cast<std::uint32_t>(y) * 0x85ebca77u;
        h ^= static_cast<std::uint32_t>(z) * 0xc2b2ae3du;
        h = mix(h);
        const std::size_t index =
            (static_cast<std::size_t>(z) * static_cast<std::size_t>(size) *
             static_cast<std::size_t>(size)) +
            (static_cast<std::size_t>(y) * static_cast<std::size_t>(size)) +
            static_cast<std::size_t>(x);
        volume.values.at(index) = toUnitFloat(h);
      }
    }
  }

  return volume;
}

} // namespace physics
