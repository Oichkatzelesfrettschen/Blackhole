#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <exception>
#include <filesystem>
#include <iostream>
#include <limits>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <highfive/H5Attribute.hpp>
#include <highfive/H5DataSet.hpp>
#include <highfive/H5DataSpace.hpp>
#include <highfive/H5File.hpp>

#include "grmhd_packed_loader.h"

namespace {

bool approxEqual(float a, float b, float tol = 1e-4f) {
  float const scale = std::max({1.0f, std::abs(a), std::abs(b)});
  return std::abs(a - b) <= tol * scale;
}

} // namespace

int main(int argc, char **argv) try {
  if (argc != 3) {
    std::cerr << "Usage: grmhd_pack_test --prepare-fixture|--validate-fixture DIRECTORY\n";
    return 2;
  }
  const std::string_view mode(argv[1]);
  const bool prepare = mode == "--prepare-fixture";
  if (!prepare && mode != "--validate-fixture") {
    std::cerr << "[FAIL] Unknown fixture mode: " << mode << '\n';
    return 2;
  }
  const std::filesystem::path outDir(argv[2]);

  std::filesystem::path const h5Path = outDir / "grmhd_fixture.h5";
  std::filesystem::path const metaPath = outDir / "grmhd_pack.json";

  const std::array<std::size_t, 4> dims = {2, 2, 2, 4};
  std::vector<float> data(dims[0] * dims[1] * dims[2] * dims[3], 0.0f);
  for (std::size_t i0 = 0; i0 < dims[0]; ++i0) {
    for (std::size_t i1 = 0; i1 < dims[1]; ++i1) {
      for (std::size_t i2 = 0; i2 < dims[2]; ++i2) {
        for (std::size_t c = 0; c < dims[3]; ++c) {
          std::size_t const idx = (((((i0 * dims[1]) + i1) * dims[2]) + i2) * dims[3]) + c;
          float const value = static_cast<float>(i0) + (static_cast<float>(i1) * 0.1f) +
                              (static_cast<float>(i2) * 0.01f) + (static_cast<float>(c) * 0.5f);
          data[idx] = value;
        }
      }
    }
  }

  if (prepare) {
    std::filesystem::create_directories(outDir);
    HighFive::File file(h5Path.string(), HighFive::File::Overwrite);
    auto space = HighFive::DataSpace({dims[0], dims[1], dims[2], dims[3]});
    auto dataset = file.createDataSet<float>("/dump/P", space);
    dataset.write_raw(data.data());
    std::vector<std::string> const vnams = {"RHO", "UU", "U1", "U2"};
    dataset.createAttribute<std::string>("vnams", HighFive::DataSpace::From(vnams)).write(vnams);
    std::cout << "[PASS] GRMHD input fixture prepared\n";
    return 0;
  }

  GrmhdPackedTexture texture;
  std::string error;
  if (!loadGrmhdPackedTexture(metaPath.string(), texture, error, true, false)) {
    std::cerr << "[FAIL] loader validation failed: " << error << "\n";
    return 1;
  }

  if (std::cmp_not_equal(texture.width, dims[0]) || std::cmp_not_equal(texture.height, dims[1]) ||
      std::cmp_not_equal(texture.depth, dims[2])) {
    std::cerr << "[FAIL] grid dims mismatch\n";
    return 1;
  }

  // Use max/lowest instead of infinity due to fast-math optimization flag
  // that makes infinity() return 0 with -ffinite-math-only
  std::array<float, 4> expectedMin{};
  std::array<float, 4> expectedMax{};
  expectedMin.fill(std::numeric_limits<float>::max());
  expectedMax.fill(std::numeric_limits<float>::lowest());
  for (std::size_t i = 0; i + 3 < data.size(); i += 4) {
    for (std::size_t c = 0; c < 4; ++c) {
      expectedMin[c] = std::min(expectedMin[c], data[i + c]);
      expectedMax[c] = std::max(expectedMax[c], data[i + c]);
    }
  }

  if (texture.minValues.size() < 4 || texture.maxValues.size() < 4) {
    std::cerr << "[FAIL] min/max metadata missing\n";
    return 1;
  }

  for (std::size_t c = 0; c < 4; ++c) {
    if (!approxEqual(texture.minValues[c], expectedMin[c]) ||
        !approxEqual(texture.maxValues[c], expectedMax[c])) {
      std::cerr << "[FAIL] min/max mismatch for channel " << c << "\n";
      return 1;
    }
  }

  std::cout << "[PASS] GRMHD pack fixture validated\n";
  return 0;
} catch (const std::exception &error) {
  std::cerr << "[FAIL] GRMHD fixture operation failed: " << error.what() << '\n';
  return 1;
} catch (...) {
  std::cerr << "[FAIL] GRMHD fixture operation failed with an unknown exception\n";
  return 1;
}
