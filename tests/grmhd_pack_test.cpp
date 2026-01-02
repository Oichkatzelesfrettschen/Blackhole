#include <highfive/H5File.hpp>

#include <array>
#include <algorithm>
#include <cmath>
#include <filesystem>
#include <iostream>
#include <limits>
#include <sstream>
#include <string>
#include <vector>

#include "grmhd_packed_loader.h"

namespace {

std::string quote(const std::filesystem::path &path) {
  std::ostringstream out;
  out << "\"" << path.string() << "\"";
  return out.str();
}

bool approxEqual(float a, float b, float tol = 1e-4f) {
  float scale = std::max(1.0f, std::max(std::abs(a), std::abs(b)));
  return std::abs(a - b) <= tol * scale;
}

} // namespace

int main(int argc, char **argv) {
  std::filesystem::path outDir = std::filesystem::current_path() / "logs" / "perf";
  std::filesystem::create_directories(outDir);

  std::filesystem::path h5Path = outDir / "grmhd_fixture.h5";
  std::filesystem::path metaPath = outDir / "grmhd_pack.json";

  const std::array<std::size_t, 4> dims = {2, 2, 2, 4};
  std::vector<float> data(dims[0] * dims[1] * dims[2] * dims[3], 0.0f);
  for (std::size_t i0 = 0; i0 < dims[0]; ++i0) {
    for (std::size_t i1 = 0; i1 < dims[1]; ++i1) {
      for (std::size_t i2 = 0; i2 < dims[2]; ++i2) {
        for (std::size_t c = 0; c < dims[3]; ++c) {
          std::size_t idx = ((i0 * dims[1] + i1) * dims[2] + i2) * dims[3] + c;
          float value = static_cast<float>(i0) + static_cast<float>(i1) * 0.1f +
                        static_cast<float>(i2) * 0.01f + static_cast<float>(c) * 0.5f;
          data[idx] = value;
        }
      }
    }
  }

  try {
    HighFive::File file(h5Path.string(), HighFive::File::Overwrite);
    auto space = HighFive::DataSpace({dims[0], dims[1], dims[2], dims[3]});
    auto dataset = file.createDataSet<float>("/dump/P", space);
    dataset.write_raw(data.data());
    std::vector<std::string> vnams = {"RHO", "UU", "U1", "U2"};
    dataset.createAttribute<std::string>("vnams", HighFive::DataSpace::From(vnams)).write(vnams);
  } catch (const std::exception &ex) {
    std::cerr << "[FAIL] Failed to write fixture: " << ex.what() << "\n";
    return 1;
  }

  if (argc < 1) {
    std::cerr << "[FAIL] Missing argv[0]\n";
    return 1;
  }
  std::filesystem::path exeDir = std::filesystem::path(argv[0]).parent_path();
  std::filesystem::path packExe = exeDir / "nubhlight_pack";
  if (!std::filesystem::exists(packExe)) {
    std::cerr << "[FAIL] nubhlight_pack not found at " << packExe << "\n";
    return 1;
  }

  std::ostringstream cmd;
  cmd << quote(packExe) << " -i " << quote(h5Path)
      << " -d /dump/P --fields RHO,UU,U1,U2 -o " << quote(metaPath);
  int rc = std::system(cmd.str().c_str());
  if (rc != 0) {
    std::cerr << "[FAIL] nubhlight_pack failed with code " << rc << "\n";
    return 1;
  }

  GrmhdPackedTexture texture;
  std::string error;
  if (!loadGrmhdPackedTexture(metaPath.string(), texture, error, true, false)) {
    std::cerr << "[FAIL] loader validation failed: " << error << "\n";
    return 1;
  }

  if (texture.width != static_cast<int>(dims[0]) ||
      texture.height != static_cast<int>(dims[1]) ||
      texture.depth != static_cast<int>(dims[2])) {
    std::cerr << "[FAIL] grid dims mismatch\n";
    return 1;
  }

  // Use max/lowest instead of infinity due to fast-math optimization flag
  // that makes infinity() return 0 with -ffinite-math-only
  std::array<float, 4> expectedMin;
  std::array<float, 4> expectedMax;
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
}
