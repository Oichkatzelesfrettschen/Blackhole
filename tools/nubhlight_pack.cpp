#include <CLI/CLI.hpp>
#include <highfive/H5File.hpp>

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <optional>
#include <sstream>
#include <numeric>
#include <string>
#include <vector>

struct ChannelSelection {
  std::string name;
  std::size_t index;
  double fill = 0.0;
};

struct PackMetadata {
  std::string input;
  std::string dataset;
  std::string layout;
  std::string format;
  std::string binPath;
  std::string checksum;
  std::vector<std::size_t> datasetDims;
  std::vector<std::size_t> gridDims;
  std::vector<std::string> channels;
  std::vector<int> sourceIndices;
  std::vector<double> fill;
  std::vector<double> minValues;
  std::vector<double> maxValues;
  std::vector<std::string> vnams;
  std::optional<std::size_t> channelDimIndex;
};

static std::string jsonEscape(const std::string &text) {
  std::string out;
  out.reserve(text.size() + 8);
  for (char c : text) {
    switch (c) {
    case '\\':
      out += "\\\\";
      break;
    case '"':
      out += "\\\"";
      break;
    case '\n':
      out += "\\n";
      break;
    case '\r':
      out += "\\r";
      break;
    case '\t':
      out += "\\t";
      break;
    default:
      out += c;
      break;
    }
  }
  return out;
}

static std::string lower(std::string value) {
  std::transform(value.begin(), value.end(), value.begin(),
                 [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
  return value;
}

static std::vector<std::string> readVnams(const HighFive::DataSet &dataset) {
  std::vector<std::string> vnams;
  if (dataset.hasAttribute("vnams")) {
    try {
      dataset.getAttribute("vnams").read(vnams);
    } catch (const std::exception &) {
    }
  }
  return vnams;
}

static void ensureParentDir(const std::string &path) {
  std::filesystem::path outputPath(path);
  auto parent = outputPath.parent_path();
  if (!parent.empty()) {
    std::filesystem::create_directories(parent);
  }
}

static std::string checksumFnv1a64(const std::vector<float> &data) {
  constexpr std::uint64_t kOffset = 14695981039346656037ull;
  constexpr std::uint64_t kPrime = 1099511628211ull;
  std::uint64_t hash = kOffset;
  const auto *bytes = reinterpret_cast<const std::uint8_t *>(data.data());
  std::size_t count = data.size() * sizeof(float);
  for (std::size_t i = 0; i < count; ++i) {
    hash ^= bytes[i];
    hash *= kPrime;
  }
  std::ostringstream out;
  out << std::hex << std::setw(16) << std::setfill('0') << hash;
  return out.str();
}

static void writeMetadata(std::ostream &out, const PackMetadata &meta) {
  out << "{\n";
  out << "  \"schema_version\": 1,\n";
  out << "  \"source\": \"nubhlight\",\n";
  out << "  \"input\": \"" << jsonEscape(meta.input) << "\",\n";
  out << "  \"dataset\": \"" << jsonEscape(meta.dataset) << "\",\n";
  out << "  \"layout\": \"" << jsonEscape(meta.layout) << "\",\n";
  out << "  \"format\": \"" << jsonEscape(meta.format) << "\",\n";
  out << "  \"bin\": \"" << jsonEscape(meta.binPath) << "\",\n";
  out << "  \"checksum_fnv1a64\": \"" << jsonEscape(meta.checksum) << "\",\n";
  out << "  \"dataset_dims\": [";
  for (std::size_t i = 0; i < meta.datasetDims.size(); ++i) {
    out << meta.datasetDims[i] << (i + 1 < meta.datasetDims.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"grid_dims\": [";
  for (std::size_t i = 0; i < meta.gridDims.size(); ++i) {
    out << meta.gridDims[i] << (i + 1 < meta.gridDims.size() ? ", " : "");
  }
  out << "],\n";
  if (meta.channelDimIndex.has_value()) {
    out << "  \"channel_dim_index\": " << *meta.channelDimIndex << ",\n";
  }
  out << "  \"channels\": [";
  for (std::size_t i = 0; i < meta.channels.size(); ++i) {
    out << "\"" << jsonEscape(meta.channels[i]) << "\""
        << (i + 1 < meta.channels.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"source_indices\": [";
  for (std::size_t i = 0; i < meta.sourceIndices.size(); ++i) {
    out << meta.sourceIndices[i] << (i + 1 < meta.sourceIndices.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"fill\": [";
  for (std::size_t i = 0; i < meta.fill.size(); ++i) {
    out << meta.fill[i] << (i + 1 < meta.fill.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"min\": [";
  for (std::size_t i = 0; i < meta.minValues.size(); ++i) {
    out << meta.minValues[i] << (i + 1 < meta.minValues.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"max\": [";
  for (std::size_t i = 0; i < meta.maxValues.size(); ++i) {
    out << meta.maxValues[i] << (i + 1 < meta.maxValues.size() ? ", " : "");
  }
  out << "]";
  if (!meta.vnams.empty()) {
    out << ",\n  \"vnams\": [";
    for (std::size_t i = 0; i < meta.vnams.size(); ++i) {
      out << "\"" << jsonEscape(meta.vnams[i]) << "\""
          << (i + 1 < meta.vnams.size() ? ", " : "");
    }
    out << "]";
  }
  out << "\n}\n";
}

int main(int argc, char **argv) {
  CLI::App app{"Pack nubhlight HDF5 datasets into RGBA texture blobs + metadata JSON"};

  std::string input;
  std::string datasetPath;
  std::string outputJson;
  std::string outputBin;
  std::string layout = "auto";
  std::string format = "RGBA32F";
  std::vector<std::string> fields;
  std::vector<std::size_t> indices;

  app.add_option("-i,--input", input, "Input HDF5 file")->required();
  app.add_option("-d,--dataset", datasetPath, "Dataset path (e.g. /dump/P)")->required();
  app.add_option("-o,--output", outputJson, "Output JSON metadata")->required();
  app.add_option("--bin", outputBin, "Output binary texture blob (default: output.json -> .bin)");
  app.add_option("--layout", layout, "auto|channels-last|channels-first");
  app.add_option("--format", format, "Texture format (RGBA32F only)");
  auto fieldOpt = app.add_option("--fields", fields, "Comma-separated vnams to pack");
  fieldOpt->delimiter(',');
  auto indexOpt = app.add_option("--indices", indices, "Comma-separated channel indices to pack");
  indexOpt->delimiter(',');

  CLI11_PARSE(app, argc, argv);

  if (outputBin.empty()) {
    std::filesystem::path outPath(outputJson);
    outPath.replace_extension(".bin");
    outputBin = outPath.string();
  }

  format = lower(format);
  if (format != "rgba32f") {
    std::cerr << "Only RGBA32F output is supported right now.\n";
    return 1;
  }

  HighFive::File file(input, HighFive::File::ReadOnly);
  HighFive::DataSet dataset = file.getDataSet(datasetPath);
  std::vector<std::size_t> dims = dataset.getSpace().getDimensions();
  std::vector<std::string> vnams = readVnams(dataset);

  if (dims.size() != 3 && dims.size() != 4) {
    std::cerr << "Expected 3D or 4D dataset, got " << dims.size() << "D.\n";
    return 1;
  }

  std::string layoutLower = lower(layout);
  std::optional<std::size_t> channelDimIndex;
  if (dims.size() == 4) {
    if (layoutLower == "auto") {
      if (!vnams.empty() && vnams.size() == dims.front()) {
        layoutLower = "channels-first";
      } else if (!vnams.empty() && vnams.size() == dims.back()) {
        layoutLower = "channels-last";
      } else if (dims.back() >= 4) {
        layoutLower = "channels-last";
      } else {
        layoutLower = "channels-first";
      }
    }

    if (layoutLower == "channels-first") {
      channelDimIndex = 0;
    } else if (layoutLower == "channels-last") {
      channelDimIndex = dims.size() - 1;
    } else {
      std::cerr << "Invalid layout: " << layout << "\n";
      return 1;
    }
  } else {
    layoutLower = "scalar";
  }

  if (!fields.empty() && !indices.empty()) {
    std::cerr << "Use either --fields or --indices, not both.\n";
    return 1;
  }
  if (dims.size() == 3 && (!fields.empty() || !indices.empty())) {
    std::cerr << "Scalar datasets do not accept --fields/--indices.\n";
    return 1;
  }

  std::size_t channelCount = 1;
  if (dims.size() == 4) {
    channelCount = (layoutLower == "channels-first") ? dims.front() : dims.back();
  }

  std::vector<ChannelSelection> selections;
  if (!fields.empty()) {
    if (vnams.empty()) {
      std::cerr << "Dataset lacks vnams attribute; use --indices instead.\n";
      return 1;
    }
    for (const auto &field : fields) {
      auto it = std::find(vnams.begin(), vnams.end(), field);
      if (it == vnams.end()) {
        std::cerr << "Field not found in vnams: " << field << "\n";
        return 1;
      }
      selections.push_back(ChannelSelection{field,
                                            static_cast<std::size_t>(std::distance(vnams.begin(), it)),
                                            0.0});
    }
  } else if (!indices.empty()) {
    for (std::size_t idx : indices) {
      if (idx >= channelCount) {
        std::cerr << "Channel index out of range: " << idx << "\n";
        return 1;
      }
      std::string label = vnams.empty() ? ("chan" + std::to_string(idx)) : vnams[idx];
      selections.push_back(ChannelSelection{label, idx, 0.0});
    }
  } else if (dims.size() == 4) {
    std::size_t count = std::min<std::size_t>(4, channelCount);
    for (std::size_t idx = 0; idx < count; ++idx) {
      std::string label = vnams.empty() ? ("chan" + std::to_string(idx)) : vnams[idx];
      selections.push_back(ChannelSelection{label, idx, 0.0});
    }
  } else {
    selections.push_back(ChannelSelection{"scalar", 0, 0.0});
  }

  if (selections.size() > 4) {
    std::cerr << "Select at most 4 channels for RGBA packing.\n";
    return 1;
  }

  while (selections.size() < 4) {
    double fill = (selections.size() == 3) ? 1.0 : 0.0;
    selections.push_back(ChannelSelection{"unused", std::numeric_limits<std::size_t>::max(), fill});
  }

  std::vector<float> raw;
  raw.resize(dataset.getSpace().getElementCount());
  try {
    dataset.read_raw(raw.data());
  } catch (const std::exception &ex) {
    std::cerr << "Failed to read dataset: " << ex.what() << "\n";
    return 1;
  }

  std::vector<std::size_t> gridDims;
  gridDims.reserve(3);
  if (dims.size() == 4) {
    for (std::size_t i = 0; i < dims.size(); ++i) {
      if (i != channelDimIndex.value()) {
        gridDims.push_back(dims[i]);
      }
    }
  } else {
    gridDims = dims;
  }

  std::size_t voxelCount = 1;
  for (auto d : gridDims) {
    voxelCount *= d;
  }

  std::vector<float> packed;
  packed.resize(voxelCount * 4);

  std::vector<double> minValues(4, std::numeric_limits<double>::infinity());
  std::vector<double> maxValues(4, -std::numeric_limits<double>::infinity());

  auto updateMinMax = [&](std::size_t channel, double value) {
    minValues[channel] = std::min(minValues[channel], value);
    maxValues[channel] = std::max(maxValues[channel], value);
  };

  const auto d0 = gridDims[0];
  const auto d1 = gridDims[1];
  const auto d2 = gridDims[2];

  for (std::size_t i0 = 0; i0 < d0; ++i0) {
    for (std::size_t i1 = 0; i1 < d1; ++i1) {
      for (std::size_t i2 = 0; i2 < d2; ++i2) {
        std::size_t gridIndex = (i0 * d1 + i1) * d2 + i2;
        std::size_t outIndex = gridIndex * 4;
        for (std::size_t c = 0; c < 4; ++c) {
          const auto &sel = selections[c];
          double value = sel.fill;
          if (sel.index != std::numeric_limits<std::size_t>::max()) {
            if (layoutLower == "channels-last") {
              std::size_t channelCountLocal = dims.back();
              std::size_t rawIndex =
                  ((i0 * d1 + i1) * d2 + i2) * channelCountLocal + sel.index;
              value = raw[rawIndex];
            } else if (layoutLower == "channels-first") {
              std::size_t d0Local = dims[1];
              std::size_t d1Local = dims[2];
              std::size_t d2Local = dims[3];
              std::size_t rawIndex =
                  ((sel.index * d0Local + i0) * d1Local + i1) * d2Local + i2;
              value = raw[rawIndex];
            } else {
              value = raw[gridIndex];
            }
          }
          packed[outIndex + c] = static_cast<float>(value);
          updateMinMax(c, value);
        }
      }
    }
  }

  ensureParentDir(outputBin);
  std::ofstream binOut(outputBin, std::ios::binary);
  if (!binOut) {
    std::cerr << "Failed to open output bin: " << outputBin << "\n";
    return 1;
  }
  binOut.write(reinterpret_cast<const char *>(packed.data()),
               static_cast<std::streamsize>(packed.size() * sizeof(float)));
  if (!binOut) {
    std::cerr << "Failed to write output bin: " << outputBin << "\n";
    return 1;
  }

  PackMetadata metadata;
  metadata.input = input;
  metadata.dataset = datasetPath;
  metadata.layout = layoutLower;
  metadata.format = "RGBA32F";
  metadata.binPath = outputBin;
  metadata.checksum = checksumFnv1a64(packed);
  metadata.datasetDims = dims;
  metadata.gridDims = gridDims;
  metadata.channels.reserve(4);
  metadata.sourceIndices.reserve(4);
  metadata.fill.reserve(4);
  for (const auto &sel : selections) {
    metadata.channels.push_back(sel.name);
    if (sel.index == std::numeric_limits<std::size_t>::max()) {
      metadata.sourceIndices.push_back(-1);
    } else {
      metadata.sourceIndices.push_back(static_cast<int>(sel.index));
    }
    metadata.fill.push_back(sel.fill);
  }
  metadata.minValues = minValues;
  metadata.maxValues = maxValues;
  metadata.vnams = vnams;
  metadata.channelDimIndex = channelDimIndex;

  ensureParentDir(outputJson);
  std::ofstream jsonOut(outputJson);
  if (!jsonOut) {
    std::cerr << "Failed to open output json: " << outputJson << "\n";
    return 1;
  }
  writeMetadata(jsonOut, metadata);

  std::cout << "Wrote " << outputBin << " and " << outputJson << "\n";
  return 0;
}
