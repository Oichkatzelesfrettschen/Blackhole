/**
 * @file nubhlight_pack.cpp
 * @brief Pack nubhlight HDF5 datasets into RGBA32F texture blobs for GPU upload.
 *
 * Reads a 3-D or 4-D floating-point dataset from a nubhlight HDF5 dump file,
 * selects up to four channels (by field name or index), reorders them into a
 * tightly-packed RGBA32F binary blob, and writes a companion JSON metadata file.
 * The binary blob can be uploaded directly to a GL_RGBA32F 3-D texture via the
 * GrmhdPBOUploader pipeline.
 *
 * Layout detection (channels-first vs channels-last) is performed automatically
 * from the vnams attribute when present, and can be overridden with --layout.
 *
 * Usage:
 *   nubhlight_pack -i dump.h5 -d /dump/P -o out.json [--bin out.bin]
 *                  [--fields rho,u,v1,v2] [--layout auto|channels-first|channels-last]
 */

#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <limits>
#include <numeric>
#include <optional>
#include <span>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include <CLI/CLI.hpp>
#include <highfive/H5Attribute.hpp>
#include <highfive/H5DataSet.hpp>
#include <highfive/H5DataSpace.hpp>
#include <highfive/H5File.hpp>

namespace {

/** @brief Describes how a single RGBA output channel is sourced from the dataset. */
struct ChannelSelection {
  std::string name; /**< Human-readable channel label (vnams entry or "chanN"). */
  std::size_t index =
      std::numeric_limits<std::size_t>::max(); /**< Source index or fill sentinel. */
  double fill = 0.0; /**< Constant value written when no source channel is mapped. */
};

/** @brief All provenance and structural information written to the companion JSON. */
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

/**
 * @brief Escape a string for safe embedding in a JSON value.
 *
 * @param text Raw string that may contain backslashes, quotes, or control chars.
 * @return JSON-safe escaped string (without surrounding quotes).
 */
std::string jsonEscape(const std::string &text) {
  std::string out;
  out.reserve(text.size() + 8);
  for (char const c : text) {
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

/**
 * @brief Convert a string to lowercase in-place.
 *
 * @param value String to convert.
 * @return Lowercase copy of @p value.
 */
std::string lower(std::string value) {
  std::ranges::transform(value, value.begin(),
                         [](unsigned char c) { return static_cast<char>(std::tolower(c)); });
  return value;
}

/**
 * @brief Read the vnams string attribute from an HDF5 dataset if present.
 *
 * @param dataset Dataset to query.
 * @return Vector of variable name strings, or empty if the attribute is absent.
 */
std::vector<std::string> readVnams(const HighFive::DataSet &dataset) {
  std::vector<std::string> vnams;
  if (dataset.hasAttribute("vnams")) {
    dataset.getAttribute("vnams").read(vnams);
  }
  return vnams;
}

/**
 * @brief Create all parent directories for a given file path if they do not exist.
 *
 * @param path Target file path whose parent directories should be created.
 */
void ensureParentDir(const std::string &path) {
  std::filesystem::path const outputPath(path);
  auto parent = outputPath.parent_path();
  if (!parent.empty()) {
    std::filesystem::create_directories(parent);
  }
}

/**
 * @brief Compute an FNV-1a 64-bit checksum over a packed float buffer.
 *
 * Used for integrity verification of the binary texture blob.
 *
 * @param data Packed float values to hash.
 * @return 16-character lowercase hex string of the 64-bit hash.
 */
std::string checksumFnv1a64(const std::vector<float> &data) {
  constexpr std::uint64_t kOffset = 14695981039346656037ull;
  constexpr std::uint64_t kPrime = 1099511628211ull;
  std::uint64_t hash = kOffset;
  for (std::byte const byte : std::as_bytes(std::span{data})) {
    hash ^= std::to_integer<std::uint8_t>(byte);
    hash *= kPrime;
  }
  std::ostringstream out;
  out << std::hex << std::setw(16) << std::setfill('0') << hash;
  return out.str();
}

/**
 * @brief Serialize pack metadata to a JSON stream.
 *
 * Writes schema_version, source, layout, channel names, per-channel min/max,
 * checksum, and grid dimensions so the GPU loader can reconstruct the texture
 * without re-reading the original HDF5 file.
 *
 * @param out  Destination stream (file or stdout).
 * @param meta Populated PackMetadata describing the packed blob.
 */
void writeMetadata(std::ostream &out, const PackMetadata &meta) {
  out << "{\n";
  out << "  \"schema_version\": 1,\n";
  out << "  \"source\": \"nubhlight\",\n";
  out << R"(  "input": ")" << jsonEscape(meta.input) << "\",\n";
  out << R"(  "dataset": ")" << jsonEscape(meta.dataset) << "\",\n";
  out << R"(  "layout": ")" << jsonEscape(meta.layout) << "\",\n";
  out << R"(  "format": ")" << jsonEscape(meta.format) << "\",\n";
  out << R"(  "bin": ")" << jsonEscape(meta.binPath) << "\",\n";
  out << R"(  "checksum_fnv1a64": ")" << jsonEscape(meta.checksum) << "\",\n";
  out << "  \"dataset_dims\": [";
  for (std::size_t i = 0; i < meta.datasetDims.size(); ++i) {
    out << meta.datasetDims.at(i) << (i + 1 < meta.datasetDims.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"grid_dims\": [";
  for (std::size_t i = 0; i < meta.gridDims.size(); ++i) {
    out << meta.gridDims.at(i) << (i + 1 < meta.gridDims.size() ? ", " : "");
  }
  out << "],\n";
  if (meta.channelDimIndex.has_value()) {
    out << "  \"channel_dim_index\": " << *meta.channelDimIndex << ",\n";
  }
  out << "  \"channels\": [";
  for (std::size_t i = 0; i < meta.channels.size(); ++i) {
    out << "\"" << jsonEscape(meta.channels.at(i)) << "\""
        << (i + 1 < meta.channels.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"source_indices\": [";
  for (std::size_t i = 0; i < meta.sourceIndices.size(); ++i) {
    out << meta.sourceIndices.at(i) << (i + 1 < meta.sourceIndices.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"fill\": [";
  for (std::size_t i = 0; i < meta.fill.size(); ++i) {
    out << meta.fill.at(i) << (i + 1 < meta.fill.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"min\": [";
  for (std::size_t i = 0; i < meta.minValues.size(); ++i) {
    out << meta.minValues.at(i) << (i + 1 < meta.minValues.size() ? ", " : "");
  }
  out << "],\n";
  out << "  \"max\": [";
  for (std::size_t i = 0; i < meta.maxValues.size(); ++i) {
    out << meta.maxValues.at(i) << (i + 1 < meta.maxValues.size() ? ", " : "");
  }
  out << "]";
  if (!meta.vnams.empty()) {
    out << ",\n  \"vnams\": [";
    for (std::size_t i = 0; i < meta.vnams.size(); ++i) {
      out << "\"" << jsonEscape(meta.vnams.at(i)) << "\""
          << (i + 1 < meta.vnams.size() ? ", " : "");
    }
    out << "]";
  }
  out << "\n}\n";
}

struct DatasetLayout {
  std::string name;
  std::optional<std::size_t> channelDimension;
  std::size_t channelCount = 1;
};

std::optional<DatasetLayout> resolveLayout(const std::vector<std::size_t> &dims,
                                           const std::vector<std::string> &vnams,
                                           const std::string &layout) {
  if (dims.size() != 3 && dims.size() != 4) {
    std::cerr << "Expected 3D or 4D dataset, got " << dims.size() << "D.\n";
    return std::nullopt;
  }

  std::string layoutLower = lower(layout);
  std::optional<std::size_t> channelDimIndex;
  if (dims.size() == 4) {
    if (layoutLower == "auto") {
      bool const namesIdentifyFirst = !vnams.empty() && vnams.size() == dims.front();
      bool const channelsLastCandidate =
          (!vnams.empty() && vnams.size() == dims.back()) || dims.back() >= 4;
      layoutLower =
          (namesIdentifyFirst || !channelsLastCandidate) ? "channels-first" : "channels-last";
    }

    if (layoutLower == "channels-first") {
      channelDimIndex = 0;
    } else if (layoutLower == "channels-last") {
      channelDimIndex = dims.size() - 1;
    } else {
      std::cerr << "Invalid layout: " << layout << "\n";
      return std::nullopt;
    }
  } else {
    layoutLower = "scalar";
  }

  std::size_t const channelCount = channelDimIndex ? dims.at(*channelDimIndex) : 1;
  if (!vnams.empty() && vnams.size() != channelCount) {
    throw std::runtime_error("vnams count differs from the selected channel dimension");
  }
  return DatasetLayout{
      .name = layoutLower, .channelDimension = channelDimIndex, .channelCount = channelCount};
}

std::optional<std::vector<ChannelSelection>>
selectChannels(const std::vector<std::size_t> &dims, const std::vector<std::string> &vnams,
               std::size_t channelCount, const std::vector<std::string> &fields,
               const std::vector<std::size_t> &indices) {
  if (!fields.empty() && !indices.empty()) {
    std::cerr << "Use either --fields or --indices, not both.\n";
    return std::nullopt;
  }
  if (dims.size() == 3 && (!fields.empty() || !indices.empty())) {
    std::cerr << "Scalar datasets do not accept --fields/--indices.\n";
    return std::nullopt;
  }

  std::vector<ChannelSelection> selections;
  if (!fields.empty()) {
    if (vnams.empty()) {
      std::cerr << "Dataset lacks vnams attribute; use --indices instead.\n";
      return std::nullopt;
    }
    for (const auto &field : fields) {
      auto it = std::ranges::find(vnams, field);
      if (it == vnams.end()) {
        std::cerr << "Field not found in vnams: " << field << "\n";
        return std::nullopt;
      }
      selections.push_back(
          ChannelSelection{.name = field,
                           .index = static_cast<std::size_t>(std::distance(vnams.begin(), it)),
                           .fill = 0.0});
    }
  } else if (!indices.empty()) {
    for (std::size_t const idx : indices) {
      if (idx >= channelCount) {
        std::cerr << "Channel index out of range: " << idx << "\n";
        return std::nullopt;
      }
      std::string const label = vnams.empty() ? ("chan" + std::to_string(idx)) : vnams.at(idx);
      selections.push_back(ChannelSelection{.name = label, .index = idx, .fill = 0.0});
    }
  } else if (dims.size() == 4) {
    std::size_t const count = std::min<std::size_t>(4, channelCount);
    for (std::size_t idx = 0; idx < count; ++idx) {
      std::string const label = vnams.empty() ? ("chan" + std::to_string(idx)) : vnams.at(idx);
      selections.push_back(ChannelSelection{.name = label, .index = idx, .fill = 0.0});
    }
  } else {
    selections.push_back(ChannelSelection{.name = "scalar", .index = 0, .fill = 0.0});
  }

  if (selections.size() > 4) {
    std::cerr << "Select at most 4 channels for RGBA packing.\n";
    return std::nullopt;
  }

  while (selections.size() < 4) {
    double const fill = (selections.size() == 3) ? 1.0 : 0.0;
    selections.push_back(ChannelSelection{
        .name = "unused", .index = std::numeric_limits<std::size_t>::max(), .fill = fill});
  }

  return selections;
}

struct PackedTexture {
  std::vector<std::size_t> gridDimensions;
  std::vector<float> values;
  std::vector<double> minValues;
  std::vector<double> maxValues;
};

std::size_t checkedProduct(std::size_t left, std::size_t right) {
  if (right != 0 && left > std::numeric_limits<std::size_t>::max() / right) {
    throw std::overflow_error("Dataset dimensions exceed the addressable element count");
  }
  return left * right;
}

PackedTexture packTexture(const std::vector<float> &raw, const std::vector<std::size_t> &dims,
                          const DatasetLayout &layout,
                          const std::vector<ChannelSelection> &selections) {
  PackedTexture result;
  for (std::size_t dimension = 0; dimension < dims.size(); ++dimension) {
    if (!layout.channelDimension || dimension != *layout.channelDimension) {
      result.gridDimensions.push_back(dims.at(dimension));
    }
  }
  std::size_t const voxelCount = std::accumulate(
      result.gridDimensions.begin(), result.gridDimensions.end(), std::size_t{1}, checkedProduct);
  if (raw.size() != checkedProduct(voxelCount, layout.channelCount)) {
    throw std::runtime_error("Dataset element count differs from its dimensions");
  }
  result.values.resize(checkedProduct(voxelCount, 4));
  result.minValues.assign(4, std::numeric_limits<double>::max());
  result.maxValues.assign(4, std::numeric_limits<double>::lowest());
  for (std::size_t voxel = 0; voxel < voxelCount; ++voxel) {
    for (std::size_t channel = 0; channel < selections.size(); ++channel) {
      const auto &selection = selections.at(channel);
      double value = selection.fill;
      if (selection.index != std::numeric_limits<std::size_t>::max()) {
        std::size_t rawIndex = voxel;
        if (layout.name == "channels-last") {
          rawIndex = (voxel * layout.channelCount) + selection.index;
        } else if (layout.name == "channels-first") {
          rawIndex = (selection.index * voxelCount) + voxel;
        }
        value = static_cast<double>(raw.at(rawIndex));
      }
      result.values.at((voxel * 4) + channel) = static_cast<float>(value);
      result.minValues.at(channel) = std::min(result.minValues.at(channel), value);
      result.maxValues.at(channel) = std::max(result.maxValues.at(channel), value);
    }
  }
  return result;
}

} // namespace

int main(int argc, char **argv) try {
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
  auto *fieldOpt = app.add_option("--fields", fields, "Comma-separated vnams to pack");
  fieldOpt->delimiter(',');
  auto *indexOpt = app.add_option("--indices", indices, "Comma-separated channel indices to pack");
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

  HighFive::File const file(input, HighFive::File::ReadOnly);
  HighFive::DataSet const dataset = file.getDataSet(datasetPath);
  std::vector<std::size_t> const dims = dataset.getSpace().getDimensions();
  std::vector<std::string> const vnams = readVnams(dataset);

  const auto resolvedLayout = resolveLayout(dims, vnams, layout);
  if (!resolvedLayout) {
    return 1;
  }
  const auto selectedChannels =
      selectChannels(dims, vnams, resolvedLayout->channelCount, fields, indices);
  if (!selectedChannels) {
    return 1;
  }
  const auto &selections = *selectedChannels;
  std::vector<float> raw;
  raw.resize(dataset.getSpace().getElementCount());
  try {
    dataset.read_raw(raw.data());
  } catch (const std::exception &ex) {
    std::cerr << "Failed to read dataset: " << ex.what() << "\n";
    return 1;
  }

  const auto texture = packTexture(raw, dims, *resolvedLayout, selections);
  const auto &packed = texture.values;
  ensureParentDir(outputBin);
  std::ofstream binOut(outputBin, std::ios::binary);
  if (!binOut) {
    std::cerr << "Failed to open output bin: " << outputBin << "\n";
    return 1;
  }
  binOut.write(reinterpret_cast<const char *>(packed.data()),
               static_cast<std::streamsize>(packed.size() * sizeof(float)));
  binOut.close();
  if (!binOut) {
    std::cerr << "Failed to write output bin: " << outputBin << "\n";
    return 1;
  }

  PackMetadata metadata;
  metadata.input = input;
  metadata.dataset = datasetPath;
  metadata.layout = resolvedLayout->name;
  metadata.format = "RGBA32F";
  metadata.binPath = outputBin;
  metadata.checksum = checksumFnv1a64(packed);
  metadata.datasetDims = dims;
  metadata.gridDims = texture.gridDimensions;
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
  metadata.minValues = texture.minValues;
  metadata.maxValues = texture.maxValues;
  metadata.vnams = vnams;
  metadata.channelDimIndex = resolvedLayout->channelDimension;

  ensureParentDir(outputJson);
  std::ofstream jsonOut(outputJson);
  if (!jsonOut) {
    std::cerr << "Failed to open output json: " << outputJson << "\n";
    return 1;
  }
  writeMetadata(jsonOut, metadata);
  jsonOut.close();
  if (!jsonOut) {
    std::cerr << "Failed to write output json: " << outputJson << "\n";
    return 1;
  }

  std::cout << "Wrote " << outputBin << " and " << outputJson << "\n";
  return 0;
} catch (const std::exception &error) {
  std::cerr << "Packing failed: " << error.what() << '\n';
  return 1;
} catch (...) {
  std::cerr << "Packing failed with an unknown exception\n";
  return 1;
}
