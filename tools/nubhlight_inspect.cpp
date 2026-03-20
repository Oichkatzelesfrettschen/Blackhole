/**
 * @file nubhlight_inspect.cpp
 * @brief Inspect nubhlight HDF5 output files and emit dataset metadata as JSON.
 *
 * Recursively walks all groups in a nubhlight HDF5 dump file, collects every
 * dataset's path, shape, and optional variable-name attribute (vnams), and
 * writes the result as a JSON document.  The output is intended for use by
 * nubhlight_pack and downstream tooling that needs to discover which datasets
 * and channels are available before packing them into GPU textures.
 *
 * Usage:
 *   nubhlight_inspect -i dump.h5 [-o metadata.json]
 *   With no -o flag the JSON is written to stdout.
 */

#include <CLI/CLI.hpp>
#include <highfive/H5File.hpp>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

/** @brief Metadata collected for a single HDF5 dataset. */
struct DatasetInfo {
  std::string path;               /**< Absolute HDF5 path (e.g. /dump/P). */
  std::vector<std::size_t> dims;  /**< Dataset dimensions in row-major order. */
  std::vector<std::string> vnams; /**< Variable names from the vnams attribute, if present. */
};

/**
 * @brief Concatenate an HDF5 group prefix and object name into an absolute path.
 *
 * @param prefix Current group path, or "" / "/" for the root group.
 * @param name   Object name within the group.
 * @return Absolute HDF5 path string.
 */
static std::string joinPath(const std::string &prefix, const std::string &name) {
  if (prefix.empty() || prefix == "/") {
    return "/" + name;
  }
  return prefix + "/" + name;
}

/**
 * @brief Escape a string for safe embedding in a JSON value.
 *
 * @param text Raw string that may contain backslashes, quotes, or control chars.
 * @return JSON-safe escaped string (without surrounding quotes).
 */
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

/**
 * @brief Recursively collect dataset metadata from an HDF5 group tree.
 *
 * Descends into subgroups and appends a DatasetInfo entry for each dataset
 * encountered.  The vnams attribute is read when present.
 *
 * @param group  HDF5 group to inspect.
 * @param prefix Absolute path of @p group used to build child paths.
 * @param out    Accumulator for discovered DatasetInfo records.
 */
static void collectDatasets(const HighFive::Group &group, const std::string &prefix,
                            std::vector<DatasetInfo> &out) {
  for (const auto &name : group.listObjectNames()) {
    std::string path = joinPath(prefix, name);
    auto type = group.getObjectType(name);
    if (type == HighFive::ObjectType::Dataset) {
      DatasetInfo info;
      info.path = path;
      auto dataset = group.getDataSet(name);
      info.dims = dataset.getSpace().getDimensions();
      if (dataset.hasAttribute("vnams")) {
        try {
          auto attr = dataset.getAttribute("vnams");
          attr.read(info.vnams);
        } catch (const std::exception &) {
        }
      }
      out.push_back(info);
    } else if (type == HighFive::ObjectType::Group) {
      collectDatasets(group.getGroup(name), path, out);
    }
  }
}

/**
 * @brief Serialize dataset metadata to JSON and write to a stream.
 *
 * @param out      Destination stream (file or stdout).
 * @param input    Original HDF5 file path, included in the JSON for provenance.
 * @param datasets List of dataset records produced by collectDatasets().
 */
static void writeJson(std::ostream &out, const std::string &input,
                      const std::vector<DatasetInfo> &datasets) {
  out << "{\n";
  out << "  \"input\": \"" << jsonEscape(input) << "\",\n";
  out << "  \"datasets\": [\n";
  for (std::size_t i = 0; i < datasets.size(); ++i) {
    const auto &item = datasets[i];
    out << "    {\"path\": \"" << jsonEscape(item.path) << "\", \"dims\": [";
    for (std::size_t d = 0; d < item.dims.size(); ++d) {
      out << item.dims[d] << (d + 1 < item.dims.size() ? ", " : "");
    }
    out << "]";
    if (!item.vnams.empty()) {
      out << ", \"vnams\": [";
      for (std::size_t v = 0; v < item.vnams.size(); ++v) {
        out << "\"" << jsonEscape(item.vnams[v]) << "\""
            << (v + 1 < item.vnams.size() ? ", " : "");
      }
      out << "]";
    }
    out << "}" << (i + 1 < datasets.size() ? "," : "") << "\n";
  }
  out << "  ]\n";
  out << "}\n";
}

int main(int argc, char **argv) {
  CLI::App app{"Inspect nubhlight HDF5 datasets and emit metadata JSON"};

  std::string input;
  std::string output;
  app.add_option("-i,--input", input, "Input HDF5 file")->required();
  app.add_option("-o,--output", output, "Output JSON file (default: stdout)");

  CLI11_PARSE(app, argc, argv);

  std::vector<DatasetInfo> datasets;
  try {
    HighFive::File file(input, HighFive::File::ReadOnly);
    auto root = file.getGroup("/");
    collectDatasets(root, "", datasets);
  } catch (const std::exception &ex) {
    std::cerr << "Failed to read HDF5: " << ex.what() << "\n";
    return 1;
  }

  if (output.empty()) {
    writeJson(std::cout, input, datasets);
  } else {
    std::filesystem::create_directories(std::filesystem::path(output).parent_path());
    std::ofstream out(output);
    if (!out) {
      std::cerr << "Failed to write output: " << output << "\n";
      return 1;
    }
    writeJson(out, input, datasets);
  }

  return 0;
}
