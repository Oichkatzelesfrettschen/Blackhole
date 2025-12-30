#include <CLI/CLI.hpp>
#include <highfive/H5File.hpp>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

struct DatasetInfo {
  std::string path;
  std::vector<std::size_t> dims;
  std::vector<std::string> vnams;
};

static std::string joinPath(const std::string &prefix, const std::string &name) {
  if (prefix.empty() || prefix == "/") {
    return "/" + name;
  }
  return prefix + "/" + name;
}

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
