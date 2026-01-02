#include <CLI/CLI.hpp>
#include <nlohmann/json.hpp>
#include <shaderc/shaderc.hpp>
#include <spirv-tools/optimizer.hpp>
#include <spirv_cross/spirv_cross.hpp>

#include <fstream>
#include <iostream>
#include <string>
#include <vector>

namespace {

std::string readTextFile(const std::string &path) {
  std::ifstream file(path, std::ios::binary);
  if (!file) {
    throw std::runtime_error("Failed to open file: " + path);
  }
  file.seekg(0, std::ios::end);
  const std::streamoff size = file.tellg();
  if (size < 0) {
    throw std::runtime_error("Failed to read size for file: " + path);
  }
  std::string data;
  data.resize(static_cast<size_t>(size));
  file.seekg(0, std::ios::beg);
  if (size > 0) {
    file.read(data.data(), size);
    if (!file) {
      throw std::runtime_error("Failed to read file: " + path);
    }
  }
  return data;
}

void writeBinaryFile(const std::string &path, const std::vector<uint32_t> &data) {
  std::ofstream out(path, std::ios::binary);
  if (!out) {
    throw std::runtime_error("Failed to write file: " + path);
  }
  out.write(reinterpret_cast<const char *>(data.data()),
            static_cast<std::streamsize>(data.size() * sizeof(uint32_t)));
}

bool endsWith(const std::string &value, const std::string &suffix) {
  if (suffix.size() > value.size()) {
    return false;
  }
  return std::equal(suffix.rbegin(), suffix.rend(), value.rbegin());
}

shaderc_shader_kind stageFromPath(const std::string &path) {
  if (endsWith(path, ".vert")) {
    return shaderc_vertex_shader;
  }
  if (endsWith(path, ".frag")) {
    return shaderc_fragment_shader;
  }
  if (endsWith(path, ".comp")) {
    return shaderc_compute_shader;
  }
  if (endsWith(path, ".geom")) {
    return shaderc_geometry_shader;
  }
  if (endsWith(path, ".tesc")) {
    return shaderc_tess_control_shader;
  }
  if (endsWith(path, ".tese")) {
    return shaderc_tess_evaluation_shader;
  }
  return shaderc_glsl_infer_from_source;
}

shaderc_shader_kind stageFromFlag(const std::string &stage) {
  if (stage == "vert") {
    return shaderc_vertex_shader;
  }
  if (stage == "frag") {
    return shaderc_fragment_shader;
  }
  if (stage == "comp") {
    return shaderc_compute_shader;
  }
  if (stage == "geom") {
    return shaderc_geometry_shader;
  }
  if (stage == "tesc") {
    return shaderc_tess_control_shader;
  }
  if (stage == "tese") {
    return shaderc_tess_evaluation_shader;
  }
  return shaderc_glsl_infer_from_source;
}

void dumpResources(const spirv_cross::Compiler &compiler) {
  auto resources = compiler.get_shader_resources();
  auto printGroup = [&](const char *label, const auto &entries) {
    if (entries.empty()) {
      return;
    }
    std::cout << label << ":\n";
    for (const auto &entry : entries) {
      uint32_t set = 0;
      uint32_t binding = 0;
      if (compiler.has_decoration(entry.id, spv::DecorationDescriptorSet)) {
        set = compiler.get_decoration(entry.id, spv::DecorationDescriptorSet);
      }
      if (compiler.has_decoration(entry.id, spv::DecorationBinding)) {
        binding = compiler.get_decoration(entry.id, spv::DecorationBinding);
      }
      std::cout << "  " << entry.name << " set=" << set << " binding=" << binding
                << "\n";
    }
  };

  printGroup("Uniform buffers", resources.uniform_buffers);
  printGroup("Storage buffers", resources.storage_buffers);
  printGroup("Sampled images", resources.sampled_images);
  printGroup("Storage images", resources.storage_images);
  printGroup("Separate samplers", resources.separate_samplers);
  printGroup("Separate images", resources.separate_images);
  printGroup("Push constants", resources.push_constant_buffers);
}

nlohmann::json buildReflectionJson(const spirv_cross::Compiler &compiler,
                                   const std::string &inputPath) {
  nlohmann::json root;
  root["schema_version"] = 1;
  root["source"] = inputPath;

  // Entry points
  nlohmann::json entries = nlohmann::json::array();
  for (const auto &entry : compiler.get_entry_points_and_stages()) {
    nlohmann::json e;
    e["name"] = entry.name;
    e["stage"] = static_cast<int>(entry.execution_model);
    entries.push_back(e);
  }
  root["entry_points"] = entries;

  auto resources = compiler.get_shader_resources();

  auto buildResourceArray = [&](const auto &resourceList) -> nlohmann::json {
    nlohmann::json arr = nlohmann::json::array();
    for (const auto &res : resourceList) {
      nlohmann::json item;
      item["name"] = res.name;
      item["id"] = static_cast<uint32_t>(res.id);
      if (compiler.has_decoration(res.id, spv::DecorationDescriptorSet)) {
        item["set"] = compiler.get_decoration(res.id, spv::DecorationDescriptorSet);
      }
      if (compiler.has_decoration(res.id, spv::DecorationBinding)) {
        item["binding"] = compiler.get_decoration(res.id, spv::DecorationBinding);
      }
      if (compiler.has_decoration(res.id, spv::DecorationLocation)) {
        item["location"] = compiler.get_decoration(res.id, spv::DecorationLocation);
      }
      arr.push_back(item);
    }
    return arr;
  };

  root["uniform_buffers"] = buildResourceArray(resources.uniform_buffers);
  root["storage_buffers"] = buildResourceArray(resources.storage_buffers);
  root["sampled_images"] = buildResourceArray(resources.sampled_images);
  root["storage_images"] = buildResourceArray(resources.storage_images);
  root["separate_samplers"] = buildResourceArray(resources.separate_samplers);
  root["separate_images"] = buildResourceArray(resources.separate_images);
  root["push_constants"] = buildResourceArray(resources.push_constant_buffers);

  // Stage inputs/outputs
  root["stage_inputs"] = buildResourceArray(resources.stage_inputs);
  root["stage_outputs"] = buildResourceArray(resources.stage_outputs);

  return root;
}

void writeJsonFile(const std::string &path, const nlohmann::json &data) {
  std::ofstream out(path);
  if (!out) {
    throw std::runtime_error("Failed to write JSON file: " + path);
  }
  out << data.dump(2);
}

} // namespace

int main(int argc, char **argv) {
  CLI::App app{"Compile GLSL into SPIR-V and optionally optimize/reflect."};

  std::string inputPath;
  std::string outputPath;
  std::string stage;
  std::string entryPoint = "main";
  std::string reflectJsonPath;
  bool optimize = false;
  bool stripDebug = false;
  bool reflect = false;

  app.add_option("input", inputPath, "Input GLSL shader")->required()->check(CLI::ExistingFile);
  app.add_option("output", outputPath, "Output SPIR-V file")->required();
  app.add_option("--stage", stage, "Stage override: vert/frag/comp/geom/tesc/tese");
  app.add_option("--entry", entryPoint, "Entry point name");
  app.add_option("--reflect-json", reflectJsonPath, "Output reflection data as JSON");
  app.add_flag("--opt", optimize, "Run SPIR-V optimizer (performance passes)");
  app.add_flag("--strip", stripDebug, "Strip debug info");
  app.add_flag("--reflect", reflect, "Dump resource bindings to stdout");

  CLI11_PARSE(app, argc, argv);

  shaderc_shader_kind kind = shaderc_glsl_infer_from_source;
  if (!stage.empty()) {
    kind = stageFromFlag(stage);
  } else {
    kind = stageFromPath(inputPath);
  }
  if (kind == shaderc_glsl_infer_from_source) {
    std::cerr << "Could not infer shader stage. Use --stage.\n";
    return 1;
  }

  const std::string source = readTextFile(inputPath);

  shaderc::Compiler compiler;
  shaderc::CompileOptions options;
  options.SetTargetEnvironment(shaderc_target_env_opengl,
                               shaderc_env_version_opengl_4_5);
  options.SetAutoBindUniforms(true);
  options.SetAutoMapLocations(true);
  if (optimize) {
    options.SetOptimizationLevel(shaderc_optimization_level_performance);
  }

  auto result = compiler.CompileGlslToSpv(source, kind, inputPath.c_str(),
                                          entryPoint.c_str(), options);
  if (result.GetCompilationStatus() != shaderc_compilation_status_success) {
    std::cerr << result.GetErrorMessage() << "\n";
    return 1;
  }

  std::vector<uint32_t> spirv(result.cbegin(), result.cend());

  if (optimize || stripDebug) {
    spvtools::Optimizer optimizer(SPV_ENV_OPENGL_4_5);
    if (stripDebug) {
      optimizer.RegisterPass(spvtools::CreateStripDebugInfoPass());
    }
    if (optimize) {
      optimizer.RegisterPerformancePasses();
    }
    std::vector<uint32_t> optimized;
    if (!optimizer.Run(spirv.data(), spirv.size(), &optimized)) {
      std::cerr << "SPIR-V optimization failed.\n";
      return 1;
    }
    spirv = std::move(optimized);
  }

  if (reflect || !reflectJsonPath.empty()) {
    spirv_cross::Compiler reflector(spirv);

    if (reflect) {
      std::cout << "Entry points:\n";
      for (const auto &entry : reflector.get_entry_points_and_stages()) {
        std::cout << "  " << entry.name << " stage=" << entry.execution_model << "\n";
      }
      dumpResources(reflector);
    }

    if (!reflectJsonPath.empty()) {
      nlohmann::json reflectionData = buildReflectionJson(reflector, inputPath);
      writeJsonFile(reflectJsonPath, reflectionData);
    }
  }

  writeBinaryFile(outputPath, spirv);
  return 0;
}
