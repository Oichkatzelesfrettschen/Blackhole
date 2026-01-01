#include <CLI/CLI.hpp>
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

} // namespace

int main(int argc, char **argv) {
  CLI::App app{"Compile GLSL into SPIR-V and optionally optimize/reflect."};

  std::string inputPath;
  std::string outputPath;
  std::string stage;
  std::string entryPoint = "main";
  bool optimize = false;
  bool stripDebug = false;
  bool reflect = false;

  app.add_option("input", inputPath, "Input GLSL shader")->required()->check(CLI::ExistingFile);
  app.add_option("output", outputPath, "Output SPIR-V file")->required();
  app.add_option("--stage", stage, "Stage override: vert/frag/comp/geom/tesc/tese");
  app.add_option("--entry", entryPoint, "Entry point name");
  app.add_flag("--opt", optimize, "Run SPIR-V optimizer (performance passes)");
  app.add_flag("--strip", stripDebug, "Strip debug info");
  app.add_flag("--reflect", reflect, "Dump resource bindings");

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

  if (reflect) {
    spirv_cross::Compiler reflector(spirv);
    std::cout << "Entry points:\n";
    for (const auto &entry : reflector.get_entry_points_and_stages()) {
      std::cout << "  " << entry.name << " stage=" << entry.execution_model << "\n";
    }
    dumpResources(reflector);
  }

  writeBinaryFile(outputPath, spirv);
  return 0;
}
