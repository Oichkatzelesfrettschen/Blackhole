/**
 * @file main.cpp
 * @author Ross Ning (rossning92@gmail.com)
 * @brief Real-time black hole rendering in OpenGL.
 * @version 0.2
 * @date 2020-08-29
 *
 * @copyright Copyright (c) 2020
 *
 */

// C system headers
#include <cassert>
#include <csignal>
#include <cstdio>
#include <cstring>
#include <unistd.h>

// C++ system headers
#include <algorithm>
#include <array>
#include <cstdlib>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <map>
#include <sstream>
#include <string>
#include <vector>
#include <limits>
#include <thread>

// Third-party library headers
#include "gl_loader.h"
#ifndef BLACKHOLE_HAS_CPPTRACE
#if __has_include(<cpptrace/cpptrace.hpp>)
#define BLACKHOLE_HAS_CPPTRACE 1
#else
#define BLACKHOLE_HAS_CPPTRACE 0
#endif
#endif
#if BLACKHOLE_HAS_CPPTRACE
#include <cpptrace/cpptrace.hpp>
#endif
#include <GLFW/glfw3.h>
#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtc/type_ptr.hpp>
#include <imgui.h>
#include <imgui_internal.h>
#include <ImGuizmo.h>
#include <implot.h>
#include <nlohmann/json.hpp>

// Local headers
#include "GLDebugMessageCallback.h"
#include "grmhd_packed_loader.h"
#include "imgui_impl_glfw.h"
#include "imgui_impl_opengl3.h"
#include "hud_overlay.h"
#include "input.h"
#include "overlay.h"
#include "physics/hawking_renderer.h"
#include "physics/lut.h"
#include "physics/noise.h"
#include "rmlui_overlay.h"
#include "render.h"
#include "render/noise_texture_cache.h"
#include "settings.h"
#include "shader.h"
#include "shader_manager.h"
#include "shader_watcher.h"
#include "texture.h"
#include "tracy_support.h"

enum class CameraMode { Input = 0, Front, Top, Orbit };

static constexpr int kBackgroundLayers = 3;

#if BLACKHOLE_HAS_CPPTRACE
namespace {
constexpr std::size_t kTraceMaxFrames = 64;
volatile sig_atomic_t gHandlingSignal = 0;
bool gCanSignalSafeUnwind = false;
bool gCanSafeObjectInfo = false;

static std::size_t cstrLength(const char *str) {
  std::size_t length = 0;
  while (str[length] != '\0') {
    ++length;
  }
  return length;
}

static void writeStderr(const char *str) {
  ssize_t rc = write(STDERR_FILENO, str, cstrLength(str));
  (void)rc;
}

static void writeDec(std::size_t value) {
  char buf[32];
  std::size_t i = 0;
  do {
    buf[i++] = static_cast<char>('0' + (value % 10));
    value /= 10;
  } while (value != 0 && i < sizeof(buf));
  for (std::size_t j = 0; j < i / 2; ++j) {
    char tmp = buf[j];
    buf[j] = buf[i - 1 - j];
    buf[i - 1 - j] = tmp;
  }
  ssize_t rc = write(STDERR_FILENO, buf, i);
  (void)rc;
}

static void writeHex(uintptr_t value) {
  static constexpr char kHex[] = "0123456789abcdef";
  char buf[2 + sizeof(uintptr_t) * 2];
  buf[0] = '0';
  buf[1] = 'x';
  for (std::size_t i = 0; i < sizeof(uintptr_t) * 2; ++i) {
    buf[2 + sizeof(uintptr_t) * 2 - 1 - i] = kHex[value & 0xF];
    value >>= 4;
  }
  ssize_t rc = write(STDERR_FILENO, buf, sizeof(buf));
  (void)rc;
}

static const char *signalName(int sig) {
  switch (sig) {
    case SIGSEGV:
      return "SIGSEGV";
    case SIGABRT:
      return "SIGABRT";
    case SIGFPE:
      return "SIGFPE";
    case SIGILL:
      return "SIGILL";
    case SIGBUS:
      return "SIGBUS";
    case SIGTERM:
      return "SIGTERM";
    default:
      return "SIGNAL";
  }
}

static void crashSignalHandler(int sig) {
  if (gHandlingSignal != 0) {
    _Exit(128 + sig);
  }
  gHandlingSignal = 1;

  writeStderr("\n==== Blackhole crash signal: ");
  writeStderr(signalName(sig));
  writeStderr(" ====\n");

  if (!gCanSignalSafeUnwind) {
    writeStderr("cpptrace: signal-safe unwind unavailable\n");
    std::signal(sig, SIG_DFL);
    std::raise(sig);
    _Exit(128 + sig);
  }

  cpptrace::frame_ptr frames[kTraceMaxFrames];
  std::size_t count = cpptrace::safe_generate_raw_trace(frames, kTraceMaxFrames, 1);
  for (std::size_t i = 0; i < count; ++i) {
    writeStderr("#");
    writeDec(i);
    writeStderr(" ");
    writeHex(reinterpret_cast<uintptr_t>(frames[i]));
    if (gCanSafeObjectInfo) {
      cpptrace::safe_object_frame object_frame{};
      cpptrace::get_safe_object_frame(frames[i], &object_frame);
      if (object_frame.object_path[0] != '\0') {
        writeStderr(" ");
        writeStderr(object_frame.object_path);
        writeStderr(" +");
        writeHex(reinterpret_cast<uintptr_t>(object_frame.address_relative_to_object_start));
      }
    }
    writeStderr("\n");
  }

  std::signal(sig, SIG_DFL);
  std::raise(sig);
  _Exit(128 + sig);
}

static void installCrashHandlers() {
  cpptrace::use_default_stderr_logger();
  cpptrace::register_terminate_handler();
  gCanSignalSafeUnwind = cpptrace::can_signal_safe_unwind();
  gCanSafeObjectInfo = cpptrace::can_get_safe_object_frame();
  if (!gCanSignalSafeUnwind) {
    std::fprintf(stderr,
                 "cpptrace: signal-safe unwinding unavailable; signal crashes will be limited\n");
  }

  std::signal(SIGSEGV, crashSignalHandler);
  std::signal(SIGABRT, crashSignalHandler);
  std::signal(SIGFPE, crashSignalHandler);
  std::signal(SIGILL, crashSignalHandler);
  std::signal(SIGBUS, crashSignalHandler);
  std::signal(SIGTERM, crashSignalHandler);
}
}  // namespace
#else
static void installCrashHandlers() {}
#endif

static glm::vec3 cameraPositionFromYawPitch(float yawDeg, float pitchDeg, float radius) {
  float yawRad = glm::radians(yawDeg);
  float pitchRad = glm::radians(pitchDeg);
  return glm::vec3(radius * std::cos(pitchRad) * std::sin(yawRad),
                   radius * std::sin(pitchRad),
                   radius * std::cos(pitchRad) * std::cos(yawRad));
}

static glm::mat3 buildCameraBasis(const glm::vec3 &cameraPos, const glm::vec3 &target,
                                  float rollDeg) {
  glm::vec3 forward = glm::normalize(target - cameraPos);
  glm::vec3 worldUp(0.0f, 1.0f, 0.0f);
  if (std::abs(glm::dot(forward, worldUp)) > 0.99f) {
    worldUp = glm::vec3(0.0f, 0.0f, 1.0f);
  }

  glm::vec3 right = glm::normalize(glm::cross(forward, worldUp));
  glm::vec3 up = glm::normalize(glm::cross(right, forward));

  if (std::abs(rollDeg) > 0.001f) {
    float rollRad = glm::radians(rollDeg);
    float cosRoll = std::cos(rollRad);
    float sinRoll = std::sin(rollRad);
    glm::vec3 rolledRight = right * cosRoll + up * sinRoll;
    glm::vec3 rolledUp = -right * sinRoll + up * cosRoll;
    right = rolledRight;
    up = rolledUp;
  }

  return glm::mat3(right, up, forward);
}

static bool readTextFile(const std::string &path, std::string &out) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::ostringstream buffer;
  buffer << file.rdbuf();
  out = buffer.str();
  return !out.empty();
}

static void printUsage(const char *argv0) {
  std::printf("Usage: %s [--curve-tsv <path>]\n", argv0);
  std::printf("  --curve-tsv <path>   Load a 2-column TSV and plot it in ImGui.\n");
}

static void drawCurvePlot(const OverlayCurve2D &curve, const ImVec2 &size) {
  ImDrawList *drawList = ImGui::GetWindowDrawList();
  ImVec2 p0 = ImGui::GetCursorScreenPos();
  ImVec2 p1 = ImVec2(p0.x + size.x, p0.y + size.y);

  ImGui::InvisibleButton("curve_plot", size);

  drawList->AddRectFilled(p0, p1, IM_COL32(20, 20, 20, 255), 0.0f);
  drawList->AddRect(p0, p1, IM_COL32(200, 200, 200, 255), 0.0f);

  float xSpan = curve.max.x - curve.min.x;
  float ySpan = curve.max.y - curve.min.y;
  if (xSpan == 0.0f) {
    xSpan = 1.0f;
  }
  if (ySpan == 0.0f) {
    ySpan = 1.0f;
  }

  const float pad = 6.0f;
  ImVec2 q0 = ImVec2(p0.x + pad, p0.y + pad);
  ImVec2 q1 = ImVec2(p1.x - pad, p1.y - pad);
  float w = std::max(1.0f, q1.x - q0.x);
  float h = std::max(1.0f, q1.y - q0.y);

  std::vector<ImVec2> pts;
  pts.reserve(curve.points.size());
  for (const auto &pt : curve.points) {
    float nx = (pt.x - curve.min.x) / xSpan;
    float ny = (pt.y - curve.min.y) / ySpan;
    float px = q0.x + nx * w;
    float py = q1.y - ny * h;
    pts.emplace_back(px, py);
  }

  if (pts.size() >= 2) {
    drawList->AddPolyline(pts.data(), static_cast<int>(pts.size()),
                          IM_COL32(80, 200, 255, 255), false, 2.0f);
  }

  ImGui::Text("x:[%.4g, %.4g]  y:[%.4g, %.4g]  n=%d",
              static_cast<double>(curve.min.x), static_cast<double>(curve.max.x),
              static_cast<double>(curve.min.y), static_cast<double>(curve.max.y),
              static_cast<int>(curve.points.size()));
}

static bool hasExtension(const char *name) {
  GLint count = 0;
  glGetIntegerv(GL_NUM_EXTENSIONS, &count);
  for (GLint i = 0; i < count; ++i) {
    const char *ext =
        reinterpret_cast<const char *>(glGetStringi(GL_EXTENSIONS, static_cast<GLuint>(i)));
    if (ext != nullptr && std::string(ext) == name) {
      return true;
    }
  }
  return false;
}

static bool supportsDrawId() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  return versionIs46 || hasExtension("GL_ARB_shader_draw_parameters");
}

static bool supportsMultiDrawIndirect() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool versionIs43 = (major > 4) || (major == 4 && minor >= 3);
  return versionIs43 || hasExtension("GL_ARB_multi_draw_indirect");
}

static bool supportsIndirectCount() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  return versionIs46 || hasExtension("GL_ARB_indirect_parameters");
}

struct BackgroundAsset {
  std::string id;
  std::string title;
  std::string path;
};

struct DrawArraysIndirectCommand {
  GLuint count = 0;
  GLuint primCount = 0;
  GLuint first = 0;
  GLuint baseInstance = 0;
};

struct DrawInstanceGpu {
  glm::vec4 offsetScale;
  glm::vec4 tint;
  glm::vec4 flags;
};

struct WiregridMesh {
  GLuint vao = 0;
  GLuint vbo = 0;
  GLsizei vertexCount = 0;
};

struct WiregridParams {
  int ringCount = 32;
  int ringSegments = 256;
  int spokeCount = 32;
  float radiusMin = 2.0f;
  float radiusMax = 50.0f;
  float curvatureScale = 1.0f;
  bool showCurvature = true;
  float schwarzschildRadius = 1.0f;
};

static bool wiregridParamsEqual(const WiregridParams &a, const WiregridParams &b) {
  return a.ringCount == b.ringCount && a.ringSegments == b.ringSegments &&
         a.spokeCount == b.spokeCount && a.radiusMin == b.radiusMin &&
         a.radiusMax == b.radiusMax && a.curvatureScale == b.curvatureScale &&
         a.showCurvature == b.showCurvature &&
         a.schwarzschildRadius == b.schwarzschildRadius;
}

static void updateWiregridMesh(WiregridMesh &mesh, const WiregridParams &params) {
  std::vector<glm::vec3> vertices;
  if (params.ringCount < 2 || params.ringSegments < 3 || params.spokeCount < 1 ||
      params.radiusMax <= params.radiusMin) {
    mesh.vertexCount = 0;
    return;
  }

  // Curvature function: Flamm's paraboloid (spatial slice embedding)
  // z(r) = 2 * sqrt(r_s * (r - r_s)) for r >= r_s
  auto computeCurvature = [&](float r) -> float {
    if (!params.showCurvature || params.schwarzschildRadius <= 0.0f) {
      return 0.0f;
    }
    float rs = params.schwarzschildRadius;
    
    // Clamp r to be slightly above rs to avoid singularity/NaN
    float effectiveR = std::max(r, rs * 1.01f);
    
    // Flamm's paraboloid formula
    // We invert it (-z) to show a "well"
    float embeddingZ = 2.0f * std::sqrt(rs * (effectiveR - rs));
    
    // Shift so that outer radius is at y=0 (optional, but keeps grid grounded)
    // float outerZ = 2.0f * std::sqrt(rs * (params.radiusMax - rs));
    // return (embeddingZ - outerZ) * params.curvatureScale; 
    
    // Standard gravity well look: 
    return -embeddingZ * params.curvatureScale;
  };

  // Ensure grid starts outside the event horizon
  float effectiveMin = std::max(params.radiusMin, params.schwarzschildRadius * 1.01f);
  float effectiveMax = std::max(params.radiusMax, effectiveMin + 1.0f);

  const float twoPi = 6.283185307179586f;
  const float logRatio = effectiveMax / effectiveMin;

  auto getRadius = [&](float t) {
    // Use logarithmic spacing to place more rings near the event horizon
    // r = r_min * (r_max/r_min)^t
    return effectiveMin * std::pow(logRatio, t);
  };

  for (int ring = 0; ring < params.ringCount; ++ring) {
    float t = static_cast<float>(ring) / static_cast<float>(params.ringCount - 1);
    float r = getRadius(t);
    float y = computeCurvature(r);
    for (int seg = 0; seg < params.ringSegments; ++seg) {
      float a0 = twoPi * static_cast<float>(seg) / static_cast<float>(params.ringSegments);
      float a1 = twoPi * static_cast<float>(seg + 1) / static_cast<float>(params.ringSegments);
      glm::vec3 p0(r * std::cos(a0), y, r * std::sin(a0));
      glm::vec3 p1(r * std::cos(a1), y, r * std::sin(a1));
      vertices.push_back(p0);
      vertices.push_back(p1);
    }
  }

  for (int spoke = 0; spoke < params.spokeCount; ++spoke) {
    float a = twoPi * static_cast<float>(spoke) / static_cast<float>(params.spokeCount);
    // Spokes need multiple segments to show curvature
    const int spokeSegments = params.ringCount * 2; // Increase resolution for smooth spokes
    for (int i = 0; i < spokeSegments; ++i) {
      float t0 = static_cast<float>(i) / static_cast<float>(spokeSegments);
      float t1 = static_cast<float>(i + 1) / static_cast<float>(spokeSegments);
      float r0 = getRadius(t0);
      float r1 = getRadius(t1);
      float y0 = computeCurvature(r0);
      float y1 = computeCurvature(r1);
      glm::vec3 p0(r0 * std::cos(a), y0, r0 * std::sin(a));
      glm::vec3 p1(r1 * std::cos(a), y1, r1 * std::sin(a));
      vertices.push_back(p0);
      vertices.push_back(p1);
    }
  }

  if (mesh.vao == 0) {
    glGenVertexArrays(1, &mesh.vao);
  }
  if (mesh.vbo == 0) {
    glGenBuffers(1, &mesh.vbo);
  }

  glBindVertexArray(mesh.vao);
  glBindBuffer(GL_ARRAY_BUFFER, mesh.vbo);
  glBufferData(GL_ARRAY_BUFFER,
               static_cast<GLsizeiptr>(vertices.size() * sizeof(glm::vec3)),
               vertices.data(), GL_STATIC_DRAW);

  glEnableVertexAttribArray(0);
  glVertexAttribPointer(0, 3, GL_FLOAT, GL_FALSE, sizeof(glm::vec3),
                        reinterpret_cast<void *>(0));

  glBindVertexArray(0);
  glBindBuffer(GL_ARRAY_BUFFER, 0);

  mesh.vertexCount = static_cast<GLsizei>(vertices.size());
}

static std::vector<BackgroundAsset> loadBackgroundAssets() {
  std::vector<BackgroundAsset> assets;
  std::string text;
  if (!readTextFile("assets/backgrounds/manifest.json", text)) {
    return assets;
  }
  auto json = nlohmann::json::parse(text, nullptr, false);
  if (json.is_discarded() || !json.contains("assets") || !json["assets"].is_array()) {
    return assets;
  }
  for (const auto &entry : json["assets"]) {
    BackgroundAsset asset;
    asset.id = entry.value("id", "");
    asset.title = entry.value("title", asset.id);
    asset.path = entry.value("path", "");
    if (!asset.id.empty() && !asset.path.empty()) {
      assets.push_back(std::move(asset));
    }
  }
  return assets;
}

static int findBackgroundIndex(const std::vector<BackgroundAsset> &assets,
                               const std::string &id) {
  for (std::size_t i = 0; i < assets.size(); ++i) {
    if (assets[i].id == id) {
      return static_cast<int>(i);
    }
  }
  return 0;
}

static bool parseJsonNumber(const std::string &text, const std::string &key, double &out) {
  std::string needle = "\"" + key + "\"";
  std::size_t pos = text.find(needle);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find(':', pos);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find_first_of("+-0123456789.", pos);
  if (pos == std::string::npos) {
    return false;
  }
  const char *start = text.c_str() + pos;
  char *end = nullptr;
  out = std::strtod(start, &end);
  return end != start;
}

struct DiffStats {
  float meanAbs = 0.0f;
  float maxAbs = 0.0f;
  float rms = 0.0f;
  bool valid = false;
};

static DiffStats sampleTextureDiff(GLuint texA, GLuint texB, int width, int height,
                                   int sampleSize) {
  DiffStats stats;
  if (texA == 0 || texB == 0 || width <= 0 || height <= 0 || sampleSize <= 0) {
    return stats;
  }

  const int sampleW = std::min(sampleSize, width);
  const int sampleH = std::min(sampleSize, height);
  const int offsetX = (width - sampleW) / 2;
  const int offsetY = (height - sampleH) / 2;
  const std::size_t pixelCount = static_cast<std::size_t>(sampleW * sampleH);
  const std::size_t channelCount = pixelCount * 4;

  std::vector<float> dataA(channelCount, 0.0f);
  std::vector<float> dataB(channelCount, 0.0f);

  glGetTextureSubImage(texA, 0, offsetX, offsetY, 0, sampleW, sampleH, 1, GL_RGBA, GL_FLOAT,
                       static_cast<GLsizei>(channelCount * sizeof(float)), dataA.data());
  glGetTextureSubImage(texB, 0, offsetX, offsetY, 0, sampleW, sampleH, 1, GL_RGBA, GL_FLOAT,
                       static_cast<GLsizei>(channelCount * sizeof(float)), dataB.data());

  double total = 0.0;
  double totalSq = 0.0;
  double maxAbs = 0.0;
  for (std::size_t i = 0; i < channelCount; i += 4) {
    for (std::size_t c = 0; c < 3; ++c) {
      double diff = std::abs(static_cast<double>(dataA[i + c]) -
                             static_cast<double>(dataB[i + c]));
      total += diff;
      totalSq += diff * diff;
      maxAbs = std::max(maxAbs, diff);
    }
  }

  const double denom = static_cast<double>(pixelCount * 3);
  if (denom > 0.0) {
    stats.meanAbs = static_cast<float>(total / denom);
    stats.rms = static_cast<float>(std::sqrt(totalSq / denom));
    stats.maxAbs = static_cast<float>(maxAbs);
    stats.valid = true;
  }

  return stats;
}

static bool readTextureRGBA(GLuint texture, int width, int height, std::vector<float> &out) {
  if (texture == 0 || width <= 0 || height <= 0) {
    return false;
  }
  const std::size_t channelCount =
      static_cast<std::size_t>(width) * static_cast<std::size_t>(height) * 4u;
  out.assign(channelCount, 0.0f);
  glGetTextureSubImage(texture, 0, 0, 0, 0, width, height, 1, GL_RGBA, GL_FLOAT,
                       static_cast<GLsizei>(channelCount * sizeof(float)), out.data());
  return true;
}

static DiffStats computeDiffStats(const std::vector<float> &a, const std::vector<float> &b) {
  DiffStats stats;
  if (a.size() != b.size() || a.empty()) {
    return stats;
  }

  double total = 0.0;
  double totalSq = 0.0;
  double maxAbs = 0.0;
  for (std::size_t i = 0; i + 3 < a.size(); i += 4) {
    for (std::size_t c = 0; c < 3; ++c) {
      double diff = std::abs(static_cast<double>(a[i + c]) -
                             static_cast<double>(b[i + c]));
      total += diff;
      totalSq += diff * diff;
      maxAbs = std::max(maxAbs, diff);
    }
  }

  const double denom = static_cast<double>((a.size() / 4) * 3);
  if (denom > 0.0) {
    stats.meanAbs = static_cast<float>(total / denom);
    stats.rms = static_cast<float>(std::sqrt(totalSq / denom));
    stats.maxAbs = static_cast<float>(maxAbs);
    stats.valid = true;
  }
  return stats;
}

static std::size_t countDiffOutliers(const std::vector<float> &a, const std::vector<float> &b,
                                     float threshold) {
  if (a.size() != b.size() || a.empty() || threshold <= 0.0f) {
    return 0;
  }
  std::size_t count = 0;
  for (std::size_t i = 0; i + 3 < a.size(); i += 4) {
    double dr = std::abs(static_cast<double>(a[i]) - static_cast<double>(b[i]));
    double dg = std::abs(static_cast<double>(a[i + 1]) - static_cast<double>(b[i + 1]));
    double db = std::abs(static_cast<double>(a[i + 2]) - static_cast<double>(b[i + 2]));
    if (std::max({dr, dg, db}) > static_cast<double>(threshold)) {
      ++count;
    }
  }
  return count;
}

static bool writePpm(const std::string &path, const std::vector<float> &rgba, int width,
                     int height, float scale) {
  if (rgba.empty() || width <= 0 || height <= 0) {
    return false;
  }
  std::ofstream out(path, std::ios::binary);
  if (!out) {
    return false;
  }
  out << "P6\n" << width << " " << height << "\n255\n";
  for (std::size_t i = 0; i + 3 < rgba.size(); i += 4) {
    auto clampChannel = [&](float v) -> unsigned char {
      float scaled = std::clamp(v * scale, 0.0f, 1.0f);
      return static_cast<unsigned char>(scaled * 255.0f);
    };
    unsigned char rgb[3] = {clampChannel(rgba[i]), clampChannel(rgba[i + 1]),
                            clampChannel(rgba[i + 2])};
    out.write(reinterpret_cast<const char *>(rgb), 3);
  }
  return true;
}

static bool writeDiffPpm(const std::string &path, const std::vector<float> &a,
                         const std::vector<float> &b, int width, int height, float scale) {
  if (a.size() != b.size() || a.empty() || width <= 0 || height <= 0) {
    return false;
  }
  std::ofstream out(path, std::ios::binary);
  if (!out) {
    return false;
  }
  out << "P6\n" << width << " " << height << "\n255\n";
  for (std::size_t i = 0; i + 3 < a.size(); i += 4) {
    auto clampChannel = [&](float v) -> unsigned char {
      float scaled = std::clamp(v * scale, 0.0f, 1.0f);
      return static_cast<unsigned char>(scaled * 255.0f);
    };
    float dr = std::abs(a[i] - b[i]);
    float dg = std::abs(a[i + 1] - b[i + 1]);
    float db = std::abs(a[i + 2] - b[i + 2]);
    unsigned char rgb[3] = {clampChannel(dr), clampChannel(dg), clampChannel(db)};
    out.write(reinterpret_cast<const char *>(rgb), 3);
  }
  return true;
}

static std::string compareSnapshotPath(int index, const std::string &tag) {
  std::filesystem::create_directories("logs/compare");
  return "logs/compare/compare_" + std::to_string(index) + "_" + tag + ".ppm";
}

static std::string compareSummaryPath() {
  std::filesystem::create_directories("logs/compare");
  return "logs/compare/compare_summary.csv";
}

static std::string compareUniformsPath() {
  std::filesystem::create_directories("logs/compare");
  return "logs/compare/compare_uniforms.csv";
}

static void appendCompareSummary(const std::string &path, int index,
                                 const std::string &primaryTag,
                                 const std::string &secondaryTag, int width, int height,
                                 const DiffStats &stats, float diffScale, bool wroteOutputs,
                                 bool wroteDiff, float threshold, bool exceeded,
                                 double timeSec, float kerrSpin, bool grbEnabled,
                                 float grbTime, int outlierCount, int outlierLimit,
                                 float outlierFrac) {
  if (!stats.valid) {
    return;
  }
  const bool exists = std::filesystem::exists(path);
  std::ofstream out(path, std::ios::app);
  if (!out) {
    return;
  }
  if (!exists) {
    out << "index,primary,secondary,width,height,mean_abs,rms,max_abs,diff_scale,threshold,exceeded,"
           "write_outputs,write_diff,time_sec,kerr_spin,grb_enabled,grb_time,outlier_count,"
           "outlier_limit,outlier_frac\n";
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << primaryTag << "," << secondaryTag << "," << width << "," << height << ","
      << stats.meanAbs << "," << stats.rms << "," << stats.maxAbs << "," << diffScale << ","
      << threshold << "," << (exceeded ? 1 : 0) << "," << (wroteOutputs ? 1 : 0) << ","
      << (wroteDiff ? 1 : 0) << "," << timeSec << "," << kerrSpin << ","
      << (grbEnabled ? 1 : 0) << "," << grbTime << "," << outlierCount << ","
      << outlierLimit << "," << outlierFrac << "\n";
}

struct ComparePreset {
  const char *label;
  CameraMode mode;
  CameraState camera;
  float orbitRadius;
  float orbitSpeed;
  float kerrSpin;
};

static constexpr float kCompareKerrSpin = 0.8f;
static constexpr int kIntegratorDebugNanFlag = 1;
static constexpr int kIntegratorDebugRangeFlag = 2;
static constexpr std::array<ComparePreset, 12> kComparePresets = {{
    {"Input Near (Schw)", CameraMode::Input, CameraState{30.0f, -10.0f, 0.0f, 8.0f, 45.0f},
     15.0f, 0.0f, 0.0f},
    {"Input Near (Kerr)", CameraMode::Input, CameraState{30.0f, -10.0f, 0.0f, 8.0f, 45.0f},
     15.0f, 0.0f, kCompareKerrSpin},
    {"Input Far (Schw)", CameraMode::Input, CameraState{60.0f, 10.0f, 0.0f, 20.0f, 45.0f},
     15.0f, 0.0f, 0.0f},
    {"Input Far (Kerr)", CameraMode::Input, CameraState{60.0f, 10.0f, 0.0f, 20.0f, 45.0f},
     15.0f, 0.0f, kCompareKerrSpin},
    {"Front (Schw)", CameraMode::Front, CameraState{}, 15.0f, 0.0f, 0.0f},
    {"Front (Kerr)", CameraMode::Front, CameraState{}, 15.0f, 0.0f, kCompareKerrSpin},
    {"Top (Schw)", CameraMode::Top, CameraState{}, 15.0f, 0.0f, 0.0f},
    {"Top (Kerr)", CameraMode::Top, CameraState{}, 15.0f, 0.0f, kCompareKerrSpin},
    {"Orbit Near (Schw)", CameraMode::Orbit, CameraState{}, 10.0f, 0.0f, 0.0f},
    {"Orbit Near (Kerr)", CameraMode::Orbit, CameraState{}, 10.0f, 0.0f, kCompareKerrSpin},
    {"Orbit Far (Schw)", CameraMode::Orbit, CameraState{}, 20.0f, 0.0f, 0.0f},
    {"Orbit Far (Kerr)", CameraMode::Orbit, CameraState{}, 20.0f, 0.0f, kCompareKerrSpin},
}};

struct InteropUniforms {
  glm::vec3 cameraPos{};
  glm::mat3 cameraBasis{1.0f};
  float fovScale = 1.0f;
  float timeSec = 0.0f;
  float schwarzschildRadius = 0.0f;
  float iscoRadius = 0.0f;
  float kerrSpin = 0.0f;
  float depthFar = 0.0f;
  int maxSteps = 0;
  float stepSize = 0.0f;
  float adiskEnabled = 0.0f;
  float enableRedshift = 0.0f;
  float useLUTs = 0.0f;
  float useSpectralLUT = 0.0f;
  float useGrbModulation = 0.0f;
  float lutRadiusMin = 0.0f;
  float lutRadiusMax = 1.0f;
  float redshiftRadiusMin = 0.0f;
  float redshiftRadiusMax = 1.0f;
  float spectralRadiusMin = 0.0f;
  float spectralRadiusMax = 1.0f;
  float grbTime = 0.0f;
  float grbTimeMin = 0.0f;
  float grbTimeMax = 1.0f;
};

static void appendCompareUniforms(const std::string &path, int index, const std::string &label,
                                  const InteropUniforms &interop, bool compareBaseline,
                                  bool compareOverrides, bool backgroundEnabled,
                                  bool noiseEnabled, bool grmhdEnabled,
                                  bool spectralEnabled, bool grbEnabled,
                                  bool photonSphereEnabled) {
  const bool exists = std::filesystem::exists(path);
  std::ofstream out(path, std::ios::app);
  if (!out) {
    return;
  }
  if (!exists) {
    out << "index,label,camera_x,camera_y,camera_z,fov_scale,time_sec,depth_far,"
           "schwarzschild_radius,isco_radius,kerr_spin,max_steps,step_size,adisk_enabled,"
           "enable_redshift,use_luts,use_spectral_lut,use_grb_modulation,background_enabled,"
           "noise_enabled,grmhd_enabled,spectral_enabled,grb_enabled,photon_sphere_enabled,"
           "compare_baseline,compare_overrides\n";
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << label << "," << interop.cameraPos.x << "," << interop.cameraPos.y
      << "," << interop.cameraPos.z << "," << interop.fovScale << "," << interop.timeSec
      << "," << interop.depthFar << "," << interop.schwarzschildRadius << ","
      << interop.iscoRadius << "," << interop.kerrSpin << "," << interop.maxSteps << ","
      << interop.stepSize << "," << interop.adiskEnabled << "," << interop.enableRedshift
      << "," << interop.useLUTs << "," << interop.useSpectralLUT << ","
      << interop.useGrbModulation << "," << (backgroundEnabled ? 1 : 0) << ","
      << (noiseEnabled ? 1 : 0) << "," << (grmhdEnabled ? 1 : 0) << ","
      << (spectralEnabled ? 1 : 0) << "," << (grbEnabled ? 1 : 0) << ","
      << (photonSphereEnabled ? 1 : 0) << "," << (compareBaseline ? 1 : 0) << ","
      << (compareOverrides ? 1 : 0) << "\n";
}

static void applyInteropUniforms(RenderToTextureInfo &rtti, const InteropUniforms &interop,
                                 bool parityMode, bool hawkingEnabled, float hawkingTempScale,
                                 float hawkingIntensity, bool hawkingUseLUTs, double blackHoleMass) {
  rtti.vec3Uniforms["cameraPos"] = interop.cameraPos;
  rtti.mat3Uniforms["cameraBasis"] = interop.cameraBasis;
  rtti.floatUniforms["fovScale"] = interop.fovScale;
  rtti.floatUniforms["time"] = interop.timeSec;
  rtti.floatUniforms["depthFar"] = interop.depthFar;
  rtti.floatUniforms["schwarzschildRadius"] = interop.schwarzschildRadius;
  rtti.floatUniforms["kerrSpin"] = interop.kerrSpin;
  rtti.floatUniforms["adiskEnabled"] = interop.adiskEnabled;
  rtti.floatUniforms["enableRedshift"] = interop.enableRedshift;
  rtti.floatUniforms["useLUTs"] = interop.useLUTs;
  rtti.floatUniforms["useSpectralLUT"] = interop.useSpectralLUT;
  rtti.floatUniforms["useGrbModulation"] = interop.useGrbModulation;
  rtti.floatUniforms["lutRadiusMin"] = interop.lutRadiusMin;
  rtti.floatUniforms["lutRadiusMax"] = interop.lutRadiusMax;
  rtti.floatUniforms["redshiftRadiusMin"] = interop.redshiftRadiusMin;
  rtti.floatUniforms["redshiftRadiusMax"] = interop.redshiftRadiusMax;
  rtti.floatUniforms["spectralRadiusMin"] = interop.spectralRadiusMin;
  rtti.floatUniforms["spectralRadiusMax"] = interop.spectralRadiusMax;
  rtti.floatUniforms["grbTime"] = interop.grbTime;
  rtti.floatUniforms["grbTimeMin"] = interop.grbTimeMin;
  rtti.floatUniforms["grbTimeMax"] = interop.grbTimeMax;
  rtti.floatUniforms["interopParityMode"] = parityMode ? 1.0f : 0.0f;
  rtti.floatUniforms["interopMaxSteps"] = static_cast<float>(interop.maxSteps);
  rtti.floatUniforms["interopStepSize"] = interop.stepSize;

  // Hawking radiation uniforms
  rtti.floatUniforms["hawkingGlowEnabled"] = hawkingEnabled ? 1.0f : 0.0f;
  rtti.floatUniforms["hawkingTempScale"] = hawkingTempScale;
  rtti.floatUniforms["hawkingGlowIntensity"] = hawkingIntensity;
  rtti.floatUniforms["useHawkingLUTs"] = hawkingUseLUTs ? 1.0f : 0.0f;
  rtti.floatUniforms["blackHoleMass"] = static_cast<float>(blackHoleMass);
}

static void applyInteropComputeUniforms(GLuint program, const InteropUniforms &interop,
                                        int width, int height) {
  glUniform2f(glGetUniformLocation(program, "resolution"), static_cast<float>(width),
              static_cast<float>(height));
  glUniformMatrix3fv(glGetUniformLocation(program, "cameraBasis"), 1, GL_FALSE,
                     glm::value_ptr(interop.cameraBasis));
  glUniform1f(glGetUniformLocation(program, "fovScale"), interop.fovScale);
  glUniform1f(glGetUniformLocation(program, "time"), interop.timeSec);
  glUniform3f(glGetUniformLocation(program, "cameraPos"), interop.cameraPos.x,
              interop.cameraPos.y, interop.cameraPos.z);
  glUniform1f(glGetUniformLocation(program, "schwarzschildRadius"),
              interop.schwarzschildRadius);
  glUniform1f(glGetUniformLocation(program, "kerrSpin"), interop.kerrSpin);
  glUniform1i(glGetUniformLocation(program, "interopMaxSteps"), interop.maxSteps);
  glUniform1f(glGetUniformLocation(program, "interopStepSize"), interop.stepSize);
  glUniform1f(glGetUniformLocation(program, "depthFar"), interop.depthFar);
  glUniform1f(glGetUniformLocation(program, "adiskEnabled"), interop.adiskEnabled);
  glUniform1f(glGetUniformLocation(program, "enableRedshift"), interop.enableRedshift);
  glUniform1f(glGetUniformLocation(program, "useLUTs"), interop.useLUTs);
  glUniform1f(glGetUniformLocation(program, "useSpectralLUT"), interop.useSpectralLUT);
  glUniform1f(glGetUniformLocation(program, "useGrbModulation"), interop.useGrbModulation);
  glUniform1f(glGetUniformLocation(program, "lutRadiusMin"), interop.lutRadiusMin);
  glUniform1f(glGetUniformLocation(program, "lutRadiusMax"), interop.lutRadiusMax);
  glUniform1f(glGetUniformLocation(program, "redshiftRadiusMin"), interop.redshiftRadiusMin);
  glUniform1f(glGetUniformLocation(program, "redshiftRadiusMax"), interop.redshiftRadiusMax);
  glUniform1f(glGetUniformLocation(program, "spectralRadiusMin"), interop.spectralRadiusMin);
  glUniform1f(glGetUniformLocation(program, "spectralRadiusMax"), interop.spectralRadiusMax);
  glUniform1f(glGetUniformLocation(program, "grbTime"), interop.grbTime);
  glUniform1f(glGetUniformLocation(program, "grbTimeMin"), interop.grbTimeMin);
  glUniform1f(glGetUniformLocation(program, "grbTimeMax"), interop.grbTimeMax);
}

static void applyHawkingUniforms(GLuint program, const physics::HawkingRenderer& renderer,
                                 bool enabled, float tempScale, float intensity,
                                 bool useLUTs, double blackHoleMass) {
  if (!renderer.isReady()) {
    return;
  }

  physics::HawkingGlowParams params;
  params.enabled = enabled;
  params.tempScale = tempScale;
  params.intensity = intensity;
  params.useLUTs = useLUTs;

  renderer.setShaderUniforms(program, blackHoleMass, params);
}

static bool loadLutCsv(const std::string &path, std::vector<float> &values) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::string line;
  bool first = true;
  while (std::getline(file, line)) {
    if (first) {
      first = false;
      continue;
    }
    if (line.empty()) {
      continue;
    }
    std::size_t comma = line.find(',');
    if (comma == std::string::npos) {
      continue;
    }
    const char *start = line.c_str() + comma + 1;
    char *end = nullptr;
    double value = std::strtod(start, &end);
    if (end == start) {
      continue;
    }
    values.push_back(static_cast<float>(value));
  }
  return !values.empty();
}

static bool loadLutAssets(physics::Lut1D &emissivity, physics::Lut1D &redshift,
                          float &spinOut) {
  std::vector<float> emissivityValues;
  std::vector<float> redshiftValues;
  if (!loadLutCsv("assets/luts/emissivity_lut.csv", emissivityValues)) {
    return false;
  }
  if (!loadLutCsv("assets/luts/redshift_lut.csv", redshiftValues)) {
    return false;
  }
  std::string metaText;
  if (!readTextFile("assets/luts/lut_meta.json", metaText)) {
    return false;
  }
  double rInOverRs = 0.0;
  double rOutOverRs = 0.0;
  double spin = 0.0;
  if (!parseJsonNumber(metaText, "r_in_over_rs", rInOverRs)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_out_over_rs", rOutOverRs)) {
    return false;
  }
  parseJsonNumber(metaText, "spin", spin);

  emissivity.values = std::move(emissivityValues);
  emissivity.r_min = static_cast<float>(rInOverRs);
  emissivity.r_max = static_cast<float>(rOutOverRs);
  redshift.values = std::move(redshiftValues);
  redshift.r_min = static_cast<float>(rInOverRs);
  redshift.r_max = static_cast<float>(rOutOverRs);
  spinOut = static_cast<float>(spin);
  return true;
}

static bool loadSpectralLutAssets(std::vector<float> &values, float &wavelengthMin,
                                  float &wavelengthMax) {
  values.clear();
  if (!loadLutCsv("assets/luts/rt_spectrum_lut.csv", values)) {
    return false;
  }
  std::string metaText;
  if (!readTextFile("assets/luts/rt_spectrum_meta.json", metaText)) {
    return false;
  }
  double waveMin = 0.0;
  double waveMax = 0.0;
  if (!parseJsonNumber(metaText, "wavelength_min_angstrom", waveMin)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "wavelength_max_angstrom", waveMax)) {
    return false;
  }
  wavelengthMin = static_cast<float>(waveMin);
  wavelengthMax = static_cast<float>(waveMax);
  return true;
}

static bool loadGrbModulationLutAssets(std::vector<float> &values, float &timeMin,
                                       float &timeMax) {
  values.clear();
  if (!loadLutCsv("assets/luts/grb_modulation_lut.csv", values)) {
    return false;
  }
  std::string metaText;
  if (!readTextFile("assets/luts/grb_modulation_meta.json", metaText)) {
    return false;
  }
  double tMin = 0.0;
  double tMax = 0.0;
  if (!parseJsonNumber(metaText, "t_min", tMin)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "t_max", tMax)) {
    return false;
  }
  timeMin = static_cast<float>(tMin);
  timeMax = static_cast<float>(tMax);
  return true;
}

static void glfwErrorCallback(int error, const char *description) {
  fprintf(stderr, "Glfw Error %d: %s\n", error, description);
}

// GLFW callbacks that delegate to InputManager
static void keyCallback(GLFWwindow * /*window*/, int key, int scancode, int action, int mods) {
  InputManager::instance().onKey(key, scancode, action, mods);
}

static void mouseButtonCallback(GLFWwindow * /*window*/, int button, int action, int mods) {
  InputManager::instance().onMouseButton(button, action, mods);
}

static void cursorPosCallback(GLFWwindow * /*window*/, double x, double y) {
  InputManager::instance().onMouseMove(x, y);
}

static void scrollCallback(GLFWwindow * /*window*/, double xoffset, double yoffset) {
  InputManager::instance().onScroll(xoffset, yoffset);
}

// Initialize OpenGL debug context (call after loader init)
static void initializeGLDebugContext() {
#ifdef ENABLE_GL_DEBUG_CONTEXT
  // Check if debug context is available (OpenGL 4.3+ or KHR_debug extension)
  GLint contextFlags = 0;
  glGetIntegerv(GL_CONTEXT_FLAGS, &contextFlags);
  const ContextFlagMask flags = static_cast<ContextFlagMask>(contextFlags);

  if ((flags & GL_CONTEXT_FLAG_DEBUG_BIT) != ContextFlagMask{}) {
    std::printf("[GL Debug] Debug context active\n");

    // Enable debug output
    glEnable(GL_DEBUG_OUTPUT);
    glEnable(GL_DEBUG_OUTPUT_SYNCHRONOUS);

    // Set debug callback
    glDebugMessageCallback(GLDebugMessageCallback, nullptr);

    // Enable all messages by default
    glDebugMessageControl(GL_DONT_CARE, GL_DONT_CARE, GL_DONT_CARE, 0, nullptr, GL_TRUE);

    // Optionally disable notification-level messages (very verbose)
    glDebugMessageControl(GL_DONT_CARE, GL_DONT_CARE, GL_DEBUG_SEVERITY_NOTIFICATION, 0, nullptr,
                          GL_FALSE);

    std::printf("[GL Debug] Debug message callback registered\n");
  } else {
    std::printf("[GL Debug] Debug context not available (need OpenGL 4.3+ or KHR_debug)\n");
  }
#endif
}

static void configureParallelShaderCompile() {
  const char *env = std::getenv("BLACKHOLE_PARALLEL_SHADER_COMPILE");
  if (env == nullptr || std::string(env) != "1") {
    return;
  }
  if (!hasExtension("GL_KHR_parallel_shader_compile")) {
    std::cout << "Parallel shader compile requested but not supported.\n";
    return;
  }
  unsigned int threads = std::thread::hardware_concurrency();
  if (threads == 0) {
    threads = 1;
  }
  const char *threadEnv = std::getenv("BLACKHOLE_SHADER_COMPILE_THREADS");
  if (threadEnv != nullptr) {
    threads = static_cast<unsigned int>(std::max(1, std::atoi(threadEnv)));
  }
  glMaxShaderCompilerThreadsKHR(static_cast<GLuint>(threads));
  std::cout << "Parallel shader compile enabled (" << threads << " threads).\n";
}

// Initialize GLFW and create window
static GLFWwindow *initializeWindow(int width, int height) {
  glfwSetErrorCallback(glfwErrorCallback);
  if (!glfwInit()) {
    return nullptr;
  }

  glfwWindowHint(GLFW_DECORATED, GLFW_TRUE);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
  glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
  glfwWindowHint(GLFW_OPENGL_FORWARD_COMPAT, GLFW_TRUE);
  const char *noErrorEnv = std::getenv("BLACKHOLE_NO_ERROR_CONTEXT");
  if (noErrorEnv != nullptr && std::string(noErrorEnv) == "1") {
    glfwWindowHint(GLFW_CONTEXT_NO_ERROR, GLFW_TRUE);
  }

#ifdef ENABLE_GL_DEBUG_CONTEXT
  // Request debug context for OpenGL error reporting
  glfwWindowHint(GLFW_OPENGL_DEBUG_CONTEXT, GLFW_TRUE);
#endif

  GLFWwindow *window = glfwCreateWindow(width, height, "Blackhole", nullptr, nullptr);
  if (window == nullptr) {
    return nullptr;
  }

  glfwMakeContextCurrent(window);

  // Set up input callbacks
  glfwSetKeyCallback(window, keyCallback);
  glfwSetMouseButtonCallback(window, mouseButtonCallback);
  glfwSetCursorPosCallback(window, cursorPosCallback);
  glfwSetScrollCallback(window, scrollCallback);

  glfwSetWindowPos(window, 0, 0);

  glbinding::initialize(glfwGetProcAddress);

  GLint glMajor = 0;
  GLint glMinor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &glMajor);
  glGetIntegerv(GL_MINOR_VERSION, &glMinor);
  if (glMajor < 4 || (glMajor == 4 && glMinor < 6)) {
    std::fprintf(stderr, "OpenGL 4.6 required, found %d.%d\n", glMajor, glMinor);
    glfwDestroyWindow(window);
    return nullptr;
  }

  // Initialize GL debug context after loader init
  initializeGLDebugContext();
  configureParallelShaderCompile();

  return window;
}

// Configure custom ImGui style for "Blackhole" theme (16-bit Voxel Aesthetic)
static void setupImGuiStyle() {
  ImGuiStyle &style = ImGui::GetStyle();
  ImVec4 *colors = style.Colors;

  // Voxel/Retro Geometry: Sharp corners, distinct borders
  style.WindowRounding = 0.0f;
  style.FrameRounding = 0.0f;
  style.PopupRounding = 0.0f;
  style.ScrollbarRounding = 0.0f;
  style.GrabRounding = 0.0f;
  style.TabRounding = 0.0f;
  style.FrameBorderSize = 1.0f;
  style.WindowBorderSize = 1.0f;
  style.PopupBorderSize = 1.0f;
  style.WindowPadding = ImVec2(8, 8);
  style.FramePadding = ImVec2(6, 4);
  style.ItemSpacing = ImVec2(8, 6);

  // Retro Palette: Deep Blue/Black bg, Cyan/Orange accents
  colors[ImGuiCol_Text] = ImVec4(0.90f, 0.90f, 0.90f, 1.00f);
  colors[ImGuiCol_TextDisabled] = ImVec4(0.50f, 0.50f, 0.50f, 1.00f);
  colors[ImGuiCol_WindowBg] = ImVec4(0.05f, 0.05f, 0.08f, 1.00f);
  colors[ImGuiCol_ChildBg] = ImVec4(0.08f, 0.08f, 0.12f, 1.00f);
  colors[ImGuiCol_PopupBg] = ImVec4(0.05f, 0.05f, 0.08f, 1.00f);
  colors[ImGuiCol_Border] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_BorderShadow] = ImVec4(0.00f, 0.00f, 0.00f, 0.00f);
  colors[ImGuiCol_FrameBg] = ImVec4(0.15f, 0.15f, 0.20f, 1.00f);
  colors[ImGuiCol_FrameBgHovered] = ImVec4(0.25f, 0.25f, 0.35f, 1.00f);
  colors[ImGuiCol_FrameBgActive] = ImVec4(0.30f, 0.30f, 0.45f, 1.00f);
  colors[ImGuiCol_TitleBg] = ImVec4(0.10f, 0.10f, 0.15f, 1.00f);
  colors[ImGuiCol_TitleBgActive] = ImVec4(0.15f, 0.15f, 0.25f, 1.00f);
  colors[ImGuiCol_TitleBgCollapsed] = ImVec4(0.05f, 0.05f, 0.08f, 1.00f);
  colors[ImGuiCol_MenuBarBg] = ImVec4(0.10f, 0.10f, 0.15f, 1.00f);
  colors[ImGuiCol_ScrollbarBg] = ImVec4(0.05f, 0.05f, 0.08f, 1.00f);
  colors[ImGuiCol_ScrollbarGrab] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_ScrollbarGrabHovered] = ImVec4(0.40f, 0.40f, 0.50f, 1.00f);
  colors[ImGuiCol_ScrollbarGrabActive] = ImVec4(0.50f, 0.50f, 0.60f, 1.00f);
  colors[ImGuiCol_CheckMark] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f); // Cyan
  colors[ImGuiCol_SliderGrab] = ImVec4(0.00f, 0.60f, 0.80f, 1.00f);
  colors[ImGuiCol_SliderGrabActive] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_Button] = ImVec4(0.20f, 0.20f, 0.25f, 1.00f);
  colors[ImGuiCol_ButtonHovered] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_ButtonActive] = ImVec4(0.00f, 0.50f, 0.70f, 1.00f);
  colors[ImGuiCol_Header] = ImVec4(0.20f, 0.20f, 0.25f, 1.00f);
  colors[ImGuiCol_HeaderHovered] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_HeaderActive] = ImVec4(0.00f, 0.50f, 0.70f, 1.00f);
  colors[ImGuiCol_Separator] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_SeparatorHovered] = ImVec4(0.40f, 0.40f, 0.50f, 1.00f);
  colors[ImGuiCol_SeparatorActive] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_ResizeGrip] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_ResizeGripHovered] = ImVec4(0.40f, 0.40f, 0.50f, 1.00f);
  colors[ImGuiCol_ResizeGripActive] = ImVec4(0.50f, 0.50f, 0.60f, 1.00f);
  colors[ImGuiCol_Tab] = ImVec4(0.15f, 0.15f, 0.20f, 1.00f);
  colors[ImGuiCol_TabHovered] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_TabActive] = ImVec4(0.20f, 0.20f, 0.25f, 1.00f);
  colors[ImGuiCol_TabUnfocused] = ImVec4(0.10f, 0.10f, 0.15f, 1.00f);
  colors[ImGuiCol_TabUnfocusedActive] = ImVec4(0.15f, 0.15f, 0.20f, 1.00f);
  colors[ImGuiCol_DockingPreview] = ImVec4(0.00f, 0.80f, 1.00f, 0.70f);
  colors[ImGuiCol_DockingEmptyBg] = ImVec4(0.10f, 0.10f, 0.10f, 1.00f);
  colors[ImGuiCol_PlotLines] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_PlotLinesHovered] = ImVec4(1.00f, 0.50f, 0.00f, 1.00f);
  colors[ImGuiCol_PlotHistogram] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_PlotHistogramHovered] = ImVec4(1.00f, 0.50f, 0.00f, 1.00f);
  colors[ImGuiCol_TextSelectedBg] = ImVec4(0.00f, 0.50f, 0.80f, 0.35f);
  colors[ImGuiCol_DragDropTarget] = ImVec4(1.00f, 1.00f, 0.00f, 0.90f);
  colors[ImGuiCol_NavHighlight] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_NavWindowingHighlight] = ImVec4(1.00f, 1.00f, 1.00f, 0.70f);
  colors[ImGuiCol_NavWindowingDimBg] = ImVec4(0.80f, 0.80f, 0.80f, 0.20f);
  colors[ImGuiCol_ModalWindowDimBg] = ImVec4(0.00f, 0.00f, 0.00f, 0.75f);
}

// Initialize ImGui context and backends
static void initializeImGui(GLFWwindow *window) {
  const char *glsl_version = "#version 460";

  IMGUI_CHECKVERSION();
  ImGui::CreateContext();
  ImPlot::CreateContext();
  ImGuiIO &io = ImGui::GetIO();
  io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard; // Enable keyboard navigation
  io.ConfigFlags |= ImGuiConfigFlags_DockingEnable;     // Enable Docking
  // io.ConfigFlags |= ImGuiConfigFlags_ViewportsEnable;   // Disable Multi-Viewport (causes artifacts on Wayland)
  ImGuizmo::SetImGuiContext(ImGui::GetCurrentContext());
  ImGuizmo::SetOrthographic(false);

  setupImGuiStyle();

  ImGui_ImplGlfw_InitForOpenGL(window, true);
  ImGui_ImplOpenGL3_Init(glsl_version);
}

// Render controls help panel
static void renderControlsHelpPanel() {
  ImGui::SetNextWindowPos(ImVec2(10, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 280), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Controls Help", nullptr, ImGuiWindowFlags_NoCollapse)) {
    auto &input = InputManager::instance();

    auto keyLabel = [&](KeyAction action) {
      return input.getKeyName(input.getKeyForAction(action));
    };

    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Keyboard Shortcuts");
    ImGui::Separator();

    ImGui::Text("%s - Quit", keyLabel(KeyAction::Quit).c_str());
    ImGui::Text("%s - Toggle UI", keyLabel(KeyAction::ToggleUI).c_str());
    ImGui::Text("%s - Toggle Fullscreen", keyLabel(KeyAction::ToggleFullscreen).c_str());
    ImGui::Text("%s - Reset Camera", keyLabel(KeyAction::ResetCamera).c_str());
    ImGui::Text("%s - Pause", keyLabel(KeyAction::Pause).c_str());
    ImGui::Text("%s - Reset Settings", keyLabel(KeyAction::ResetSettings).c_str());

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Camera Controls");
    ImGui::Separator();

    ImGui::Text("%s/%s - Pitch Up/Down", keyLabel(KeyAction::CameraMoveForward).c_str(),
                keyLabel(KeyAction::CameraMoveBackward).c_str());
    ImGui::Text("%s/%s - Yaw Left/Right", keyLabel(KeyAction::CameraMoveLeft).c_str(),
                keyLabel(KeyAction::CameraMoveRight).c_str());
    ImGui::Text("%s/%s - Zoom In/Out", keyLabel(KeyAction::CameraMoveUp).c_str(),
                keyLabel(KeyAction::CameraMoveDown).c_str());
    ImGui::Text("%s/%s - Roll Left/Right", keyLabel(KeyAction::CameraRollLeft).c_str(),
                keyLabel(KeyAction::CameraRollRight).c_str());
    ImGui::Text("%s/%s - Zoom In/Out", keyLabel(KeyAction::ZoomIn).c_str(),
                keyLabel(KeyAction::ZoomOut).c_str());

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Mouse Controls");
    ImGui::Separator();

    ImGui::Text("Right-drag - Orbit Camera");
    ImGui::Text("Mid-drag   - Roll Camera");
    ImGui::Text("Scroll     - Zoom");

    ImGui::Spacing();
    ImGui::Separator();

    // Show current camera state
    const auto &cam = input.camera();
    ImGui::Text("Camera: Y%.1f P%.1f R%.1f D%.1f", static_cast<double>(cam.yaw),
                static_cast<double>(cam.pitch), static_cast<double>(cam.roll),
                static_cast<double>(cam.distance));
  }
  ImGui::End();
}

static void renderControlsSettingsPanel(int &cameraModeIndex, float &orbitRadius,
                                        float &orbitSpeed) {
  auto &input = InputManager::instance();

  // Stack on the right side
  ImGui::SetNextWindowPos(ImVec2(1020, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(360, 520), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Controls", nullptr, ImGuiWindowFlags_NoCollapse)) {
    auto gamepadButtonName = [](int button) {
      switch (button) {
      case GLFW_GAMEPAD_BUTTON_A:
        return "A";
      case GLFW_GAMEPAD_BUTTON_B:
        return "B";
      case GLFW_GAMEPAD_BUTTON_X:
        return "X";
      case GLFW_GAMEPAD_BUTTON_Y:
        return "Y";
      case GLFW_GAMEPAD_BUTTON_LEFT_BUMPER:
        return "LB";
      case GLFW_GAMEPAD_BUTTON_RIGHT_BUMPER:
        return "RB";
      case GLFW_GAMEPAD_BUTTON_BACK:
        return "Back";
      case GLFW_GAMEPAD_BUTTON_START:
        return "Start";
      case GLFW_GAMEPAD_BUTTON_GUIDE:
        return "Guide";
      case GLFW_GAMEPAD_BUTTON_LEFT_THUMB:
        return "L3";
      case GLFW_GAMEPAD_BUTTON_RIGHT_THUMB:
        return "R3";
      case GLFW_GAMEPAD_BUTTON_DPAD_UP:
        return "DPad Up";
      case GLFW_GAMEPAD_BUTTON_DPAD_RIGHT:
        return "DPad Right";
      case GLFW_GAMEPAD_BUTTON_DPAD_DOWN:
        return "DPad Down";
      case GLFW_GAMEPAD_BUTTON_DPAD_LEFT:
        return "DPad Left";
      default:
        return "Unknown";
      }
    };
    auto gamepadAxisHint = [](int axis) {
      switch (axis) {
      case GLFW_GAMEPAD_AXIS_LEFT_X:
        return "Left X";
      case GLFW_GAMEPAD_AXIS_LEFT_Y:
        return "Left Y";
      case GLFW_GAMEPAD_AXIS_RIGHT_X:
        return "Right X";
      case GLFW_GAMEPAD_AXIS_RIGHT_Y:
        return "Right Y";
      case GLFW_GAMEPAD_AXIS_LEFT_TRIGGER:
        return "Left Trigger";
      case GLFW_GAMEPAD_AXIS_RIGHT_TRIGGER:
        return "Right Trigger";
      default:
        return "Unknown";
      }
    };
    auto applyControlPreset = [&](float mouseSens, float keySens, float scrollSens,
                                  float timeScale, float padDeadzone, float padLook,
                                  float padRoll, float padZoom, float padTrigger) {
      input.setMouseSensitivity(mouseSens);
      input.setKeyboardSensitivity(keySens);
      input.setScrollSensitivity(scrollSens);
      input.setTimeScale(timeScale);
      input.setGamepadDeadzone(padDeadzone);
      input.setGamepadLookSensitivity(padLook);
      input.setGamepadRollSensitivity(padRoll);
      input.setGamepadZoomSensitivity(padZoom);
      input.setGamepadTriggerZoomSensitivity(padTrigger);
    };
    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Presets");
    ImGui::Separator();

    if (ImGui::Button("Balanced")) {
      Settings defaults;
      applyControlPreset(defaults.mouseSensitivity, defaults.keyboardSensitivity,
                         defaults.scrollSensitivity, defaults.timeScale,
                         defaults.gamepadDeadzone, defaults.gamepadLookSensitivity,
                         defaults.gamepadRollSensitivity, defaults.gamepadZoomSensitivity,
                         defaults.gamepadTriggerZoomSensitivity);
    }
    ImGui::SameLine();
    if (ImGui::Button("Precision")) {
      applyControlPreset(0.6f, 0.6f, 0.7f, 0.75f, 0.10f, 70.0f, 70.0f, 5.0f, 7.0f);
    }
    ImGui::SameLine();
    if (ImGui::Button("Fast")) {
      applyControlPreset(1.4f, 1.4f, 1.2f, 1.25f, 0.20f, 120.0f, 120.0f, 8.0f, 12.0f);
    }

    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Sensitivity");
    ImGui::Separator();

    float mouseSensitivity = input.getMouseSensitivity();
    if (ImGui::SliderFloat("Mouse Sensitivity", &mouseSensitivity, 0.1f, 3.0f)) {
      input.setMouseSensitivity(mouseSensitivity);
    }

    float keyboardSensitivity = input.getKeyboardSensitivity();
    if (ImGui::SliderFloat("Keyboard Sensitivity", &keyboardSensitivity, 0.1f, 3.0f)) {
      input.setKeyboardSensitivity(keyboardSensitivity);
    }

    float scrollSensitivity = input.getScrollSensitivity();
    if (ImGui::SliderFloat("Scroll Sensitivity", &scrollSensitivity, 0.1f, 3.0f)) {
      input.setScrollSensitivity(scrollSensitivity);
    }

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Inversion");
    ImGui::Separator();

    bool invertMouseX = input.isMouseXInverted();
    if (ImGui::Checkbox("Invert Mouse X", &invertMouseX)) {
      input.setMouseXInverted(invertMouseX);
    }
    bool invertMouseY = input.isMouseYInverted();
    if (ImGui::Checkbox("Invert Mouse Y", &invertMouseY)) {
      input.setMouseYInverted(invertMouseY);
    }
    bool invertKeyboardX = input.isKeyboardXInverted();
    if (ImGui::Checkbox("Invert Keyboard X", &invertKeyboardX)) {
      input.setKeyboardXInverted(invertKeyboardX);
    }
    bool invertKeyboardY = input.isKeyboardYInverted();
    if (ImGui::Checkbox("Invert Keyboard Y", &invertKeyboardY)) {
      input.setKeyboardYInverted(invertKeyboardY);
    }

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Camera Control");
    ImGui::Separator();

    const char *cameraModeLabels[] = {"Input", "Front", "Top", "Orbit"};
    ImGui::Combo("Camera Mode", &cameraModeIndex, cameraModeLabels,
                 IM_ARRAYSIZE(cameraModeLabels));

    if (cameraModeIndex == static_cast<int>(CameraMode::Orbit)) {
      ImGui::SliderFloat("Orbit Radius", &orbitRadius, 2.0f, 50.0f);
      ImGui::SliderFloat("Orbit Speed (deg/s)", &orbitSpeed, 0.0f, 30.0f);
    }

    bool holdToToggle = input.isHoldToToggleCamera();
    if (ImGui::Checkbox("Hold-to-Toggle Camera", &holdToToggle)) {
      input.setHoldToToggleCamera(holdToToggle);
    }

    float timeScale = input.getTimeScale();
    if (ImGui::SliderFloat("Time Scale", &timeScale, 0.0f, 4.0f)) {
      input.setTimeScale(timeScale);
    }

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Gamepad");
    ImGui::Separator();

    ImGui::Text("Status: %s", input.isGamepadConnected() ? "Connected" : "Not detected");

    bool gamepadEnabled = input.isGamepadEnabled();
    if (ImGui::Checkbox("Enable Gamepad", &gamepadEnabled)) {
      input.setGamepadEnabled(gamepadEnabled);
    }

    float gamepadDeadzone = input.getGamepadDeadzone();
    if (ImGui::SliderFloat("Deadzone", &gamepadDeadzone, 0.0f, 0.5f)) {
      input.setGamepadDeadzone(gamepadDeadzone);
    }

    float gamepadLookSensitivity = input.getGamepadLookSensitivity();
    if (ImGui::SliderFloat("Look Sensitivity", &gamepadLookSensitivity, 10.0f, 180.0f)) {
      input.setGamepadLookSensitivity(gamepadLookSensitivity);
    }

    float gamepadRollSensitivity = input.getGamepadRollSensitivity();
    if (ImGui::SliderFloat("Roll Sensitivity", &gamepadRollSensitivity, 10.0f, 180.0f)) {
      input.setGamepadRollSensitivity(gamepadRollSensitivity);
    }

    float gamepadZoomSensitivity = input.getGamepadZoomSensitivity();
    if (ImGui::SliderFloat("Zoom Sensitivity", &gamepadZoomSensitivity, 1.0f, 20.0f)) {
      input.setGamepadZoomSensitivity(gamepadZoomSensitivity);
    }

    float gamepadTriggerZoomSensitivity = input.getGamepadTriggerZoomSensitivity();
    if (ImGui::SliderFloat("Trigger Zoom Sensitivity", &gamepadTriggerZoomSensitivity, 1.0f,
                           20.0f)) {
      input.setGamepadTriggerZoomSensitivity(gamepadTriggerZoomSensitivity);
    }

    bool gamepadInvertX = input.isGamepadXInverted();
    if (ImGui::Checkbox("Invert Gamepad X", &gamepadInvertX)) {
      input.setGamepadXInverted(gamepadInvertX);
    }
    bool gamepadInvertY = input.isGamepadYInverted();
    if (ImGui::Checkbox("Invert Gamepad Y", &gamepadInvertY)) {
      input.setGamepadYInverted(gamepadInvertY);
    }
    bool gamepadInvertRoll = input.isGamepadRollInverted();
    if (ImGui::Checkbox("Invert Gamepad Roll", &gamepadInvertRoll)) {
      input.setGamepadRollInverted(gamepadInvertRoll);
    }
    bool gamepadInvertZoom = input.isGamepadZoomInverted();
    if (ImGui::Checkbox("Invert Gamepad Zoom", &gamepadInvertZoom)) {
      input.setGamepadZoomInverted(gamepadInvertZoom);
    }

    if (ImGui::Button("Reset Gamepad Mapping to Defaults")) {
      Settings defaults;
      input.setGamepadYawAxis(defaults.gamepadYawAxis);
      input.setGamepadPitchAxis(defaults.gamepadPitchAxis);
      input.setGamepadRollAxis(defaults.gamepadRollAxis);
      input.setGamepadZoomAxis(defaults.gamepadZoomAxis);
      input.setGamepadZoomInAxis(defaults.gamepadZoomInAxis);
      input.setGamepadZoomOutAxis(defaults.gamepadZoomOutAxis);
      input.setGamepadResetButton(defaults.gamepadResetButton);
      input.setGamepadPauseButton(defaults.gamepadPauseButton);
      input.setGamepadToggleUIButton(defaults.gamepadToggleUIButton);
    }

    if (ImGui::CollapsingHeader("Gamepad Axis Mapping")) {
      int yawAxis = input.getGamepadYawAxis();
      if (ImGui::SliderInt("Yaw Axis", &yawAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadYawAxis(yawAxis);
      }
      ImGui::Text("Yaw uses: %s", gamepadAxisHint(yawAxis));
      int pitchAxis = input.getGamepadPitchAxis();
      if (ImGui::SliderInt("Pitch Axis", &pitchAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadPitchAxis(pitchAxis);
      }
      ImGui::Text("Pitch uses: %s", gamepadAxisHint(pitchAxis));
      int rollAxis = input.getGamepadRollAxis();
      if (ImGui::SliderInt("Roll Axis", &rollAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadRollAxis(rollAxis);
      }
      ImGui::Text("Roll uses: %s", gamepadAxisHint(rollAxis));
      int zoomAxis = input.getGamepadZoomAxis();
      if (ImGui::SliderInt("Zoom Axis", &zoomAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadZoomAxis(zoomAxis);
      }
      ImGui::Text("Zoom uses: %s", gamepadAxisHint(zoomAxis));
      int zoomInAxis = input.getGamepadZoomInAxis();
      if (ImGui::SliderInt("Zoom In Trigger", &zoomInAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadZoomInAxis(zoomInAxis);
      }
      ImGui::Text("Zoom In uses: %s", gamepadAxisHint(zoomInAxis));
      int zoomOutAxis = input.getGamepadZoomOutAxis();
      if (ImGui::SliderInt("Zoom Out Trigger", &zoomOutAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadZoomOutAxis(zoomOutAxis);
      }
      ImGui::Text("Zoom Out uses: %s", gamepadAxisHint(zoomOutAxis));
    }

    if (ImGui::CollapsingHeader("Gamepad Button Mapping")) {
      int resetButton = input.getGamepadResetButton();
      if (ImGui::SliderInt("Reset Camera Button", &resetButton, 0, GLFW_GAMEPAD_BUTTON_LAST)) {
        input.setGamepadResetButton(resetButton);
      }
      ImGui::Text("Reset Camera: %s", gamepadButtonName(resetButton));

      int pauseButton = input.getGamepadPauseButton();
      if (ImGui::SliderInt("Pause Button", &pauseButton, 0, GLFW_GAMEPAD_BUTTON_LAST)) {
        input.setGamepadPauseButton(pauseButton);
      }
      ImGui::Text("Pause: %s", gamepadButtonName(pauseButton));

      int toggleUIButton = input.getGamepadToggleUIButton();
      if (ImGui::SliderInt("Toggle UI Button", &toggleUIButton, 0, GLFW_GAMEPAD_BUTTON_LAST)) {
        input.setGamepadToggleUIButton(toggleUIButton);
      }
      ImGui::Text("Toggle UI: %s", gamepadButtonName(toggleUIButton));
    }

    if (ImGui::CollapsingHeader("Gamepad Deadzone Monitor")) {
      auto axisBar = [&](const char *label, float value, float rawValue, float minValue,
                         float maxValue) {
        float normalized = (value - minValue) / (maxValue - minValue);
        normalized = std::clamp(normalized, 0.0f, 1.0f);
        ImGui::Text("%s: %.2f (raw %.2f)", label, static_cast<double>(value),
                    static_cast<double>(rawValue));
        ImGui::ProgressBar(normalized, ImVec2(0.0f, 0.0f));
      };

      int yawAxis = input.getGamepadYawAxis();
      int pitchAxis = input.getGamepadPitchAxis();
      int rollAxis = input.getGamepadRollAxis();
      int zoomAxis = input.getGamepadZoomAxis();
      int zoomInAxis = input.getGamepadZoomInAxis();
      int zoomOutAxis = input.getGamepadZoomOutAxis();

      std::string yawLabel = std::string("Yaw (") + gamepadAxisHint(yawAxis) + ")";
      std::string pitchLabel = std::string("Pitch (") + gamepadAxisHint(pitchAxis) + ")";
      std::string rollLabel = std::string("Roll (") + gamepadAxisHint(rollAxis) + ")";
      std::string zoomLabel = std::string("Zoom (") + gamepadAxisHint(zoomAxis) + ")";
      std::string zoomInLabel = std::string("Zoom In (") + gamepadAxisHint(zoomInAxis) + ")";
      std::string zoomOutLabel = std::string("Zoom Out (") + gamepadAxisHint(zoomOutAxis) + ")";

      axisBar(yawLabel.c_str(), input.getGamepadAxisFiltered(yawAxis),
              input.getGamepadAxisRaw(yawAxis), -1.0f, 1.0f);
      axisBar(pitchLabel.c_str(), input.getGamepadAxisFiltered(pitchAxis),
              input.getGamepadAxisRaw(pitchAxis), -1.0f, 1.0f);
      axisBar(rollLabel.c_str(), input.getGamepadAxisFiltered(rollAxis),
              input.getGamepadAxisRaw(rollAxis), -1.0f, 1.0f);
      axisBar(zoomLabel.c_str(), input.getGamepadAxisFiltered(zoomAxis),
              input.getGamepadAxisRaw(zoomAxis), -1.0f, 1.0f);
      axisBar(zoomInLabel.c_str(), input.getGamepadAxisRaw(zoomInAxis),
              input.getGamepadAxisRaw(zoomInAxis), 0.0f, 1.0f);
      axisBar(zoomOutLabel.c_str(), input.getGamepadAxisRaw(zoomOutAxis),
              input.getGamepadAxisRaw(zoomOutAxis), 0.0f, 1.0f);
    }

    if (ImGui::CollapsingHeader("Key Bindings", ImGuiTreeNodeFlags_DefaultOpen)) {
      if (input.isRemappingKey()) {
        ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.0f, 1.0f),
                           "Press a key to bind to: %s",
                           input.getActionName(input.getRemappingAction()));
        if (ImGui::Button("Cancel")) {
          input.cancelKeyRemapping();
        }
      } else {
        if (ImGui::BeginTable("KeyBindings", 2, ImGuiTableFlags_SizingStretchProp)) {
          for (int i = 0; i < static_cast<int>(KeyAction::COUNT); i++) {
            KeyAction action = static_cast<KeyAction>(i);
            const char *actionName = input.getActionName(action);
            int currentKey = input.getKeyForAction(action);
            std::string keyName = input.getKeyName(currentKey);

            ImGui::TableNextRow();
            ImGui::TableNextColumn();
            ImGui::Text("%s", actionName);
            ImGui::TableNextColumn();

            ImGui::PushID(i);
            char buttonLabel[64];
            std::snprintf(buttonLabel, sizeof(buttonLabel), "[%s]##%d", keyName.c_str(), i);
            if (ImGui::Button(buttonLabel)) {
              input.startKeyRemapping(action);
            }
            ImGui::PopID();
          }
          ImGui::EndTable();
        }
      }
    }

    ImGui::Spacing();
    if (ImGui::Button("Save Settings")) {
      input.syncToSettings();
      auto &settings = SettingsManager::instance().get();
      settings.cameraMode = cameraModeIndex;
      settings.orbitRadius = orbitRadius;
      settings.orbitSpeed = orbitSpeed;
      SettingsManager::instance().save();
    }
    ImGui::SameLine();
    if (ImGui::Button("Reset Defaults")) {
      SettingsManager::instance().resetToDefaults();
      input.syncFromSettings();
      auto &settings = SettingsManager::instance().get();
      cameraModeIndex = settings.cameraMode;
      orbitRadius = settings.orbitRadius;
      orbitSpeed = settings.orbitSpeed;
      SettingsManager::instance().save();
    }
  }
  ImGui::End();
}

static void renderGizmoPanel(bool &gizmoEnabled, ImGuizmo::OPERATION &operation,
                             ImGuizmo::MODE &mode, glm::mat4 &gizmoTransform) {
  ImGui::SetNextWindowPos(ImVec2(1020, 220), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 220), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Gizmo", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable Gizmo Target", &gizmoEnabled);

    const char *operationLabels[] = {"Translate", "Rotate", "Scale"};
    int operationIndex = 0;
    switch (operation) {
    case ImGuizmo::TRANSLATE:
      operationIndex = 0;
      break;
    case ImGuizmo::ROTATE:
      operationIndex = 1;
      break;
    case ImGuizmo::SCALE:
      operationIndex = 2;
      break;
    default:
      operationIndex = 0;
      break;
    }

    if (ImGui::Combo("Operation", &operationIndex, operationLabels,
                     IM_ARRAYSIZE(operationLabels))) {
      operation = (operationIndex == 0)   ? ImGuizmo::TRANSLATE
                  : (operationIndex == 1) ? ImGuizmo::ROTATE
                                          : ImGuizmo::SCALE;
    }

    const char *modeLabels[] = {"World", "Local"};
    int modeIndex = (mode == ImGuizmo::WORLD) ? 0 : 1;
    if (ImGui::Combo("Mode", &modeIndex, modeLabels, IM_ARRAYSIZE(modeLabels))) {
      mode = (modeIndex == 0) ? ImGuizmo::WORLD : ImGuizmo::LOCAL;
    }

    if (ImGui::Button("Reset Target")) {
      gizmoTransform = glm::mat4(1.0f);
    }

    glm::vec3 target = glm::vec3(gizmoTransform[3]);
    ImGui::Text("Target: %.2f %.2f %.2f", static_cast<double>(target.x),
                static_cast<double>(target.y), static_cast<double>(target.z));
  }
  ImGui::End();
}

static void renderDisplaySettingsPanel(GLFWwindow *window, int &swapInterval, float &renderScale,
                                       int windowWidth, int windowHeight) {
  auto &input = InputManager::instance();
  auto &settings = SettingsManager::instance().get();

  // Stack below Controls
  ImGui::SetNextWindowPos(ImVec2(1020, 540), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(360, 220), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Display", nullptr, ImGuiWindowFlags_NoCollapse)) {
    bool fullscreen = input.isFullscreen();
    if (ImGui::Checkbox("Fullscreen", &fullscreen)) {
      input.toggleFullscreen();
      settings.fullscreen = fullscreen;
      if (!fullscreen) {
        glfwGetWindowSize(window, &settings.windowWidth, &settings.windowHeight);
      }
    }

    const char *swapModes[] = {"Off (0)", "VSync (1)", "Triple (2)"};
    int interval = std::clamp(swapInterval, 0, 2);
    if (ImGui::Combo("Swap Interval", &interval, swapModes, IM_ARRAYSIZE(swapModes))) {
      swapInterval = interval;
      settings.swapInterval = swapInterval;
      glfwSwapInterval(swapInterval);
    }

    if (ImGui::SliderFloat("Render Scale", &renderScale, 0.25f, 1.5f)) {
      settings.renderScale = renderScale;
    }

    const char *presets[] = {"Native", "720p", "1080p", "1440p", "4K", "UW 3440x1440",
                             "UW 5120x2160"};
    static int presetIndex = 0;
    if (ImGui::Combo("Resolution Preset", &presetIndex, presets, IM_ARRAYSIZE(presets))) {
      float targetHeight = 0.0f;
      float targetWidth = 0.0f;
      bool useWidth = false;
      switch (presetIndex) {
      case 0:
        targetHeight = 0.0f;
        break;
      case 1:
        targetHeight = 720.0f;
        break;
      case 2:
        targetHeight = 1080.0f;
        break;
      case 3:
        targetHeight = 1440.0f;
        break;
      case 4:
        targetHeight = 2160.0f;
        break;
      case 5:
        targetWidth = 3440.0f;
        useWidth = true;
        break;
      case 6:
        targetWidth = 5120.0f;
        useWidth = true;
        break;
      default:
        targetHeight = 0.0f;
        break;
      }

      float newScale = 1.0f;
      if (presetIndex != 0 && windowWidth > 0 && windowHeight > 0) {
        if (useWidth) {
          newScale = targetWidth / static_cast<float>(windowWidth);
        } else {
          newScale = targetHeight / static_cast<float>(windowHeight);
        }
      }
      renderScale = newScale;
      settings.renderScale = renderScale;
    }

    float clampedScale = std::clamp(renderScale, 0.25f, 1.5f);
    int targetWidth =
        std::max(1, static_cast<int>(static_cast<float>(windowWidth) * clampedScale));
    int targetHeight =
        std::max(1, static_cast<int>(static_cast<float>(windowHeight) * clampedScale));
    ImGui::Text("Window: %dx%d", windowWidth, windowHeight);
    ImGui::Text("Render: %dx%d", targetWidth, targetHeight);
  }
  ImGui::End();
}

static void renderBackgroundPanel(const std::vector<BackgroundAsset> &assets,
                                  int &backgroundIndex,
                                  float &parallaxStrength,
                                  float &driftStrength,
                                  std::array<float, kBackgroundLayers> &layerDepth,
                                  std::array<float, kBackgroundLayers> &layerScale,
                                  std::array<float, kBackgroundLayers> &layerIntensity,
                                  std::array<float, kBackgroundLayers> &layerLodBias) {
  auto &settings = SettingsManager::instance().get();

  // Stack on the left side
  ImGui::SetNextWindowPos(ImVec2(10, 300), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 260), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Background", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable Background", &settings.backgroundEnabled);
    ImGui::SliderFloat("Intensity", &settings.backgroundIntensity, 0.0f, 2.0f);

    if (assets.empty()) {
      ImGui::TextDisabled("No manifest assets loaded.");
    } else {
      backgroundIndex = std::clamp(backgroundIndex, 0, static_cast<int>(assets.size() - 1));
      const char *preview = assets[static_cast<std::size_t>(backgroundIndex)].title.c_str();
      if (ImGui::BeginCombo("Background Asset", preview)) {
        for (int i = 0; i < static_cast<int>(assets.size()); ++i) {
          bool selected = (i == backgroundIndex);
          if (ImGui::Selectable(assets[static_cast<std::size_t>(i)].title.c_str(),
                                selected)) {
            backgroundIndex = i;
            settings.backgroundId = assets[static_cast<std::size_t>(i)].id;
          }
          if (selected) {
            ImGui::SetItemDefaultFocus();
          }
        }
        ImGui::EndCombo();
      }
    }

    ImGui::Separator();
    ImGui::SliderFloat("Parallax Strength", &parallaxStrength, 0.0f, 0.01f, "%.6f");
    ImGui::SliderFloat("Drift Strength", &driftStrength, 0.0f, 0.05f, "%.4f");

    if (ImGui::TreeNode("Layers")) {
      for (int i = 0; i < kBackgroundLayers; ++i) {
        ImGui::PushID(i);
        ImGui::SliderFloat("Depth", &layerDepth[static_cast<std::size_t>(i)], 0.0f, 2.0f);
        ImGui::SliderFloat("Scale", &layerScale[static_cast<std::size_t>(i)], 0.5f, 2.0f);
        ImGui::SliderFloat("Weight", &layerIntensity[static_cast<std::size_t>(i)], 0.0f, 2.0f);
        ImGui::SliderFloat("LOD Bias", &layerLodBias[static_cast<std::size_t>(i)], 0.0f, 6.0f,
                           "%.2f");
        ImGui::Separator();
        ImGui::PopID();
      }
      ImGui::TreePop();
    }
  }
  ImGui::End();
}

static void renderWiregridPanel(bool &wiregridEnabled, WiregridParams &params,
                                glm::vec4 &color) {
  // Stack below Background
  ImGui::SetNextWindowPos(ImVec2(10, 570), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 220), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Wiregrid", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable Wiregrid", &wiregridEnabled);
    ImGui::SliderInt("Rings", &params.ringCount, 4, 64);
    ImGui::SliderInt("Ring Segments", &params.ringSegments, 16, 256);
    ImGui::SliderInt("Spokes", &params.spokeCount, 4, 64);
    ImGui::SliderFloat("Radius Min", &params.radiusMin, 0.5f, 10.0f);
    ImGui::SliderFloat("Radius Max", &params.radiusMax, 10.0f, 200.0f);
    ImGui::Separator();
    ImGui::Checkbox("Show Curvature", &params.showCurvature);
    if (params.showCurvature) {
      ImGui::SliderFloat("Curvature Scale", &params.curvatureScale, 0.0f, 10.0f);
    }
    ImGui::ColorEdit4("Color", reinterpret_cast<float *>(&color));
  }
  ImGui::End();
}

static void renderRmlUiPanel(bool &rmluiEnabled) {
  ImGui::SetNextWindowPos(ImVec2(1020, 450), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 140), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("RmlUi", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable RmlUi overlay", &rmluiEnabled);
    ImGui::TextDisabled("Experimental: placeholder only");
  }
  ImGui::End();
}

// Cleanup resources
static void cleanup(GLFWwindow *window) {
  // Sync and save settings before shutdown
  InputManager::instance().syncToSettings();
  SettingsManager::instance().save();

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
  ShaderWatcher::instance().stop();
#endif
  InputManager::instance().shutdown();
  ImGui_ImplOpenGL3_Shutdown();
  ImGui_ImplGlfw_Shutdown();
  ImPlot::DestroyContext();
  ImGui::DestroyContext();
  glfwDestroyWindow(window);
  glfwTerminate();
}

class PostProcessPass {
private:
  GLuint program;

public:
  explicit PostProcessPass(const std::string &fragShader) {
    this->program = createShaderProgram(std::string("shader/simple.vert"), fragShader);

    glUseProgram(this->program);
    glUniform1i(glGetUniformLocation(program, "texture0"), 0);
    glUseProgram(0);
  }

  void render(GLuint inputColorTexture, int width, int height, GLuint destFramebuffer = 0) {
    static GLuint quadVao = 0;
    if (quadVao == 0) {
      quadVao = createQuadVAO();
    }

    glBindFramebuffer(GL_FRAMEBUFFER, destFramebuffer);

    glDisable(GL_DEPTH_TEST);

    glClearColor(1.0f, 0.0f, 0.0f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT);

    glUseProgram(this->program);
    glBindVertexArray(quadVao);

    glUniform2f(glGetUniformLocation(this->program, "resolution"), static_cast<float>(width),
                static_cast<float>(height));

    glUniform1f(glGetUniformLocation(this->program, "time"), static_cast<float>(glfwGetTime()));

    glActiveTexture(GL_TEXTURE0);
    glBindTexture(GL_TEXTURE_2D, inputColorTexture);

    glDrawArrays(GL_TRIANGLES, 0, 6);

    glUseProgram(0);
  }
};

struct GpuTimer {
  GLuint queries[2] = {0, 0};
  bool issued[2] = {false, false};
  int index = 0;
  double lastMs = 0.0;
  bool active = false;

  bool ensureQueries() {
    if (queries[0] != 0 && queries[1] != 0) {
      return true;
    }
    if (queries[0] != 0 || queries[1] != 0) {
      glDeleteQueries(2, queries);
    }
    glGenQueries(2, queries);
    issued[0] = false;
    issued[1] = false;
    active = false;
    return (queries[0] != 0 && queries[1] != 0);
  }

  bool init() {
    glGenQueries(2, queries);
    if (queries[0] == 0 || queries[1] == 0) {
      queries[0] = 0;
      queries[1] = 0;
      issued[0] = false;
      issued[1] = false;
      active = false;
      return false;
    }
    issued[0] = false;
    issued[1] = false;
    return true;
  }
  void shutdown() {
    if (queries[0] != 0 || queries[1] != 0) {
      glDeleteQueries(2, queries);
    }
    queries[0] = 0;
    queries[1] = 0;
    issued[0] = false;
    issued[1] = false;
    active = false;
  }
  void begin() {
    if (active) {
      return;
    }
    if (!ensureQueries()) {
      return;
    }
    glBeginQuery(GL_TIME_ELAPSED, queries[index]);
    issued[index] = true;
    active = true;
  }
  void end() {
    if (!active) {
      return;
    }
    glEndQuery(GL_TIME_ELAPSED);
    active = false;
  }
  void resolve() {
    if (!ensureQueries()) {
      return;
    }
    int prev = 1 - index;
    if (queries[prev] == 0 || !issued[prev]) {
      return;
    }
    GLuint available = 0;
    glGetQueryObjectuiv(queries[prev], GL_QUERY_RESULT_AVAILABLE, &available);
    if (available != 0u) {
      GLuint64 timeNs = 0;
      glGetQueryObjectui64v(queries[prev], GL_QUERY_RESULT, &timeNs);
      lastMs = static_cast<double>(timeNs) / 1.0e6;
      issued[prev] = false;
    }
  }
  void swap() {
    index = 1 - index;
    active = false;
  }
};

struct GpuTimerSet {
  bool initialized = false;
  GpuTimer blackholeFragment;
  GpuTimer blackholeCompute;
  GpuTimer bloom;
  GpuTimer tonemap;
  GpuTimer depth;
  GpuTimer grmhdSlice;

  void init() {
    bool ok = true;
    ok &= blackholeFragment.init();
    ok &= blackholeCompute.init();
    ok &= bloom.init();
    ok &= tonemap.init();
    ok &= depth.init();
    ok &= grmhdSlice.init();
    initialized = ok;
    if (!ok) {
      shutdown();
    }
  }

  void shutdown() {
    blackholeFragment.shutdown();
    blackholeCompute.shutdown();
    bloom.shutdown();
    tonemap.shutdown();
    depth.shutdown();
    grmhdSlice.shutdown();
    initialized = false;
  }

  void resolve() {
    blackholeFragment.resolve();
    blackholeCompute.resolve();
    bloom.resolve();
    tonemap.resolve();
    depth.resolve();
    grmhdSlice.resolve();
  }

  void swap() {
    blackholeFragment.swap();
    blackholeCompute.swap();
    bloom.swap();
    tonemap.swap();
    depth.swap();
    grmhdSlice.swap();
  }
};

struct TimingHistory {
  static constexpr int kCapacity = 240;
  std::array<float, kCapacity> cpuMs{};
  std::array<float, kCapacity> gpuFragmentMs{};
  std::array<float, kCapacity> gpuComputeMs{};
  std::array<float, kCapacity> gpuBloomMs{};
  std::array<float, kCapacity> gpuTonemapMs{};
  std::array<float, kCapacity> gpuDepthMs{};
  std::array<float, kCapacity> gpuGrmhdSliceMs{};
  int offset = 0;
  int count = 0;

  void push(float cpuMsSample, const GpuTimerSet &timers) {
    const std::size_t index = static_cast<std::size_t>(offset);
    cpuMs[index] = cpuMsSample;
    if (timers.initialized) {
      gpuFragmentMs[index] = static_cast<float>(timers.blackholeFragment.lastMs);
      gpuComputeMs[index] = static_cast<float>(timers.blackholeCompute.lastMs);
      gpuBloomMs[index] = static_cast<float>(timers.bloom.lastMs);
      gpuTonemapMs[index] = static_cast<float>(timers.tonemap.lastMs);
      gpuDepthMs[index] = static_cast<float>(timers.depth.lastMs);
      gpuGrmhdSliceMs[index] = static_cast<float>(timers.grmhdSlice.lastMs);
    } else {
      const float nan = std::numeric_limits<float>::quiet_NaN();
      gpuFragmentMs[index] = nan;
      gpuComputeMs[index] = nan;
      gpuBloomMs[index] = nan;
      gpuTonemapMs[index] = nan;
      gpuDepthMs[index] = nan;
      gpuGrmhdSliceMs[index] = nan;
    }
    offset = (offset + 1) % kCapacity;
    if (count < kCapacity) {
      ++count;
    }
  }
};

static std::string gpuTimingPath() {
  std::filesystem::create_directories("logs/perf");
  return "logs/perf/gpu_timing.csv";
}

static void appendGpuTimingSample(const std::string &path, int index, int width, int height,
                                  float cpuFrameMs, const GpuTimerSet &timers,
                                  bool computeActive, float kerrSpin, double timeSec) {
  const bool exists = std::filesystem::exists(path);
  std::ofstream out(path, std::ios::app);
  if (!out) {
    return;
  }
  if (!exists) {
    out << "index,time_sec,width,height,cpu_ms,gpu_fragment_ms,gpu_compute_ms,gpu_bloom_ms,"
           "gpu_tonemap_ms,gpu_depth_ms,gpu_grmhd_slice_ms,compute_active,kerr_spin\n";
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << timeSec << "," << width << "," << height << "," << cpuFrameMs << ","
      << timers.blackholeFragment.lastMs << "," << timers.blackholeCompute.lastMs << ","
      << timers.bloom.lastMs << "," << timers.tonemap.lastMs << "," << timers.depth.lastMs << ","
      << timers.grmhdSlice.lastMs << "," << (computeActive ? 1 : 0) << "," << kerrSpin << "\n";
}

static void writeTimingHistoryCsv(const TimingHistory &history, const std::string &path) {
  std::filesystem::create_directories("logs/perf");
  std::ofstream out(path);
  if (!out) {
    return;
  }
  out << "index,cpu_ms,gpu_fragment_ms,gpu_compute_ms,gpu_bloom_ms,gpu_tonemap_ms,gpu_depth_ms,"
         "gpu_grmhd_slice_ms\n";
  out << std::fixed << std::setprecision(6);

  int count = history.count;
  int start = history.offset - count;
  if (start < 0) {
    start += TimingHistory::kCapacity;
  }
  for (int i = 0; i < count; ++i) {
    int rawIndex = (start + i) % TimingHistory::kCapacity;
    std::size_t idx = static_cast<std::size_t>(rawIndex);
    out << i << "," << history.cpuMs[idx] << "," << history.gpuFragmentMs[idx] << ","
        << history.gpuComputeMs[idx] << "," << history.gpuBloomMs[idx] << ","
        << history.gpuTonemapMs[idx] << "," << history.gpuDepthMs[idx] << ","
        << history.gpuGrmhdSliceMs[idx] << "\n";
  }
}

static void renderPerformancePanel(bool &gpuTimingEnabled, const GpuTimerSet &timers,
                                   const TimingHistory &history, float cpuFrameMs,
                                   bool &perfOverlayEnabled, float &perfOverlayScale,
                                   bool &depthPrepassEnabled) {
  // Stack below Wiregrid
  ImGui::SetNextWindowPos(ImVec2(10, 800), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 200), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Performance", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("GPU Timing", &gpuTimingEnabled);
    ImGui::Checkbox("HUD Overlay", &perfOverlayEnabled);
    ImGui::SliderFloat("HUD Scale", &perfOverlayScale, 0.5f, 2.0f);

    // Depth pre-pass (for future mesh-based disk rendering)
    ImGui::BeginDisabled(true); // Disabled until mesh geometry exists
    ImGui::Checkbox("Depth Pre-pass", &depthPrepassEnabled);
    ImGui::EndDisabled();
    if (ImGui::IsItemHovered(ImGuiHoveredFlags_AllowWhenDisabled)) {
      ImGui::SetTooltip("Reduces overdraw for mesh geometry.\nCurrently unused (ray marching has zero overdraw).");
    }
    double cpuFrameMsD = static_cast<double>(cpuFrameMs);
    double fps = cpuFrameMs > 0.0f ? 1000.0 / cpuFrameMsD : 0.0;
    ImGui::Text("CPU frame: %.2f ms (%.1f FPS)", cpuFrameMsD, fps);

    if (timers.initialized) {
      ImGui::Separator();
      ImGui::Text("GPU Fragment:  %.2f ms", timers.blackholeFragment.lastMs);
      ImGui::Text("GPU Compute:   %.2f ms", timers.blackholeCompute.lastMs);
      ImGui::Text("GPU Bloom:     %.2f ms", timers.bloom.lastMs);
      ImGui::Text("GPU Tonemap:   %.2f ms", timers.tonemap.lastMs);
      ImGui::Text("GPU Depth:     %.2f ms", timers.depth.lastMs);
      ImGui::Text("GPU GRMHD:     %.2f ms", timers.grmhdSlice.lastMs);
    } else {
      ImGui::TextDisabled("GPU timings inactive");
    }

    if (history.count > 0 && ImPlot::BeginPlot("Frame Times (ms)", ImVec2(-1, 140))) {
      ImPlot::SetupAxes(nullptr, "ms", ImPlotAxisFlags_NoTickLabels, ImPlotAxisFlags_AutoFit);
      ImPlot::PlotLine("CPU", history.cpuMs.data(), history.count, 1.0, 0.0,
                       ImPlotLineFlags_None, history.offset);
      ImPlot::PlotLine("GPU Frag", history.gpuFragmentMs.data(), history.count, 1.0, 0.0,
                       ImPlotLineFlags_SkipNaN, history.offset);
      ImPlot::PlotLine("GPU Comp", history.gpuComputeMs.data(), history.count, 1.0, 0.0,
                       ImPlotLineFlags_SkipNaN, history.offset);
      ImPlot::PlotLine("GPU Depth", history.gpuDepthMs.data(), history.count, 1.0, 0.0,
                       ImPlotLineFlags_SkipNaN, history.offset);
      ImPlot::PlotLine("GPU GRMHD", history.gpuGrmhdSliceMs.data(), history.count, 1.0, 0.0,
                       ImPlotLineFlags_SkipNaN, history.offset);
      ImPlot::EndPlot();
    }

    if (ImGui::Button("Dump Frame CSV")) {
      writeTimingHistoryCsv(history, "logs/perf/frame_times.csv");
    }
    ImGui::SameLine();
    ImGui::TextDisabled("logs/perf/frame_times.csv");
  }
  ImGui::End();
}

static void resetLayout(ImGuiID dockspaceId) {
    ImGui::DockBuilderRemoveNode(dockspaceId);
    ImGui::DockBuilderAddNode(dockspaceId, ImGuiDockNodeFlags_DockSpace);
    ImGui::DockBuilderSetNodeSize(dockspaceId, ImGui::GetMainViewport()->Size);

    ImGuiID dockMainId = dockspaceId;
    ImGuiID dockLeftId = ImGui::DockBuilderSplitNode(dockMainId, ImGuiDir_Left, 0.30f, nullptr, &dockMainId);
    ImGuiID dockLeftDownId = ImGui::DockBuilderSplitNode(dockLeftId, ImGuiDir_Down, 0.50f, nullptr, &dockLeftId);

    // Dock Windows
    ImGui::DockBuilderDockWindow("Viewport", dockMainId);
    
    // Left Upper: Main Settings
    ImGui::DockBuilderDockWindow("Settings", dockLeftId);
    ImGui::DockBuilderDockWindow("Display", dockLeftId);
    ImGui::DockBuilderDockWindow("Background", dockLeftId);

    // Left Lower: Controls, Performance, Tools
    ImGui::DockBuilderDockWindow("Controls", dockLeftDownId);
    ImGui::DockBuilderDockWindow("Performance", dockLeftDownId);
    ImGui::DockBuilderDockWindow("Wiregrid", dockLeftDownId);
    ImGui::DockBuilderDockWindow("Depth Effects", dockLeftDownId);
    ImGui::DockBuilderDockWindow("Gizmo", dockLeftDownId);
    ImGui::DockBuilderDockWindow("Controls Help", dockLeftDownId);
    ImGui::DockBuilderDockWindow("RmlUi", dockLeftDownId);

    ImGui::DockBuilderFinish(dockspaceId);
}

int main(int argc, char **argv) {
  installCrashHandlers();
  try {
    std::string curveTsvPath;
    for (int i = 1; i < argc; ++i) {
      std::string arg = argv[i];
      if (arg == "--help" || arg == "-h") {
        printUsage(argv[0]);
        return 0;
      }
      if (arg == "--curve-tsv" && i + 1 < argc) {
        curveTsvPath = argv[++i];
        continue;
      }
      std::printf("Unknown argument: %s\n", arg.c_str());
      printUsage(argv[0]);
      return 2;
    }

    // Load settings first
    SettingsManager::instance().load();
    auto &settings = SettingsManager::instance().get();

  // Initialize window and OpenGL context
  GLFWwindow *window = initializeWindow(settings.windowWidth, settings.windowHeight);
  if (window == nullptr) {
    return 1;
  }

  glfwSwapInterval(settings.swapInterval);

  // Initialize shader manager (must be after OpenGL context)
  ShaderManager::instance().init();

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
  // Initialize shader hot-reload watcher
  ShaderWatcher::instance().start(getShaderBaseDir());
#endif

  // Initialize input manager and sync with settings
  InputManager::instance().init(window);
  InputManager::instance().syncFromSettings();
  if (settings.fullscreen) {
    InputManager::instance().toggleFullscreen();
  }

  // Initialize ImGui
  initializeImGui(window);

  // Curve overlay for plotting (e.g., critical curves)
  static OverlayCurve2D curveOverlay;
  static bool curveOverlayLoaded = false;

  if (!curveTsvPath.empty()) {
    curveOverlayLoaded = curveOverlay.LoadFromTsv(curveTsvPath);
    if (!curveOverlayLoaded) {
      std::fprintf(stderr, "curve overlay load failed: %s\n",
                   curveOverlay.lastError.c_str());
    }
  }

  // Create fullscreen quad for rendering
  GLuint quadVAO = createQuadVAO();
  glBindVertexArray(quadVAO);

  // Main loop
  PostProcessPass passthrough("shader/passthrough.frag");

  double lastTime = glfwGetTime();

  static constexpr int kMaxBloomIterations = 8;
  static float depthFar = 100.0f;
  static int cameraModeIndex = static_cast<int>(CameraMode::Input);
  static float orbitTime = 0.0f;
  static float orbitRadius = 15.0f;
  static float orbitSpeed = 6.0f;
  static bool gizmoEnabled = false;
  static ImGuizmo::OPERATION gizmoOperation = ImGuizmo::TRANSLATE;
  static ImGuizmo::MODE gizmoMode = ImGuizmo::WORLD;
  static glm::mat4 gizmoTransform(1.0f);
  static bool cameraSettingsLoaded = false;
  static bool displaySettingsLoaded = false;
  static int swapInterval = 1;
  static float renderScale = 1.0f;
  static bool bloomSettingsLoaded = false;
  static int bloomIterations = kMaxBloomIterations;
  static bool postProcessingSettingsLoaded = false;
  static float bloomStrength = 0.1f;
  static bool tonemappingEnabled = true;
  static float gamma = 2.5f;
  static bool gravitationalLensing = true;
  static bool renderBlackHole = true;
  static bool adiskEnabled = true;
  static bool adiskParticle = true;
  static float adiskDensityV = 2.0f;
  static float adiskDensityH = 4.0f;
  static float adiskHeight = 0.55f;
  static float adiskLit = 0.25f;
  static float adiskNoiseLOD = 5.0f;
  static float adiskNoiseScale = 0.8f;
  static bool useNoiseTexture = true;
  static float noiseTextureScale = 0.25f;
  [[maybe_unused]] static int noiseTextureSize = 32;
  static float adiskSpeed = 0.5f;
  static float dopplerStrength = 1.0f;
  static bool useGrmhd = false;
  static bool grmhdLoaded = false;
  static GrmhdPackedTexture grmhdTexture;
  static std::string grmhdLoadError;
  static std::array<char, 256> grmhdPathBuffer{};
  static bool grmhdPathInit = false;
  static glm::vec3 grmhdBoundsMin(-10.0f, -2.0f, -10.0f);
  static glm::vec3 grmhdBoundsMax(10.0f, 2.0f, 10.0f);
  static bool grmhdSliceEnabled = false;
  static int grmhdSliceAxis = 2;
  static int grmhdSliceChannel = 0;
  static float grmhdSliceCoord = 0.5f;
  static bool grmhdSliceUseColorMap = true;
  static bool grmhdSliceAutoRange = true;
  static float grmhdSliceMin = 0.0f;
  static float grmhdSliceMax = 1.0f;
  static int grmhdSliceSize = 256;
  static int grmhdSliceSizeCached = 0;

  // GRMHD Time-Series Playback (Phase 4.3 - streaming infrastructure)
  static bool grmhdTimeSeriesEnabled = false;
  static std::array<char, 256> grmhdTimeSeriesJsonBuffer{};
  static std::array<char, 256> grmhdTimeSeriesBinBuffer{};
  static bool grmhdTimeSeriesLoaded = false;
  static int grmhdCurrentFrame = 0;
  static int grmhdMaxFrame = 0;
  static bool grmhdPlaying = false;
  static float grmhdPlaybackSpeed = 1.0f;
  static double grmhdCacheHitRate = 0.0;
  static int grmhdQueueDepth = 0;
  // Note: GRMHDStreamer instance will be added when implementation is complete

  static float blackHoleMass = 1.0f;
  static float kerrSpin = 0.0f;
  static bool enablePhotonSphere = false;
  static bool enableRedshift = false;
  static bool hawkingGlowEnabled = false;
  static float hawkingTempScale = 1.0f;
  static float hawkingGlowIntensity = 1.0f;
  static bool hawkingUseLUTs = true;
  static int hawkingPreset = 0; // 0=Physical, 1=Primordial, 2=Extreme
  static physics::HawkingRenderer hawkingRenderer;
  static bool hawkingLutsLoaded = false;
  static bool useComputeRaytracer = false;
  static bool compareComputeFragment = false;
  static int compareSampleSize = 16;
  static int compareFrameStride = 1;
  static DiffStats compareStats;
  static DiffStats compareFullStats;
  static bool compareWriteOutputs = false;
  static bool compareWriteDiff = true;
  static bool compareWriteSummary = true;
  static float compareDiffScale = 8.0f;
  static float compareThreshold = 0.02f;
  static int compareMaxOutliers = 10000;       // Enable outlier gating by default
  static float compareMaxOutlierFrac = 0.006f; // 0.6% tolerance for Kerr divergence
  static bool compareOverridesEnabled = false;
  static int compareMaxStepsOverride = 0;
  static float compareStepSizeOverride = 0.0f;
  static bool compareBaselineEnabled = false;
  static int integratorDebugFlags = 0;
  static bool integratorDebugConfigInit = false;
  static int compareFailureCount = 0;
  static bool compareLastExceeded = false;
  static int compareLastOutliers = 0;
  static int compareLastOutlierLimit = 0;
  static int compareSnapshotIndex = 0;
  static bool compareAutoCapture = false;
  static int compareAutoCount = static_cast<int>(kComparePresets.size());
  static int compareAutoStride = 30;
  static int compareAutoRemaining = 0;
  static int compareAutoStrideCounter = 0;
  static bool comparePresetSweep = false;
  static bool comparePresetSaved = false;
  static bool compareRestorePending = false;
  static int comparePresetIndex = 0;
  static int comparePresetFrameCounter = 0;
  static int comparePresetSettleFrames = 2;
  static CameraState comparePresetSavedCamera{};
  static int comparePresetSavedMode = 0;
  static float comparePresetSavedOrbitRadius = 0.0f;
  static float comparePresetSavedOrbitSpeed = 0.0f;
  static float comparePresetSavedOrbitTime = 0.0f;
  static float comparePresetSavedKerrSpin = 0.0f;
  static bool captureCompareSnapshot = false;
  static int compareFrameCounter = 0;
  static bool compareAutoInit = false;
  static bool drawIdProbeEnabled = false;
  static bool drawIdProbeConfigInit = false;
  static bool drawIdProbeSupported = false;
  static bool multiDrawMainEnabled = false;
  static bool multiDrawMainConfigInit = false;
  static bool multiDrawIndirectCount = false;
  static bool multiDrawSupported = false;
  static bool multiDrawCountSupported = false;
  [[maybe_unused]] static bool multiDrawOverlayEnabled = true;
  [[maybe_unused]] static int multiDrawInstanceCount = 2;
  [[maybe_unused]] static GLuint multiDrawProgram = 0;
  [[maybe_unused]] static GLuint multiDrawInstanceBuffer = 0;
  [[maybe_unused]] static GLuint multiDrawCommandBuffer = 0;
  [[maybe_unused]] static GLuint multiDrawCountBuffer = 0;
  [[maybe_unused]] static GLuint multiDrawComputeProgram = 0;
  static bool gpuTimingEnabled = false;
  static bool gpuTimingLogInit = false;
  static bool gpuTimingLogEnabled = false;
  static int gpuTimingLogStride = 60;
  static int gpuTimingLogCounter = 0;
  static int gpuTimingLogIndex = 0;
  static GpuTimerSet gpuTimers;
  static TimingHistory timingHistory;
  static HudOverlay controlsOverlay;
  static bool controlsOverlayReady = false;
  static bool controlsOverlayConfigInit = false;
  static bool controlsOverlayEnabled = true;
  static float controlsOverlayScale = 1.1f;
  static HudOverlay perfOverlay;
  static bool perfOverlayReady = false;
  static bool perfOverlayConfigInit = false;
  [[maybe_unused]] static bool perfOverlayEnabled = true;
  [[maybe_unused]] static float perfOverlayScale = 1.0f;
  [[maybe_unused]] static bool depthPrepassEnabled = false; // For future mesh-based disk rendering
  static ui::RmlUiOverlay rmluiOverlay;
  static bool rmluiEnabled = false;
  static bool rmluiReady = false;
  static int rmluiWidth = 0;
  static int rmluiHeight = 0;
  // curveOverlay and curveOverlayLoaded are declared earlier near curve TSV loading
  static bool curveOverlayEnabled = true;
  static bool curveOverlayWindowOpen = true;
  static int computeMaxSteps = 300;
  static float computeStepSize = 0.1f;
  static bool computeTiled = false;
  static int computeTileSize = 256;
  static bool lutAssetsTried = false;
  static bool lutAssetsLoaded = false;
  static bool lutFromAssets = false;
  static bool lutAssetOnly = false;
  static bool lutAssetOnlyWarned = false;
  static bool lutAssetConfigInit = false;
  static float lutAssetSpin = 0.0f;
  static physics::Lut1D lutAssetEmissivity;
  static physics::Lut1D lutAssetRedshift;
  static bool spectralLutTried = false;
  static bool spectralLutLoaded = false;
  static bool useSpectralLut = false;
  static float spectralWavelengthMin = 0.0f;
  static float spectralWavelengthMax = 0.0f;
  static float spectralRadiusMin = 0.0f;
  static float spectralRadiusMax = 0.0f;
  static bool grbModulationTried = false;
  static bool grbModulationLoaded = false;
  static bool useGrbModulation = false;
  static bool grbTimeManual = false;
  static float grbTimeManualValue = 0.0f;
  static float grbTimeMin = 0.0f;
  static float grbTimeMax = 1.0f;
  static std::vector<float> grbModulationValues;
  static GLuint texGrbModulationLUT = 0;
  static std::vector<float> spectralLutValues;
  static bool lutInitialized = false;
  static float lutSpin = 0.0f;
  static float lutRadiusMin = 0.0f;
  static float lutRadiusMax = 0.0f;
  static float redshiftRadiusMin = 0.0f;
  static float redshiftRadiusMax = 0.0f;
  static GLuint texEmissivityLUT = 0;
  static GLuint texRedshiftLUT = 0;
  static GLuint texPhotonGlowLUT = 0;    // Phase 8.2: Photon sphere glow effect LUT
  static GLuint texDiskDensityLUT = 0;   // Phase 8.2: Accretion disk density profile LUT
  static GLuint texSpectralLUT = 0;
  static GLuint texNoiseVolume = 0;
  static GLuint texGrmhdSlice = 0;
  static GLuint texBlackhole = 0;
  static GLuint texBlackholeCompare = 0;
  static GLuint texBrightness = 0;
  static GLuint texBloomFinal = 0;
  static GLuint texTonemapped = 0;
  static GLuint texDepthEffects = 0;
  static std::array<GLuint, kMaxBloomIterations> texDownsampled = {};
  static std::array<GLuint, kMaxBloomIterations> texUpsampled = {};
  static int renderWidth = 0;
  static int renderHeight = 0;
  static bool noiseTextureReady = false;
  static blackhole::NoiseTextureCache noiseCache;

  auto loadGrmhdPacked = [&](const std::string &path) {
    std::string error;
    if (!loadGrmhdPackedTexture(path, grmhdTexture, error, true, true)) {
      grmhdLoadError = error;
      grmhdLoaded = false;
      return false;
    }
    grmhdLoadError.clear();
    grmhdLoaded = true;
    return true;
  };

  if (!grmhdPathInit) {
    std::snprintf(grmhdPathBuffer.data(), grmhdPathBuffer.size(),
                  "assets/grmhd/grmhd_pack.json");
    grmhdPathInit = true;
  }

  if (!compareAutoInit) {
    const char *sweepEnv = std::getenv("BLACKHOLE_COMPARE_SWEEP");
    if (sweepEnv != nullptr && std::string(sweepEnv) == "1") {
      useComputeRaytracer = true;
      compareComputeFragment = true;
      comparePresetSweep = true;
      compareWriteSummary = true;
      compareWriteOutputs = false;
      compareWriteDiff = false;
      compareAutoCapture = true;
      compareAutoCount = static_cast<int>(kComparePresets.size());
      compareAutoRemaining = compareAutoCount;
      compareAutoStrideCounter = 0;
      compareAutoStride = comparePresetSettleFrames;
      compareRestorePending = false;
      const char *writeDiffEnv = std::getenv("BLACKHOLE_COMPARE_WRITE_DIFF");
      if (writeDiffEnv != nullptr && std::string(writeDiffEnv) == "1") {
        compareWriteDiff = true;
      }
      const char *writeOutputsEnv = std::getenv("BLACKHOLE_COMPARE_WRITE_OUTPUTS");
      if (writeOutputsEnv != nullptr && std::string(writeOutputsEnv) == "1") {
        compareWriteOutputs = true;
      }
      const char *writeSummaryEnv = std::getenv("BLACKHOLE_COMPARE_WRITE_SUMMARY");
      if (writeSummaryEnv != nullptr && std::string(writeSummaryEnv) == "0") {
        compareWriteSummary = false;
      }
      const char *outlierCountEnv = std::getenv("BLACKHOLE_COMPARE_OUTLIER_COUNT");
      if (outlierCountEnv != nullptr) {
        compareMaxOutliers = std::max(0, std::atoi(outlierCountEnv));
      }
      const char *outlierFracEnv = std::getenv("BLACKHOLE_COMPARE_OUTLIER_FRAC");
      if (outlierFracEnv != nullptr) {
        compareMaxOutlierFrac =
            std::max(0.0f, static_cast<float>(std::atof(outlierFracEnv)));
      }
      const char *maxStepsEnv = std::getenv("BLACKHOLE_COMPARE_MAX_STEPS");
      if (maxStepsEnv != nullptr) {
        compareMaxStepsOverride = std::max(0, std::atoi(maxStepsEnv));
        if (compareMaxStepsOverride > 0) {
          compareOverridesEnabled = true;
        }
      }
      const char *stepSizeEnv = std::getenv("BLACKHOLE_COMPARE_STEP_SIZE");
      if (stepSizeEnv != nullptr) {
        compareStepSizeOverride = static_cast<float>(std::atof(stepSizeEnv));
        if (compareStepSizeOverride > 0.0f) {
          compareOverridesEnabled = true;
        }
      }
      const char *baselineEnv = std::getenv("BLACKHOLE_COMPARE_BASELINE");
      if (baselineEnv != nullptr && std::string(baselineEnv) == "1") {
        compareBaselineEnabled = true;
      }
    }
    compareAutoInit = true;
  }

  if (!gpuTimingLogInit) {
    const char *logEnv = std::getenv("BLACKHOLE_GPU_TIMING_LOG");
    if (logEnv != nullptr && std::string(logEnv) == "1") {
      gpuTimingLogEnabled = true;
      gpuTimingEnabled = true;
      const char *strideEnv = std::getenv("BLACKHOLE_GPU_TIMING_LOG_STRIDE");
      if (strideEnv != nullptr) {
        int stride = std::atoi(strideEnv);
        gpuTimingLogStride = std::max(1, stride);
      }
    }
    gpuTimingLogInit = true;
  }

  if (!drawIdProbeConfigInit) {
    const char *probeEnv = std::getenv("BLACKHOLE_DRAWID_PROBE");
    if (probeEnv != nullptr && std::string(probeEnv) == "1") {
      drawIdProbeEnabled = true;
    }
    drawIdProbeSupported = supportsDrawId() && supportsMultiDrawIndirect();
    if (drawIdProbeEnabled && !drawIdProbeSupported) {
      std::cout << "DrawID probe requested but not supported by the driver.\n";
      drawIdProbeEnabled = false;
    }
    drawIdProbeConfigInit = true;
  }

  if (!multiDrawMainConfigInit) {
    const char *multiDrawEnv = std::getenv("BLACKHOLE_MULTIDRAW_MAIN");
    if (multiDrawEnv != nullptr && std::string(multiDrawEnv) == "1") {
      multiDrawMainEnabled = true;
    }
    const char *overlayEnv = std::getenv("BLACKHOLE_MULTIDRAW_OVERLAY");
    if (overlayEnv != nullptr && std::string(overlayEnv) == "0") {
      multiDrawOverlayEnabled = false;
    }
    const char *countEnv = std::getenv("BLACKHOLE_MULTIDRAW_INDIRECT_COUNT");
    if (countEnv != nullptr && std::string(countEnv) == "1") {
      multiDrawIndirectCount = true;
    }
    multiDrawSupported = supportsDrawId() && supportsMultiDrawIndirect();
    multiDrawCountSupported = supportsIndirectCount();
    if (multiDrawMainEnabled && !multiDrawSupported) {
      std::cout << "Multi-draw main path requested but not supported.\n";
      multiDrawMainEnabled = false;
    }
    if (multiDrawIndirectCount && !multiDrawCountSupported) {
      std::cout << "Indirect count requested but not supported.\n";
      multiDrawIndirectCount = false;
    }
    multiDrawMainConfigInit = true;
  }

  if (!lutAssetConfigInit) {
    const char *assetOnlyEnv = std::getenv("BLACKHOLE_LUT_ASSET_ONLY");
    if (assetOnlyEnv != nullptr && std::string(assetOnlyEnv) == "1") {
      lutAssetOnly = true;
    }
    lutAssetConfigInit = true;
  }

  if (!controlsOverlayConfigInit) {
    const char *overlayEnv = std::getenv("BLACKHOLE_OPENGL_CONTROLS");
    if (overlayEnv != nullptr && std::string(overlayEnv) == "0") {
      controlsOverlayEnabled = false;
    }
    const char *scaleEnv = std::getenv("BLACKHOLE_OPENGL_CONTROLS_SCALE");
    if (scaleEnv != nullptr) {
      float scale = static_cast<float>(std::atof(scaleEnv));
      controlsOverlayScale = std::max(scale, 0.5f);
    }
    controlsOverlayConfigInit = true;
  }

  if (!perfOverlayConfigInit) {
    const char *overlayEnv = std::getenv("BLACKHOLE_PERF_HUD");
    if (overlayEnv != nullptr && std::string(overlayEnv) == "0") {
      perfOverlayEnabled = false;
    }
    const char *scaleEnv = std::getenv("BLACKHOLE_PERF_HUD_SCALE");
    if (scaleEnv != nullptr) {
      float scale = static_cast<float>(std::atof(scaleEnv));
      perfOverlayScale = std::max(scale, 0.5f);
    }
    perfOverlayConfigInit = true;
  }

  if (!integratorDebugConfigInit) {
    const char *debugEnv = std::getenv("BLACKHOLE_INTEGRATOR_DEBUG_FLAGS");
    if (debugEnv != nullptr) {
      integratorDebugFlags = std::max(0, std::atoi(debugEnv));
    }
    integratorDebugConfigInit = true;
  }

  auto recreateRenderTargets = [&](int newWidth, int newHeight) {
    auto deleteTexture = [](GLuint &texture) {
      if (texture != 0) {
        glDeleteTextures(1, &texture);
        texture = 0;
      }
    };

    clearRenderToTextureCache();
    deleteTexture(texBlackhole);
    deleteTexture(texBlackholeCompare);
    deleteTexture(texBrightness);
    deleteTexture(texBloomFinal);
    deleteTexture(texTonemapped);
    deleteTexture(texDepthEffects);
    for (auto &texture : texDownsampled) {
      deleteTexture(texture);
    }
    for (auto &texture : texUpsampled) {
      deleteTexture(texture);
    }

    texBlackhole = createColorTexture32f(newWidth, newHeight);
    texBlackholeCompare = createColorTexture32f(newWidth, newHeight);
    texBrightness = createColorTexture(newWidth, newHeight);
    texBloomFinal = createColorTexture(newWidth, newHeight);
    texTonemapped = createColorTexture(newWidth, newHeight);
    texDepthEffects = createColorTexture(newWidth, newHeight);

    for (int i = 0; i < kMaxBloomIterations; ++i) {
      std::size_t index = static_cast<std::size_t>(i);
      int downWidth = std::max(1, newWidth >> (i + 1));
      int downHeight = std::max(1, newHeight >> (i + 1));
      int upWidth = std::max(1, newWidth >> i);
      int upHeight = std::max(1, newHeight >> i);
      texDownsampled[index] = createColorTexture(downWidth, downHeight);
      texUpsampled[index] = createColorTexture(upWidth, upHeight);
    }

    renderWidth = newWidth;
    renderHeight = newHeight;
  };

  static float lutAdiskDensityV = 0.0f;

  auto updateLuts = [&](float spin, float densityV) {
    spin = std::clamp(spin, -0.99f, 0.99f);
    if (!lutAssetsTried) {
      lutAssetsTried = true;
      lutAssetsLoaded = loadLutAssets(lutAssetEmissivity, lutAssetRedshift, lutAssetSpin);
    }

    bool useAssetLuts =
        lutAssetsLoaded && std::abs(spin - lutAssetSpin) <= 1e-3f &&
        !lutAssetEmissivity.values.empty() && !lutAssetRedshift.values.empty();
    if (useAssetLuts) {
      if (!lutInitialized || !lutFromAssets) {
        if (texEmissivityLUT != 0) { glDeleteTextures(1, &texEmissivityLUT); texEmissivityLUT = 0; }
        if (texRedshiftLUT != 0) { glDeleteTextures(1, &texRedshiftLUT); texRedshiftLUT = 0; }
        if (texPhotonGlowLUT != 0) { glDeleteTextures(1, &texPhotonGlowLUT); texPhotonGlowLUT = 0; }
        if (texDiskDensityLUT != 0) { glDeleteTextures(1, &texDiskDensityLUT); texDiskDensityLUT = 0; }

        int lutSize = static_cast<int>(lutAssetEmissivity.values.size());
        texEmissivityLUT = createFloatTexture2D(lutSize, 1, lutAssetEmissivity.values);
        texRedshiftLUT = createFloatTexture2D(lutSize, 1, lutAssetRedshift.values);

        lutRadiusMin = lutAssetEmissivity.r_min;
        lutRadiusMax = lutAssetEmissivity.r_max;
        redshiftRadiusMin = lutAssetRedshift.r_min;
        redshiftRadiusMax = lutAssetRedshift.r_max;
        lutSpin = lutAssetSpin;
        lutFromAssets = true;
        lutInitialized = true;
      }
      return;
    }

    if (lutAssetOnly) {
      if (!lutAssetOnlyWarned) {
        std::cout << "LUT asset-only mode active; skipping generated LUT fallback.\n";
        lutAssetOnlyWarned = true;
      }
      if (texEmissivityLUT != 0) { glDeleteTextures(1, &texEmissivityLUT); texEmissivityLUT = 0; }
      if (texRedshiftLUT != 0) { glDeleteTextures(1, &texRedshiftLUT); texRedshiftLUT = 0; }
      if (texPhotonGlowLUT != 0) { glDeleteTextures(1, &texPhotonGlowLUT); texPhotonGlowLUT = 0; }
      lutInitialized = false;
      lutFromAssets = false;
      return;
    }

    // Only regenerate if parameters changed or not initialized
    if (!lutInitialized || std::abs(spin - lutSpin) > 1e-3f || std::abs(densityV - lutAdiskDensityV) > 1e-3f || lutFromAssets) {
      // Cleanup existing textures
      if (texEmissivityLUT != 0) { glDeleteTextures(1, &texEmissivityLUT); texEmissivityLUT = 0; }
      if (texRedshiftLUT != 0) { glDeleteTextures(1, &texRedshiftLUT); texRedshiftLUT = 0; }
      if (texPhotonGlowLUT != 0) { glDeleteTextures(1, &texPhotonGlowLUT); texPhotonGlowLUT = 0; }
      if (texDiskDensityLUT != 0) { glDeleteTextures(1, &texDiskDensityLUT); texDiskDensityLUT = 0; }

      constexpr int kLutSize = 256;
      constexpr double kMassSolar = 4.0e6;
      constexpr double kMdotEdd = 0.1;

      auto emissivityLut =
          physics::generate_emissivity_lut(kLutSize, kMassSolar, static_cast<double>(spin), kMdotEdd, true);
      auto redshiftLut = physics::generate_redshift_lut(kLutSize, kMassSolar, static_cast<double>(spin));

      texEmissivityLUT = createFloatTexture2D(kLutSize, 1, emissivityLut.values);
      texRedshiftLUT = createFloatTexture2D(kLutSize, 1, redshiftLut.values);

      auto photonGlowLut = physics::generate_photon_glow_lut(256);
      texPhotonGlowLUT = createFloatTexture2D(256, 1, photonGlowLut.values);

      // Connect adiskDensityV to LUT generation
      // Use densityV as the exponent or scale factor for the density profile
      double densityScale = static_cast<double>(std::max(0.1f, densityV));
      auto diskDensityLut = physics::generate_disk_density_lut(256, densityScale);
      texDiskDensityLUT = createFloatTexture2D(256, 1, diskDensityLut.values);

      lutRadiusMin = emissivityLut.r_min;
      lutRadiusMax = emissivityLut.r_max;
      redshiftRadiusMin = redshiftLut.r_min;
      redshiftRadiusMax = redshiftLut.r_max;
      lutSpin = spin;
      lutAdiskDensityV = densityV;
      lutFromAssets = false;
      lutInitialized = true;
      std::cout << "LUTs regenerated. Spin: " << spin << ", DensityV: " << densityV << std::endl;
    }
  };

  // ... (rest of main) ...

  while (!glfwWindowShouldClose(window)) {
    // Clear default framebuffer (essential for ImGui Docking over Viewport)
    glClearColor(0.0f, 0.0f, 0.0f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

    // std::cout << "Frame start" << std::endl; // Debug instrumentation
    ZoneScopedN("Frame");
    // ...
    // Calculate delta time
    double currentTime = glfwGetTime();
    float frameTime = static_cast<float>(currentTime);
    float deltaTime = static_cast<float>(currentTime - lastTime);
    lastTime = currentTime;
    const float cpuFrameMs = deltaTime * 1000.0f;

    glfwPollEvents();

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
    // Check for shader file changes (hot-reload)
    if (ShaderWatcher::instance().hasPendingReloads()) {
      auto changedShaders = ShaderWatcher::instance().pollChangedShaders();
      for (const auto &path : changedShaders) {
        std::cout << "[HotReload] Shader changed: " << path << std::endl;
        // TODO: Implement actual shader recompilation
        // For now, log changes - full reload requires shader registry refactor
      }
      ShaderWatcher::instance().clearPendingReloads();
    }
#endif

    // Update input manager
    InputManager::instance().update(deltaTime);
    auto &input = InputManager::instance();

    if (gpuTimingEnabled && !gpuTimers.initialized) {
      gpuTimers.init();
    } else if (!gpuTimingEnabled && gpuTimers.initialized) {
      gpuTimers.shutdown();
    }
    if (gpuTimers.initialized) {
      gpuTimers.resolve();
    }
    timingHistory.push(cpuFrameMs, gpuTimers);
    TracyPlot("cpu_frame_ms", cpuFrameMs);
    if (gpuTimers.initialized) {
      TracyPlot("gpu_fragment_ms", gpuTimers.blackholeFragment.lastMs);
      TracyPlot("gpu_compute_ms", gpuTimers.blackholeCompute.lastMs);
      TracyPlot("gpu_bloom_ms", gpuTimers.bloom.lastMs);
      TracyPlot("gpu_tonemap_ms", gpuTimers.tonemap.lastMs);
      TracyPlot("gpu_depth_ms", gpuTimers.depth.lastMs);
      TracyPlot("gpu_grmhd_slice_ms", gpuTimers.grmhdSlice.lastMs);
    }

    ImGui_ImplOpenGL3_NewFrame();
    ImGui_ImplGlfw_NewFrame();
    ImGui::NewFrame();
    ImGuizmo::BeginFrame();

    int windowWidth, windowHeight;
    glfwGetFramebufferSize(window, &windowWidth, &windowHeight);
    if (windowWidth == 0 || windowHeight == 0) {
      glfwWaitEvents();
      continue;
    }
    glViewport(0, 0, windowWidth, windowHeight);

    // ---------------------------------------------------------
    // DOCKING & VIEWPORT SETUP (EARLY)
    // ---------------------------------------------------------
    static bool firstLayout = true;
    ImGuiID dockspaceId = ImGui::GetID("MyDockSpace");
    ImGui::DockSpaceOverViewport(dockspaceId, ImGui::GetMainViewport(), ImGuiDockNodeFlags_None);

    if (firstLayout) {
        resetLayout(dockspaceId);
        firstLayout = false;
    }

    ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(0.0f, 0.0f));
    ImGui::Begin("Viewport", nullptr, ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse | ImGuiWindowFlags_NoTitleBar);
    ImVec2 viewportSize = ImGui::GetContentRegionAvail();
    
    // Resize render targets to match viewport
    if (viewportSize.x > 0 && viewportSize.y > 0 && 
        (static_cast<int>(viewportSize.x) != renderWidth || static_cast<int>(viewportSize.y) != renderHeight)) {
        recreateRenderTargets(static_cast<int>(viewportSize.x), static_cast<int>(viewportSize.y));
    }
    ImGui::End();
    ImGui::PopStyleVar();

    if (rmluiEnabled) {
      if (!rmluiReady) {
        rmluiReady = rmluiOverlay.init(window, windowWidth, windowHeight);
      }
      if (rmluiReady && (windowWidth != rmluiWidth || windowHeight != rmluiHeight)) {
        rmluiOverlay.resize(windowWidth, windowHeight);
        rmluiWidth = windowWidth;
        rmluiHeight = windowHeight;
      }
    } else if (rmluiReady) {
      rmluiOverlay.shutdown();
      rmluiReady = false;
    }

    static GLuint galaxy = loadCubemap(std::string("assets/skybox_nebula_dark"));
    static GLuint colorMap = loadTexture2D(std::string("assets/color_map.png"));
    static std::vector<BackgroundAsset> backgroundAssets;
    static int backgroundIndex = 0;
    static std::string backgroundLoadedId;
    static GLuint backgroundBase = 0;
    static std::array<GLuint, kBackgroundLayers> backgroundTextures = {};
    static std::array<glm::vec4, kBackgroundLayers> backgroundLayerParams = {};
    static std::array<float, kBackgroundLayers> backgroundLayerDepth = {0.2f, 0.5f, 0.9f};
    static std::array<float, kBackgroundLayers> backgroundLayerScale = {1.0f, 1.08f, 1.16f};
    static std::array<float, kBackgroundLayers> backgroundLayerIntensity = {1.0f, 0.6f, 0.35f};
    static std::array<float, kBackgroundLayers> backgroundLayerLodBias = {0.0f, 1.0f, 2.0f};
    static bool wiregridEnabled = false;
    static WiregridParams wiregridParams;
    static WiregridParams wiregridParamsCached;
    static WiregridMesh wiregridMesh;
    static glm::vec4 wiregridColor = glm::vec4(0.2f, 0.6f, 1.0f, 0.4f);
    static GLuint fallback2D = 0;
    static GLuint fallback3D = 0;
    static GLuint fallbackCubemap = 0;
    if (fallback2D == 0) {
      fallback2D = createColorTexture(1, 1, false);
    }
    if (fallback3D == 0) {
      fallback3D = createFloatTexture3D(1, 1, 1, std::vector<float>{0.0f});
    }
    if (fallbackCubemap == 0) {
      fallbackCubemap = createSolidCubemap1x1(0, 0, 0);
    }
    if (backgroundAssets.empty()) {
      backgroundAssets = loadBackgroundAssets();
    }
    if (!backgroundAssets.empty()) {
      backgroundIndex = findBackgroundIndex(backgroundAssets, settings.backgroundId);
      if (backgroundIndex < 0 ||
          backgroundIndex >= static_cast<int>(backgroundAssets.size())) {
        backgroundIndex = 0;
      }
      const auto &asset = backgroundAssets[static_cast<std::size_t>(backgroundIndex)];
      if (backgroundLoadedId != asset.id) {
        GLuint nextTexture = loadTexture2D(asset.path, true);
        if (nextTexture != 0) {
          if (backgroundBase != 0) {
            glDeleteTextures(1, &backgroundBase);
          }
          backgroundBase = nextTexture;
          backgroundLoadedId = asset.id;
        }
      }
    }
    GLuint backgroundFallback = backgroundBase != 0 ? backgroundBase : fallback2D;
    backgroundTextures.fill(backgroundFallback);
    if (!noiseTextureReady) {
      noiseTextureReady = noiseCache.initialize();
      if (noiseTextureReady) {
        texNoiseVolume = noiseCache.getTurbulenceTexture();
      }
    }

    if (!cameraSettingsLoaded) {
      cameraModeIndex = settings.cameraMode;
      orbitRadius = settings.orbitRadius;
      orbitSpeed = settings.orbitSpeed;
      cameraSettingsLoaded = true;
    }

    if (!displaySettingsLoaded) {
      renderScale = settings.renderScale;
      swapInterval = settings.swapInterval;
      displaySettingsLoaded = true;
    }
    if (!postProcessingSettingsLoaded) {
      bloomStrength = settings.bloomStrength;
      tonemappingEnabled = settings.tonemappingEnabled;
      gamma = settings.gamma;
      postProcessingSettingsLoaded = true;
    }
    if (!bloomSettingsLoaded) {
      bloomIterations = std::clamp(settings.bloomIterations, 1, kMaxBloomIterations);
      bloomSettingsLoaded = true;
    }

    renderScale = std::clamp(renderScale, 0.25f, 1.5f);
    // Legacy resize logic disabled in favor of Viewport-based sizing
    /*
    int targetWidth =
        std::max(1, static_cast<int>(static_cast<float>(windowWidth) * renderScale));
    int targetHeight =
        std::max(1, static_cast<int>(static_cast<float>(windowHeight) * renderScale));
    if (targetWidth != renderWidth || targetHeight != renderHeight) {
      recreateRenderTargets(targetWidth, targetHeight);
    }
    */
    settings.fullscreen = input.isFullscreen();
    settings.swapInterval = swapInterval;
    settings.renderScale = renderScale;
    settings.bloomStrength = bloomStrength;
    settings.tonemappingEnabled = tonemappingEnabled;
    settings.gamma = gamma;
    settings.bloomIterations = bloomIterations;

    comparePresetSettleFrames = std::clamp(comparePresetSettleFrames, 1, 10);
    bool compareSweepAllowed =
        compareComputeFragment && ShaderManager::instance().canUseComputeShaders();
    if (comparePresetSweep && !compareSweepAllowed) {
      comparePresetSweep = false;
      if (comparePresetSaved) {
        compareRestorePending = true;
      }
    }
    if (comparePresetSweep) {
      if (!comparePresetSaved) {
        comparePresetSavedCamera = input.camera();
        comparePresetSavedMode = cameraModeIndex;
        comparePresetSavedOrbitRadius = orbitRadius;
        comparePresetSavedOrbitSpeed = orbitSpeed;
        comparePresetSavedOrbitTime = orbitTime;
        comparePresetSavedKerrSpin = kerrSpin;
        comparePresetSaved = true;
      }
      int presetCount = static_cast<int>(kComparePresets.size());
      comparePresetIndex = std::clamp(comparePresetIndex, 0, presetCount);
      if (comparePresetIndex >= presetCount) {
        comparePresetSweep = false;
        compareRestorePending = true;
      } else {
        const auto &preset = kComparePresets[static_cast<std::size_t>(comparePresetIndex)];
        CameraState &camMutable = input.camera();
        camMutable = preset.camera;
        cameraModeIndex = static_cast<int>(preset.mode);
        orbitRadius = preset.orbitRadius;
        orbitSpeed = preset.orbitSpeed;
        orbitTime = 0.0f;
        kerrSpin = preset.kerrSpin;
        comparePresetFrameCounter++;
        if (comparePresetFrameCounter >= comparePresetSettleFrames) {
          captureCompareSnapshot = true;
          comparePresetFrameCounter = 0;
          comparePresetIndex++;
          if (comparePresetIndex >= presetCount) {
            comparePresetSweep = false;
            compareRestorePending = true;
          }
        }
      }
    }

    // Get camera state for shader
    const auto &cam = input.camera();
    cameraModeIndex = std::clamp(cameraModeIndex, 0, 3);
    orbitRadius = std::max(orbitRadius, 2.0f);
    orbitSpeed = std::max(orbitSpeed, 0.0f);

    glm::vec3 focusTarget = gizmoEnabled ? glm::vec3(gizmoTransform[3]) : glm::vec3(0.0f);

    orbitTime += input.getEffectiveDeltaTime(deltaTime);
    glm::vec3 cameraPos;
    CameraMode cameraMode = static_cast<CameraMode>(cameraModeIndex);
    switch (cameraMode) {
    case CameraMode::Front:
      cameraPos = focusTarget + glm::vec3(10.0f, 1.0f, 10.0f);
      break;
    case CameraMode::Top:
      cameraPos = focusTarget + glm::vec3(15.0f, 15.0f, 0.0f);
      break;
    case CameraMode::Orbit: {
      float angle = orbitTime * glm::radians(orbitSpeed);
      cameraPos = focusTarget + glm::vec3(-std::cos(angle) * orbitRadius,
                                          std::sin(angle) * orbitRadius,
                                          std::sin(angle) * orbitRadius);
      break;
    }
    case CameraMode::Input:
    default:
      cameraPos = focusTarget + cameraPositionFromYawPitch(cam.yaw, cam.pitch, cam.distance);
      break;
    }

    glm::mat3 cameraBasis = buildCameraBasis(cameraPos, focusTarget, cam.roll);
    float fovScale = 1.0f;
    glm::mat4 viewRotation(1.0f);
    viewRotation[0] = glm::vec4(cameraBasis[0], 0.0f);
    viewRotation[1] = glm::vec4(cameraBasis[1], 0.0f);
    viewRotation[2] = glm::vec4(cameraBasis[2], 0.0f);

    glm::vec2 parallaxBase =
        glm::vec2(cameraPos.x, cameraPos.y) * settings.backgroundParallaxStrength;
    glm::vec2 drift = glm::vec2(std::cos(static_cast<float>(currentTime) * 0.02f),
                                std::sin(static_cast<float>(currentTime) * 0.02f)) *
                      settings.backgroundDriftStrength;
    for (std::size_t i = 0; i < static_cast<std::size_t>(kBackgroundLayers); ++i) {
      glm::vec2 offset = drift + parallaxBase * backgroundLayerDepth[i];
      backgroundLayerParams[i] =
          glm::vec4(offset, backgroundLayerScale[i], backgroundLayerIntensity[i]);
    }
    wiregridParams.radiusMax =
        std::max(wiregridParams.radiusMax, wiregridParams.radiusMin + 0.1f);
    wiregridParams.schwarzschildRadius = 2.0f * blackHoleMass;
    if (wiregridEnabled &&
        (wiregridMesh.vao == 0 ||
         !wiregridParamsEqual(wiregridParams, wiregridParamsCached))) {
      // std::cout << "Updating wiregrid mesh..." << std::endl;
      updateWiregridMesh(wiregridMesh, wiregridParams);
      wiregridParamsCached = wiregridParams;
    }

    glm::mat4 projectionMatrix = glm::perspective(glm::radians(cam.fov),
                                                  static_cast<float>(renderWidth) /
                                                      static_cast<float>(renderHeight),
                                                  0.1f, depthFar);
    glm::mat4 gizmoViewMatrix = glm::lookAt(cameraPos, focusTarget, cameraBasis[1]);
    bool computeActiveForLog = false;
    bool grmhdReady = grmhdLoaded && grmhdTexture.texture != 0;
    bool grmhdEnabled = useGrmhd && grmhdReady;
    bool spectralReady = spectralLutLoaded && texSpectralLUT != 0;
    bool spectralEnabled = useSpectralLut && spectralReady;
    spectralRadiusMin = std::max(0.0f, spectralRadiusMin);
    spectralRadiusMax = std::max(spectralRadiusMax, spectralRadiusMin + 0.001f);

    if (!grbModulationTried) {
      grbModulationTried = true;
      grbModulationLoaded =
          loadGrbModulationLutAssets(grbModulationValues, grbTimeMin, grbTimeMax);
      if (grbModulationLoaded) {
        if (texGrbModulationLUT != 0) {
          glDeleteTextures(1, &texGrbModulationLUT);
          texGrbModulationLUT = 0;
        }
        int lutSize = static_cast<int>(grbModulationValues.size());
        texGrbModulationLUT = createFloatTexture2D(lutSize, 1, grbModulationValues);
        grbTimeManualValue = grbTimeMin;
      }
    }
    bool grbModulationReady = grbModulationLoaded && texGrbModulationLUT != 0;
    bool grbModulationEnabled = useGrbModulation && grbModulationReady;
    float grbSpan = std::max(grbTimeMax - grbTimeMin, 0.001f);
    float grbTimeSeconds = 0.0f;
    if (grbModulationReady) {
      if (grbTimeManual) {
        grbTimeSeconds = std::clamp(grbTimeManualValue, grbTimeMin, grbTimeMax);
      } else {
        grbTimeSeconds = grbTimeMin +
                         std::fmod(static_cast<float>(currentTime), grbSpan);
      }
    }

    bool lutReady = texEmissivityLUT != 0 && texRedshiftLUT != 0;

    {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/blackhole_main.frag";
      rtti.cubemapUniforms["galaxy"] = galaxy != 0 ? galaxy : fallbackCubemap;
      rtti.textureUniforms["colorMap"] = colorMap != 0 ? colorMap : fallback2D;
      rtti.textureUniforms["emissivityLUT"] = lutReady ? texEmissivityLUT : fallback2D;
      rtti.textureUniforms["redshiftLUT"] = lutReady ? texRedshiftLUT : fallback2D;
      rtti.textureUniforms["photonGlowLUT"] = texPhotonGlowLUT != 0 ? texPhotonGlowLUT : fallback2D;  // Phase 8.2
      rtti.textureUniforms["diskDensityLUT"] = texDiskDensityLUT != 0 ? texDiskDensityLUT : fallback2D;  // Phase 8.2 P2
      rtti.textureUniforms["spectralLUT"] = spectralEnabled ? texSpectralLUT : fallback2D;
      rtti.textureUniforms["grbModulationLUT"] = grbModulationReady ? texGrbModulationLUT : fallback2D;
      rtti.textureUniforms["hawkingTempLUT"] = hawkingLutsLoaded ? hawkingRenderer.getTempLUTTexture() : fallback2D;
      rtti.textureUniforms["hawkingSpectrumLUT"] = hawkingLutsLoaded ? hawkingRenderer.getSpectrumLUTTexture() : fallback2D;
      for (int i = 0; i < kBackgroundLayers; ++i) {
        const std::string name = "backgroundLayers[" + std::to_string(i) + "]";
        rtti.textureUniforms[name] =
            backgroundTextures[static_cast<std::size_t>(i)];
      }
      noiseTextureScale = std::max(noiseTextureScale, 0.01f);
      bool noiseReady = useNoiseTexture && texNoiseVolume != 0;
      rtti.texture3DUniforms["noiseTexture"] = noiseReady ? texNoiseVolume : fallback3D;
      rtti.texture3DUniforms["grmhdTexture"] = grmhdEnabled ? grmhdTexture.texture : fallback3D;

      rtti.floatUniforms["useNoiseTexture"] = noiseReady ? 1.0f : 0.0f;
      rtti.floatUniforms["useGrmhd"] = grmhdEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["noiseTextureScale"] = noiseTextureScale;
      rtti.floatUniforms["backgroundEnabled"] = settings.backgroundEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["backgroundIntensity"] = settings.backgroundIntensity;
      rtti.floatUniforms["time"] = frameTime;
      rtti.vec3Uniforms["grmhdBoundsMin"] = grmhdBoundsMin;
      rtti.vec3Uniforms["grmhdBoundsMax"] = grmhdBoundsMax;
      for (int i = 0; i < kBackgroundLayers; ++i) {
        const std::string name = "backgroundLayerParams[" + std::to_string(i) + "]";
        rtti.vec4Uniforms[name] =
            backgroundLayerParams[static_cast<std::size_t>(i)];
      }
      for (int i = 0; i < kBackgroundLayers; ++i) {
        const std::string name = "backgroundLayerLodBias[" + std::to_string(i) + "]";
        rtti.floatUniforms[name] =
            std::max(backgroundLayerLodBias[static_cast<std::size_t>(i)], 0.0f);
      }

      rtti.targetTexture = texBlackhole;
      rtti.width = renderWidth;
      rtti.height = renderHeight;

      // Render UI controls only if visible
      if (input.isUIVisible()) {
        ImGui::SetNextWindowSize(ImVec2(450, 700), ImGuiCond_FirstUseEver);
        ImGui::Begin("Settings", nullptr, ImGuiWindowFlags_NoCollapse);
        if (ImGui::BeginTabBar("MainTabs")) {
          if (ImGui::BeginTabItem("Visuals")) {
            ImGui::Checkbox("gravitationalLensing", &gravitationalLensing);
            ImGui::SliderInt("Bloom Iterations", &bloomIterations, 1, kMaxBloomIterations);
            settings.bloomIterations = bloomIterations;
        ImGui::Checkbox("renderBlackHole", &renderBlackHole);
        ImGui::Checkbox("adiskEnabled", &adiskEnabled);
        ImGui::Checkbox("adiskParticle", &adiskParticle);
        ImGui::SliderFloat("adiskDensityV", &adiskDensityV, 0.0f, 10.0f);
        ImGui::SliderFloat("adiskDensityH", &adiskDensityH, 0.0f, 10.0f);
        ImGui::SliderFloat("adiskHeight", &adiskHeight, 0.0f, 1.0f);
        ImGui::SliderFloat("adiskLit", &adiskLit, 0.0f, 4.0f);
        ImGui::SliderFloat("adiskNoiseLOD", &adiskNoiseLOD, 1.0f, 12.0f);
        ImGui::SliderFloat("adiskNoiseScale", &adiskNoiseScale, 0.0f, 10.0f);
        ImGui::Checkbox("Noise Texture", &useNoiseTexture);
        ImGui::SliderFloat("Noise Tex Scale", &noiseTextureScale, 0.05f, 2.0f);
        ImGui::SliderFloat("adiskSpeed", &adiskSpeed, 0.0f, 1.0f);
        ImGui::SliderFloat("dopplerStrength", &dopplerStrength, 0.0f, 5.0f);

        ImGui::EndTabItem();
          }
          if (ImGui::BeginTabItem("GRMHD")) {
            ImGui::Text("GRMHD Packed");
        ImGui::Checkbox("Use GRMHD Field", &useGrmhd);
        ImGui::InputText("GRMHD Meta", grmhdPathBuffer.data(), grmhdPathBuffer.size());
        if (ImGui::Button("Load GRMHD")) {
          loadGrmhdPacked(grmhdPathBuffer.data());
        }
        ImGui::SameLine();
        if (ImGui::Button("Unload GRMHD")) {
          destroyGrmhdPackedTexture(grmhdTexture);
          grmhdLoaded = false;
          grmhdLoadError.clear();
        }
        if (!grmhdLoadError.empty()) {
          ImGui::TextColored(ImVec4(1.0f, 0.35f, 0.35f, 1.0f), "%s",
                             grmhdLoadError.c_str());
        }
        if (grmhdLoaded) {
          ImGui::Text("GRMHD grid: %d x %d x %d", grmhdTexture.width, grmhdTexture.height,
                      grmhdTexture.depth);
        }
        ImGui::SliderFloat3("GRMHD Bounds Min", &grmhdBoundsMin.x, -50.0f, 50.0f);
        ImGui::SliderFloat3("GRMHD Bounds Max", &grmhdBoundsMax.x, -50.0f, 50.0f);
        ImGui::BeginDisabled(!grmhdLoaded);
        ImGui::Checkbox("Show GRMHD Slice", &grmhdSliceEnabled);
        const char *axisLabels[] = {"X", "Y", "Z"};
        ImGui::Combo("Slice Axis", &grmhdSliceAxis, axisLabels, 3);
        ImGui::SliderFloat("Slice Coord", &grmhdSliceCoord, 0.0f, 1.0f);
        ImGui::SliderInt("Slice Channel", &grmhdSliceChannel, 0, 3);
        if (grmhdLoaded && grmhdSliceChannel >= 0 &&
            static_cast<std::size_t>(grmhdSliceChannel) < grmhdTexture.channels.size()) {
          std::size_t channelIndex = static_cast<std::size_t>(grmhdSliceChannel);
          ImGui::Text("Channel: %s", grmhdTexture.channels[channelIndex].c_str());
        }
        ImGui::Checkbox("Slice Auto Range", &grmhdSliceAutoRange);
        if (!grmhdSliceAutoRange) {
          ImGui::InputFloat("Slice Min", &grmhdSliceMin);
          ImGui::InputFloat("Slice Max", &grmhdSliceMax);
        }
        ImGui::Checkbox("Slice Color Map", &grmhdSliceUseColorMap);
        ImGui::SliderInt("Slice Size", &grmhdSliceSize, 64, 1024);
        if (texGrmhdSlice != 0) {
          ImTextureID sliceId =
              static_cast<ImTextureID>(static_cast<uintptr_t>(texGrmhdSlice));
          ImGui::Image(sliceId, ImVec2(192.0f, 192.0f));
        }
        ImGui::EndDisabled();

        // GRMHD Time-Series Playback (Phase 4.3)
        ImGui::Separator();
        ImGui::TextColored(ImVec4(0.3f, 0.9f, 0.9f, 1.0f), "GRMHD Time-Series");
        ImGui::Checkbox("Enable Time-Series Playback", &grmhdTimeSeriesEnabled);

        ImGui::BeginDisabled(!grmhdTimeSeriesEnabled);

        // File paths
        ImGui::InputText("JSON Metadata", grmhdTimeSeriesJsonBuffer.data(),
                         grmhdTimeSeriesJsonBuffer.size());
        ImGui::InputText("Binary Data", grmhdTimeSeriesBinBuffer.data(),
                         grmhdTimeSeriesBinBuffer.size());

        // Load/Unload buttons
        if (ImGui::Button("Load Time-Series")) {
          // TODO: Initialize GRMHDStreamer when implementation is complete
          // For now, just set placeholder state
          grmhdTimeSeriesLoaded = true;
          grmhdMaxFrame = 100;  // Placeholder: actual value from metadata
          grmhdCurrentFrame = 0;
        }
        ImGui::SameLine();
        if (ImGui::Button("Unload Time-Series")) {
          // TODO: Shutdown GRMHDStreamer
          grmhdTimeSeriesLoaded = false;
          grmhdCurrentFrame = 0;
          grmhdMaxFrame = 0;
          grmhdPlaying = false;
        }

        ImGui::BeginDisabled(!grmhdTimeSeriesLoaded);

        // Frame control
        ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Playback");
        if (ImGui::SliderInt("Frame", &grmhdCurrentFrame, 0, grmhdMaxFrame)) {
          // TODO: Call streamer.seekFrame(grmhdCurrentFrame)
        }
        ImGui::Text("Time: %.2f s", static_cast<double>(grmhdCurrentFrame) / 30.0);

        // Play/Pause button
        if (grmhdPlaying) {
          if (ImGui::Button("Pause")) {
            grmhdPlaying = false;
            // TODO: Call streamer.pause()
          }
        } else {
          if (ImGui::Button("Play")) {
            grmhdPlaying = true;
            // TODO: Call streamer.play()
          }
        }
        ImGui::SameLine();
        if (ImGui::Button("Reset")) {
          grmhdCurrentFrame = 0;
          // TODO: Call streamer.seekFrame(0)
        }

        // Playback speed
        if (ImGui::SliderFloat("Playback Speed", &grmhdPlaybackSpeed, 0.1f, 4.0f)) {
          // TODO: Call streamer.setPlaybackSpeed(grmhdPlaybackSpeed)
        }

        // Cache statistics
        ImGui::Separator();
        ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Cache Statistics");
        ImGui::Text("Hit Rate: %.1f%%", grmhdCacheHitRate * 100.0);
        ImGui::Text("Queue Depth: %d", grmhdQueueDepth);

        // Progress indicator for queue
        if (grmhdQueueDepth > 0) {
          ImGui::ProgressBar(static_cast<float>(grmhdQueueDepth) / 10.0f, ImVec2(-1.0f, 0.0f),
                             nullptr);
        }

        // Performance targets reference
        ImGui::Separator();
        ImGui::TextDisabled("Performance Targets:");
        ImGui::TextDisabled("  Cache hit rate: >90%%");
        ImGui::TextDisabled("  Frame load time: <16ms (60 fps)");
        ImGui::TextDisabled("  Memory footprint: <4GB");

        ImGui::EndDisabled();  // !grmhdTimeSeriesLoaded
        ImGui::EndDisabled();  // !grmhdTimeSeriesEnabled

        ImGui::EndTabItem();
          }
          if (ImGui::BeginTabItem("Physics")) {
            ImGui::Text("Physics Parameters");

        // Black hole mass in solar masses (scaled for visualization)
        ImGui::SliderFloat("blackHoleMass", &blackHoleMass, 0.1f, 10.0f);
        // Kerr spin parameter a (|a|<M)
        ImGui::SliderFloat("kerrSpin(a/M)", &kerrSpin, -0.99f, 0.99f);

        // Physics visualization toggles
        ImGui::Checkbox("enablePhotonSphere", &enablePhotonSphere);
        ImGui::Checkbox("enableRedshift", &enableRedshift);

        ImGui::Separator();
        ImGui::Text("Hawking Radiation Glow");
        ImGui::Checkbox("Enable Hawking Glow", &hawkingGlowEnabled);

        if (hawkingGlowEnabled) {
          // Preset buttons
          const char* presetLabels[] = {"Physical", "Primordial", "Extreme"};
          if (ImGui::Combo("Preset", &hawkingPreset, presetLabels, 3)) {
            // Apply preset
            physics::HawkingPreset preset = static_cast<physics::HawkingPreset>(hawkingPreset);
            physics::HawkingGlowParams params = physics::HawkingRenderer::applyPreset(preset);
            hawkingTempScale = params.tempScale;
            hawkingGlowIntensity = params.intensity;
          }

          // Manual controls
          ImGui::SliderFloat("Temp Scale", &hawkingTempScale, 1.0f, 1e9f, "%.1e",
                           ImGuiSliderFlags_Logarithmic);
          ImGui::TextDisabled("1=physical, 1e6=primordial, 1e9=extreme");
          ImGui::SliderFloat("Glow Intensity", &hawkingGlowIntensity, 0.0f, 5.0f);
          ImGui::Checkbox("Use LUTs", &hawkingUseLUTs);

          if (hawkingLutsLoaded) {
            ImGui::TextColored(ImVec4(0.0f, 1.0f, 0.0f, 1.0f), "LUTs loaded");
          } else {
            ImGui::TextColored(ImVec4(1.0f, 0.35f, 0.35f, 1.0f), "LUTs not loaded");
          }
        }

        ImGui::Separator();
        ImGui::Text("Spectral LUT");
        ImGui::Checkbox("Use Spectral LUT", &useSpectralLut);
        if (spectralLutLoaded) {
          ImGui::Text("Wavelength: %.0f - %.0f A", static_cast<double>(spectralWavelengthMin),
                      static_cast<double>(spectralWavelengthMax));
        } else {
          ImGui::TextDisabled("rt_spectrum_lut.csv not loaded");
        }
        if (ImGui::Button("Reload Spectral LUT")) {
          spectralLutTried = false;
          spectralLutLoaded = false;
          spectralLutValues.clear();
          if (texSpectralLUT != 0) {
            glDeleteTextures(1, &texSpectralLUT);
            texSpectralLUT = 0;
          }
        }

        ImGui::Separator();
        ImGui::Text("GRB Modulation");
        ImGui::Checkbox("Use GRB Modulation", &useGrbModulation);
        if (grbModulationLoaded) {
          ImGui::Text("Time: %.2f - %.2f s", static_cast<double>(grbTimeMin),
                      static_cast<double>(grbTimeMax));
        } else {
          ImGui::TextDisabled("grb_modulation_lut.csv not loaded");
        }
        ImGui::BeginDisabled(!grbModulationLoaded);
        ImGui::Checkbox("Manual GRB Time", &grbTimeManual);
        if (grbTimeManual) {
          ImGui::SliderFloat("GRB Time", &grbTimeManualValue, grbTimeMin, grbTimeMax);
        }
        ImGui::EndDisabled();
        if (ImGui::Button("Reload GRB LUT")) {
          grbModulationTried = false;
          grbModulationLoaded = false;
          grbModulationValues.clear();
          if (texGrbModulationLUT != 0) {
            glDeleteTextures(1, &texGrbModulationLUT);
            texGrbModulationLUT = 0;
          }
        }
        ImGui::SliderFloat("Spectral Radius Min", &spectralRadiusMin, 0.0f, 50.0f);
        ImGui::SliderFloat("Spectral Radius Max", &spectralRadiusMax, 0.0f, 50.0f);

        const double referenceMass = physics::M_SUN;
        const double referenceRs = physics::schwarzschild_radius(referenceMass);
        const double referenceRg = physics::G * referenceMass / physics::C2;
        const double referenceA = static_cast<double>(kerrSpin) * referenceRg;
        const bool progradeSpin = kerrSpin >= 0.0f;
        const double iscoRatio =
            physics::kerr_isco_radius(referenceMass, referenceA, progradeSpin) / referenceRs;
        const double photonRatio = (progradeSpin ? physics::kerr_photon_orbit_prograde
                                                 : physics::kerr_photon_orbit_retrograde)(
                                        referenceMass, referenceA) /
                                    referenceRs;

        float schwarzschildRadius = 2.0f * blackHoleMass;
        float photonSphereRadius = static_cast<float>(photonRatio) * schwarzschildRadius;
        float iscoRadius = static_cast<float>(iscoRatio) * schwarzschildRadius;
      ImGui::Text("r_s = %.2f, r_ph = %.2f, r_ISCO = %.2f",
                  static_cast<double>(schwarzschildRadius),
                  static_cast<double>(photonSphereRadius),
                  static_cast<double>(iscoRadius));

        ImGui::EndTabItem();
          }
          if (ImGui::BeginTabItem("Compute")) {
            ImGui::Text("Compute Raytracer");
        bool computeAvailable = ShaderManager::instance().canUseComputeShaders();
        if (!computeAvailable) {
          ImGui::TextDisabled("Compute shaders unavailable");
          useComputeRaytracer = false;
          compareComputeFragment = false;
        }
        ImGui::Checkbox("Use Compute Raytracer", &useComputeRaytracer);
        if (useComputeRaytracer) {
          ImGui::SliderInt("Compute Steps", &computeMaxSteps, 50, 600);
          ImGui::SliderFloat("Compute Step Size", &computeStepSize, 0.01f, 1.0f);
          ImGui::Checkbox("Compute Tiled", &computeTiled);
          if (computeTiled) {
            ImGui::SliderInt("Compute Tile Size", &computeTileSize, 64, 1024);
          }
        }
        ImGui::Checkbox("Compare Compute vs Fragment", &compareComputeFragment);
        if (compareComputeFragment) {
          ImGui::SliderInt("Compare Sample Size", &compareSampleSize, 4, 64);
          ImGui::SliderInt("Compare Frame Stride", &compareFrameStride, 1, 60);
          if (compareStats.valid) {
            ImGui::Text("Diff mean=%.6f max=%.6f", static_cast<double>(compareStats.meanAbs),
                        static_cast<double>(compareStats.maxAbs));
          } else {
            ImGui::TextDisabled("Diff metrics unavailable");
          }
          if (compareFullStats.valid) {
            ImGui::Text("Full diff mean=%.6f rms=%.6f max=%.6f",
                        static_cast<double>(compareFullStats.meanAbs),
                        static_cast<double>(compareFullStats.rms),
                        static_cast<double>(compareFullStats.maxAbs));
          }
          ImGui::Checkbox("Write Snapshot PPMs", &compareWriteOutputs);
          ImGui::Checkbox("Write Diff PPM", &compareWriteDiff);
          ImGui::Checkbox("Write Summary CSV", &compareWriteSummary);
          ImGui::SliderFloat("Diff Scale", &compareDiffScale, 0.1f, 32.0f);
          ImGui::SliderFloat("Max Diff Threshold", &compareThreshold, 0.0f, 0.5f);
          compareThreshold = std::max(compareThreshold, 0.0f);
          ImGui::SliderInt("Allowed Outliers", &compareMaxOutliers, 0, 50000);
          ImGui::SliderFloat("Allowed Outlier Frac", &compareMaxOutlierFrac, 0.0f, 0.01f,
                             "%.5f");
          compareMaxOutlierFrac = std::max(compareMaxOutlierFrac, 0.0f);
          ImGui::Checkbox("Compare Baseline (disable extras)", &compareBaselineEnabled);
          if (ImGui::Checkbox("Compare Overrides", &compareOverridesEnabled)) {
            if (compareOverridesEnabled) {
              if (compareMaxStepsOverride <= 0) {
                compareMaxStepsOverride = computeMaxSteps;
              }
              if (compareStepSizeOverride <= 0.0f) {
                compareStepSizeOverride = computeStepSize;
              }
            }
          }
          ImGui::BeginDisabled(!compareOverridesEnabled);
          ImGui::SliderInt("Compare Max Steps Override", &compareMaxStepsOverride, 0, 1000);
          ImGui::SliderFloat("Compare Step Size Override", &compareStepSizeOverride, 0.0f, 2.0f);
          ImGui::EndDisabled();
          ImGui::Separator();
          ImGui::Text("Integrator Debug");
          bool debugNan = (integratorDebugFlags & kIntegratorDebugNanFlag) != 0;
          bool debugRange = (integratorDebugFlags & kIntegratorDebugRangeFlag) != 0;
          ImGui::Checkbox("Flag NaN/Inf", &debugNan);
          ImGui::SameLine();
          ImGui::Checkbox("Flag Out-of-Range", &debugRange);
          integratorDebugFlags = (debugNan ? kIntegratorDebugNanFlag : 0) |
                                 (debugRange ? kIntegratorDebugRangeFlag : 0);
          ImGui::Text("Threshold failures: %d", compareFailureCount);
          if (compareFullStats.valid) {
            ImGui::Text("Last capture: %s", compareLastExceeded ? "FAIL" : "PASS");
            ImGui::Text("Outliers: %d (limit %d)", compareLastOutliers,
                        compareLastOutlierLimit);
          }
          if (ImGui::Checkbox("Auto Capture", &compareAutoCapture)) {
            compareAutoRemaining = compareAutoCapture ? std::max(compareAutoCount, 1) : 0;
            compareAutoStrideCounter = 0;
          }
          ImGui::SliderInt("Auto Capture Count", &compareAutoCount, 1, 120);
          ImGui::SliderInt("Auto Capture Stride", &compareAutoStride, 1, 600);
          if (compareAutoCapture) {
            ImGui::Text("Auto remaining: %d", compareAutoRemaining);
          }
          if (ImGui::Button("Capture Preset Sweep")) {
            comparePresetSweep = true;
            comparePresetIndex = 0;
            comparePresetFrameCounter = 0;
            compareAutoCapture = false;
            compareAutoRemaining = 0;
            compareRestorePending = false;
          }
          ImGui::SliderInt("Preset Settle Frames", &comparePresetSettleFrames, 1, 10);
          if (comparePresetSweep) {
            std::size_t presetCount = kComparePresets.size();
            int displayIndex =
                std::clamp(comparePresetIndex + 1, 1, static_cast<int>(presetCount));
            std::size_t labelIndex = static_cast<std::size_t>(displayIndex - 1);
            const char *label = kComparePresets[labelIndex].label;
            ImGui::Text("Preset sweep: %s (%d/%d)", label, displayIndex,
                        static_cast<int>(presetCount));
          }
          if (ImGui::Button("Capture A/B Snapshot")) {
            captureCompareSnapshot = true;
          }
        }
            ImGui::EndTabItem();
          }
          ImGui::EndTabBar();
        }
        ImGui::End();
      }

      if (curveOverlayWindowOpen) {
        ImGui::Begin("Curve Overlay", &curveOverlayWindowOpen);
        ImGui::Checkbox("Enabled", &curveOverlayEnabled);
        if (ImGui::Button("Reload") && !curveTsvPath.empty()) {
          curveOverlayLoaded = curveOverlay.LoadFromTsv(curveTsvPath);
        }
        if (!curveTsvPath.empty()) {
          ImGui::SameLine();
          ImGui::Text("%s", curveTsvPath.c_str());
        }

        if (curveTsvPath.empty()) {
          ImGui::Text("Pass --curve-tsv <path> to plot a 2-column TSV.");
        } else if (!curveOverlayLoaded) {
          ImGui::Text("Load error: %s", curveOverlay.lastError.c_str());
        } else if (curveOverlayEnabled) {
          ImVec2 plotSize = ImGui::GetContentRegionAvail();
          plotSize.y = std::max(plotSize.y, 220.0f);
          drawCurvePlot(curveOverlay, plotSize);
        }

        ImGui::End();
      }

      updateLuts(kerrSpin, adiskDensityV);
      if (!spectralLutTried) {
        spectralLutTried = true;
        spectralLutLoaded =
            loadSpectralLutAssets(spectralLutValues, spectralWavelengthMin, spectralWavelengthMax);
        if (spectralLutLoaded && !spectralLutValues.empty()) {
          if (texSpectralLUT != 0) {
            glDeleteTextures(1, &texSpectralLUT);
            texSpectralLUT = 0;
          }
          int lutSize = static_cast<int>(spectralLutValues.size());
          texSpectralLUT = createFloatTexture2D(lutSize, 1, spectralLutValues);
          spectralRadiusMin = lutRadiusMin;
          spectralRadiusMax = lutRadiusMax;
          if (spectralRadiusMax <= spectralRadiusMin) {
            spectralRadiusMin = 0.0f;
            spectralRadiusMax = 1.0f;
          }
        }
      }

      // Load Hawking radiation LUTs
      if (!hawkingLutsLoaded) {
        std::filesystem::path lutPath = "assets/luts";
        if (std::filesystem::exists(lutPath)) {
          hawkingLutsLoaded = hawkingRenderer.loadLUTs(lutPath);
          if (hawkingLutsLoaded) {
            std::cout << "Hawking radiation LUTs loaded successfully" << std::endl;
          } else {
            std::cerr << "Failed to load Hawking radiation LUTs" << std::endl;
          }
        }
      }

      const double referenceMass = physics::M_SUN;
      const double referenceRs = physics::schwarzschild_radius(referenceMass);
      const double referenceRg = physics::G * referenceMass / physics::C2;
      const double referenceA = static_cast<double>(kerrSpin) * referenceRg;
      const bool progradeSpin = kerrSpin >= 0.0f;
      const double iscoRatio =
          physics::kerr_isco_radius(referenceMass, referenceA, progradeSpin) / referenceRs;

      float schwarzschildRadius = 2.0f * blackHoleMass;
      float iscoRadius = static_cast<float>(iscoRatio) * schwarzschildRadius;
      bool computeSupported = ShaderManager::instance().canUseComputeShaders();
      bool computeActive = useComputeRaytracer && computeSupported;
      bool compareActive = compareComputeFragment && computeSupported;
      bool compareBaselineActive = compareBaselineEnabled && compareActive;
      bool adiskEnabledEffective = adiskEnabled && !compareBaselineActive;
      bool adiskParticleEffective = adiskParticle && !compareBaselineActive;
      bool enableRedshiftEffective = enableRedshift && !compareBaselineActive;
      bool useNoiseTextureEffective = useNoiseTexture && !compareBaselineActive;
      bool useGrmhdEffective = useGrmhd && !compareBaselineActive;
      bool useSpectralLutEffective = useSpectralLut && !compareBaselineActive;
      bool useGrbModulationEffective = useGrbModulation && !compareBaselineActive;
      bool enablePhotonSphereEffective = enablePhotonSphere && !compareBaselineActive;
      bool backgroundEnabledEffective =
          settings.backgroundEnabled && !compareBaselineActive;
      computeActiveForLog = computeActive;
      compareSampleSize = std::clamp(compareSampleSize, 4, 64);
      compareFrameStride = std::max(compareFrameStride, 1);
      compareAutoCount = std::max(compareAutoCount, 1);
      compareAutoStride = std::max(compareAutoStride, 1);
      if (!compareActive) {
        compareAutoCapture = false;
        compareAutoRemaining = 0;
        compareAutoStrideCounter = 0;
      }
      computeMaxSteps = std::clamp(computeMaxSteps, 10, 1000);
      computeStepSize = std::clamp(computeStepSize, 0.001f, 2.0f);
      int compareSteps = computeMaxSteps;
      float compareStepSize = computeStepSize;
      if (compareOverridesEnabled) {
        if (compareMaxStepsOverride > 0) {
          compareSteps = compareMaxStepsOverride;
        }
        if (compareStepSizeOverride > 0.0f) {
          compareStepSize = compareStepSizeOverride;
        }
      }

      grmhdEnabled = useGrmhdEffective && grmhdReady;
      spectralEnabled = useSpectralLutEffective && spectralReady;
      grbModulationEnabled = useGrbModulationEffective && grbModulationReady;
      noiseReady = useNoiseTextureEffective && texNoiseVolume != 0;
      rtti.texture3DUniforms["noiseTexture"] = noiseReady ? texNoiseVolume : fallback3D;
      rtti.texture3DUniforms["grmhdTexture"] =
          grmhdEnabled ? grmhdTexture.texture : fallback3D;
      rtti.textureUniforms["spectralLUT"] = spectralEnabled ? texSpectralLUT : fallback2D;
      rtti.textureUniforms["grbModulationLUT"] =
          grbModulationEnabled ? texGrbModulationLUT : fallback2D;
      rtti.textureUniforms["hawkingTempLUT"] = hawkingLutsLoaded ? hawkingRenderer.getTempLUTTexture() : fallback2D;
      rtti.textureUniforms["hawkingSpectrumLUT"] = hawkingLutsLoaded ? hawkingRenderer.getSpectrumLUTTexture() : fallback2D;
      rtti.floatUniforms["useNoiseTexture"] = noiseReady ? 1.0f : 0.0f;
      rtti.floatUniforms["useGrmhd"] = grmhdEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["backgroundEnabled"] =
          backgroundEnabledEffective ? 1.0f : 0.0f;
      rtti.floatUniforms["bhDebugFlags"] = static_cast<float>(integratorDebugFlags);

      InteropUniforms interop;
      interop.cameraPos = cameraPos;
      interop.cameraBasis = cameraBasis;
      interop.fovScale = fovScale;
      interop.timeSec = frameTime;
      interop.schwarzschildRadius = schwarzschildRadius;
      interop.iscoRadius = iscoRadius;
      interop.kerrSpin = kerrSpin;
      interop.depthFar = depthFar;
      if (compareActive) {
        interop.maxSteps = compareSteps;
        interop.stepSize = compareStepSize;
      } else {
        interop.maxSteps = computeMaxSteps;
        interop.stepSize = computeStepSize;
      }
      interop.adiskEnabled = adiskEnabledEffective ? 1.0f : 0.0f;
      interop.enableRedshift = enableRedshiftEffective ? 1.0f : 0.0f;
      interop.useLUTs = lutReady ? 1.0f : 0.0f;
      interop.useSpectralLUT = spectralEnabled ? 1.0f : 0.0f;
      interop.useGrbModulation = grbModulationEnabled ? 1.0f : 0.0f;
      interop.lutRadiusMin = lutRadiusMin;
      interop.lutRadiusMax = lutRadiusMax;
      interop.redshiftRadiusMin = redshiftRadiusMin;
      interop.redshiftRadiusMax = redshiftRadiusMax;
      interop.spectralRadiusMin = spectralRadiusMin;
      interop.spectralRadiusMax = spectralRadiusMax;
      interop.grbTime = grbTimeSeconds;
      interop.grbTimeMin = grbTimeMin;
      interop.grbTimeMax = grbTimeMax;

      // Convert black hole mass to grams (CGS units for Hawking calculation)
      double bhMassGrams = static_cast<double>(blackHoleMass) * physics::M_SUN;
      applyInteropUniforms(rtti, interop, compareActive, hawkingGlowEnabled,
                          hawkingTempScale, hawkingGlowIntensity, hawkingUseLUTs, bhMassGrams);

      rtti.floatUniforms["gravitationalLensing"] = gravitationalLensing ? 1.0f : 0.0f;
      rtti.floatUniforms["renderBlackHole"] = renderBlackHole ? 1.0f : 0.0f;
      rtti.floatUniforms["adiskParticle"] = adiskParticleEffective ? 1.0f : 0.0f;
      // rtti.floatUniforms["adiskDensityV"] = adiskDensityV; // Removed: consumed by LUT generation
      rtti.floatUniforms["adiskDensityH"] = adiskDensityH;
      rtti.floatUniforms["adiskHeight"] = adiskHeight;
      rtti.floatUniforms["adiskLit"] = adiskLit;
      rtti.floatUniforms["adiskNoiseLOD"] = adiskNoiseLOD;
      rtti.floatUniforms["adiskNoiseScale"] = adiskNoiseScale;
      rtti.floatUniforms["adiskSpeed"] = adiskSpeed;
      rtti.floatUniforms["dopplerStrength"] = dopplerStrength;
      rtti.floatUniforms["enablePhotonSphere"] = enablePhotonSphereEffective ? 1.0f : 0.0f;

      GLuint fragmentTarget = computeActive ? (compareActive ? texBlackholeCompare : 0)
                                            : texBlackhole;
      GLuint computeTarget = computeActive ? texBlackhole
                                           : (compareActive ? texBlackholeCompare : 0);
      if (gpuTimers.initialized && fragmentTarget != 0) {
        gpuTimers.blackholeFragment.begin();
      }
      if (fragmentTarget != 0) {
        ZoneScopedN("Blackhole Fragment");
        rtti.targetTexture = fragmentTarget;
        // std::cout << "Rendering to texture..." << std::endl;
        renderToTexture(rtti);
      }
      if (gpuTimers.initialized && fragmentTarget != 0) {
        gpuTimers.blackholeFragment.end();
      }

      if (gpuTimers.initialized && computeTarget != 0) {
        gpuTimers.blackholeCompute.begin();
      }
      if (computeTarget != 0) {
        ZoneScopedN("Blackhole Compute");
        static GLuint computeProgram = 0;
        if (computeProgram == 0) {
          computeProgram = createComputeProgram(std::string("shader/geodesic_trace.comp"));
        }

        glUseProgram(computeProgram);
        applyInteropComputeUniforms(computeProgram, interop, renderWidth, renderHeight);

        // Apply Hawking radiation uniforms
        double bhMass = static_cast<double>(blackHoleMass) * physics::M_SUN;
        applyHawkingUniforms(computeProgram, hawkingRenderer, hawkingGlowEnabled,
                           hawkingTempScale, hawkingGlowIntensity, hawkingUseLUTs, bhMass);

        GLint texUnit = 0;
        glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
        glBindTexture(GL_TEXTURE_2D, lutReady ? texEmissivityLUT : fallback2D);
        glUniform1i(glGetUniformLocation(computeProgram, "emissivityLUT"), texUnit);
        texUnit++;
        glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
        glBindTexture(GL_TEXTURE_2D, lutReady ? texRedshiftLUT : fallback2D);
        glUniform1i(glGetUniformLocation(computeProgram, "redshiftLUT"), texUnit);
        texUnit++;
        glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
        glBindTexture(GL_TEXTURE_2D, spectralEnabled ? texSpectralLUT : fallback2D);
        glUniform1i(glGetUniformLocation(computeProgram, "spectralLUT"), texUnit);
        texUnit++;
        glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
        glBindTexture(GL_TEXTURE_2D, grbModulationEnabled ? texGrbModulationLUT : fallback2D);
        glUniform1i(glGetUniformLocation(computeProgram, "grbModulationLUT"), texUnit);
        texUnit++;
        glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
        glBindTexture(GL_TEXTURE_CUBE_MAP, galaxy != 0 ? galaxy : fallbackCubemap);
        glUniform1i(glGetUniformLocation(computeProgram, "galaxy"), texUnit);
        texUnit++;
        for (int i = 0; i < kBackgroundLayers; ++i) {
          glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
          glBindTexture(GL_TEXTURE_2D,
                        backgroundTextures[static_cast<std::size_t>(i)]);
          std::string name = "backgroundLayers[" + std::to_string(i) + "]";
          glUniform1i(glGetUniformLocation(computeProgram, name.c_str()), texUnit);
          texUnit++;
        }
        glUniform1f(glGetUniformLocation(computeProgram, "backgroundEnabled"),
                    backgroundEnabledEffective ? 1.0f : 0.0f);
        glUniform1f(glGetUniformLocation(computeProgram, "bhDebugFlags"),
                    static_cast<float>(integratorDebugFlags));
        glUniform1f(glGetUniformLocation(computeProgram, "backgroundIntensity"),
                    settings.backgroundIntensity);
        for (int i = 0; i < kBackgroundLayers; ++i) {
          std::string name = "backgroundLayerParams[" + std::to_string(i) + "]";
          const auto &params = backgroundLayerParams[static_cast<std::size_t>(i)];
          glUniform4f(glGetUniformLocation(computeProgram, name.c_str()),
                      params.x, params.y, params.z, params.w);
        }
        for (int i = 0; i < kBackgroundLayers; ++i) {
          std::string name = "backgroundLayerLodBias[" + std::to_string(i) + "]";
          float bias = std::max(backgroundLayerLodBias[static_cast<std::size_t>(i)], 0.0f);
          glUniform1f(glGetUniformLocation(computeProgram, name.c_str()), bias);
        }

        glBindImageTexture(0, computeTarget, 0, GL_FALSE, 0, GL_WRITE_ONLY, GL_RGBA32F);
        GLint tileOffsetLoc = glGetUniformLocation(computeProgram, "tileOffset");
        constexpr int kGroupSize = 16;
        if (computeTiled) {
          computeTileSize = std::clamp(computeTileSize, kGroupSize, 2048);
          for (int y = 0; y < renderHeight; y += computeTileSize) {
            for (int x = 0; x < renderWidth; x += computeTileSize) {
              int tileWidth = std::min(computeTileSize, renderWidth - x);
              int tileHeight = std::min(computeTileSize, renderHeight - y);
              if (tileOffsetLoc != -1) {
                glUniform2i(tileOffsetLoc, x, y);
              }
              GLuint groupsX = static_cast<GLuint>((tileWidth + kGroupSize - 1) / kGroupSize);
              GLuint groupsY = static_cast<GLuint>((tileHeight + kGroupSize - 1) / kGroupSize);
              glDispatchCompute(groupsX, groupsY, 1);
              glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);
            }
          }
        } else {
          if (tileOffsetLoc != -1) {
            glUniform2i(tileOffsetLoc, 0, 0);
          }
          GLuint groupsX = static_cast<GLuint>((renderWidth + kGroupSize - 1) / kGroupSize);
          GLuint groupsY = static_cast<GLuint>((renderHeight + kGroupSize - 1) / kGroupSize);
          glDispatchCompute(groupsX, groupsY, 1);
          glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);
        }
        glUseProgram(0);
      }
      if (gpuTimers.initialized && computeTarget != 0) {
        gpuTimers.blackholeCompute.end();
      }

      if (compareActive && fragmentTarget != 0 && computeTarget != 0) {
        if (compareAutoCapture && compareAutoRemaining > 0) {
          compareAutoStrideCounter++;
          if (compareAutoStrideCounter >= compareAutoStride) {
            captureCompareSnapshot = true;
            compareAutoStrideCounter = 0;
            compareAutoRemaining--;
            if (compareAutoRemaining <= 0) {
              compareAutoCapture = false;
            }
          }
        }

        if (++compareFrameCounter >= compareFrameStride) {
          compareStats =
              sampleTextureDiff(texBlackhole, texBlackholeCompare, renderWidth, renderHeight,
                                compareSampleSize);
          compareFrameCounter = 0;
        }

        if (captureCompareSnapshot) {
          std::vector<float> primary;
          std::vector<float> secondary;
          if (readTextureRGBA(texBlackhole, renderWidth, renderHeight, primary) &&
              readTextureRGBA(texBlackholeCompare, renderWidth, renderHeight, secondary)) {
            compareFullStats = computeDiffStats(primary, secondary);
            std::size_t outlierCount =
                countDiffOutliers(primary, secondary, compareThreshold);
            std::size_t totalPixels = primary.size() / 4;
            std::size_t limitFromFrac = 0;
            if (compareMaxOutlierFrac > 0.0f && totalPixels > 0) {
              limitFromFrac = static_cast<std::size_t>(
                  static_cast<double>(compareMaxOutlierFrac) * static_cast<double>(totalPixels));
            }
            std::size_t limitFromCount =
                static_cast<std::size_t>(std::max(compareMaxOutliers, 0));
            std::size_t outlierLimit = std::max(limitFromCount, limitFromFrac);
            compareLastOutliers = static_cast<int>(outlierCount);
            compareLastOutlierLimit = static_cast<int>(outlierLimit);
            float outlierFrac = totalPixels > 0
                                    ? static_cast<float>(outlierCount) /
                                          static_cast<float>(totalPixels)
                                    : 0.0f;
            bool outlierGateEnabled = (compareMaxOutliers > 0) ||
                                      (compareMaxOutlierFrac > 0.0f);
            compareLastExceeded =
                compareFullStats.valid && compareFullStats.maxAbs > compareThreshold &&
                (!outlierGateEnabled || outlierCount > outlierLimit);
            if (compareLastExceeded) {
              ++compareFailureCount;
            }

            const bool computeIsPrimary = (computeTarget == texBlackhole);
            const std::string primaryTag = computeIsPrimary ? "compute" : "fragment";
            const std::string secondaryTag = computeIsPrimary ? "fragment" : "compute";
            std::string presetLabel = "custom";
            if (compareSnapshotIndex >= 0 &&
                compareSnapshotIndex < static_cast<int>(kComparePresets.size())) {
              presetLabel =
                  kComparePresets[static_cast<std::size_t>(compareSnapshotIndex)].label;
            }

            if (compareWriteOutputs) {
              writePpm(compareSnapshotPath(compareSnapshotIndex, primaryTag), primary, renderWidth,
                       renderHeight, 1.0f);
              writePpm(compareSnapshotPath(compareSnapshotIndex, secondaryTag), secondary,
                       renderWidth, renderHeight, 1.0f);
            }
            if (compareWriteDiff) {
              writeDiffPpm(compareSnapshotPath(compareSnapshotIndex, "diff"), primary, secondary,
                           renderWidth, renderHeight, compareDiffScale);
            }
            if (compareWriteSummary) {
              appendCompareSummary(compareSummaryPath(), compareSnapshotIndex, primaryTag,
                                   secondaryTag, renderWidth, renderHeight, compareFullStats,
                                   compareDiffScale, compareWriteOutputs, compareWriteDiff,
                                   compareThreshold, compareLastExceeded, glfwGetTime(), kerrSpin,
                                   grbModulationEnabled, grbTimeSeconds, compareLastOutliers,
                                   compareLastOutlierLimit, outlierFrac);
              appendCompareUniforms(compareUniformsPath(), compareSnapshotIndex, presetLabel,
                                    interop, compareBaselineActive, compareOverridesEnabled,
                                    backgroundEnabledEffective, noiseReady, grmhdEnabled,
                                    spectralEnabled, grbModulationEnabled,
                                    enablePhotonSphereEffective);
            }
            compareSnapshotIndex++;
          } else {
            compareFullStats.valid = false;
            compareLastExceeded = false;
          }
          captureCompareSnapshot = false;
        }
      } else {
        compareStats.valid = false;
        compareFullStats.valid = false;
        captureCompareSnapshot = false;
        compareLastExceeded = false;
        compareLastOutliers = 0;
        compareLastOutlierLimit = 0;
      }
    }
    if (compareRestorePending && !comparePresetSweep && comparePresetSaved &&
        !captureCompareSnapshot) {
      CameraState &camMutable = input.camera();
      camMutable = comparePresetSavedCamera;
      cameraModeIndex = comparePresetSavedMode;
      orbitRadius = comparePresetSavedOrbitRadius;
      orbitSpeed = comparePresetSavedOrbitSpeed;
      orbitTime = comparePresetSavedOrbitTime;
      kerrSpin = comparePresetSavedKerrSpin;
      comparePresetSaved = false;
      compareRestorePending = false;
    }

    if (gpuTimers.initialized) {
      gpuTimers.bloom.begin();
    }
    {
      ZoneScopedN("Bloom Brightness");
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/bloom_brightness_pass.frag";
      rtti.textureUniforms["texture0"] = texBlackhole;
      rtti.targetTexture = texBrightness;
      rtti.width = renderWidth;
      rtti.height = renderHeight;
      renderToTexture(rtti);
    }

    // Post Processing panel moved to Main Settings
    if (false) {
      ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
      ImGui::SliderInt("bloomIterations", &bloomIterations, 1, kMaxBloomIterations);
      settings.bloomIterations = bloomIterations;
      ImGui::End();
    }

    {
      ZoneScopedN("Bloom Downsample");
      for (int level = 0; level < bloomIterations; level++) {
        std::size_t levelIndex = static_cast<std::size_t>(level);
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/bloom_downsample.frag";
        rtti.textureUniforms["texture0"] =
            level == 0 ? texBrightness : texDownsampled[static_cast<std::size_t>(level - 1)];
        rtti.targetTexture = texDownsampled[levelIndex];
        int downWidth = std::max(1, renderWidth >> (level + 1));
        int downHeight = std::max(1, renderHeight >> (level + 1));
        rtti.width = downWidth;
        rtti.height = downHeight;
        renderToTexture(rtti);
      }
    }

    {
      ZoneScopedN("Bloom Upsample");
      for (int level = bloomIterations - 1; level >= 0; level--) {
        std::size_t levelIndex = static_cast<std::size_t>(level);
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/bloom_upsample.frag";
        rtti.textureUniforms["texture0"] =
            level == bloomIterations - 1 ? texDownsampled[levelIndex]
                                         : texUpsampled[static_cast<std::size_t>(level + 1)];
        rtti.textureUniforms["texture1"] =
            level == 0 ? texBrightness : texDownsampled[static_cast<std::size_t>(level - 1)];
        rtti.targetTexture = texUpsampled[levelIndex];
        int upWidth = std::max(1, renderWidth >> level);
        int upHeight = std::max(1, renderHeight >> level);
        rtti.width = upWidth;
        rtti.height = upHeight;
        renderToTexture(rtti);
      }
    }

    {
      ZoneScopedN("Bloom Composite");
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/bloom_composite.frag";
      rtti.textureUniforms["texture0"] = texBlackhole;
      rtti.textureUniforms["texture1"] = texUpsampled[0];
      rtti.targetTexture = texBloomFinal;
      rtti.width = renderWidth;
      rtti.height = renderHeight;

      if (input.isUIVisible()) {
        ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
        ImGui::SliderFloat("bloomStrength", &bloomStrength, 0.0f, 1.0f);
        settings.bloomStrength = bloomStrength;
        ImGui::End();
      }
      rtti.floatUniforms["bloomStrength"] = bloomStrength;

      renderToTexture(rtti);
    }
    if (gpuTimers.initialized) {
      gpuTimers.bloom.end();
    }

    if (gpuTimers.initialized) {
      gpuTimers.tonemap.begin();
    }
    {
      ZoneScopedN("Tonemap");
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/tonemapping.frag";
      rtti.textureUniforms["texture0"] = texBloomFinal;
      rtti.targetTexture = texTonemapped;
      rtti.width = renderWidth;
      rtti.height = renderHeight;

      if (input.isUIVisible()) {
        ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
        ImGui::Checkbox("tonemappingEnabled", &tonemappingEnabled);
        ImGui::SliderFloat("gamma", &gamma, 1.0f, 4.0f);
        settings.tonemappingEnabled = tonemappingEnabled;
        settings.gamma = gamma;
        ImGui::End();
      }
      rtti.floatUniforms["tonemappingEnabled"] = tonemappingEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["gamma"] = gamma;

      renderToTexture(rtti);
    }
    if (gpuTimers.initialized) {
      gpuTimers.tonemap.end();
    }

    static bool depthEffectsEnabled = true;
    static bool fogEnabled = true;
  static float fogDensity = 0.08f;
  static float fogStart = 0.6f;
  static float fogEnd = 0.98f;
  static float fogColor[3] = {0.06f, 0.06f, 0.10f};
    static bool edgeOutlinesEnabled = false;
    static float edgeThreshold = 0.5f;
    static float edgeWidth = 1.0f;
    static float edgeColor[3] = {1.0f, 1.0f, 1.0f};
    static bool depthDesatEnabled = true;
  static float desatStrength = 0.10f;
    static bool chromaDepthEnabled = false;
    static bool motionParallaxHint = false;
    static bool dofEnabled = false;
    static float dofFocusNear = 0.3f;
    static float dofFocusFar = 0.9f;
  static float dofMaxRadius = 2.0f;
  static float depthCurve = 1.0f;

    if (input.isUIVisible()) {
      ImGui::Begin("Depth Effects", nullptr, ImGuiWindowFlags_NoCollapse);
      ImGui::Checkbox("Enable Depth Effects", &depthEffectsEnabled);
      ImGui::SliderFloat("Depth Far", &depthFar, 10.0f, 200.0f);
      if (ImGui::Button("Preset: Subtle")) {
        depthEffectsEnabled = true;
        fogEnabled = true;
        fogDensity = 0.08f;
        fogStart = 0.6f;
        fogEnd = 0.98f;
        fogColor[0] = 0.06f;
        fogColor[1] = 0.06f;
        fogColor[2] = 0.10f;
        edgeOutlinesEnabled = false;
        edgeThreshold = 0.5f;
        edgeWidth = 1.0f;
        depthDesatEnabled = true;
        desatStrength = 0.10f;
        chromaDepthEnabled = false;
        motionParallaxHint = false;
        dofEnabled = false;
        dofFocusNear = 0.3f;
        dofFocusFar = 0.9f;
        dofMaxRadius = 2.0f;
        depthCurve = 1.0f;
        depthFar = 100.0f;
      }
      ImGui::SameLine();
      if (ImGui::Button("Preset: Cinematic")) {
        depthEffectsEnabled = true;
        fogEnabled = true;
        fogDensity = 0.3f;
        fogStart = 0.25f;
        fogEnd = 0.85f;
        fogColor[0] = 0.08f;
        fogColor[1] = 0.08f;
        fogColor[2] = 0.12f;
        edgeOutlinesEnabled = true;
        edgeThreshold = 0.5f;
        edgeWidth = 1.2f;
        depthDesatEnabled = true;
        desatStrength = 0.35f;
        chromaDepthEnabled = true;
        motionParallaxHint = false;
        dofEnabled = true;
        dofFocusNear = 0.25f;
        dofFocusFar = 0.75f;
        dofMaxRadius = 5.0f;
        depthCurve = 0.95f;
        depthFar = 100.0f;
      }
      ImGui::SameLine();
      if (ImGui::Button("Preset: Clarity")) {
        depthEffectsEnabled = true;
        fogEnabled = true;
        fogDensity = 0.12f;
        fogStart = 0.45f;
        fogEnd = 0.95f;
        fogColor[0] = 0.05f;
        fogColor[1] = 0.05f;
        fogColor[2] = 0.08f;
        edgeOutlinesEnabled = true;
        edgeThreshold = 0.42f;
        edgeWidth = 1.4f;
        depthDesatEnabled = true;
        desatStrength = 0.15f;
        chromaDepthEnabled = false;
        motionParallaxHint = false;
        dofEnabled = false;
        dofFocusNear = 0.35f;
        dofFocusFar = 0.95f;
        dofMaxRadius = 2.5f;
        depthCurve = 1.15f;
        depthFar = 100.0f;
      }
      ImGui::Separator();

      ImGui::Checkbox("Fog", &fogEnabled);
      ImGui::SliderFloat("Fog Density", &fogDensity, 0.0f, 1.0f);
      ImGui::SliderFloat("Fog Start", &fogStart, 0.0f, 1.0f);
      ImGui::SliderFloat("Fog End", &fogEnd, 0.0f, 1.0f);
      if (fogStart > fogEnd) {
        fogStart = fogEnd;
      }
      ImGui::ColorEdit3("Fog Color", fogColor);

      ImGui::Separator();
      ImGui::Checkbox("Edge Outlines", &edgeOutlinesEnabled);
      ImGui::SliderFloat("Edge Threshold", &edgeThreshold, 0.0f, 1.0f);
      ImGui::SliderFloat("Edge Width", &edgeWidth, 0.5f, 3.0f);
      ImGui::ColorEdit3("Edge Color", edgeColor);

      ImGui::Separator();
      ImGui::Checkbox("Depth Desaturation", &depthDesatEnabled);
      ImGui::SliderFloat("Desaturation", &desatStrength, 0.0f, 1.0f);
      ImGui::Checkbox("Chroma Depth", &chromaDepthEnabled);
      ImGui::Checkbox("Motion Parallax Hint", &motionParallaxHint);

      ImGui::Separator();
      ImGui::Checkbox("Depth of Field", &dofEnabled);
      ImGui::SliderFloat("DoF Focus Near", &dofFocusNear, 0.0f, 1.0f);
      ImGui::SliderFloat("DoF Focus Far", &dofFocusFar, 0.0f, 1.0f);
      if (dofFocusNear > dofFocusFar) {
        dofFocusNear = dofFocusFar;
      }
      ImGui::SliderFloat("DoF Max Radius", &dofMaxRadius, 0.0f, 12.0f);
      ImGui::SliderFloat("Depth Curve", &depthCurve, 0.5f, 2.0f);
      ImGui::End();
    }

    GLuint finalTexture = texTonemapped;
    if (depthEffectsEnabled) {
      ZoneScopedN("Depth Cues");
      if (gpuTimers.initialized) {
        gpuTimers.depth.begin();
      }
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/depth_cues.frag";
      rtti.textureUniforms["texture0"] = texTonemapped;
      rtti.textureUniforms["depthTexture"] = texBlackhole;
      rtti.targetTexture = texDepthEffects;
      rtti.width = renderWidth;
      rtti.height = renderHeight;
      rtti.floatUniforms["depthEffectsEnabled"] = 1.0f;
      rtti.floatUniforms["fogEnabled"] = fogEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["fogDensity"] = fogDensity;
      rtti.floatUniforms["fogStart"] = fogStart;
      rtti.floatUniforms["fogEnd"] = fogEnd;
      rtti.floatUniforms["fogColorR"] = fogColor[0];
      rtti.floatUniforms["fogColorG"] = fogColor[1];
      rtti.floatUniforms["fogColorB"] = fogColor[2];
      rtti.floatUniforms["edgeOutlinesEnabled"] = edgeOutlinesEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["edgeThreshold"] = edgeThreshold;
      rtti.floatUniforms["edgeWidth"] = edgeWidth;
      rtti.floatUniforms["edgeColorR"] = edgeColor[0];
      rtti.floatUniforms["edgeColorG"] = edgeColor[1];
      rtti.floatUniforms["edgeColorB"] = edgeColor[2];
      rtti.floatUniforms["depthDesatEnabled"] = depthDesatEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["desatStrength"] = desatStrength;
      rtti.floatUniforms["chromaDepthEnabled"] = chromaDepthEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["motionParallaxHint"] = motionParallaxHint ? 1.0f : 0.0f;
      rtti.floatUniforms["dofEnabled"] = dofEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["dofFocusNear"] = dofFocusNear;
      rtti.floatUniforms["dofFocusFar"] = dofFocusFar;
      rtti.floatUniforms["dofMaxRadius"] = dofMaxRadius;
      rtti.floatUniforms["depthCurve"] = depthCurve;
      renderToTexture(rtti);
      finalTexture = texDepthEffects;
      if (gpuTimers.initialized) {
        gpuTimers.depth.end();
      }
    }

    // Re-open Viewport to render the scene image
    ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(0.0f, 0.0f));
    ImGui::Begin("Viewport", nullptr, ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse | ImGuiWindowFlags_NoTitleBar);
    viewportSize = ImGui::GetContentRegionAvail();

    // ---------------------------------------------------------
    // SCENE COMPOSITION (Post-process overlay passes)
    // ---------------------------------------------------------
    // Render wiregrid and overlays into the final texture before display
    {
        static GLuint sceneFbo = 0;
        if (sceneFbo == 0) {
            glGenFramebuffers(1, &sceneFbo);
        }
        glBindFramebuffer(GL_FRAMEBUFFER, sceneFbo);
        glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, finalTexture, 0);
        glViewport(0, 0, renderWidth, renderHeight);

        // 1. Wiregrid
        if (wiregridEnabled && wiregridMesh.vertexCount > 0) {
            static GLuint wiregridProgram = 0;
            if (wiregridProgram == 0) {
                wiregridProgram = createShaderProgram(std::string("shader/wiregrid.vert"),
                                                    std::string("shader/wiregrid.frag"));
            }
            glm::mat4 viewProj = projectionMatrix * gizmoViewMatrix;
            glUseProgram(wiregridProgram);
            GLint viewProjLoc = glGetUniformLocation(wiregridProgram, "viewProj");
            if (viewProjLoc != -1) glUniformMatrix4fv(viewProjLoc, 1, GL_FALSE, glm::value_ptr(viewProj));
            
            GLint colorLoc = glGetUniformLocation(wiregridProgram, "color");
            if (colorLoc != -1) glUniform4f(colorLoc, wiregridColor.r, wiregridColor.g, wiregridColor.b, wiregridColor.a);
            
            GLint timeLoc = glGetUniformLocation(wiregridProgram, "time");
            if (timeLoc != -1) glUniform1f(timeLoc, frameTime);
            
            GLint camPosLoc = glGetUniformLocation(wiregridProgram, "cameraPos");
            if (camPosLoc != -1) glUniform3fv(camPosLoc, 1, glm::value_ptr(cameraPos));

            glEnable(GL_BLEND);
            glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
            glBindVertexArray(wiregridMesh.vao);
            glDrawArrays(GL_LINES, 0, wiregridMesh.vertexCount);
            glBindVertexArray(0);
            glDisable(GL_BLEND);
            glUseProgram(0);
        }

        // 2. GRMHD Slice
        if (grmhdSliceEnabled && grmhdReady) {
            ZoneScopedN("GRMHD Slice");
            grmhdSliceAxis = std::clamp(grmhdSliceAxis, 0, 2);
            grmhdSliceChannel = std::clamp(grmhdSliceChannel, 0, 3);
            grmhdSliceCoord = std::clamp(grmhdSliceCoord, 0.0f, 1.0f);
            grmhdSliceSize = std::clamp(grmhdSliceSize, 64, 1024);

            const std::size_t channelIndex = static_cast<std::size_t>(grmhdSliceChannel);
            if (grmhdSliceAutoRange && channelIndex < grmhdTexture.minValues.size() &&
                channelIndex < grmhdTexture.maxValues.size()) {
                grmhdSliceMin = grmhdTexture.minValues[channelIndex];
                grmhdSliceMax = grmhdTexture.maxValues[channelIndex];
            }
            if (grmhdSliceMax <= grmhdSliceMin) {
                grmhdSliceMax = grmhdSliceMin + 1.0f;
            }

            if (texGrmhdSlice == 0 || grmhdSliceSizeCached != grmhdSliceSize) {
                if (texGrmhdSlice != 0) {
                    glDeleteTextures(1, &texGrmhdSlice);
                    texGrmhdSlice = 0;
                }
                texGrmhdSlice = createColorTexture32f(grmhdSliceSize, grmhdSliceSize);
                grmhdSliceSizeCached = grmhdSliceSize;
            }

            RenderToTextureInfo sliceRtti;
            sliceRtti.fragShader = "shader/grmhd_slice.frag";
            sliceRtti.texture3DUniforms["grmhdTexture"] = grmhdTexture.texture;
            sliceRtti.textureUniforms["colorMap"] = colorMap;
            sliceRtti.floatUniforms["sliceAxis"] = static_cast<float>(grmhdSliceAxis);
            sliceRtti.floatUniforms["sliceCoord"] = grmhdSliceCoord;
            sliceRtti.floatUniforms["sliceChannel"] = static_cast<float>(grmhdSliceChannel);
            sliceRtti.floatUniforms["sliceMin"] = grmhdSliceMin;
            sliceRtti.floatUniforms["sliceMax"] = grmhdSliceMax;
            sliceRtti.floatUniforms["useColorMap"] = grmhdSliceUseColorMap ? 1.0f : 0.0f;
            sliceRtti.targetTexture = texGrmhdSlice;
            sliceRtti.width = grmhdSliceSize;
            sliceRtti.height = grmhdSliceSize;
            if (gpuTimers.initialized) {
                gpuTimers.grmhdSlice.begin();
            }
            renderToTexture(sliceRtti); // Note: renderToTexture manages its own FBO binding
            if (gpuTimers.initialized) {
                gpuTimers.grmhdSlice.end();
            }
            
            // Re-bind Scene FBO to draw the slice texture on top? 
            // Actually, renderToTexture renders TO texGrmhdSlice.
            // We need to composite texGrmhdSlice onto the scene?
            // The original code rendered the slice to a separate texture, then displayed it in ImGui Image?
            // "ImGui::Image(sliceId, ...)" in the UI panel.
            // So we don't need to composite it here.
            
            // Restore FBO for subsequent passes if any
            glBindFramebuffer(GL_FRAMEBUFFER, sceneFbo);
        }

        // 3. RmlUi Overlay
        if (rmluiReady) {
            rmluiOverlay.render();
        }

        // 4. HUD Overlays (Perf/Controls)
        // Note: These renderers assume default framebuffer dimensions. 
        // We set viewport to renderWidth/Height, which matches our FBO.
        if (controlsOverlayEnabled && !input.isUIVisible()) {
             if (!controlsOverlayReady) {
                HudOverlayOptions opts;
                opts.scale = controlsOverlayScale;
                opts.margin = 16.0f;
                opts.align = HudOverlayOptions::Align::Left;
                controlsOverlay.setOptions(opts);
                controlsOverlayReady = true;
             }
             if (controlsOverlayReady) controlsOverlay.render(renderWidth, renderHeight);
             if (perfOverlayReady) perfOverlay.render(renderWidth, renderHeight);
        }

        glBindFramebuffer(GL_FRAMEBUFFER, 0);
    }

    // Draw Final Texture to Viewport
    ImGui::Image(reinterpret_cast<void*>(static_cast<intptr_t>(finalTexture)), viewportSize, ImVec2(0, 1), ImVec2(1, 0));
    
    // Enable mouse/keyboard interaction when hovering the viewport
    bool isViewportHovered = ImGui::IsItemHovered();
    InputManager::instance().setIgnoreGuiCapture(isViewportHovered);

    // Gizmo
    if (gizmoEnabled) {
        ImGuizmo::SetDrawlist();
        ImVec2 windowPos = ImGui::GetWindowPos();
        ImGuizmo::SetRect(windowPos.x, windowPos.y, viewportSize.x, viewportSize.y);
        ImGuizmo::Manipulate(glm::value_ptr(gizmoViewMatrix), glm::value_ptr(projectionMatrix),
                           gizmoOperation, gizmoMode, glm::value_ptr(gizmoTransform));
    }

    ImGui::End(); // End Viewport
    ImGui::PopStyleVar(); // WindowPadding

    if (input.isUIVisible()) {
      renderControlsHelpPanel();
      renderControlsSettingsPanel(cameraModeIndex, orbitRadius, orbitSpeed);
      renderDisplaySettingsPanel(window, swapInterval, renderScale, windowWidth, windowHeight);
      renderBackgroundPanel(backgroundAssets, backgroundIndex,
                            settings.backgroundParallaxStrength,
                            settings.backgroundDriftStrength, backgroundLayerDepth,
                            backgroundLayerScale, backgroundLayerIntensity,
                            backgroundLayerLodBias);
      renderWiregridPanel(wiregridEnabled, wiregridParams, wiregridColor);
      renderRmlUiPanel(rmluiEnabled);
      renderGizmoPanel(gizmoEnabled, gizmoOperation, gizmoMode, gizmoTransform);
      renderPerformancePanel(gpuTimingEnabled, gpuTimers, timingHistory, cpuFrameMs,
                             perfOverlayEnabled, perfOverlayScale, depthPrepassEnabled);
    }

    // ImGui Render
    ImGui::Render();
    ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());
    
    // Update Platform Windows (Docking)
    if (ImGui::GetIO().ConfigFlags & ImGuiConfigFlags_ViewportsEnable) {
        GLFWwindow* backup_current_context = glfwGetCurrentContext();
        ImGui::UpdatePlatformWindows();
        ImGui::RenderPlatformWindowsDefault();
        glfwMakeContextCurrent(backup_current_context);
    }

    if (gpuTimingLogEnabled && gpuTimers.initialized) {
      gpuTimingLogCounter++;
      if (gpuTimingLogCounter >= gpuTimingLogStride) {
        appendGpuTimingSample(gpuTimingPath(), gpuTimingLogIndex++, renderWidth, renderHeight,
                              cpuFrameMs, gpuTimers,
                              computeActiveForLog, kerrSpin, glfwGetTime());
        gpuTimingLogCounter = 0;
      }
    }

    if (gpuTimers.initialized) {
      gpuTimers.swap();
    }
    FrameMark;
    glfwSwapBuffers(window);
  }

  {
    int finalWindowWidth = 0;
    int finalWindowHeight = 0;
    glfwGetWindowSize(window, &finalWindowWidth, &finalWindowHeight);
    if (!InputManager::instance().isFullscreen()) {
      settings.windowWidth = finalWindowWidth;
      settings.windowHeight = finalWindowHeight;
    }
    settings.fullscreen = InputManager::instance().isFullscreen();
    settings.swapInterval = swapInterval;
    settings.renderScale = renderScale;
    settings.cameraMode = cameraModeIndex;
    settings.orbitRadius = orbitRadius;
    settings.orbitSpeed = orbitSpeed;
  }

  if (controlsOverlayReady) {
    controlsOverlay.shutdown();
  }
  if (rmluiReady) {
    rmluiOverlay.shutdown();
  }

  // Explicitly clean up static resources before GL context destruction
  noiseCache.cleanup();
  hawkingRenderer.cleanup();
  if (grmhdTexture.texture != 0) {
    destroyGrmhdPackedTexture(grmhdTexture);
  }

    cleanup(window);
    return 0;
#if BLACKHOLE_HAS_CPPTRACE
  } catch (const cpptrace::exception &err) {
    std::fprintf(stderr, "Unhandled cpptrace exception: %s\n", err.what());
    err.trace().print();
    return 1;
  } catch (const std::exception &err) {
    std::fprintf(stderr, "Unhandled std::exception: %s\n", err.what());
    cpptrace::generate_trace(1).print();
    return 1;
  } catch (...) {
    std::fprintf(stderr, "Unhandled non-standard exception\n");
    cpptrace::generate_trace(1).print();
    return 1;
  }
#else
  } catch (const std::exception &err) {
    std::fprintf(stderr, "Unhandled std::exception: %s\n", err.what());
    return 1;
  } catch (...) {
    std::fprintf(stderr, "Unhandled non-standard exception\n");
    return 1;
  }
#endif
}
