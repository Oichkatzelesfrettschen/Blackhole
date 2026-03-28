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
#include <algorithm>
#include <cassert>
#include <cmath>
#include <csignal>
#include <cstdio>
#include <cstring>

#include <glbinding/gl/bitfield.h>
#include <glbinding/gl/boolean.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <glbinding/glbinding.h>
#include <sys/types.h>
#include <unistd.h>

#include <cpptrace/basic.hpp>
#include <cpptrace/exceptions.hpp>
#include <cpptrace/forward.hpp>
#include <cpptrace/utils.hpp>
#include <glm/ext/matrix_clip_space.hpp>
#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/matrix_transform.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/geometric.hpp>
#include <glm/trigonometric.hpp>
#include <nlohmann/json_fwd.hpp>

// C++ system headers
#include <array>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <ios>
#include <iostream>
#include <limits>
#include <map>
#include <ostream>
#include <sstream>
#include <string>
#include <thread>
#include <utility>
#include <vector>

// Third-party library headers
#include "constants.h"
#include "kerr.h"
#include "schwarzschild.h"
#ifndef BLACKHOLE_HAS_CPPTRACE
#if __has_include(<cpptrace/cpptrace.hpp>)
#define BLACKHOLE_HAS_CPPTRACE 1
#else
#define BLACKHOLE_HAS_CPPTRACE 0
#endif
#endif
#if BLACKHOLE_HAS_CPPTRACE
#endif
#include <GLFW/glfw3.h>
#include <imgui.h>
#include <imgui_internal.h>
#include <ImGuizmo.h>
#include <implot.h>

#include <glm/gtc/type_ptr.hpp>
#include <nlohmann/json.hpp>

// Local headers
#include "GLDebugMessageCallback.h"
#include "grmhd_packed_loader.h"
#include "grmhd_pbo_uploader.h"
#include "grmhd_streaming.h"
#include "hud_overlay.h"
#include "imgui_impl_glfw.h"
#include "imgui_impl_opengl3.h"
#include "input.h"
#include "overlay.h"
#include "physics/hawking_renderer.h"
#include "physics/lut.h"
#include "physics/synchrotron.h"
#include "render.h"
#include "render/noise_texture_cache.h"
#include "rmlui_overlay.h"
#include "settings.h"
#include "shader.h"
#include "shader_manager.h"
#include "texture.h"
#include <stb_image_write.h>
#include "cinematic.h"
#include "tracy_support.h"

#ifndef BLACKHOLE_HAS_CUDA
#define BLACKHOLE_HAS_CUDA 0
#endif
#ifndef BLACKHOLE_APP_VARIANT_GLSL_ONLY
#define BLACKHOLE_APP_VARIANT_GLSL_ONLY 0
#endif
#ifndef BLACKHOLE_APP_VARIANT_CUDA_ONLY
#define BLACKHOLE_APP_VARIANT_CUDA_ONLY 0
#endif
#if BLACKHOLE_APP_VARIANT_GLSL_ONLY && BLACKHOLE_APP_VARIANT_CUDA_ONLY
#error "Blackhole desktop variant cannot be both GLSL-only and CUDA-only"
#endif
#if BLACKHOLE_APP_VARIANT_CUDA_ONLY && !BLACKHOLE_HAS_CUDA
#error "Blackhole CUDA-only desktop variant requires BLACKHOLE_HAS_CUDA=1"
#endif
#if BLACKHOLE_HAS_CUDA
#include "cuda/cuda_render_manager.h"
#endif

namespace { // NOLINT(misc-use-anonymous-namespace) -- file-scope helpers

/** @brief Active camera control mode governing how cameraPos is computed each frame. */
enum class CameraMode { Input = 0, Front, Top, Orbit };

constexpr int K_BACKGROUND_LAYERS = 3;
constexpr bool kAppVariantGlslOnly = BLACKHOLE_APP_VARIANT_GLSL_ONLY != 0;
constexpr bool kAppVariantCudaOnly = BLACKHOLE_APP_VARIANT_CUDA_ONLY != 0;
constexpr const char *kWindowTitle = kAppVariantCudaOnly
                                         ? "BlackholeCUDA"
                                         : (kAppVariantGlslOnly ? "BlackholeGLSL" : "Blackhole");

#if BLACKHOLE_HAS_CPPTRACE
namespace {
constexpr std::size_t K_TRACE_MAX_FRAMES = 64;
volatile sig_atomic_t gHandlingSignal = 0;
bool gCanSignalSafeUnwind = false;
bool gCanSafeObjectInfo = false;

std::size_t cstrLength(const char *str) {
  std::size_t length = 0;
  while (str[length] != '\0') {
    ++length;
  }
  return length;
}

void writeStderr(const char *str) {
  ssize_t const rc = write(STDERR_FILENO, str, cstrLength(str));
  (void)rc;
}

void writeDec(std::size_t value) {
  char buf[32];
  std::size_t i = 0;
  do { // NOLINT(cppcoreguidelines-avoid-do-while) -- digit extraction requires do-while
    buf[i++] = static_cast<char>('0' + (value % 10));
    value /= 10;
  } while (value != 0 && i < sizeof(buf));
  for (std::size_t j = 0; j < i / 2; ++j) {
    char const tmp = buf[j];
    buf[j] = buf[i - 1 - j];
    buf[i - 1 - j] = tmp;
  }
  ssize_t const rc = write(STDERR_FILENO, buf, i);
  (void)rc;
}

void writeHex(uintptr_t value) {
  static constexpr char kHex[] = "0123456789abcdef";
  char buf[2 + (sizeof(uintptr_t) * 2)];
  buf[0] = '0';
  buf[1] = 'x';
  for (std::size_t i = 0; i < sizeof(uintptr_t) * 2; ++i) {
    buf[2 + (sizeof(uintptr_t) * 2) - 1 - i] = kHex[value & 0xF];
    value >>= 4;
  }
  ssize_t const rc = write(STDERR_FILENO, buf, sizeof(buf));
  (void)rc;
}

const char *signalName(int sig) {
  switch (sig) {
  case SIGSEGV:
    return "SIGSEGV";
  case SIGABRT:
    return "SIGABRT";
  case SIGFPE:
    return "SIGFPE";
  case SIGILL:
    return "SIGILL";
  case SIGBUS: // NOLINT(misc-include-cleaner) -- SIGBUS is POSIX, provided via <csignal> on
               // Linux/glibc
    return "SIGBUS";
  case SIGTERM:
    return "SIGTERM";
  default:
    return "SIGNAL";
  }
}

void crashSignalHandler(int sig) {
  if (gHandlingSignal != 0) {
    _Exit(128 + sig);
  }
  gHandlingSignal = 1;

  writeStderr("\n==== Blackhole crash signal: ");
  writeStderr(signalName(sig));
  writeStderr(" ====\n");

  if (!gCanSignalSafeUnwind) {
    writeStderr("cpptrace: signal-safe unwind unavailable\n");
    std::signal(sig, SIG_DFL); // NOLINT(cert-err33-c) -- signal handler, cannot check return
    std::raise(sig);           // NOLINT(cert-err33-c) -- signal handler, cannot check return
    _Exit(128 + sig);
  }

  cpptrace::frame_ptr frames[K_TRACE_MAX_FRAMES];
  std::size_t const count = cpptrace::safe_generate_raw_trace(frames, K_TRACE_MAX_FRAMES, 1);
  for (std::size_t i = 0; i < count; ++i) {
    writeStderr("#");
    writeDec(i);
    writeStderr(" ");
    writeHex(reinterpret_cast<uintptr_t>(frames[i]));
    if (gCanSafeObjectInfo) {
      cpptrace::safe_object_frame objectFrame{};
      cpptrace::get_safe_object_frame(frames[i], &objectFrame);
      if (objectFrame.object_path[0] != '\0') {
        writeStderr(" ");
        writeStderr(objectFrame.object_path);
        writeStderr(" +");
        writeHex(reinterpret_cast<uintptr_t>(objectFrame.address_relative_to_object_start));
      }
    }
    writeStderr("\n");
  }

  std::signal(sig, SIG_DFL); // NOLINT(cert-err33-c) -- signal handler, cannot check return
  std::raise(sig);           // NOLINT(cert-err33-c) -- signal handler, cannot check return
  _Exit(128 + sig);
}

void installCrashHandlers() {
  cpptrace::use_default_stderr_logger();
  cpptrace::register_terminate_handler();
  gCanSignalSafeUnwind = cpptrace::can_signal_safe_unwind();
  gCanSafeObjectInfo = cpptrace::can_get_safe_object_frame();
  if (!gCanSignalSafeUnwind) {
    std::fprintf(stderr, // NOLINT(cert-err33-c) -- informational message, return unused
                 "cpptrace: signal-safe unwinding unavailable; signal crashes will be limited\n");
  }

  std::signal(SIGSEGV,
              crashSignalHandler); // NOLINT(cert-err33-c) -- signal handler, cannot check return
  std::signal(SIGABRT,
              crashSignalHandler); // NOLINT(cert-err33-c) -- signal handler, cannot check return
  std::signal(SIGFPE,
              crashSignalHandler); // NOLINT(cert-err33-c) -- signal handler, cannot check return
  std::signal(SIGILL,
              crashSignalHandler); // NOLINT(cert-err33-c) -- signal handler, cannot check return
  std::signal(SIGBUS,
              crashSignalHandler); // NOLINT(cert-err33-c) -- signal handler, cannot check return
  std::signal(SIGTERM,
              crashSignalHandler); // NOLINT(cert-err33-c) -- signal handler, cannot check return
}
} // namespace
#else
static void installCrashHandlers() {}
#endif

namespace {
std::filesystem::path gResourceRoot = ".";

bool isValidResourceRoot(const std::filesystem::path &root) {
  std::error_code ec;
  return std::filesystem::exists(root / "shader" / "simple.vert", ec) &&
         std::filesystem::exists(root / "assets" / "backgrounds" / "manifest.json", ec) &&
         std::filesystem::exists(root / "src" / "main.cpp", ec);
}

std::filesystem::path detectResourceRoot(const char *argv0) {
  std::error_code ec;
  std::vector<std::filesystem::path> seeds;
  seeds.push_back(std::filesystem::current_path(ec));
  if (argv0 != nullptr && argv0[0] != '\0') {
    std::filesystem::path const exePath = std::filesystem::absolute(argv0, ec);
    if (!ec) {
      seeds.push_back(exePath.parent_path());
    }
  }

  for (const auto &seed : seeds) {
    std::filesystem::path probe = seed;
    while (!probe.empty()) {
      if (isValidResourceRoot(probe)) {
        return probe;
      }
      std::filesystem::path const parent = probe.parent_path();
      if (parent == probe) {
        break;
      }
      probe = parent;
    }
  }
  return std::filesystem::current_path(ec);
}

std::string resourcePath(std::string_view relativePath) {
  return (gResourceRoot / std::filesystem::path(relativePath)).string();
}
} // namespace

/**
 * @brief Convert spherical yaw/pitch angles to a Cartesian camera position.
 *
 * @param yawDeg   Horizontal rotation in degrees (0 = +Z axis).
 * @param pitchDeg Vertical elevation in degrees (positive = above equator).
 * @param radius   Distance from origin in world units.
 * @return World-space camera position on the sphere of the given radius.
 */
glm::vec3 cameraPositionFromYawPitch(float yawDeg, float pitchDeg, float radius) {
  float const yawRad = glm::radians(yawDeg);
  float const pitchRad = glm::radians(pitchDeg);
  return {radius * std::cos(pitchRad) * std::sin(yawRad), radius * std::sin(pitchRad),
          radius * std::cos(pitchRad) * std::cos(yawRad)};
}

/**
 * @brief Build an orthonormal camera basis (right, up, forward) from a look-at pair plus roll.
 *
 * Handles the degenerate case where forward is nearly parallel to world-up by
 * falling back to the +Z world axis as the up reference.
 *
 * @param cameraPos World-space camera origin.
 * @param target    World-space look-at point.
 * @param rollDeg   Camera roll in degrees applied after the standard basis is constructed.
 * @return Column-major mat3 with columns [right, up, forward].
 */
glm::mat3 buildCameraBasis(const glm::vec3 &cameraPos, const glm::vec3 &target, float rollDeg) {
  glm::vec3 const forward = glm::normalize(target - cameraPos);
  glm::vec3 worldUp(0.0f, 1.0f, 0.0f);
  if (std::abs(glm::dot(forward, worldUp)) > 0.99f) {
    worldUp = glm::vec3(0.0f, 0.0f, 1.0f);
  }

  glm::vec3 right = glm::normalize(glm::cross(forward, worldUp));
  glm::vec3 up = glm::normalize(glm::cross(right, forward));

  if (std::abs(rollDeg) > 0.001f) {
    float const rollRad = glm::radians(rollDeg);
    float const cosRoll = std::cos(rollRad);
    float const sinRoll = std::sin(rollRad);
    glm::vec3 const rolledRight = right * cosRoll + up * sinRoll;
    glm::vec3 const rolledUp = -right * sinRoll + up * cosRoll;
    right = rolledRight;
    up = rolledUp;
  }

  return {right, up, forward};
}

struct ShowcaseOrbitComposition {
  const char *name;
  const char *backgroundId;
  float frameOffsetX;
  float frameOffsetY;
  float pitchDeg;
  float distance;
  float fovDeg;
  float exposure;
  float backgroundIntensity;
  float backgroundYawDeg;
  float backgroundPitchDeg;
  float backgroundOffsetX;
  float backgroundOffsetY;
  float sweepDeg;
};

constexpr std::array<ShowcaseOrbitComposition, 5> K_SHOWCASE_ORBIT_COMPOSITIONS = {{
    {"centered", "nasa_deep_starmap_galactic", 0.0f, 0.0f, -8.0f, 21.0f, 60.0f, 3.05f, 0.74f, -18.0f, 6.0f, 0.00f, 0.00f, 8.0f},
    {"left-third", "nasa_deep_starmap", 0.18f, 0.03f, -8.0f, 23.0f, 58.0f, 2.95f, 0.76f, -34.0f, 7.0f, 0.05f, -0.02f, 7.0f},
    {"right-third", "nasa_deep_starmap_galactic", -0.18f, 0.03f, -8.0f, 23.0f, 58.0f, 2.95f, 0.76f, 18.0f, 7.0f, -0.05f, -0.02f, 7.0f},
    {"wide-left", "eso_milkyway_brunier", 0.12f, -0.02f, -7.0f, 27.5f, 54.0f, 2.75f, 0.70f, -42.0f, 8.0f, 0.08f, -0.03f, 6.0f},
    {"wide-right", "nasa_deep_starmap_galactic", -0.12f, -0.02f, -7.0f, 27.5f, 54.0f, 2.9f, 0.80f, 26.0f, 8.0f, -0.08f, -0.03f, 6.0f},
}};

const ShowcaseOrbitComposition *findShowcaseOrbitComposition(std::string_view name) {
  for (const auto &composition : K_SHOWCASE_ORBIT_COMPOSITIONS) {
    if (name == composition.name) {
      return &composition;
    }
  }
  return nullptr;
}

bool readTextFile(const std::string &path, std::string &out) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::ostringstream buffer;
  buffer << file.rdbuf();
  out = buffer.str();
  return !out.empty();
}

void printUsage(const char *argv0) {
  std::printf("Usage: %s [--curve-tsv <path>] [--export-frame <path.png>]"
              " [--record-frames <dir> <N>] [--record-profile <name>]\n", argv0);
  std::printf("  --curve-tsv <path>       Load a 2-column TSV and plot it in ImGui.\n");
  std::printf("  --export-frame <path>    Render one frame, save as PNG, then exit.\n");
  std::printf("  --record-frames <dir> N  Record N profile-driven frames as PNG into <dir>.\n");
  std::printf("                           N defaults to %d (3 min @ 60 fps).\n",
              K_CINEMATIC_FRAMES);
  std::printf("  --record-profile <name>  Recording profile: cinematic | compare-orbit-near | showcase-orbit.\n");
  std::printf("  --start-frame N          Start recording from frame N (default: 0).\n");
  std::printf("  --record-yaw <deg>       Override record camera yaw.\n");
  std::printf("  --record-pitch <deg>     Override record camera pitch.\n");
  std::printf("  --record-distance <r>    Override record camera distance.\n");
  std::printf("  --record-fov <deg>       Override record camera field of view.\n");
  std::printf("  --record-exposure <x>    Override record tone-map exposure.\n");
  std::printf("  --record-sweep-deg <x>   Override orbit sweep degrees across frames.\n");
  std::printf("  --record-composition <n> Showcase framing: centered | left-third | right-third | wide-left | wide-right.\n");
  std::printf("  --record-frame-x <n>     Override horizontal framing offset in half-frame units.\n");
  std::printf("  --record-frame-y <n>     Override vertical framing offset in half-frame units.\n");
  std::printf("  --record-background-id <id>  Override showcase background asset id.\n");
  std::printf("  --record-bg-yaw <deg>    Override showcase background yaw.\n");
  std::printf("  --record-bg-pitch <deg>  Override showcase background pitch.\n");
}

void drawCurvePlot(const OverlayCurve2D &curve, const ImVec2 &size) {
  ImDrawList *drawList = ImGui::GetWindowDrawList();
  ImVec2 const p0 = ImGui::GetCursorScreenPos();
  ImVec2 const p1 = ImVec2(p0.x + size.x, p0.y + size.y);

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
  ImVec2 const q0 = ImVec2(p0.x + pad, p0.y + pad);
  ImVec2 const q1 = ImVec2(p1.x - pad, p1.y - pad);
  float const w = std::max(1.0f, q1.x - q0.x);
  float const h = std::max(1.0f, q1.y - q0.y);

  std::vector<ImVec2> pts;
  pts.reserve(curve.points.size());
  for (const auto &pt : curve.points) {
    float const nx = (pt.x - curve.min.x) / xSpan;
    float const ny = (pt.y - curve.min.y) / ySpan;
    float const px = q0.x + (nx * w);
    float const py = q1.y - (ny * h);
    pts.emplace_back(px, py);
  }

  if (pts.size() >= 2) {
    drawList->AddPolyline(pts.data(), static_cast<int>(pts.size()), IM_COL32(80, 200, 255, 255), 0,
                          2.0f);
  }

  ImGui::Text("x:[%.4g, %.4g]  y:[%.4g, %.4g]  n=%d", static_cast<double>(curve.min.x),
              static_cast<double>(curve.max.x), static_cast<double>(curve.min.y),
              static_cast<double>(curve.max.y), static_cast<int>(curve.points.size()));
}

bool hasExtension(const char *name) {
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

bool supportsDrawId() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool const versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  return versionIs46 || hasExtension("GL_ARB_shader_draw_parameters");
}

bool supportsMultiDrawIndirect() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool const versionIs43 = (major > 4) || (major == 4 && minor >= 3);
  return versionIs43 || hasExtension("GL_ARB_multi_draw_indirect");
}

bool supportsIndirectCount() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool const versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  return versionIs46 || hasExtension("GL_ARB_indirect_parameters");
}

/** @brief Metadata for a single background skybox asset loaded from manifest.json. */
struct BackgroundAsset {
  std::string id;        ///< Unique asset identifier matching the manifest "id" field.
  std::string title;     ///< Human-readable display name shown in the UI.
  std::string path;      ///< Relative file path to the 2D background image on disk.
  std::string skyboxDir; ///< Directory containing 6 cubemap face PNGs (empty = use default).
};

/**
 * @brief GPU-side draw command for glMultiDrawArraysIndirect.
 *
 * Layout matches the OpenGL specification for GL_DRAW_ARRAYS_INDIRECT_BUFFER.
 */
struct DrawArraysIndirectCommand {
  GLuint count = 0;        ///< Number of vertices to draw.
  GLuint primCount = 0;    ///< Number of instances.
  GLuint first = 0;        ///< Starting index in the enabled arrays.
  GLuint baseInstance = 0; ///< Base instance for instanced attributes.
};

/**
 * @brief Per-instance data uploaded to the GPU for instanced background rendering.
 *
 * Matches the std140 layout expected by the corresponding GLSL shader.
 */
struct DrawInstanceGpu {
  glm::vec4 offsetScale; ///< xy = NDC offset, zw = scale factors.
  glm::vec4 tint;        ///< RGBA tint multiplier applied in the fragment shader.
  glm::vec4 flags;       ///< Bit-packed feature flags (x = layer index, etc.).
};

/**
 * @brief Parameters for the Boyer-Lindquist coordinate wiregrid overlay.
 *
 * Controls the fragment-shader wiregridOverlay() call (wiregrid.glsl) and the
 * matching CUDA kernel path.  The overlay replaces the former Euclidean
 * Flamm's-paraboloid mesh, which was geometrically inconsistent with the
 * ray-traced geodesic view.
 */
struct WiregridParams {
  bool  showErgosphere = true; ///< Render ergosphere boundary and interior glow.
  float gridScale      = 1.0f; ///< Grid density: 1.0 = pi/6 angular spacing; >1 = denser.
};

std::vector<BackgroundAsset> loadBackgroundAssets() {
  std::vector<BackgroundAsset> assets;
  std::string text;
  if (!readTextFile(resourcePath("assets/backgrounds/manifest.json"), text)) {
    return assets;
  }
  auto json = nlohmann::json::parse(text, nullptr, false);
  if (json.is_discarded() || !json.contains("assets") || !json.at("assets").is_array()) {
    return assets;
  }
  for (const auto &entry : json.at("assets")) {
    BackgroundAsset asset;
    asset.id = entry.value("id", "");
    asset.title = entry.value("title", asset.id);
    asset.path = entry.value("path", "");
    asset.skyboxDir = entry.value("skyboxDir", "");
    if (!asset.path.empty() && !std::filesystem::path(asset.path).is_absolute()) {
      asset.path = resourcePath(asset.path);
    }
    if (!asset.skyboxDir.empty() && !std::filesystem::path(asset.skyboxDir).is_absolute()) {
      asset.skyboxDir = resourcePath(asset.skyboxDir);
    }
    if (!asset.id.empty() && !asset.path.empty()) {
      assets.push_back(std::move(asset));
    }
  }
  return assets;
}

int findBackgroundIndex(const std::vector<BackgroundAsset> &assets, const std::string &id) {
  for (std::size_t i = 0; i < assets.size(); ++i) {
    if (assets.at(i).id == id) {
      return static_cast<int>(i);
    }
  }
  return 0;
}

bool parseJsonNumber(const std::string &text, const std::string &key, double &out) {
  std::string const needle = "\"" + key + "\"";
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

/** @brief Summary statistics for a per-pixel difference image used in compute/fragment parity tests. */
struct DiffStats {
  float meanAbs = 0.0f; ///< Mean absolute per-channel difference across sampled pixels.
  float maxAbs  = 0.0f; ///< Maximum absolute per-channel difference.
  float rms     = 0.0f; ///< Root-mean-square per-channel difference.
  bool  valid   = false; ///< False if inputs were invalid or no pixels were sampled.
};

DiffStats sampleTextureDiff(GLuint texA, GLuint texB, int width, int height, int sampleSize) {
  DiffStats stats;
  if (texA == 0 || texB == 0 || width <= 0 || height <= 0 || sampleSize <= 0) {
    return stats;
  }

  const int sampleW = std::min(sampleSize, width);
  const int sampleH = std::min(sampleSize, height);
  const int offsetX = (width - sampleW) / 2;
  const int offsetY = (height - sampleH) / 2;
  const auto pixelCount = static_cast<std::size_t>(sampleW) * static_cast<std::size_t>(sampleH);
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
      double const diff =
          std::abs(static_cast<double>(dataA.at(i + c)) - static_cast<double>(dataB.at(i + c)));
      total += diff;
      totalSq += diff * diff;
      maxAbs = std::max(maxAbs, diff);
    }
  }

  const auto denom = static_cast<double>(pixelCount * 3);
  if (denom > 0.0) {
    stats.meanAbs = static_cast<float>(total / denom);
    stats.rms = static_cast<float>(std::sqrt(totalSq / denom));
    stats.maxAbs = static_cast<float>(maxAbs);
    stats.valid = true;
  }

  return stats;
}

bool readTextureRGBA(GLuint texture, int width, int height, std::vector<float> &out) {
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

DiffStats computeDiffStats(const std::vector<float> &a, const std::vector<float> &b) {
  DiffStats stats;
  if (a.size() != b.size() || a.empty()) {
    return stats;
  }

  double total = 0.0;
  double totalSq = 0.0;
  double maxAbs = 0.0;
  for (std::size_t i = 0; i + 3 < a.size(); i += 4) {
    for (std::size_t c = 0; c < 3; ++c) {
      double const diff =
          std::abs(static_cast<double>(a.at(i + c)) - static_cast<double>(b.at(i + c)));
      total += diff;
      totalSq += diff * diff;
      maxAbs = std::max(maxAbs, diff);
    }
  }

  const auto denom = static_cast<double>(
      (a.size() / 4) *
      3); // NOLINT(bugprone-integer-division) -- intentional: pixel count * 3 channels
  if (denom > 0.0) {
    stats.meanAbs = static_cast<float>(total / denom);
    stats.rms = static_cast<float>(std::sqrt(totalSq / denom));
    stats.maxAbs = static_cast<float>(maxAbs);
    stats.valid = true;
  }
  return stats;
}

std::size_t countDiffOutliers(const std::vector<float> &a, const std::vector<float> &b,
                              float threshold) {
  if (a.size() != b.size() || a.empty() || threshold <= 0.0f) {
    return 0;
  }
  std::size_t count = 0;
  for (std::size_t i = 0; i + 3 < a.size(); i += 4) {
    double const dr = std::abs(static_cast<double>(a.at(i)) - static_cast<double>(b.at(i)));
    double const dg = std::abs(static_cast<double>(a.at(i + 1)) - static_cast<double>(b.at(i + 1)));
    double const db = std::abs(static_cast<double>(a.at(i + 2)) - static_cast<double>(b.at(i + 2)));
    if (std::max({dr, dg, db}) > static_cast<double>(threshold)) {
      ++count;
    }
  }
  return count;
}

bool writePpm(const std::string &path, const std::vector<float> &rgba, int width, int height,
              float scale) {
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
      float const scaled = std::clamp(v * scale, 0.0f, 1.0f);
      return static_cast<unsigned char>(scaled * 255.0f);
    };
    unsigned char rgb[3] = {clampChannel(rgba.at(i)), clampChannel(rgba.at(i + 1)),
                            clampChannel(rgba.at(i + 2))};
    out.write(reinterpret_cast<const char *>(rgb), 3);
  }
  return true;
}

bool writeDiffPpm(const std::string &path, const std::vector<float> &a, const std::vector<float> &b,
                  int width, int height, float scale) {
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
      float const scaled = std::clamp(v * scale, 0.0f, 1.0f);
      return static_cast<unsigned char>(scaled * 255.0f);
    };
    float const dr = std::abs(a.at(i) - b.at(i));
    float const dg = std::abs(a.at(i + 1) - b.at(i + 1));
    float const db = std::abs(a.at(i + 2) - b.at(i + 2));
    unsigned char rgb[3] = {clampChannel(dr), clampChannel(dg), clampChannel(db)};
    out.write(reinterpret_cast<const char *>(rgb), 3);
  }
  return true;
}

std::string compareSnapshotPath(int index, const std::string &tag) {
  std::filesystem::create_directories("logs/compare");
  return "logs/compare/compare_" + std::to_string(index) + "_" + tag + ".ppm";
}

std::string compareSummaryPath() {
  std::filesystem::create_directories("logs/compare");
  return "logs/compare/compare_summary.csv";
}

std::string compareUniformsPath() {
  std::filesystem::create_directories("logs/compare");
  return "logs/compare/compare_uniforms.csv";
}

void appendCompareSummary(const std::string &path, int index, const std::string &primaryTag,
                          const std::string &secondaryTag, int width, int height,
                          const DiffStats &stats, float diffScale, bool wroteOutputs,
                          bool wroteDiff, float threshold, bool exceeded, double timeSec,
                          float kerrSpin, bool grbEnabled, float grbTime, int outlierCount,
                          int outlierLimit, float outlierFrac) {
  if (!stats.valid) {
    return;
  }
  const bool exists = std::filesystem::exists(path);
  std::ofstream out(path, std::ios::app);
  if (!out) {
    return;
  }
  if (!exists) {
    out << "index,primary,secondary,width,height,mean_abs,rms,max_abs,diff_scale,threshold,"
           "exceeded,"
           "write_outputs,write_diff,time_sec,kerr_spin,grb_enabled,grb_time,outlier_count,"
           "outlier_limit,outlier_frac\n";
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << primaryTag << "," << secondaryTag << "," << width << "," << height << ","
      << stats.meanAbs << "," << stats.rms << "," << stats.maxAbs << "," << diffScale << ","
      << threshold << "," << (exceeded ? 1 : 0) << "," << (wroteOutputs ? 1 : 0) << ","
      << (wroteDiff ? 1 : 0) << "," << timeSec << "," << kerrSpin << "," << (grbEnabled ? 1 : 0)
      << "," << grbTime << "," << outlierCount << "," << outlierLimit << "," << outlierFrac << "\n";
}

/**
 * @brief A named camera + physics configuration used by the compute/fragment parity test suite.
 *
 * Each preset is rendered with both the GL fragment path and the CUDA compute
 * path; DiffStats are compared to detect arithmetic divergence (Issue-009).
 */
struct ComparePreset {
  const char *label{};               ///< Human-readable name shown in the compare UI.
  CameraMode  mode{CameraMode::Input}; ///< Camera positioning mode for this preset.
  CameraState camera;                ///< Camera state (used when mode == Input).
  float       orbitRadius{};         ///< Orbit radius in gravitational radii (Orbit mode).
  float       orbitSpeed{};          ///< Orbit angular speed in degrees per second.
  float       kerrSpin{};            ///< Dimensionless Kerr spin parameter a* in [0, 1).
};

constexpr float K_COMPARE_KERR_SPIN = 0.8f;
constexpr int K_INTEGRATOR_DEBUG_NAN_FLAG = 1;
constexpr int K_INTEGRATOR_DEBUG_RANGE_FLAG = 2;
constexpr std::array<ComparePreset, 12> K_COMPARE_PRESETS = {{
    {.label = "Input Near (Schw)",
     .mode = CameraMode::Input,
     .camera =
         CameraState{.yaw = 30.0f, .pitch = -10.0f, .roll = 0.0f, .distance = 8.0f, .fov = 45.0f},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Input Near (Kerr)",
     .mode = CameraMode::Input,
     .camera =
         CameraState{.yaw = 30.0f, .pitch = -10.0f, .roll = 0.0f, .distance = 8.0f, .fov = 45.0f},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Input Far (Schw)",
     .mode = CameraMode::Input,
     .camera =
         CameraState{.yaw = 60.0f, .pitch = 10.0f, .roll = 0.0f, .distance = 20.0f, .fov = 45.0f},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Input Far (Kerr)",
     .mode = CameraMode::Input,
     .camera =
         CameraState{.yaw = 60.0f, .pitch = 10.0f, .roll = 0.0f, .distance = 20.0f, .fov = 45.0f},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Front (Schw)",
     .mode = CameraMode::Front,
     .camera = CameraState{},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Front (Kerr)",
     .mode = CameraMode::Front,
     .camera = CameraState{},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Top (Schw)",
     .mode = CameraMode::Top,
     .camera = CameraState{},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Top (Kerr)",
     .mode = CameraMode::Top,
     .camera = CameraState{},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Orbit Near (Schw)",
     .mode = CameraMode::Orbit,
     .camera = CameraState{},
     .orbitRadius = 10.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Orbit Near (Kerr)",
     .mode = CameraMode::Orbit,
     .camera = CameraState{},
     .orbitRadius = 10.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Orbit Far (Schw)",
     .mode = CameraMode::Orbit,
     .camera = CameraState{},
     .orbitRadius = 20.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Orbit Far (Kerr)",
     .mode = CameraMode::Orbit,
     .camera = CameraState{},
     .orbitRadius = 20.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
}};

/**
 * @brief Aggregated uniform values shared between the GL fragment shader and the CUDA compute path.
 *
 * applyInteropUniforms() copies these fields into a RenderToTextureInfo uniform
 * map before each render call, ensuring both paths receive identical inputs for
 * the compute/fragment parity comparison (Issue-009).
 */
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
  // D2: volumetric RTE
  float rteEnabled      = 0.0f;
  float rteOpacityScale = 0.5f;
};

void appendCompareUniforms(const std::string &path, int index, const std::string &label,
                           const InteropUniforms &interop, bool compareBaseline,
                           bool compareOverrides, bool backgroundEnabled, bool noiseEnabled,
                           bool grmhdEnabled, bool spectralEnabled, bool grbEnabled,
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
  out << index << "," << label << "," << interop.cameraPos.x << "," << interop.cameraPos.y << ","
      << interop.cameraPos.z << "," << interop.fovScale << "," << interop.timeSec << ","
      << interop.depthFar << "," << interop.schwarzschildRadius << "," << interop.iscoRadius << ","
      << interop.kerrSpin << "," << interop.maxSteps << "," << interop.stepSize << ","
      << interop.adiskEnabled << "," << interop.enableRedshift << "," << interop.useLUTs << ","
      << interop.useSpectralLUT << "," << interop.useGrbModulation << ","
      << (backgroundEnabled ? 1 : 0) << "," << (noiseEnabled ? 1 : 0) << ","
      << (grmhdEnabled ? 1 : 0) << "," << (spectralEnabled ? 1 : 0) << "," << (grbEnabled ? 1 : 0)
      << "," << (photonSphereEnabled ? 1 : 0) << "," << (compareBaseline ? 1 : 0) << ","
      << (compareOverrides ? 1 : 0) << "\n";
}

void applyInteropUniforms(RenderToTextureInfo &rtti, const InteropUniforms &interop,
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
  // D2: volumetric RTE
  rtti.floatUniforms["rteEnabled"]      = interop.rteEnabled;
  rtti.floatUniforms["rteOpacityScale"] = interop.rteOpacityScale;
  // Wiregrid BL-coord overlay (task A2) -- filled by caller via wiregridEnabled flag
  // (wiregridEnabled/ShowErgo/GridScale are set in the render loop after this call)
}

void applyInteropComputeUniforms(GLuint program, const InteropUniforms &interop, int width,
                                 int height) {
  glUniform2f(glGetUniformLocation(program, "resolution"), static_cast<float>(width),
              static_cast<float>(height));
  glUniformMatrix3fv(glGetUniformLocation(program, "cameraBasis"), 1, GL_FALSE,
                     glm::value_ptr(interop.cameraBasis));
  glUniform1f(glGetUniformLocation(program, "fovScale"), interop.fovScale);
  glUniform1f(glGetUniformLocation(program, "time"), interop.timeSec);
  glUniform3f(glGetUniformLocation(program, "cameraPos"), interop.cameraPos.x, interop.cameraPos.y,
              interop.cameraPos.z);
  glUniform1f(glGetUniformLocation(program, "schwarzschildRadius"), interop.schwarzschildRadius);
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
  // D2: volumetric RTE -- same source as fragment path
  glUniform1f(glGetUniformLocation(program, "rteEnabled"),      interop.rteEnabled);
  glUniform1f(glGetUniformLocation(program, "rteOpacityScale"), interop.rteOpacityScale);
}

void applyHawkingUniforms(GLuint program, const physics::HawkingRenderer &renderer, bool enabled,
                          float tempScale, float intensity, bool useLUTs, double blackHoleMass) {
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

bool loadLutCsv(const std::string &path, std::vector<float> &values) {
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
    std::size_t const comma = line.find(',');
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

bool loadLutAssets(physics::Lut1D &emissivity, physics::Lut1D &redshift, float &spinOut) {
  std::vector<float> emissivityValues;
  std::vector<float> redshiftValues;
  if (!loadLutCsv(resourcePath("assets/luts/emissivity_lut.csv"), emissivityValues)) {
    return false;
  }
  if (!loadLutCsv(resourcePath("assets/luts/redshift_lut.csv"), redshiftValues)) {
    return false;
  }
  std::string metaText;
  if (!readTextFile(resourcePath("assets/luts/lut_meta.json"), metaText)) {
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
  emissivity.rMin = static_cast<float>(rInOverRs);
  emissivity.rMax = static_cast<float>(rOutOverRs);
  redshift.values = std::move(redshiftValues);
  redshift.rMin = static_cast<float>(rInOverRs);
  redshift.rMax = static_cast<float>(rOutOverRs);
  spinOut = static_cast<float>(spin);
  return true;
}

bool loadSpectralLutAssets(std::vector<float> &values, float &wavelengthMin, float &wavelengthMax) {
  values.clear();
  if (!loadLutCsv(resourcePath("assets/luts/rt_spectrum_lut.csv"), values)) {
    return false;
  }
  std::string metaText;
  if (!readTextFile(resourcePath("assets/luts/rt_spectrum_meta.json"), metaText)) {
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

bool loadGrbModulationLutAssets(std::vector<float> &values, float &timeMin, float &timeMax) {
  values.clear();
  if (!loadLutCsv(resourcePath("assets/luts/grb_modulation_lut.csv"), values)) {
    return false;
  }
  std::string metaText;
  if (!readTextFile(resourcePath("assets/luts/grb_modulation_meta.json"), metaText)) {
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

void glfwErrorCallback(int error, const char *description) {
  fprintf(stderr, "Glfw Error %d: %s\n", error,
          description); // NOLINT(cert-err33-c) -- diagnostic output, return unused
}

// GLFW callbacks that delegate to InputManager
void keyCallback(GLFWwindow * /*window*/, int key, int scancode, int action, int mods) {
  InputManager::instance().onKey(key, scancode, action, mods);
}

void mouseButtonCallback(GLFWwindow * /*window*/, int button, int action, int mods) {
  InputManager::instance().onMouseButton(button, action, mods);
}

void cursorPosCallback(GLFWwindow * /*window*/, double x, double y) {
  InputManager::instance().onMouseMove(x, y);
}

void scrollCallback(GLFWwindow * /*window*/, double xoffset, double yoffset) {
  InputManager::instance().onScroll(xoffset, yoffset);
}

// Initialize OpenGL debug context (call after loader init)
void initializeGLDebugContext() {
#ifdef ENABLE_GL_DEBUG_CONTEXT
  // Check if debug context is available (OpenGL 4.3+ or KHR_debug extension)
  GLint contextFlags = 0;
  glGetIntegerv(GL_CONTEXT_FLAGS, &contextFlags);
  const auto flags = static_cast<ContextFlagMask>(contextFlags);

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

void configureParallelShaderCompile() {
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
    threads = static_cast<unsigned int>(
        std::max(1, std::atoi(threadEnv))); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                            // -- env var, invalid input defaults to 0
  }
  glMaxShaderCompilerThreadsKHR(static_cast<GLuint>(threads));
  std::cout << "Parallel shader compile enabled (" << threads << " threads).\n";
}

// Initialize GLFW and create window
GLFWwindow *initializeWindow(int width, int height) {
  glfwSetErrorCallback(glfwErrorCallback);
  if (glfwInit() == 0) {
    return nullptr;
  }

  glfwWindowHint(GLFW_DECORATED, GLFW_TRUE);
  const char *hiddenWindowEnv = std::getenv("BLACKHOLE_WINDOW_HIDDEN");
  if (hiddenWindowEnv != nullptr && std::string(hiddenWindowEnv) == "1") {
    glfwWindowHint(GLFW_VISIBLE, GLFW_FALSE);
    glfwWindowHint(GLFW_FOCUSED, GLFW_FALSE);
#if GLFW_VERSION_MAJOR > 3 || (GLFW_VERSION_MAJOR == 3 && GLFW_VERSION_MINOR >= 3)
    glfwWindowHint(GLFW_FOCUS_ON_SHOW, GLFW_FALSE);
#endif
  }
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

  GLFWwindow *window = glfwCreateWindow(width, height, kWindowTitle, nullptr, nullptr);
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
    std::fprintf(stderr, "OpenGL 4.6 required, found %d.%d\n", glMajor,
                 glMinor); // NOLINT(cert-err33-c) -- diagnostic output, return unused
    glfwDestroyWindow(window);
    return nullptr;
  }

  // Initialize GL debug context after loader init
  initializeGLDebugContext();
  configureParallelShaderCompile();

  return window;
}

// Configure custom ImGui style for "Blackhole" theme (16-bit Voxel Aesthetic)
void setupImGuiStyle() {
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
void initializeImGui(GLFWwindow *window) {
  const char *glslVersion = "#version 460";

  IMGUI_CHECKVERSION();
  ImGui::CreateContext();
  ImPlot::CreateContext();
  ImGuiIO &io = ImGui::GetIO();
  io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard; // Enable keyboard navigation
  io.ConfigFlags |= ImGuiConfigFlags_DockingEnable;     // Enable Docking
  // io.ConfigFlags |= ImGuiConfigFlags_ViewportsEnable;   // Disable Multi-Viewport (causes
  // artifacts on Wayland)
  ImGuizmo::SetImGuiContext(ImGui::GetCurrentContext());
  ImGuizmo::SetOrthographic(false);

  setupImGuiStyle();

  ImGui_ImplGlfw_InitForOpenGL(window, true);
  ImGui_ImplOpenGL3_Init(glslVersion);
}

// Render controls help panel
void renderControlsHelpPanel() {
  ImGui::SetNextWindowPos(ImVec2(10, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 280), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Controls Help", nullptr, ImGuiWindowFlags_NoCollapse)) {
    auto &input = InputManager::instance();

    auto keyLabel = [&](KeyAction action) {
      return InputManager::getKeyName(
          input.getKeyForAction(action)); // NOLINT(readability-static-accessed-through-instance)
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

// NOLINTNEXTLINE(readability-function-cognitive-complexity) -- ImGui panel has many controls
void renderControlsSettingsPanel(int &cameraModeIndex, float &orbitRadius, float &orbitSpeed) {
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
    auto applyControlPreset = [&](float mouseSens, float keySens, float scrollSens, float timeScale,
                                  float padDeadzone, float padLook, float padRoll, float padZoom,
                                  float padTrigger) {
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
      Settings const defaults;
      applyControlPreset(defaults.mouseSensitivity, defaults.keyboardSensitivity,
                         defaults.scrollSensitivity, defaults.timeScale, defaults.gamepadDeadzone,
                         defaults.gamepadLookSensitivity, defaults.gamepadRollSensitivity,
                         defaults.gamepadZoomSensitivity, defaults.gamepadTriggerZoomSensitivity);
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

    const char *const cameraModeLabels[] = {"Input", "Front", "Top", "Orbit"};
    ImGui::Combo("Camera Mode", &cameraModeIndex, cameraModeLabels, IM_ARRAYSIZE(cameraModeLabels));

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

    ImGui::Text("Status: %s",
                InputManager::isGamepadConnected()
                    ? "Connected"
                    : "Not detected"); // NOLINT(readability-static-accessed-through-instance)

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
      Settings const defaults;
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

      int const yawAxis = input.getGamepadYawAxis();
      int const pitchAxis = input.getGamepadPitchAxis();
      int const rollAxis = input.getGamepadRollAxis();
      int const zoomAxis = input.getGamepadZoomAxis();
      int const zoomInAxis = input.getGamepadZoomInAxis();
      int const zoomOutAxis = input.getGamepadZoomOutAxis();

      std::string const yawLabel = std::string("Yaw (") + gamepadAxisHint(yawAxis) + ")";
      std::string const pitchLabel = std::string("Pitch (") + gamepadAxisHint(pitchAxis) + ")";
      std::string const rollLabel = std::string("Roll (") + gamepadAxisHint(rollAxis) + ")";
      std::string const zoomLabel = std::string("Zoom (") + gamepadAxisHint(zoomAxis) + ")";
      std::string const zoomInLabel = std::string("Zoom In (") + gamepadAxisHint(zoomInAxis) + ")";
      std::string const zoomOutLabel =
          std::string("Zoom Out (") + gamepadAxisHint(zoomOutAxis) + ")";

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
        ImGui::TextColored(
            ImVec4(1.0f, 0.8f, 0.0f, 1.0f), "Press a key to bind to: %s",
            InputManager::getActionName(
                input
                    .getRemappingAction())); // NOLINT(readability-static-accessed-through-instance)
        if (ImGui::Button("Cancel")) {
          input.cancelKeyRemapping();
        }
      } else {
        if (ImGui::BeginTable("KeyBindings", 2, ImGuiTableFlags_SizingStretchProp)) {
          for (int i = 0; i < static_cast<int>(KeyAction::COUNT); i++) {
            auto const action = static_cast<KeyAction>(i);
            const char *actionName = InputManager::getActionName(
                action); // NOLINT(readability-static-accessed-through-instance)
            int const currentKey = input.getKeyForAction(action);
            std::string const keyName = InputManager::getKeyName(
                currentKey); // NOLINT(readability-static-accessed-through-instance)

            ImGui::TableNextRow();
            ImGui::TableNextColumn();
            ImGui::Text("%s", actionName);
            ImGui::TableNextColumn();

            ImGui::PushID(i);
            char buttonLabel[64];
            std::snprintf(buttonLabel, sizeof(buttonLabel), "[%s]##%d", keyName.c_str(),
                          i); // NOLINT(cert-err33-c) -- diagnostic output, return unused
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

void renderGizmoPanel(bool &gizmoEnabled, ImGuizmo::OPERATION &operation, ImGuizmo::MODE &mode,
                      glm::mat4 &gizmoTransform) {
  ImGui::SetNextWindowPos(ImVec2(1020, 220), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 220), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Gizmo", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable Gizmo Target", &gizmoEnabled);

    const char *const operationLabels[] = {"Translate", "Rotate", "Scale"};
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
      if (operationIndex == 0) {
        operation = ImGuizmo::TRANSLATE;
      } else if (operationIndex == 1) {
        operation = ImGuizmo::ROTATE;
      } else {
        operation = ImGuizmo::SCALE;
      }
    }

    const char *const modeLabels[] = {"World", "Local"};
    int modeIndex = (mode == ImGuizmo::WORLD) ? 0 : 1;
    if (ImGui::Combo("Mode", &modeIndex, modeLabels, IM_ARRAYSIZE(modeLabels))) {
      mode = (modeIndex == 0) ? ImGuizmo::WORLD : ImGuizmo::LOCAL;
    }

    if (ImGui::Button("Reset Target")) {
      gizmoTransform = glm::mat4(1.0f);
    }

    auto const target = glm::vec3(gizmoTransform[3]); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                      // -- glm::mat has no .at()
    ImGui::Text("Target: %.2f %.2f %.2f", static_cast<double>(target.x),
                static_cast<double>(target.y), static_cast<double>(target.z));
  }
  ImGui::End();
}

void renderDisplaySettingsPanel(GLFWwindow *window, int &swapInterval, float &renderScale,
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

    const char *const swapModes[] = {"Off (0)", "VSync (1)", "Triple (2)"};
    int interval = std::clamp(swapInterval, 0, 2);
    if (ImGui::Combo("Swap Interval", &interval, swapModes, IM_ARRAYSIZE(swapModes))) {
      swapInterval = interval;
      settings.swapInterval = swapInterval;
      glfwSwapInterval(swapInterval);
    }

    if (ImGui::SliderFloat("Render Scale", &renderScale, 0.25f, 1.5f)) {
      settings.renderScale = renderScale;
    }

    const char *const presets[] = {"Native", "720p",         "1080p",       "1440p",
                                   "4K",     "UW 3440x1440", "UW 5120x2160"};
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

    float const clampedScale = std::clamp(renderScale, 0.25f, 1.5f);
    int const targetWidth =
        std::max(1, static_cast<int>(static_cast<float>(windowWidth) * clampedScale));
    int const targetHeight =
        std::max(1, static_cast<int>(static_cast<float>(windowHeight) * clampedScale));
    ImGui::Text("Window: %dx%d", windowWidth, windowHeight);
    ImGui::Text("Render: %dx%d", targetWidth, targetHeight);
  }
  ImGui::End();
}

void renderBackgroundPanel(const std::vector<BackgroundAsset> &assets, int &backgroundIndex,
                           float &parallaxStrength, float &driftStrength,
                           std::array<float, K_BACKGROUND_LAYERS> &layerDepth,
                           std::array<float, K_BACKGROUND_LAYERS> &layerScale,
                           std::array<float, K_BACKGROUND_LAYERS> &layerIntensity,
                           std::array<float, K_BACKGROUND_LAYERS> &layerLodBias) {
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
      const char *preview = assets.at(static_cast<std::size_t>(backgroundIndex)).title.c_str();
      if (ImGui::BeginCombo("Background Asset", preview)) {
        for (int i = 0; std::cmp_less(i, assets.size()); ++i) {
          bool const selected = (i == backgroundIndex);
          if (ImGui::Selectable(assets.at(static_cast<std::size_t>(i)).title.c_str(), selected)) {
            backgroundIndex = i;
            settings.backgroundId = assets.at(static_cast<std::size_t>(i)).id;
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
      for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
        ImGui::PushID(i);
        ImGui::SliderFloat("Depth", &layerDepth.at(static_cast<std::size_t>(i)), 0.0f, 2.0f);
        ImGui::SliderFloat("Scale", &layerScale.at(static_cast<std::size_t>(i)), 0.5f, 2.0f);
        ImGui::SliderFloat("Weight", &layerIntensity.at(static_cast<std::size_t>(i)), 0.0f, 2.0f);
        ImGui::SliderFloat("LOD Bias", &layerLodBias.at(static_cast<std::size_t>(i)), 0.0f, 6.0f,
                           "%.2f");
        ImGui::Separator();
        ImGui::PopID();
      }
      ImGui::TreePop();
    }
  }
  ImGui::End();
}

void renderWiregridPanel(bool &wiregridEnabled, WiregridParams &params, glm::vec4 &color) {
  ImGui::SetNextWindowPos(ImVec2(10, 570), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 140), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Wiregrid", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable Wiregrid", &wiregridEnabled);
    ImGui::Checkbox("Show Ergosphere", &params.showErgosphere);
    ImGui::SliderFloat("Grid Scale", &params.gridScale, 0.25f, 4.0f);
    ImGui::Separator();
    ImGui::ColorEdit4("Color", reinterpret_cast<float *>(&color));
  }
  ImGui::End();
}

void renderRmlUiPanel(bool &rmluiEnabled) {
  ImGui::SetNextWindowPos(ImVec2(1020, 450), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 140), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("RmlUi", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable RmlUi overlay", &rmluiEnabled);
    ImGui::TextDisabled("Experimental: placeholder only");
  }
  ImGui::End();
}

// Cleanup resources
void cleanup(GLFWwindow *window) {
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
  GLuint program_;

public:
  explicit PostProcessPass(const std::string &fragShader) {
    this->program_ = createShaderProgram(std::string("shader/simple.vert"), fragShader);

    glUseProgram(this->program_);
    glUniform1i(glGetUniformLocation(program_, "texture0"), 0);
    glUseProgram(0);
  }

  void render(GLuint inputColorTexture, int width, int height, GLuint destFramebuffer = 0) const {
    static GLuint quadVao = 0;
    if (quadVao == 0) {
      quadVao = createQuadVAO();
    }

    glBindFramebuffer(GL_FRAMEBUFFER, destFramebuffer);

    glDisable(GL_DEPTH_TEST);

    glClearColor(1.0f, 0.0f, 0.0f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT);

    glUseProgram(this->program_);
    glBindVertexArray(quadVao);

    glUniform2f(glGetUniformLocation(this->program_, "resolution"), static_cast<float>(width),
                static_cast<float>(height));

    glUniform1f(glGetUniformLocation(this->program_, "time"), static_cast<float>(glfwGetTime()));

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
    int const prev = 1 - index;
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
  static constexpr int K_CAPACITY = 240;
  std::array<float, K_CAPACITY> cpuMs{};
  std::array<float, K_CAPACITY> gpuFragmentMs{};
  std::array<float, K_CAPACITY> gpuComputeMs{};
  std::array<float, K_CAPACITY> gpuBloomMs{};
  std::array<float, K_CAPACITY> gpuTonemapMs{};
  std::array<float, K_CAPACITY> gpuDepthMs{};
  std::array<float, K_CAPACITY> gpuGrmhdSliceMs{};
  int offset = 0;
  int count = 0;

  void push(float cpuMsSample, const GpuTimerSet &timers) {
    const auto index = static_cast<std::size_t>(offset);
    cpuMs.at(index) = cpuMsSample;
    if (timers.initialized) {
      gpuFragmentMs.at(index) = static_cast<float>(timers.blackholeFragment.lastMs);
      gpuComputeMs.at(index) = static_cast<float>(timers.blackholeCompute.lastMs);
      gpuBloomMs.at(index) = static_cast<float>(timers.bloom.lastMs);
      gpuTonemapMs.at(index) = static_cast<float>(timers.tonemap.lastMs);
      gpuDepthMs.at(index) = static_cast<float>(timers.depth.lastMs);
      gpuGrmhdSliceMs.at(index) = static_cast<float>(timers.grmhdSlice.lastMs);
    } else {
      const float nan = std::numeric_limits<float>::quiet_NaN();
      gpuFragmentMs.at(index) = nan;
      gpuComputeMs.at(index) = nan;
      gpuBloomMs.at(index) = nan;
      gpuTonemapMs.at(index) = nan;
      gpuDepthMs.at(index) = nan;
      gpuGrmhdSliceMs.at(index) = nan;
    }
    offset = (offset + 1) % K_CAPACITY;
    if (count < K_CAPACITY) {
      ++count;
    }
  }
};

std::string gpuTimingPath() {
  std::filesystem::create_directories("logs/perf");
  return "logs/perf/gpu_timing.csv";
}

void appendGpuTimingSample(const std::string &path, int index, int width, int height,
                           float cpuFrameMs, const GpuTimerSet &timers, bool computeActive,
                           float kerrSpin, double timeSec) {
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

void writeTimingHistoryCsv(const TimingHistory &history, const std::string &path) {
  std::filesystem::create_directories("logs/perf");
  std::ofstream out(path);
  if (!out) {
    return;
  }
  out << "index,cpu_ms,gpu_fragment_ms,gpu_compute_ms,gpu_bloom_ms,gpu_tonemap_ms,gpu_depth_ms,"
         "gpu_grmhd_slice_ms\n";
  out << std::fixed << std::setprecision(6);

  int const count = history.count;
  int start = history.offset - count;
  if (start < 0) {
    start += TimingHistory::K_CAPACITY;
  }
  for (int i = 0; i < count; ++i) {
    int const rawIndex = (start + i) % TimingHistory::K_CAPACITY;
    auto const idx = static_cast<std::size_t>(rawIndex);
    out << i << "," << history.cpuMs.at(idx) << "," << history.gpuFragmentMs.at(idx) << ","
        << history.gpuComputeMs.at(idx) << "," << history.gpuBloomMs.at(idx) << ","
        << history.gpuTonemapMs.at(idx) << "," << history.gpuDepthMs.at(idx) << ","
        << history.gpuGrmhdSliceMs.at(idx) << "\n";
  }
}

void renderPerformancePanel(bool &gpuTimingEnabled, const GpuTimerSet &timers,
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
      ImGui::SetTooltip("Reduces overdraw for mesh geometry.\nCurrently unused (ray marching has "
                        "zero overdraw).");
    }
    auto const cpuFrameMsD = static_cast<double>(cpuFrameMs);
    double const fps = cpuFrameMs > 0.0f ? 1000.0 / cpuFrameMsD : 0.0;
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
      ImPlot::PlotLine("CPU", history.cpuMs.data(), history.count, 1.0, 0.0, ImPlotLineFlags_None,
                       history.offset);
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

void resetLayout(ImGuiID dockspaceId) {
  ImGui::DockBuilderRemoveNode(dockspaceId);
  ImGui::DockBuilderAddNode(dockspaceId, ImGuiDockNodeFlags_DockSpace);
  ImGui::DockBuilderSetNodeSize(dockspaceId, ImGui::GetMainViewport()->Size);

  ImGuiID dockMainId = dockspaceId;
  ImGuiID dockLeftId =
      ImGui::DockBuilderSplitNode(dockMainId, ImGuiDir_Left, 0.30f, nullptr, &dockMainId);
  ImGuiID const dockLeftDownId =
      ImGui::DockBuilderSplitNode(dockLeftId, ImGuiDir_Down, 0.50f, nullptr, &dockLeftId);

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

} // anonymous namespace

// NOLINTNEXTLINE(readability-function-cognitive-complexity,readability-function-size) --
// application main loop
int main(int argc, char **argv) {
  installCrashHandlers();
  try {
    std::string curveTsvPath;
    std::string exportFramePath;
    std::string recordFramesDir;
    std::string recordProfile = "cinematic";
    std::string recordComposition = "wide-right";
    std::string recordBackgroundId;
    int         recordFramesTotal = K_CINEMATIC_FRAMES;
    int         recordStartFrame  = 0;
    float       recordYawDeg = 0.0f;
    bool        hasRecordYaw = false;
    float       recordPitchDeg = 0.0f;
    bool        hasRecordPitch = false;
    float       recordDistance = 0.0f;
    bool        hasRecordDistance = false;
    float       recordFovDeg = 0.0f;
    bool        hasRecordFov = false;
    float       recordExposure = 0.0f;
    bool        hasRecordExposure = false;
    float       recordSweepDeg = 0.0f;
    bool        hasRecordSweep = false;
    float       recordFrameX = 0.0f;
    bool        hasRecordFrameX = false;
    float       recordFrameY = 0.0f;
    bool        hasRecordFrameY = false;
    bool        hasRecordBackgroundId = false;
    float       recordBackgroundYawDeg = 0.0f;
    bool        hasRecordBackgroundYaw = false;
    float       recordBackgroundPitchDeg = 0.0f;
    bool        hasRecordBackgroundPitch = false;
    for (int i = 1; i < argc; ++i) {
      std::string const arg = argv[i];
      if (arg == "--help" || arg == "-h") {
        printUsage(argv[0]);
        return 0;
      }
      if (arg == "--curve-tsv" && i + 1 < argc) {
        curveTsvPath = argv[++i];
        continue;
      }
      if (arg == "--export-frame" && i + 1 < argc) {
        exportFramePath = argv[++i];
        continue;
      }
      if (arg == "--record-frames" && i + 1 < argc) {
        recordFramesDir = argv[++i];
        if (i + 1 < argc && argv[i + 1][0] != '-') {
          recordFramesTotal = std::atoi(argv[++i]);
        }
        continue;
      }
      if (arg == "--start-frame" && i + 1 < argc) {
        recordStartFrame = std::atoi(argv[++i]);
        continue;
      }
      if (arg == "--record-profile" && i + 1 < argc) {
        recordProfile = argv[++i];
        continue;
      }
      if (arg == "--record-composition" && i + 1 < argc) {
        recordComposition = argv[++i];
        continue;
      }
      if (arg == "--record-yaw" && i + 1 < argc) {
        recordYawDeg = std::strtof(argv[++i], nullptr);
        hasRecordYaw = true;
        continue;
      }
      if (arg == "--record-pitch" && i + 1 < argc) {
        recordPitchDeg = std::strtof(argv[++i], nullptr);
        hasRecordPitch = true;
        continue;
      }
      if (arg == "--record-distance" && i + 1 < argc) {
        recordDistance = std::strtof(argv[++i], nullptr);
        hasRecordDistance = true;
        continue;
      }
      if (arg == "--record-fov" && i + 1 < argc) {
        recordFovDeg = std::strtof(argv[++i], nullptr);
        hasRecordFov = true;
        continue;
      }
      if (arg == "--record-exposure" && i + 1 < argc) {
        recordExposure = std::strtof(argv[++i], nullptr);
        hasRecordExposure = true;
        continue;
      }
      if (arg == "--record-sweep-deg" && i + 1 < argc) {
        recordSweepDeg = std::strtof(argv[++i], nullptr);
        hasRecordSweep = true;
        continue;
      }
      if (arg == "--record-frame-x" && i + 1 < argc) {
        recordFrameX = std::strtof(argv[++i], nullptr);
        hasRecordFrameX = true;
        continue;
      }
      if (arg == "--record-frame-y" && i + 1 < argc) {
        recordFrameY = std::strtof(argv[++i], nullptr);
        hasRecordFrameY = true;
        continue;
      }
      if (arg == "--record-background-id" && i + 1 < argc) {
        recordBackgroundId = argv[++i];
        hasRecordBackgroundId = true;
        continue;
      }
      if (arg == "--record-bg-yaw" && i + 1 < argc) {
        recordBackgroundYawDeg = std::strtof(argv[++i], nullptr);
        hasRecordBackgroundYaw = true;
        continue;
      }
      if (arg == "--record-bg-pitch" && i + 1 < argc) {
        recordBackgroundPitchDeg = std::strtof(argv[++i], nullptr);
        hasRecordBackgroundPitch = true;
        continue;
      }
      std::printf("Unknown argument: %s\n", arg.c_str());
      printUsage(argv[0]);
      return 2;
    }

    if (recordProfile != "cinematic" && recordProfile != "compare-orbit-near" &&
        recordProfile != "showcase-orbit") {
      std::printf("Unknown record profile: %s\n", recordProfile.c_str());
      printUsage(argv[0]);
      return 2;
    }
    if (recordProfile == "showcase-orbit" &&
        findShowcaseOrbitComposition(recordComposition) == nullptr) {
      std::printf("Unknown showcase composition: %s\n", recordComposition.c_str());
      printUsage(argv[0]);
      return 2;
    }

    gResourceRoot = detectResourceRoot(argv[0]);
    setShaderBaseDir(gResourceRoot.string() + "/");

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
    ShaderWatcher::instance().start((std::filesystem::path(getShaderBaseDir()) / "shader").string());
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
      curveOverlayLoaded = curveOverlay.loadFromTsv(curveTsvPath);
      if (!curveOverlayLoaded) {
        std::fprintf(stderr, "curve overlay load failed: %s\n", // NOLINT(cert-err33-c) --
                                                                // diagnostic output, return unused
                     curveOverlay.lastError.c_str());
      }
    }

    // Create fullscreen quad for rendering
    GLuint const quadVAO = createQuadVAO();
    glBindVertexArray(quadVAO);

    // Main loop
    PostProcessPass const passthrough("shader/passthrough.frag");

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
    static float toneExposure = 1.0f;
    static float gamma = 2.5f;
    static bool gravitationalLensing = true;
    static bool renderBlackHole = true;
    static bool adiskEnabled = true;
    static bool adiskParticle = true;
    // D2: volumetric RTE
    static bool  rteVolumetricEnabled = false;
    static float rteOpacityScale      = 0.5f;
    // D4: polarized Stokes IQUV
    static bool  stokesEnabled        = false;
    static float stokesBFieldAngle    = 0.0f;   // EVPA of projected B field [rad]
    static float stokesNeScale        = 0.0f;   // Faraday rotation strength (0 = off)
    static float adiskDensityV = 2.0f;
    static float adiskDensityH = 4.0f;
    static float adiskHeight = 0.55f;
    static float adiskLit = 0.25f;
    static float adiskNoiseLOD = 5.0f;
    static float adiskNoiseScale = 0.8f;
    static bool useNoiseTexture = true;
    static float noiseTextureScale = 0.25f;
    [[maybe_unused]] static int const noiseTextureSize = 32;
    static float adiskSpeed = 0.5f;
    static float dopplerStrength = 1.0f;
    static float photonSphereGlowStrength = 1.0f;
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
    static std::unique_ptr<blackhole::GRMHDStreamer> grmhdStreamer;
    /* PBO uploader for streaming time-series tiles.  Initialized once when the
     * streamer loads a dataset and shut down when the dataset is unloaded.
     * Its texture() replaces grmhdTexture.texture for the time-series path. */
    static blackhole::GrmhdPBOUploader grmhdPboUploader;
    /* C1d: second PBO uploader for the adjacent (next) GRMHD frame.
     * Holds frame N+1; blended with grmhdPboUploader (frame N) using grmhdFrameAlpha. */
    static blackhole::GrmhdPBOUploader grmhdPboUploaderRight;
    /* Sub-frame blend factor [0,1): fraction of current inter-frame interval elapsed. */
    static float grmhdFrameAlpha = 0.0f;

    // --record-frames: cinematic recording state
    static bool         recordInitDone    = false;
    static int          recordFrameIndex  = recordStartFrame;
    static int          recordWarmup      = 0;
    static float        recordCinematic   = static_cast<float>(recordStartFrame) / static_cast<float>(K_CINEMATIC_FPS);
    static CinematicPath recordPath;
    static CamKeyframe  recordCurrentKf   = K_CINEMATIC_KEYFRAMES[0];
    static float        recordCurRs       = 2.0f;
    static float        recordCurIsco     = 1.0f;

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
#if BLACKHOLE_HAS_CUDA
    static CudaRenderManager cudaManager;
#endif
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
    static int compareAutoCount = static_cast<int>(K_COMPARE_PRESETS.size());
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
    [[maybe_unused]] static int const multiDrawInstanceCount = 2;
    [[maybe_unused]] static GLuint const multiDrawProgram = 0;
    [[maybe_unused]] static GLuint const multiDrawInstanceBuffer = 0;
    [[maybe_unused]] static GLuint const multiDrawCommandBuffer = 0;
    [[maybe_unused]] static GLuint const multiDrawCountBuffer = 0;
    [[maybe_unused]] static GLuint const multiDrawComputeProgram = 0;
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
    static bool const perfOverlayReady = false;
    static bool perfOverlayConfigInit = false;
    [[maybe_unused]] static bool perfOverlayEnabled = true;
    [[maybe_unused]] static float perfOverlayScale = 1.0f;
    [[maybe_unused]] static bool depthPrepassEnabled =
        false; // For future mesh-based disk rendering
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
    static bool synchGLutCreated = false;
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
    static GLuint texPhotonGlowLUT = 0;  // Phase 8.2: Photon sphere glow effect LUT
    static GLuint texDiskDensityLUT = 0; // Phase 8.2: Accretion disk density profile LUT
    static GLuint texSpectralLUT = 0;
    static GLuint texSynchGLut = 0;   /**< @brief Synchrotron G(x) LUT (GL_TEXTURE_2D, height=1). */
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
      /* Wire BL radial extent from grid header into the Cartesian bounds uniforms.
       * The grid is spherical so the conservative bounding box is [-rMax, rMax]^3. */
      const float r = grmhdTexture.rMax;
      grmhdBoundsMin = glm::vec3(-r, -r, -r);
      grmhdBoundsMax = glm::vec3( r,  r,  r);
      /* Register GRMHD volume as CUDA texture object (slot 5 = BhLutGrmhd).
       * Registration is non-fatal: CUDA kernel falls back to no GRMHD sampling
       * if the backend is not active or registration fails. */
#if BLACKHOLE_HAS_CUDA
      if (grmhdTexture.texture != 0) {
        cudaManager.registerLut(5 /*BhLutGrmhd*/, grmhdTexture.texture,
                                static_cast<unsigned int>(GL_TEXTURE_3D));
      }
#endif
      return true;
    };

    if (!grmhdPathInit) {
      std::snprintf(
          grmhdPathBuffer.data(),
          grmhdPathBuffer.size(), // NOLINT(cert-err33-c) -- diagnostic output, return unused
          "%s", resourcePath("assets/grmhd/grmhd_pack.json").c_str());
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
        compareAutoCount = static_cast<int>(K_COMPARE_PRESETS.size());
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
          compareMaxOutliers =
              std::max(0, std::atoi(outlierCountEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                       // -- env var, invalid input defaults to 0
        }
        const char *outlierFracEnv = std::getenv("BLACKHOLE_COMPARE_OUTLIER_FRAC");
        if (outlierFracEnv != nullptr) {
          compareMaxOutlierFrac =
              std::max(0.0f, static_cast<float>(std::atof(
                                 outlierFracEnv))); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                    // -- env var, invalid input defaults to 0
        }
        const char *maxStepsEnv = std::getenv("BLACKHOLE_COMPARE_MAX_STEPS");
        if (maxStepsEnv != nullptr) {
          compareMaxStepsOverride =
              std::max(0, std::atoi(maxStepsEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                   // -- env var, invalid input defaults to 0
          if (compareMaxStepsOverride > 0) {
            compareOverridesEnabled = true;
          }
        }
        const char *stepSizeEnv = std::getenv("BLACKHOLE_COMPARE_STEP_SIZE");
        if (stepSizeEnv != nullptr) {
          compareStepSizeOverride =
              static_cast<float>(std::atof(stepSizeEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                          // -- env var, invalid input defaults to 0
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
          int const stride = std::atoi(strideEnv); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                   // -- env var, invalid input defaults to 0
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
        auto const scale =
            static_cast<float>(std::atof(scaleEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                     // -- env var, invalid input defaults to 0
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
        auto const scale =
            static_cast<float>(std::atof(scaleEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                     // -- env var, invalid input defaults to 0
        perfOverlayScale = std::max(scale, 0.5f);
      }
      perfOverlayConfigInit = true;
    }

    if (!integratorDebugConfigInit) {
      const char *debugEnv = std::getenv("BLACKHOLE_INTEGRATOR_DEBUG_FLAGS");
      if (debugEnv != nullptr) {
        integratorDebugFlags =
            std::max(0, std::atoi(debugEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                              // -- env var, invalid input defaults to 0
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
        auto const index = static_cast<std::size_t>(i);
        int const downWidth = std::max(1, newWidth >> (i + 1));
        int const downHeight = std::max(1, newHeight >> (i + 1));
        int const upWidth = std::max(1, newWidth >> i);
        int const upHeight = std::max(1, newHeight >> i);
        texDownsampled.at(index) = createColorTexture(downWidth, downHeight);
        texUpsampled.at(index) = createColorTexture(upWidth, upHeight);
      }

      renderWidth = newWidth;
      renderHeight = newHeight;

#if BLACKHOLE_HAS_CUDA
      cudaManager.resize(texBlackhole, newWidth, newHeight);
#endif
    };

    static float lutAdiskDensityV = 0.0f;

    auto updateLuts = [&](float spin, float densityV) {
      spin = std::clamp(spin, -0.99f, 0.99f);
      if (!lutAssetsTried) {
        lutAssetsTried = true;
        lutAssetsLoaded = loadLutAssets(lutAssetEmissivity, lutAssetRedshift, lutAssetSpin);
      }

      bool const useAssetLuts = lutAssetsLoaded && std::abs(spin - lutAssetSpin) <= 1e-3f &&
                                !lutAssetEmissivity.values.empty() &&
                                !lutAssetRedshift.values.empty();
      if (useAssetLuts) {
        if (!lutInitialized || !lutFromAssets) {
          if (texEmissivityLUT != 0) {
            glDeleteTextures(1, &texEmissivityLUT);
            texEmissivityLUT = 0;
          }
          if (texRedshiftLUT != 0) {
            glDeleteTextures(1, &texRedshiftLUT);
            texRedshiftLUT = 0;
          }
          if (texPhotonGlowLUT != 0) {
            glDeleteTextures(1, &texPhotonGlowLUT);
            texPhotonGlowLUT = 0;
          }
          if (texDiskDensityLUT != 0) {
            glDeleteTextures(1, &texDiskDensityLUT);
            texDiskDensityLUT = 0;
          }

          int const lutSize = static_cast<int>(lutAssetEmissivity.values.size());
          texEmissivityLUT = createFloatTexture2D(lutSize, 1, lutAssetEmissivity.values);
          texRedshiftLUT = createFloatTexture2D(lutSize, 1, lutAssetRedshift.values);

#if BLACKHOLE_HAS_CUDA
          /* Share asset LUTs with CUDA backend (slot 0=emissivity, 1=redshift) */
          cudaManager.registerLut(0, texEmissivityLUT, static_cast<unsigned int>(GL_TEXTURE_2D));
          cudaManager.registerLut(1, texRedshiftLUT,   static_cast<unsigned int>(GL_TEXTURE_2D));
#endif

          lutRadiusMin = lutAssetEmissivity.rMin;
          lutRadiusMax = lutAssetEmissivity.rMax;
          redshiftRadiusMin = lutAssetRedshift.rMin;
          redshiftRadiusMax = lutAssetRedshift.rMax;
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
        if (texEmissivityLUT != 0) {
          glDeleteTextures(1, &texEmissivityLUT);
          texEmissivityLUT = 0;
        }
        if (texRedshiftLUT != 0) {
          glDeleteTextures(1, &texRedshiftLUT);
          texRedshiftLUT = 0;
        }
        if (texPhotonGlowLUT != 0) {
          glDeleteTextures(1, &texPhotonGlowLUT);
          texPhotonGlowLUT = 0;
        }
        lutInitialized = false;
        lutFromAssets = false;
        return;
      }

      // Only regenerate if parameters changed or not initialized
      if (!lutInitialized || std::abs(spin - lutSpin) > 1e-3f ||
          std::abs(densityV - lutAdiskDensityV) > 1e-3f || lutFromAssets) {
        // Cleanup existing textures
        if (texEmissivityLUT != 0) {
          glDeleteTextures(1, &texEmissivityLUT);
          texEmissivityLUT = 0;
        }
        if (texRedshiftLUT != 0) {
          glDeleteTextures(1, &texRedshiftLUT);
          texRedshiftLUT = 0;
        }
        if (texPhotonGlowLUT != 0) {
          glDeleteTextures(1, &texPhotonGlowLUT);
          texPhotonGlowLUT = 0;
        }
        if (texDiskDensityLUT != 0) {
          glDeleteTextures(1, &texDiskDensityLUT);
          texDiskDensityLUT = 0;
        }

        constexpr int kLutSize = 256;
        constexpr double kMassSolar = 4.0e6;
        constexpr double kMdotEdd = 0.1;

        auto emissivityLut = physics::generateEmissivityLut(
            kLutSize, kMassSolar, static_cast<double>(spin), kMdotEdd, true);
        auto redshiftLut =
            physics::generateRedshiftLut(kLutSize, kMassSolar, static_cast<double>(spin));

        texEmissivityLUT = createFloatTexture2D(kLutSize, 1, emissivityLut.values);
        texRedshiftLUT = createFloatTexture2D(kLutSize, 1, redshiftLut.values);

#if BLACKHOLE_HAS_CUDA
        /* Share generated LUTs with CUDA backend (slot 0=emissivity, 1=redshift) */
        cudaManager.registerLut(0, texEmissivityLUT, static_cast<unsigned int>(GL_TEXTURE_2D));
        cudaManager.registerLut(1, texRedshiftLUT,   static_cast<unsigned int>(GL_TEXTURE_2D));
#endif

        auto photonGlowLut = physics::generatePhotonGlowLut(256);
        texPhotonGlowLUT = createFloatTexture2D(256, 1, photonGlowLut.values);

        // Connect adiskDensityV to LUT generation
        // Use densityV as the exponent or scale factor for the density profile
        double const densityScale = static_cast<double>(std::max(0.1f, densityV));
        auto diskDensityLut = physics::generateDiskDensityLut(256, densityScale);
        texDiskDensityLUT = createFloatTexture2D(256, 1, diskDensityLut.values);

        lutRadiusMin = emissivityLut.rMin;
        lutRadiusMax = emissivityLut.rMax;
        redshiftRadiusMin = redshiftLut.rMin;
        redshiftRadiusMax = redshiftLut.rMax;
        lutSpin = spin;
        lutAdiskDensityV = densityV;
        lutFromAssets = false;
        lutInitialized = true;
        std::cout << "LUTs regenerated. Spin: " << spin << ", DensityV: " << densityV << '\n';
      }
    };

    // ... (rest of main) ...

    /* WHY: computeProgram is hoisted here (rather than a static local inside the
     * frame loop) so the hot-reload handler at the top of each frame can delete
     * and reset it to 0, triggering lazy re-creation on the next iteration. */
    GLuint computeProgram = 0;

    while (glfwWindowShouldClose(window) == 0) {
      // Clear default framebuffer (essential for ImGui Docking over Viewport)
      glClearColor(0.0f, 0.0f, 0.0f, 1.0f);
      glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

      // std::cout << "Frame start" << std::endl; // Debug instrumentation
      ZONE_SCOPED_N("Frame");
      // ...
      // Calculate delta time
      double const currentTime = glfwGetTime();
      auto const frameTime = static_cast<float>(currentTime);
      auto const deltaTime = static_cast<float>(currentTime - lastTime);
      lastTime = currentTime;
      const float cpuFrameMs = deltaTime * 1000.0f;

      glfwPollEvents();

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
      // Check for shader file changes and recompile all affected programs.
      if (ShaderWatcher::instance().hasPendingReloads()) {
        auto changedShaders = ShaderWatcher::instance().pollChangedShaders();
        for (const auto &path : changedShaders) {
          std::cout << "[HotReload] Shader changed: " << path << "\n";
        }
        ShaderWatcher::instance().clearPendingReloads();

        /* WHY: reloadAllRenderShaders() recompiles every render-to-texture
         * program cached in render.cpp's shaderProgramMap.  This covers
         * blackhole_main.frag, all bloom stages, tonemapping.frag, and
         * depth_cues.frag -- any shader routed through renderToTexture().
         * The compute shader (computeProgram) is managed here in main.cpp;
         * resetting it to 0 triggers lazy re-creation on the next frame. */
        reloadAllRenderShaders();

        if (computeProgram != 0) {
          glDeleteProgram(computeProgram);
          computeProgram = 0;
          std::cout << "[HotReload] Queued recompile: shader/geodesic_trace.comp\n";
        }
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
      TRACY_PLOT("cpu_frame_ms", cpuFrameMs);
      if (gpuTimers.initialized) {
        TRACY_PLOT("gpu_fragment_ms", gpuTimers.blackholeFragment.lastMs);
        TRACY_PLOT("gpu_compute_ms", gpuTimers.blackholeCompute.lastMs);
        TRACY_PLOT("gpu_bloom_ms", gpuTimers.bloom.lastMs);
        TRACY_PLOT("gpu_tonemap_ms", gpuTimers.tonemap.lastMs);
        TRACY_PLOT("gpu_depth_ms", gpuTimers.depth.lastMs);
        TRACY_PLOT("gpu_grmhd_slice_ms", gpuTimers.grmhdSlice.lastMs);
      }

      // --record-frames: one-time initialization (cinematic quality, 1920x1080, no vsync)
      if (!recordFramesDir.empty() && !recordInitDone) {
        std::error_code recordDirEc;
        std::filesystem::create_directories(recordFramesDir, recordDirEc);
        if (recordDirEc) {
          std::fprintf(stderr, "record output directory create failed: %s (%s)\n",
                       recordFramesDir.c_str(), recordDirEc.message().c_str());
          return 1;
        }
        recordInitDone     = true;
        int recordWidth = 1920;
        int recordHeight = 1080;
        if (char const *const envWidth = std::getenv("BLACKHOLE_RECORD_WIDTH")) {
          int const parsed = std::atoi(envWidth);
          if (parsed > 0) {
            recordWidth = parsed;
          }
        }
        if (char const *const envHeight = std::getenv("BLACKHOLE_RECORD_HEIGHT")) {
          int const parsed = std::atoi(envHeight);
          if (parsed > 0) {
            recordHeight = parsed;
          }
        }
        glfwSetWindowSize(window, recordWidth, recordHeight);
        glfwSwapInterval(0);
        swapInterval       = 0;
        if (recordProfile == "compare-orbit-near") {
          adiskEnabled       = false;
          adiskParticle      = false;
          enableRedshift     = false;
          enablePhotonSphere = false;
          hawkingGlowEnabled = false;
          rteVolumetricEnabled = false;
          stokesEnabled      = false;
          useNoiseTexture    = false;
          noiseTextureReady  = true;
          adiskNoiseLOD      = 3.0f;
          adiskNoiseScale    = 0.5f;
          adiskDensityV      = 2.0f;
          adiskLit           = 0.25f;
          dopplerStrength    = 1.0f;
          photonSphereGlowStrength = 1.0f;
          bloomIterations    = 4;
          bloomStrength      = 0.08f;
          tonemappingEnabled = true;
          toneExposure       = 6.0f;
          gamma              = 2.35f;
          computeMaxSteps    = 1000;
          computeStepSize    = 0.02f;
          depthFar           = 154.367004f;
          kerrSpin           = 0.0f;
          SettingsManager::instance().get().backgroundId = "eso_milkyway_brunier";
          SettingsManager::instance().get().backgroundEnabled = true;
          SettingsManager::instance().get().backgroundIntensity = 0.8f;
          CameraState &camMutable = input.camera();
          camMutable = CameraState{.yaw = -90.0f, .pitch = 0.0f, .roll = 0.0f, .distance = 10.0f, .fov = 90.0f};
          cameraModeIndex = static_cast<int>(CameraMode::Input);
        } else if (recordProfile == "showcase-orbit") {
          const ShowcaseOrbitComposition *const composition =
              findShowcaseOrbitComposition(recordComposition);
          adiskEnabled       = true;
          adiskParticle      = false;
          enableRedshift     = true;
          enablePhotonSphere = true;
          hawkingGlowEnabled = false;
          rteVolumetricEnabled = false;
          stokesEnabled      = false;
          useNoiseTexture    = false;
          noiseTextureReady  = true;
          adiskNoiseLOD      = 3.0f;
          adiskNoiseScale    = 0.35f;
          adiskDensityV      = 1.6f;
          adiskDensityH      = 2.1f;
          adiskHeight        = 0.42f;
          adiskLit           = 0.24f;
          dopplerStrength    = 1.15f;
          photonSphereGlowStrength = 1.15f;
          bloomIterations    = 5;
          bloomStrength      = 0.055f;
          tonemappingEnabled = true;
          toneExposure       = 1.0f;
          gamma              = 2.35f;
          computeMaxSteps    = 1000;
          computeStepSize    = 0.016f;
          depthFar           = 154.367004f;
          kerrSpin           = 0.62f;
          SettingsManager::instance().get().backgroundId =
              hasRecordBackgroundId
                  ? recordBackgroundId
                  : (composition != nullptr ? composition->backgroundId
                                            : "nasa_deep_starmap_galactic");
          SettingsManager::instance().get().backgroundEnabled = true;
          SettingsManager::instance().get().backgroundIntensity =
              composition != nullptr ? composition->backgroundIntensity : 0.72f;
          CameraState &camMutable = input.camera();
          camMutable = CameraState{
              .yaw = hasRecordYaw ? recordYawDeg : -90.0f,
              .pitch = hasRecordPitch ? recordPitchDeg
                                      : (composition != nullptr ? composition->pitchDeg : -6.0f),
              .roll = 0.0f,
              .distance = hasRecordDistance ? recordDistance
                                            : (composition != nullptr ? composition->distance
                                                                      : 14.0f),
              .fov = hasRecordFov ? recordFovDeg
                                  : (composition != nullptr ? composition->fovDeg : 68.0f)};
          if (hasRecordExposure) {
            toneExposure = recordExposure;
          } else if (composition != nullptr) {
            toneExposure = composition->exposure;
          }
          cameraModeIndex = static_cast<int>(CameraMode::Input);
        } else {
          // Physics: on, but not everything -- avoids noise pileup / fuzz
          adiskEnabled       = true;
          adiskParticle      = false;  // particle mode adds visual noise
          enableRedshift     = true;
          enablePhotonSphere = true;
          hawkingGlowEnabled = false;  // haze effect competes with disk shading
          rteVolumetricEnabled = false; // volumetric fog washes out fine detail
          stokesEnabled      = false;
          // Skip noise texture LUT generation in record mode: FastNoise2
          // SIMD code has a heap double-free at >= 128^3 on this system.
          // The disk looks clean without it.
          useNoiseTexture    = false;
          noiseTextureReady  = true;   // mark done so we never call initialize()
          adiskNoiseLOD      = 3.0f;
          adiskNoiseScale    = 0.5f;
          adiskDensityV      = 1.4f;
          adiskLit           = 0.08f;
          dopplerStrength    = 1.0f;
          photonSphereGlowStrength = 1.0f;
          // Post-processing: preserve ring detail instead of washing it out
          bloomIterations    = 3;
          bloomStrength      = 0.03f;
          tonemappingEnabled = true;
          toneExposure       = 0.02f;
          gamma              = 2.25f;
          // Integration quality
          computeMaxSteps    = 500;   // more steps for wide shots at 350+ rs
          computeStepSize    = 0.08f;
          // Escape radius must exceed the maximum camera distance (380 rs).
          // depthFar is passed as interop.depthFar and used as the ray max_dist.
          depthFar           = 500.0f;
          kerrSpin           = K_CINEMATIC_KEYFRAMES[0].kerrSpin;
          // Background: override to the ESO Milky Way panorama which ships as a real
          // JPEG (not a Git LFS pointer) -- the default "nasa_pia22085" is LFS-tracked.
          SettingsManager::instance().get().backgroundId = "eso_milkyway_brunier";
          SettingsManager::instance().get().backgroundEnabled = true;
          SettingsManager::instance().get().backgroundIntensity = 0.8f;
        }
#if BLACKHOLE_HAS_CUDA
        // Keep legacy record profiles on the CUDA path in the hybrid app, but let
        // showcase-orbit remain a true GLSL lane for apples-to-apples captures.
        if (recordProfile != "showcase-orbit") {
          // isEnabled() gates the CUDA dispatch path (line ~4295). It is normally set
          // via the ImGui "Use CUDA Raytracer" checkbox; record mode must set it directly.
          // useComputeRaytracer alone is insufficient -- it only controls the GLSL compute
          // path, not the CUDA path.
          cudaManager.setEnabled(true);
        } else {
          cudaManager.setEnabled(false);
          useComputeRaytracer = false;
          compareComputeFragment = false;
        }
#endif
        std::printf("Record mode: dir=%s  frames=%d  duration=%.0f s @ %d fps\n",
                    recordFramesDir.c_str(), recordFramesTotal,
                    static_cast<double>(K_CINEMATIC_DURATION_S), K_CINEMATIC_FPS);
        std::printf("Record profile: %s\n", recordProfile.c_str());
      }

      ImGui_ImplOpenGL3_NewFrame();
      ImGui_ImplGlfw_NewFrame();
      ImGui::NewFrame();
      ImGuizmo::BeginFrame();

      int windowWidth;
      int windowHeight;
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
      ImGuiID const dockspaceId = ImGui::GetID("MyDockSpace");
      ImGui::DockSpaceOverViewport(dockspaceId, ImGui::GetMainViewport(), ImGuiDockNodeFlags_None);

      if (firstLayout) {
        resetLayout(dockspaceId);
        firstLayout = false;
      }

      ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(0.0f, 0.0f));
      ImGui::Begin("Viewport", nullptr,
                   ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse |
                       ImGuiWindowFlags_NoTitleBar);
      ImVec2 viewportSize = ImGui::GetContentRegionAvail();

      // Resize render targets to match viewport
      if (viewportSize.x > 0 && viewportSize.y > 0 &&
          (static_cast<int>(viewportSize.x) != renderWidth ||
           static_cast<int>(viewportSize.y) != renderHeight)) {
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

      static GLuint galaxy = loadCubemap(resourcePath("assets/skybox_nebula_dark"));
      static GLuint const colorMap = loadTexture2D(resourcePath("assets/color_map.png"));
      static std::vector<BackgroundAsset> backgroundAssets;
      static int backgroundIndex = 0;
      static std::string backgroundLoadedId;
      static std::string skyboxLoadedDir;
      static GLuint backgroundBase = 0;
      static std::array<GLuint, K_BACKGROUND_LAYERS> backgroundTextures = {};
      static std::array<glm::vec4, K_BACKGROUND_LAYERS> backgroundLayerParams = {};
      static std::array<float, K_BACKGROUND_LAYERS> backgroundLayerDepth = {0.2f, 0.5f, 0.9f};
      static std::array<float, K_BACKGROUND_LAYERS> backgroundLayerScale = {1.0f, 1.08f, 1.16f};
      static std::array<float, K_BACKGROUND_LAYERS> backgroundLayerIntensity = {1.0f, 0.6f, 0.35f};
      static std::array<float, K_BACKGROUND_LAYERS> backgroundLayerLodBias = {0.0f, 1.0f, 2.0f};
      static glm::vec2 backgroundLayerGlobalOffset = glm::vec2(0.0f);
      static float backgroundYawRad = 0.0f;
      static float backgroundPitchRad = 0.0f;
      static float tonemapChromaticAberrationStrength = 0.002f;
      static float tonemapVignetteStrength = 1.0f;
      static float tonemapFilmGrainStrength = 0.005f;
      if (!recordFramesDir.empty() && recordProfile == "showcase-orbit") {
        const ShowcaseOrbitComposition *const composition =
            findShowcaseOrbitComposition(recordComposition);
        backgroundLayerScale = {1.0f, 1.18f, 1.42f};
        backgroundLayerIntensity = {1.0f, 0.94f, 0.72f};
        backgroundLayerLodBias = {0.45f, 1.2f, 1.9f};
        backgroundLayerGlobalOffset =
            composition != nullptr
                ? glm::vec2(composition->backgroundOffsetX, composition->backgroundOffsetY)
                : glm::vec2(0.0f);
        backgroundYawRad = glm::radians(hasRecordBackgroundYaw
                                            ? recordBackgroundYawDeg
                                            : (composition != nullptr ? composition->backgroundYawDeg
                                                                      : 0.0f));
        backgroundPitchRad = glm::radians(hasRecordBackgroundPitch
                                              ? recordBackgroundPitchDeg
                                              : (composition != nullptr
                                                     ? composition->backgroundPitchDeg
                                                     : 0.0f));
        tonemapChromaticAberrationStrength = 0.00015f;
        tonemapVignetteStrength = 0.05f;
        tonemapFilmGrainStrength = 0.0f;
      } else {
        backgroundLayerScale = {1.0f, 1.08f, 1.16f};
        backgroundLayerIntensity = {1.0f, 0.6f, 0.35f};
        backgroundLayerLodBias = {0.0f, 1.0f, 2.0f};
        backgroundLayerGlobalOffset = glm::vec2(0.0f);
        backgroundYawRad = 0.0f;
        backgroundPitchRad = 0.0f;
        tonemapChromaticAberrationStrength = 0.002f;
        tonemapVignetteStrength = 1.0f;
        tonemapFilmGrainStrength = 0.005f;
      }
      static bool wiregridEnabled = false;
      static WiregridParams wiregridParams;
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
            std::cmp_greater_equal(backgroundIndex, backgroundAssets.size())) {
          backgroundIndex = 0;
        }
        const auto &asset = backgroundAssets.at(static_cast<std::size_t>(backgroundIndex));
        if (backgroundLoadedId != asset.id) {
          GLuint const nextTexture = loadTexture2D(asset.path, true);
          if (nextTexture != 0) {
            if (backgroundBase != 0) {
              glDeleteTextures(1, &backgroundBase);
            }
            backgroundBase = nextTexture;
            backgroundLoadedId = asset.id;
          }
          // Swap cubemap skybox if the asset specifies one.
          if (!asset.skyboxDir.empty() && skyboxLoadedDir != asset.skyboxDir) {
            GLuint const nextCubemap = loadCubemap(asset.skyboxDir);
            if (nextCubemap != 0) {
              if (galaxy != 0) {
                glDeleteTextures(1, &galaxy);
              }
              galaxy = nextCubemap;
              skyboxLoadedDir = asset.skyboxDir;
            }
          }
        }
      }
      GLuint const backgroundFallback = backgroundBase != 0 ? backgroundBase : fallback2D;
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
        toneExposure = 1.0f;
        gamma = settings.gamma;
        postProcessingSettingsLoaded = true;
      }
      if (!recordFramesDir.empty()) {
        const ShowcaseOrbitComposition *const composition =
            recordProfile == "showcase-orbit" ? findShowcaseOrbitComposition(recordComposition)
                                              : nullptr;
        if (hasRecordExposure) {
          toneExposure = recordExposure;
        } else if (recordProfile == "showcase-orbit") {
          toneExposure = composition != nullptr ? composition->exposure : 3.4f;
        }
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
      bool const compareSweepAllowed =
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
        int const presetCount = static_cast<int>(K_COMPARE_PRESETS.size());
        comparePresetIndex = std::clamp(comparePresetIndex, 0, presetCount);
        if (comparePresetIndex >= presetCount) {
          comparePresetSweep = false;
          compareRestorePending = true;
        } else {
          const auto &preset = K_COMPARE_PRESETS.at(static_cast<std::size_t>(comparePresetIndex));
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

      // --record-frames: drive camera and spin from the selected record path
      if (!recordFramesDir.empty()) {
        if (recordProfile == "compare-orbit-near") {
          float const denom = static_cast<float>(std::max(recordFramesTotal - 1, 1));
          float const progress =
              static_cast<float>(recordFrameIndex - recordStartFrame) / denom;
          CameraState &camMutable = input.camera();
          camMutable.yaw = -90.0f + progress * 18.0f;
          camMutable.pitch = 0.0f;
          camMutable.roll = 0.0f;
          camMutable.distance = 10.0f;
          camMutable.fov = 90.0f;
          cameraModeIndex = static_cast<int>(CameraMode::Input);
          kerrSpin = 0.0f;
        } else if (recordProfile == "showcase-orbit") {
          const ShowcaseOrbitComposition *const composition =
              findShowcaseOrbitComposition(recordComposition);
          float const denom = static_cast<float>(std::max(recordFramesTotal - 1, 1));
          float const progress =
              static_cast<float>(recordFrameIndex - recordStartFrame) / denom;
          float const baseYaw = hasRecordYaw ? recordYawDeg : -90.0f;
          float const sweepDeg =
              hasRecordSweep ? recordSweepDeg
                             : (composition != nullptr ? composition->sweepDeg : 10.0f);
          CameraState &camMutable = input.camera();
          camMutable.yaw = baseYaw + progress * sweepDeg;
          camMutable.pitch = hasRecordPitch ? recordPitchDeg
                                            : (composition != nullptr ? composition->pitchDeg
                                                                      : -6.0f);
          camMutable.roll = 0.0f;
          camMutable.distance = hasRecordDistance ? recordDistance
                                                  : (composition != nullptr
                                                         ? composition->distance
                                                         : 14.0f);
          camMutable.fov = hasRecordFov ? recordFovDeg
                                        : (composition != nullptr ? composition->fovDeg : 68.0f);
          cameraModeIndex = static_cast<int>(CameraMode::Input);
          kerrSpin = 0.0f;
          recordCurrentKf = CamKeyframe{
              .t_sec = static_cast<float>(recordFrameIndex - recordStartFrame) /
                       static_cast<float>(K_CINEMATIC_FPS),
              .cam = camMutable,
              .kerrSpin = kerrSpin,
              .caption = "Showcase orbit",
          };
        } else {
          recordCurrentKf = recordPath.evaluate(recordCinematic);
          CameraState &camMutable = input.camera();
          camMutable   = recordCurrentKf.cam;
          cameraModeIndex = static_cast<int>(CameraMode::Input);
          kerrSpin     = recordCurrentKf.kerrSpin;
        }
      }

      // Get camera state for shader
      const auto &cam = input.camera();
      cameraModeIndex = std::clamp(cameraModeIndex, 0, 3);
      orbitRadius = std::max(orbitRadius, 2.0f);
      orbitSpeed = std::max(orbitSpeed, 0.0f);

      glm::vec3 const focusTarget =
          gizmoEnabled ? glm::vec3(gizmoTransform[3]) : glm::vec3(0.0f); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                                         // -- glm::mat has no .at()

      orbitTime += input.getEffectiveDeltaTime(deltaTime);
      glm::vec3 cameraPos;
      auto const cameraMode = static_cast<CameraMode>(cameraModeIndex);
      switch (cameraMode) {
      case CameraMode::Front:
        cameraPos = focusTarget + glm::vec3(10.0f, 1.0f, 10.0f);
        break;
      case CameraMode::Top:
        cameraPos = focusTarget + glm::vec3(15.0f, 15.0f, 0.0f);
        break;
      case CameraMode::Orbit: {
        float const angle = orbitTime * glm::radians(orbitSpeed);
        cameraPos =
            focusTarget + glm::vec3(-std::cos(angle) * orbitRadius, std::sin(angle) * orbitRadius,
                                    std::sin(angle) * orbitRadius);
        break;
      }
      case CameraMode::Input:
      default:
        cameraPos = focusTarget + cameraPositionFromYawPitch(cam.yaw, cam.pitch, cam.distance);
        break;
      }

      glm::vec3 aimTarget = focusTarget;
      if (!recordFramesDir.empty() && recordProfile == "showcase-orbit") {
        const ShowcaseOrbitComposition *const composition =
            findShowcaseOrbitComposition(recordComposition);
        float const frameX =
            hasRecordFrameX ? recordFrameX
                            : (composition != nullptr ? composition->frameOffsetX : 0.0f);
        float const frameY =
            hasRecordFrameY ? recordFrameY
                            : (composition != nullptr ? composition->frameOffsetY : 0.0f);
        if (std::abs(frameX) > 0.0001f || std::abs(frameY) > 0.0001f) {
          glm::mat3 const baseBasis = buildCameraBasis(cameraPos, focusTarget, cam.roll);
          float const halfHeight = std::tan(glm::radians(cam.fov) * 0.5f) * cam.distance;
          float const aspect =
              static_cast<float>(std::max(renderWidth, 1)) /
              static_cast<float>(std::max(renderHeight, 1));
          float const halfWidth = halfHeight * aspect;
          aimTarget = focusTarget + baseBasis[0] * (frameX * halfWidth) +
                      baseBasis[1] * (frameY * halfHeight);
        }
      }

      glm::mat3 cameraBasis = buildCameraBasis(cameraPos, aimTarget, cam.roll);
      float const fovScale = std::tan(glm::radians(cam.fov) * 0.5f);
      glm::mat4 viewRotation(1.0f);
      viewRotation[0] = glm::vec4(cameraBasis[0], 0.0f); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                         // -- glm::mat has no .at()
      viewRotation[1] = glm::vec4(cameraBasis[1], 0.0f); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                         // -- glm::mat has no .at()
      viewRotation[2] = glm::vec4(cameraBasis[2], 0.0f); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                         // -- glm::mat has no .at()

      glm::vec2 const parallaxBase =
          glm::vec2(cameraPos.x, cameraPos.y) * settings.backgroundParallaxStrength;
      glm::vec2 const drift = glm::vec2(std::cos(static_cast<float>(currentTime) * 0.02f),
                                        std::sin(static_cast<float>(currentTime) * 0.02f)) *
                              settings.backgroundDriftStrength;
      for (std::size_t i = 0; i < static_cast<std::size_t>(K_BACKGROUND_LAYERS); ++i) {
        glm::vec2 const offset = drift + parallaxBase * backgroundLayerDepth.at(i);
        backgroundLayerParams.at(i) =
            glm::vec4(offset + backgroundLayerGlobalOffset, backgroundLayerScale.at(i),
                      backgroundLayerIntensity.at(i));
      }
      glm::mat4 projectionMatrix = glm::perspective(
          glm::radians(cam.fov), static_cast<float>(renderWidth) / static_cast<float>(renderHeight),
          0.1f, depthFar);
      glm::mat4 gizmoViewMatrix =
          glm::lookAt(cameraPos, aimTarget, cameraBasis[1]); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                               // -- glm::mat has no .at()
      bool computeActiveForLog = false;

      /* Per-frame streaming tile upload: when GRMHDStreamer is running and the
       * PBOUploader is initialized, obtain the current frame tile and upload.
       * getTile() is non-blocking; on a cache miss it enqueues the request. */
      if (grmhdStreamer && grmhdPboUploader.texture() != 0) {
        auto tile = grmhdStreamer->getTile(0, 0, 0, 0);
        if (tile && tile->ready()) {
          grmhdPboUploader.upload(tile->data.data(), tile->data.size());
        }
      }
      /* C1d: upload adjacent (next) frame into the right PBO uploader for
       * temporal interpolation.  getAdjacentTile() returns nullptr at the last
       * frame or on a cache miss (seekFrame prefetch keeps it warm).
       * grmhdFrameAlpha is the sub-frame blend fraction; sub-frame position is
       * approximated as the fractional part of (current_frame + time_bias). */
      grmhdFrameAlpha = 0.0f;
      if (grmhdStreamer && grmhdPboUploaderRight.texture() != 0) {
        auto rightTile = grmhdStreamer->getAdjacentTile(0, 0, 0, 0);
        if (rightTile && rightTile->ready()) {
          grmhdPboUploaderRight.upload(rightTile->data.data(), rightTile->data.size());
        }
        /* Advance CUDA slot 7 registration when the right PBO first becomes ready */
#if BLACKHOLE_HAS_CUDA
        if (grmhdPboUploaderRight.ready()) {
          static GLuint registeredRightTex = 0;
          if (registeredRightTex != grmhdPboUploaderRight.texture()) {
            registeredRightTex = grmhdPboUploaderRight.texture();
            cudaManager.registerLut(7 /*BhLutGrmhdRight*/, registeredRightTex,
                                    static_cast<unsigned int>(GL_TEXTURE_3D));
          }
        }
#endif
        if (grmhdPboUploaderRight.ready()) {
          /* Sub-frame alpha: fraction of inter-frame interval elapsed.
           * grmhdPlaybackSpeed controls simulation-time advance per real second. */
          grmhdFrameAlpha = std::fmod(
              static_cast<float>(grmhdCurrentFrame) * grmhdPlaybackSpeed, 1.0f);
          grmhdFrameAlpha = std::max(0.0f, std::min(1.0f, grmhdFrameAlpha));
        }
      }

      /* grmhdReady: true when packed texture OR PBO streaming path is valid. */
      bool const grmhdReady = (grmhdLoaded && grmhdTexture.texture != 0) ||
                              (grmhdTimeSeriesLoaded && grmhdPboUploader.ready());
      bool grmhdEnabled = useGrmhd && grmhdReady;
      /* grmhdTexId: prefer PBO streaming texture when the streamer is running;
       * fall back to the packed static texture otherwise. */
      GLuint const grmhdTexId =
          (grmhdTimeSeriesLoaded && grmhdPboUploader.ready())
              ? grmhdPboUploader.texture()
              : grmhdTexture.texture;
      bool const spectralReady = spectralLutLoaded && texSpectralLUT != 0;
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
          int const lutSize = static_cast<int>(grbModulationValues.size());
          texGrbModulationLUT = createFloatTexture2D(lutSize, 1, grbModulationValues);
          grbTimeManualValue = grbTimeMin;
        }
      }
      bool const grbModulationReady = grbModulationLoaded && texGrbModulationLUT != 0;
      bool grbModulationEnabled = false;
      float const grbSpan = std::max(grbTimeMax - grbTimeMin, 0.001f);
      float grbTimeSeconds = 0.0f;
      if (grbModulationReady) {
        if (grbTimeManual) {
          grbTimeSeconds = std::clamp(grbTimeManualValue, grbTimeMin, grbTimeMax);
        } else {
          grbTimeSeconds = grbTimeMin + std::fmod(static_cast<float>(currentTime), grbSpan);
        }
      }

      bool const lutReady = texEmissivityLUT != 0 && texRedshiftLUT != 0;

      {
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/blackhole_main.frag";
        rtti.cubemapUniforms["galaxy"] = galaxy != 0 ? galaxy : fallbackCubemap;
        rtti.textureUniforms["colorMap"] = colorMap != 0 ? colorMap : fallback2D;
        rtti.textureUniforms["emissivityLUT"] = lutReady ? texEmissivityLUT : fallback2D;
        rtti.textureUniforms["redshiftLUT"] = lutReady ? texRedshiftLUT : fallback2D;
        rtti.textureUniforms["photonGlowLUT"] =
            texPhotonGlowLUT != 0 ? texPhotonGlowLUT : fallback2D; // Phase 8.2
        rtti.textureUniforms["diskDensityLUT"] =
            texDiskDensityLUT != 0 ? texDiskDensityLUT : fallback2D; // Phase 8.2 P2
        rtti.textureUniforms["spectralLUT"] = spectralEnabled ? texSpectralLUT : fallback2D;
        rtti.textureUniforms["grbModulationLUT"] =
            grbModulationReady ? texGrbModulationLUT : fallback2D;
        rtti.textureUniforms["hawkingTempLUT"] =
            hawkingLutsLoaded ? hawkingRenderer.getTempLUTTexture() : fallback2D;
        rtti.textureUniforms["hawkingSpectrumLUT"] =
            hawkingLutsLoaded ? hawkingRenderer.getSpectrumLUTTexture() : fallback2D;
        for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
          const std::string name = "backgroundLayers[" + std::to_string(i) + "]";
          rtti.textureUniforms[name] = backgroundTextures.at(static_cast<std::size_t>(i));
        }
        noiseTextureScale = std::max(noiseTextureScale, 0.01f);
        bool noiseReady = useNoiseTexture && texNoiseVolume != 0;
        rtti.texture3DUniforms["noiseTexture"] = noiseReady ? texNoiseVolume : fallback3D;
        rtti.texture3DUniforms["grmhdTexture"] = grmhdEnabled ? grmhdTexId : fallback3D;

        rtti.floatUniforms["useNoiseTexture"] = noiseReady ? 1.0f : 0.0f;
        rtti.floatUniforms["useGrmhd"] = grmhdEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["noiseTextureScale"] = noiseTextureScale;
        rtti.floatUniforms["backgroundEnabled"] = settings.backgroundEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["backgroundIntensity"] = settings.backgroundIntensity;
        rtti.floatUniforms["backgroundYawRad"] = backgroundYawRad;
        rtti.floatUniforms["backgroundPitchRad"] = backgroundPitchRad;
        rtti.floatUniforms["time"] = frameTime;
        rtti.vec3Uniforms["grmhdBoundsMin"] = grmhdBoundsMin;
        rtti.vec3Uniforms["grmhdBoundsMax"] = grmhdBoundsMax;
        for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
          const std::string name = "backgroundLayerParams[" + std::to_string(i) + "]";
          rtti.vec4Uniforms[name] = backgroundLayerParams.at(static_cast<std::size_t>(i));
        }
        for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
          const std::string name = "backgroundLayerLodBias[" + std::to_string(i) + "]";
          rtti.floatUniforms[name] =
              std::max(backgroundLayerLodBias.at(static_cast<std::size_t>(i)), 0.0f);
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

              ImGui::Separator();
              ImGui::Text("Volumetric RTE (D2)");
              ImGui::Checkbox("Volumetric RTE", &rteVolumetricEnabled);
              if (rteVolumetricEnabled) {
                ImGui::SliderFloat("RTE Opacity Scale", &rteOpacityScale, 0.0f, 5.0f);
              }

              ImGui::Separator();
              ImGui::Text("Polarized Stokes IQUV (D4)");
              ImGui::Checkbox("Stokes Transport", &stokesEnabled);
              if (stokesEnabled) {
                ImGui::SliderFloat("B Field Angle (rad)", &stokesBFieldAngle, -3.14159f, 3.14159f);
                ImGui::SliderFloat("Faraday Ne Scale",   &stokesNeScale,     0.0f, 5.0f);
              }

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
                ImGui::TextColored(ImVec4(1.0f, 0.35f, 0.35f, 1.0f), "%s", grmhdLoadError.c_str());
              }
              if (grmhdLoaded) {
                ImGui::Text("GRMHD grid: %d x %d x %d", grmhdTexture.width, grmhdTexture.height,
                            grmhdTexture.depth);
              }
              ImGui::SliderFloat3("GRMHD Bounds Min", &grmhdBoundsMin.x, -50.0f, 50.0f);
              ImGui::SliderFloat3("GRMHD Bounds Max", &grmhdBoundsMax.x, -50.0f, 50.0f);
              ImGui::BeginDisabled(!grmhdLoaded);
              ImGui::Checkbox("Show GRMHD Slice", &grmhdSliceEnabled);
              const char *const axisLabels[] = {"X", "Y", "Z"};
              ImGui::Combo("Slice Axis", &grmhdSliceAxis, axisLabels, 3);
              ImGui::SliderFloat("Slice Coord", &grmhdSliceCoord, 0.0f, 1.0f);
              ImGui::SliderInt("Slice Channel", &grmhdSliceChannel, 0, 3);
              if (grmhdLoaded && grmhdSliceChannel >= 0 &&
                  static_cast<std::size_t>(grmhdSliceChannel) < grmhdTexture.channels.size()) {
                auto const channelIndex = static_cast<std::size_t>(grmhdSliceChannel);
                ImGui::Text("Channel: %s", grmhdTexture.channels.at(channelIndex).c_str());
              }
              ImGui::Checkbox("Slice Auto Range", &grmhdSliceAutoRange);
              if (!grmhdSliceAutoRange) {
                ImGui::InputFloat("Slice Min", &grmhdSliceMin);
                ImGui::InputFloat("Slice Max", &grmhdSliceMax);
              }
              ImGui::Checkbox("Slice Color Map", &grmhdSliceUseColorMap);
              ImGui::SliderInt("Slice Size", &grmhdSliceSize, 64, 1024);
              if (texGrmhdSlice != 0) {
                auto const sliceId =
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
                /* Shut down any previously loaded dataset */
                if (grmhdStreamer) {
                  grmhdStreamer->shutdown();
                  grmhdStreamer.reset();
                  grmhdTimeSeriesLoaded = false;
                }
                std::string const jsonPath(grmhdTimeSeriesJsonBuffer.data());
                std::string const binPath(grmhdTimeSeriesBinBuffer.data());
                if (!jsonPath.empty()) {
                  grmhdStreamer = std::make_unique<blackhole::GRMHDStreamer>(jsonPath, binPath);
                  if (grmhdStreamer->init()) {
                    grmhdTimeSeriesLoaded = true;
                    grmhdMaxFrame = static_cast<int>(grmhdStreamer->metadata().frameCount) - 1;
                    grmhdCurrentFrame = 0;
                    grmhdStreamer->seekFrame(0);
                    /* Initialize PBOUploader with the grid dimensions from metadata.
                     * Shuts down any previous allocation first. */
                    const auto &meta = grmhdStreamer->metadata();
                    if (grmhdPboUploader.texture() != 0) {
                      grmhdPboUploader.shutdown();
                    }
                    grmhdPboUploader.init(static_cast<int>(meta.gridX),
                                         static_cast<int>(meta.gridY),
                                         static_cast<int>(meta.gridZ));
                    /* C1d: initialize right-frame uploader with same dimensions */
                    if (grmhdPboUploaderRight.texture() != 0) {
                      grmhdPboUploaderRight.shutdown();
                    }
                    grmhdPboUploaderRight.init(static_cast<int>(meta.gridX),
                                              static_cast<int>(meta.gridY),
                                              static_cast<int>(meta.gridZ));
                  } else {
                    grmhdStreamer.reset();
                  }
                }
              }
              ImGui::SameLine();
              if (ImGui::Button("Unload Time-Series")) {
                if (grmhdStreamer) {
                  grmhdStreamer->shutdown();
                  grmhdStreamer.reset();
                }
                grmhdPboUploader.shutdown();
                grmhdPboUploaderRight.shutdown();  /* C1d: tear down right-frame uploader */
                grmhdFrameAlpha = 0.0f;
                grmhdTimeSeriesLoaded = false;
                grmhdCurrentFrame = 0;
                grmhdMaxFrame = 0;
                grmhdPlaying = false;
                grmhdCacheHitRate = 0.0;
                grmhdQueueDepth = 0;
              }

              ImGui::BeginDisabled(!grmhdTimeSeriesLoaded);

              // Frame control
              ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Playback");
              if (ImGui::SliderInt("Frame", &grmhdCurrentFrame, 0, grmhdMaxFrame)) {
                if (grmhdStreamer) {
                  grmhdStreamer->seekFrame(static_cast<uint32_t>(grmhdCurrentFrame));
                }
              }
              ImGui::Text("Time: %.2f s", static_cast<double>(grmhdCurrentFrame) / 30.0);

              // Play/Pause button
              if (grmhdPlaying) {
                if (ImGui::Button("Pause")) {
                  grmhdPlaying = false;
                  if (grmhdStreamer) { grmhdStreamer->pause(); }
                }
              } else {
                if (ImGui::Button("Play")) {
                  grmhdPlaying = true;
                  if (grmhdStreamer) { grmhdStreamer->play(); }
                }
              }
              ImGui::SameLine();
              if (ImGui::Button("Reset")) {
                grmhdCurrentFrame = 0;
                if (grmhdStreamer) { grmhdStreamer->seekFrame(0); }
              }

              // Playback speed
              if (ImGui::SliderFloat("Playback Speed", &grmhdPlaybackSpeed, 0.1f, 4.0f)) {
                if (grmhdStreamer) {
                  grmhdStreamer->setPlaybackSpeed(static_cast<double>(grmhdPlaybackSpeed));
                }
              }

              // Cache statistics
              /* Refresh cache stats from live streamer each frame */
              if (grmhdStreamer) {
                grmhdCacheHitRate = grmhdStreamer->cacheHitRate();
                grmhdQueueDepth = static_cast<int>(grmhdStreamer->queueDepth());
                /* Mirror current frame from streamer (updated by background thread) */
                grmhdCurrentFrame = static_cast<int>(grmhdStreamer->currentFrame());
              }

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

              ImGui::EndDisabled(); // !grmhdTimeSeriesLoaded
              ImGui::EndDisabled(); // !grmhdTimeSeriesEnabled

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
                const char *const presetLabels[] = {"Physical", "Primordial", "Extreme"};
                if (ImGui::Combo("Preset", &hawkingPreset, presetLabels, 3)) {
                  // Apply preset
                  auto const preset = static_cast<physics::HawkingPreset>(hawkingPreset);
                  physics::HawkingGlowParams const params =
                      physics::HawkingRenderer::applyPreset(preset);
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
              const double referenceRs = physics::schwarzschildRadius(referenceMass);
              const double referenceRg = physics::G * referenceMass / physics::C2;
              const double referenceA = static_cast<double>(kerrSpin) * referenceRg;
              const bool progradeSpin = kerrSpin >= 0.0f;
              const double iscoRatio =
                  physics::kerrIscoRadius(referenceMass, referenceA, progradeSpin) / referenceRs;
              const double photonRatio =
                  (progradeSpin ? physics::kerrPhotonOrbitPrograde
                                : physics::kerrPhotonOrbitRetrograde)(referenceMass, referenceA) /
                  referenceRs;

              float const schwarzschildRadius = 2.0f * blackHoleMass;
              float const photonSphereRadius =
                  static_cast<float>(photonRatio) * schwarzschildRadius;
              float const iscoRadius = static_cast<float>(iscoRatio) * schwarzschildRadius;
              ImGui::Text("r_s = %.2f, r_ph = %.2f, r_ISCO = %.2f",
                          static_cast<double>(schwarzschildRadius),
                          static_cast<double>(photonSphereRadius), static_cast<double>(iscoRadius));

              ImGui::EndTabItem();
            }
            if (ImGui::BeginTabItem("Compute")) {
              ImGui::Text("Compute Raytracer");
              bool const computeAvailable = ShaderManager::instance().canUseComputeShaders();
              if (!computeAvailable) {
                ImGui::TextDisabled("Compute shaders unavailable");
                useComputeRaytracer = false;
                compareComputeFragment = false;
              }
              if (kAppVariantCudaOnly) {
                useComputeRaytracer = false;
                compareComputeFragment = false;
                ImGui::TextDisabled("Compute/fragment comparison is disabled in BlackholeCUDA.");
              } else {
                ImGui::Checkbox("Use Compute Raytracer", &useComputeRaytracer);
              }
              if (useComputeRaytracer && !kAppVariantCudaOnly) {
                ImGui::SliderInt("Compute Steps", &computeMaxSteps, 50, 600);
                ImGui::SliderFloat("Compute Step Size", &computeStepSize, 0.01f, 1.0f);
                ImGui::Checkbox("Compute Tiled", &computeTiled);
                if (computeTiled) {
                  ImGui::SliderInt("Compute Tile Size", &computeTileSize, 64, 1024);
                }
              }
#if BLACKHOLE_HAS_CUDA
              ImGui::Separator();
              ImGui::Text("CUDA Backend");
              {
                bool cudaEnabled = cudaManager.isEnabled();
                if (ImGui::Checkbox("Use CUDA Raytracer", &cudaEnabled)) {
                  cudaManager.setEnabled(cudaEnabled);
                }
              }
              if (cudaManager.isEnabled()) {
                const char *const variantNames[] = {"FP32 Baseline",
                                                    "FP32 Coarsened (2 ray/thread)", "FP16 Storage",
                                                    "FP16 H2 ILP (2 ray/thread)", "Auto"};
                int variantUI = cudaManager.kernelVariant() < 0 ? 4 : cudaManager.kernelVariant();
                if (ImGui::Combo("Kernel Variant", &variantUI, variantNames, 5)) {
                  cudaManager.setKernelVariant((variantUI >= 4) ? -1 : variantUI);
                }
                if (cudaManager.isReady()) {
                  int const actual = cudaManager.activeVariant();
                  if (actual >= 0 && actual < BH_KERNEL_COUNT) {
                    ImGui::TextDisabled("Active: %s", variantNames[actual]);
                  }
                } else if (cudaManager.wasInitAttempted()) {
                  ImGui::TextColored(ImVec4(1.f, 0.4f, 0.4f, 1.f),
                                     "Init failed -- toggle checkbox to retry");
                } else {
                  ImGui::TextDisabled("Will init on next frame");
                }
              }
              ImGui::Separator();
#endif
              if (!kAppVariantCudaOnly) {
                ImGui::Checkbox("Compare Compute vs Fragment", &compareComputeFragment);
              }
              if (compareComputeFragment && !kAppVariantCudaOnly) {
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
                ImGui::SliderFloat("Compare Step Size Override", &compareStepSizeOverride, 0.0f,
                                   2.0f);
                ImGui::EndDisabled();
                ImGui::Separator();
                ImGui::Text("Integrator Debug");
                bool debugNan = (integratorDebugFlags & K_INTEGRATOR_DEBUG_NAN_FLAG) != 0;
                bool debugRange = (integratorDebugFlags & K_INTEGRATOR_DEBUG_RANGE_FLAG) != 0;
                ImGui::Checkbox("Flag NaN/Inf", &debugNan);
                ImGui::SameLine();
                ImGui::Checkbox("Flag Out-of-Range", &debugRange);
                integratorDebugFlags = (debugNan ? K_INTEGRATOR_DEBUG_NAN_FLAG : 0) |
                                       (debugRange ? K_INTEGRATOR_DEBUG_RANGE_FLAG : 0);
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
                  std::size_t const presetCount = K_COMPARE_PRESETS.size();
                  int const displayIndex =
                      std::clamp(comparePresetIndex + 1, 1, static_cast<int>(presetCount));
                  auto const labelIndex = static_cast<std::size_t>(displayIndex - 1);
                  const char *label = K_COMPARE_PRESETS.at(labelIndex).label;
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
            curveOverlayLoaded = curveOverlay.loadFromTsv(curveTsvPath);
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
          spectralLutLoaded = loadSpectralLutAssets(spectralLutValues, spectralWavelengthMin,
                                                    spectralWavelengthMax);
          if (spectralLutLoaded && !spectralLutValues.empty()) {
            if (texSpectralLUT != 0) {
              glDeleteTextures(1, &texSpectralLUT);
              texSpectralLUT = 0;
            }
            int const lutSize = static_cast<int>(spectralLutValues.size());
            texSpectralLUT = createFloatTexture2D(lutSize, 1, spectralLutValues);
#if BLACKHOLE_HAS_CUDA
            /* Share spectral LUT with CUDA backend (slot 2=spectral) */
            cudaManager.registerLut(2, texSpectralLUT, static_cast<unsigned int>(GL_TEXTURE_2D));
#endif
            spectralRadiusMin = lutRadiusMin;
            spectralRadiusMax = lutRadiusMax;
            if (spectralRadiusMax <= spectralRadiusMin) {
              spectralRadiusMin = 0.0f;
              spectralRadiusMax = 1.0f;
            }
          }
        }

        /* Generate synchrotron G(x)=x*K_{2/3}(x) LUT once (task E5).
         * Stored as GL_TEXTURE_2D (width=256, height=1) so the same handle
         * can be registered for CUDA-GL interop via cudaGraphicsGLRegisterImage,
         * which does not support GL_TEXTURE_1D.  The GLSL path samples it
         * via sampler2D with y=0.5; the CUDA path uses tex2D at v=0.5. */
        if (!synchGLutCreated) {
          synchGLutCreated = true;
          constexpr int kSynchGLutSize = 256;
          std::vector<float> synchGData(static_cast<std::size_t>(kSynchGLutSize));
          physics::synchrotronGGenerateLut(synchGData.data(), kSynchGLutSize,
                                           static_cast<double>(physics::SYNCH_G_LUT_X_MIN),
                                           static_cast<double>(physics::SYNCH_G_LUT_X_MAX));
          if (texSynchGLut != 0) {
            glDeleteTextures(1, &texSynchGLut);
            texSynchGLut = 0;
          }
          texSynchGLut = createFloatTexture2D(kSynchGLutSize, 1, synchGData);
#if BLACKHOLE_HAS_CUDA
          cudaManager.registerLut(6 /*BhLutSynchG*/, texSynchGLut,
                                  static_cast<unsigned int>(GL_TEXTURE_2D));
#endif
        }

        // Load Hawking radiation LUTs
        if (!hawkingLutsLoaded) {
          std::filesystem::path const lutPath = resourcePath("assets/luts");
          if (std::filesystem::exists(lutPath)) {
            hawkingLutsLoaded = hawkingRenderer.loadLUTs(lutPath);
            if (hawkingLutsLoaded) {
              std::cout << "Hawking radiation LUTs loaded successfully" << '\n';
            } else {
              std::cerr << "Failed to load Hawking radiation LUTs" << '\n';
            }
          }
        }

        const double referenceMass = physics::M_SUN;
        const double referenceRs = physics::schwarzschildRadius(referenceMass);
        const double referenceRg = physics::G * referenceMass / physics::C2;
        const double referenceA = static_cast<double>(kerrSpin) * referenceRg;
        const bool progradeSpin = kerrSpin >= 0.0f;
        const double iscoRatio =
            physics::kerrIscoRadius(referenceMass, referenceA, progradeSpin) / referenceRs;

        float const schwarzschildRadius = 2.0f * blackHoleMass;
        float const iscoRadius = static_cast<float>(iscoRatio) * schwarzschildRadius;
        // Keep record-mode copies accessible outside this inner block
        recordCurRs   = schwarzschildRadius;
        recordCurIsco = iscoRadius;
#if BLACKHOLE_HAS_CUDA
        if (kAppVariantCudaOnly) {
          cudaManager.setEnabled(true);
          useComputeRaytracer = false;
          compareComputeFragment = false;
        }
#endif
        bool const computeSupported = ShaderManager::instance().canUseComputeShaders();
        bool const computeActive = useComputeRaytracer && computeSupported;
        bool const compareActive =
            compareComputeFragment && computeSupported && !kAppVariantCudaOnly;
        bool const compareBaselineActive = compareBaselineEnabled && compareActive;
        bool const adiskEnabledEffective = adiskEnabled && !compareBaselineActive;
        bool const adiskParticleEffective = adiskParticle && !compareBaselineActive;
        bool const enableRedshiftEffective = enableRedshift && !compareBaselineActive;
        bool const useNoiseTextureEffective = useNoiseTexture && !compareBaselineActive;
        bool const useGrmhdEffective = useGrmhd && !compareBaselineActive;
        bool const useSpectralLutEffective = useSpectralLut && !compareBaselineActive;
        bool const useGrbModulationEffective = useGrbModulation && !compareBaselineActive;
        bool const enablePhotonSphereEffective = enablePhotonSphere && !compareBaselineActive;
        bool const backgroundEnabledEffective =
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
        rtti.texture3DUniforms["grmhdTexture"] = grmhdEnabled ? grmhdTexId : fallback3D;
        rtti.textureUniforms["spectralLUT"] = spectralEnabled ? texSpectralLUT : fallback2D;
        rtti.textureUniforms["grbModulationLUT"] =
            grbModulationEnabled ? texGrbModulationLUT : fallback2D;
        rtti.textureUniforms["hawkingTempLUT"] =
            hawkingLutsLoaded ? hawkingRenderer.getTempLUTTexture() : fallback2D;
        rtti.textureUniforms["hawkingSpectrumLUT"] =
            hawkingLutsLoaded ? hawkingRenderer.getSpectrumLUTTexture() : fallback2D;
        rtti.floatUniforms["useNoiseTexture"] = noiseReady ? 1.0f : 0.0f;
        rtti.floatUniforms["useGrmhd"] = grmhdEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["backgroundEnabled"] = backgroundEnabledEffective ? 1.0f : 0.0f;
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
        // D2: volumetric RTE
        interop.rteEnabled      = rteVolumetricEnabled ? 1.0f : 0.0f;
        interop.rteOpacityScale = rteOpacityScale;

        // Convert black hole mass to grams (CGS units for Hawking calculation)
        double const bhMassGrams = static_cast<double>(blackHoleMass) * physics::M_SUN;
        applyInteropUniforms(rtti, interop, compareActive, hawkingGlowEnabled, hawkingTempScale,
                             hawkingGlowIntensity, hawkingUseLUTs, bhMassGrams);

        rtti.floatUniforms["wiregridEnabled"]   = wiregridEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["wiregridShowErgo"]  = wiregridParams.showErgosphere ? 1.0f : 0.0f;
        rtti.floatUniforms["wiregridGridScale"] = wiregridParams.gridScale;
        // D4: polarized Stokes IQUV
        rtti.floatUniforms["stokesEnabled"]     = stokesEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["stokesBFieldAngle"] = stokesBFieldAngle;
        rtti.floatUniforms["stokesNeScale"]     = stokesNeScale;
        rtti.floatUniforms["gravitationalLensing"] = gravitationalLensing ? 1.0f : 0.0f;
        rtti.floatUniforms["renderBlackHole"] = renderBlackHole ? 1.0f : 0.0f;
        rtti.floatUniforms["adiskParticle"] = adiskParticleEffective ? 1.0f : 0.0f;
        // rtti.floatUniforms["adiskDensityV"] = adiskDensityV; // Removed: consumed by LUT
        // generation
        rtti.floatUniforms["adiskDensityH"] = adiskDensityH;
        rtti.floatUniforms["adiskHeight"] = adiskHeight;
        rtti.floatUniforms["adiskLit"] = adiskLit;
        rtti.floatUniforms["adiskNoiseLOD"] = adiskNoiseLOD;
        rtti.floatUniforms["adiskNoiseScale"] = adiskNoiseScale;
        rtti.floatUniforms["adiskSpeed"] = adiskSpeed;
        rtti.floatUniforms["dopplerStrength"] = dopplerStrength;
        rtti.floatUniforms["photonSphereGlowStrength"] = photonSphereGlowStrength;
        rtti.floatUniforms["enablePhotonSphere"] = enablePhotonSphereEffective ? 1.0f : 0.0f;

#if BLACKHOLE_HAS_CUDA
        /* CUDA dispatch path: bypasses both fragment and compute GLSL paths */
        if (cudaManager.isEnabled()) {
          ZONE_SCOPED_N("Blackhole CUDA");

          /* Lazy init on first use or after resize.
           * Track pre-call state to detect the single frame where init succeeds. */
          bool const wasReady = cudaManager.isReady();
          cudaManager.ensureInit(texBlackhole, renderWidth, renderHeight);
          if (!wasReady && cudaManager.isReady()) {
            /* Register galaxy cubemap as CUDA texture object (slot 4 = BhLutGalaxy).
             * Done exactly once on the frame that init first succeeds.
             * Registration failure is non-fatal: kernels fall back to no background. */
            GLuint const galaxyTexForCuda = (galaxy != 0) ? galaxy : fallbackCubemap;
            if (galaxyTexForCuda != 0) {
              cudaManager.registerLut(4, galaxyTexForCuda,
                                      static_cast<unsigned int>(GL_TEXTURE_CUBE_MAP));
            }
          }

          if (cudaManager.isReady()) {
            BH_LaunchParams cp = {};
            cp.rs = interop.schwarzschildRadius;
            cp.spin = interop.kerrSpin;
            cp.isco = interop.iscoRadius;
            cp.step_size = interop.stepSize;
            cp.fov_scale = interop.fovScale;
            cp.max_dist = interop.depthFar;
            cp.cam_pos[0] = interop.cameraPos.x;
            cp.cam_pos[1] = interop.cameraPos.y;
            cp.cam_pos[2] = interop.cameraPos.z;
            /* glm mat3 is column-major, same layout as our flat array */
            std::memcpy(cp.cam_basis, glm::value_ptr(interop.cameraBasis), 9 * sizeof(float));
            cp.max_steps = interop.maxSteps;
            cp.width = renderWidth;
            cp.height = renderHeight;
            cp.adisk_enabled = adiskEnabledEffective ? 1 : 0;
            cp.redshift_enabled = enableRedshiftEffective ? 1 : 0;
            cp.kerr_enabled = (fabsf(interop.kerrSpin) > 1e-6f) ? 1 : 0;
            cp.use_luts = (interop.useLUTs > 0.5f) ? 1 : 0;
            cp.lut_radius_min = interop.lutRadiusMin;
            cp.lut_radius_max = interop.lutRadiusMax;
            cp.redshift_radius_min = interop.redshiftRadiusMin;
            cp.redshift_radius_max = interop.redshiftRadiusMax;
            cp.spectral_radius_min = interop.spectralRadiusMin;
            cp.spectral_radius_max = interop.spectralRadiusMax;
            cp.time_sec = interop.timeSec;
            cp.doppler_strength = dopplerStrength;
            cp.background_intensity = settings.backgroundIntensity;
            cp.background_enabled = backgroundEnabledEffective ? 1 : 0;
            // Wiregrid BL-coord overlay (task A4)
            cp.wiregrid_enabled    = wiregridEnabled ? 1 : 0;
            cp.wiregrid_show_ergo  = wiregridParams.showErgosphere ? 1.0f : 0.0f;
            cp.wiregrid_grid_scale = wiregridParams.gridScale;
            // GRMHD volume radial bounds (task C1l) + temporal blend (C1d)
            cp.grmhd_r_min  = grmhdTexture.rMin;
            cp.grmhd_r_max  = grmhdTexture.rMax;
            cp.grmhd_alpha  = grmhdFrameAlpha;
            // Volumetric RTE (D3): mirrors GLSL rteEnabled path
            cp.rte_enabled       = (interop.rteEnabled > 0.5f) ? 1 : 0;
            cp.rte_opacity_scale = interop.rteOpacityScale;
            // D4: polarized Stokes IQUV
            cp.stokes_enabled     = stokesEnabled ? 1 : 0;
            cp.stokes_b_field_angle = stokesBFieldAngle;
            cp.stokes_ne_scale    = stokesNeScale;
            // Disk brightness: matches adiskLit GLSL uniform (record mode sets 0.35)
            cp.adisk_lit = adiskLit;

            cudaManager.renderFrame(&cp);
          }
        } else
#endif
        {
          /* Original GLSL fragment/compute paths */

          GLuint fragmentTarget = 0;
          if (computeActive) {
            fragmentTarget = compareActive ? texBlackholeCompare : 0;
          } else {
            fragmentTarget = texBlackhole;
          }
          GLuint computeTarget = 0;
          if (computeActive) {
            computeTarget = texBlackhole;
          } else {
            computeTarget = compareActive ? texBlackholeCompare : 0;
          }
          if (gpuTimers.initialized && fragmentTarget != 0) {
            gpuTimers.blackholeFragment.begin();
          }
          if (fragmentTarget != 0) {
            ZONE_SCOPED_N("Blackhole Fragment");
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
            ZONE_SCOPED_N("Blackhole Compute");
            if (computeProgram == 0) {
              computeProgram = createComputeProgram(std::string("shader/geodesic_trace.comp"));
            }

            glUseProgram(computeProgram);
            applyInteropComputeUniforms(computeProgram, interop, renderWidth, renderHeight);

            // Apply Hawking radiation uniforms
            double const bhMass = static_cast<double>(blackHoleMass) * physics::M_SUN;
            applyHawkingUniforms(computeProgram, hawkingRenderer, hawkingGlowEnabled,
                                 hawkingTempScale, hawkingGlowIntensity, hawkingUseLUTs, bhMass);

            // Wiregrid BL-coord overlay (parity with fragment path)
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridEnabled"),
                        wiregridEnabled ? 1.0f : 0.0f);
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridShowErgo"),
                        wiregridParams.showErgosphere ? 1.0f : 0.0f);
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridGridScale"),
                        wiregridParams.gridScale);

            // D4: polarized Stokes IQUV (parity with fragment path)
            glUniform1f(glGetUniformLocation(computeProgram, "stokesEnabled"),
                        stokesEnabled ? 1.0f : 0.0f);
            glUniform1f(glGetUniformLocation(computeProgram, "stokesBFieldAngle"),
                        stokesBFieldAngle);
            glUniform1f(glGetUniformLocation(computeProgram, "stokesNeScale"),
                        stokesNeScale);

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
            for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
              glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
              glBindTexture(GL_TEXTURE_2D, backgroundTextures.at(static_cast<std::size_t>(i)));
              std::string const name = "backgroundLayers[" + std::to_string(i) + "]";
              glUniform1i(glGetUniformLocation(computeProgram, name.c_str()), texUnit);
              texUnit++;
            }
            glUniform1f(glGetUniformLocation(computeProgram, "backgroundEnabled"),
                        backgroundEnabledEffective ? 1.0f : 0.0f);
            glUniform1f(glGetUniformLocation(computeProgram, "bhDebugFlags"),
                        static_cast<float>(integratorDebugFlags));
            glUniform1f(glGetUniformLocation(computeProgram, "backgroundIntensity"),
                        settings.backgroundIntensity);
            for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
              std::string const name = "backgroundLayerParams[" + std::to_string(i) + "]";
              const auto &params = backgroundLayerParams.at(static_cast<std::size_t>(i));
              glUniform4f(glGetUniformLocation(computeProgram, name.c_str()), params.x, params.y,
                          params.z, params.w);
            }
            for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
              std::string const name = "backgroundLayerLodBias[" + std::to_string(i) + "]";
              float const bias =
                  std::max(backgroundLayerLodBias.at(static_cast<std::size_t>(i)), 0.0f);
              glUniform1f(glGetUniformLocation(computeProgram, name.c_str()), bias);
            }

            glBindImageTexture(0, computeTarget, 0, GL_FALSE, 0, GL_WRITE_ONLY, GL_RGBA32F);
            GLint const tileOffsetLoc = glGetUniformLocation(computeProgram, "tileOffset");
            constexpr int kGroupSize = 16;
            if (computeTiled) {
              computeTileSize = std::clamp(computeTileSize, kGroupSize, 2048);
              for (int y = 0; y < renderHeight; y += computeTileSize) {
                for (int x = 0; x < renderWidth; x += computeTileSize) {
                  int const tileWidth = std::min(computeTileSize, renderWidth - x);
                  int const tileHeight = std::min(computeTileSize, renderHeight - y);
                  if (tileOffsetLoc != -1) {
                    glUniform2i(tileOffsetLoc, x, y);
                  }
                  auto const groupsX =
                      static_cast<GLuint>((tileWidth + kGroupSize - 1) / kGroupSize);
                  auto const groupsY =
                      static_cast<GLuint>((tileHeight + kGroupSize - 1) / kGroupSize);
                  glDispatchCompute(groupsX, groupsY, 1);
                  glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);
                }
              }
            } else {
              if (tileOffsetLoc != -1) {
                glUniform2i(tileOffsetLoc, 0, 0);
              }
              auto const groupsX = static_cast<GLuint>((renderWidth + kGroupSize - 1) / kGroupSize);
              auto const groupsY =
                  static_cast<GLuint>((renderHeight + kGroupSize - 1) / kGroupSize);
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
                  sampleTextureDiff(texBlackhole, texBlackholeCompare, renderWidth,
                                    renderHeight, // NOLINT(readability-suspicious-call-argument) --
                                                  // order is correct: primary then compare
                                    compareSampleSize);
              compareFrameCounter = 0;
            }

            if (captureCompareSnapshot) {
              std::vector<float> primary;
              std::vector<float> secondary;
              if (readTextureRGBA(texBlackhole, renderWidth, renderHeight, primary) &&
                  readTextureRGBA(texBlackholeCompare, renderWidth, renderHeight, secondary)) {
                compareFullStats = computeDiffStats(primary, secondary);
                std::size_t const outlierCount =
                    countDiffOutliers(primary, secondary, compareThreshold);
                std::size_t const totalPixels = primary.size() / 4;
                std::size_t limitFromFrac = 0;
                if (compareMaxOutlierFrac > 0.0f && totalPixels > 0) {
                  limitFromFrac =
                      static_cast<std::size_t>(static_cast<double>(compareMaxOutlierFrac) *
                                               static_cast<double>(totalPixels));
                }
                std::size_t const limitFromCount =
                    static_cast<std::size_t>(std::max(compareMaxOutliers, 0));
                std::size_t const outlierLimit = std::max(limitFromCount, limitFromFrac);
                compareLastOutliers = static_cast<int>(outlierCount);
                compareLastOutlierLimit = static_cast<int>(outlierLimit);
                float const outlierFrac = totalPixels > 0 ? static_cast<float>(outlierCount) /
                                                                static_cast<float>(totalPixels)
                                                          : 0.0f;
                bool const outlierGateEnabled =
                    (compareMaxOutliers > 0) || (compareMaxOutlierFrac > 0.0f);
                compareLastExceeded = compareFullStats.valid &&
                                      compareFullStats.maxAbs > compareThreshold &&
                                      (!outlierGateEnabled || outlierCount > outlierLimit);
                if (compareLastExceeded) {
                  ++compareFailureCount;
                }

                const bool computeIsPrimary = (computeTarget == texBlackhole);
                const std::string primaryTag = computeIsPrimary ? "compute" : "fragment";
                const std::string secondaryTag = computeIsPrimary ? "fragment" : "compute";
                std::string presetLabel = "custom";
                if (compareSnapshotIndex >= 0 &&
                    std::cmp_less(compareSnapshotIndex, K_COMPARE_PRESETS.size())) {
                  presetLabel =
                      K_COMPARE_PRESETS.at(static_cast<std::size_t>(compareSnapshotIndex)).label;
                }

                if (compareWriteOutputs) {
                  writePpm(compareSnapshotPath(compareSnapshotIndex, primaryTag), primary,
                           renderWidth, renderHeight, 1.0f);
                  writePpm(compareSnapshotPath(compareSnapshotIndex, secondaryTag), secondary,
                           renderWidth, renderHeight, 1.0f);
                }
                if (compareWriteDiff) {
                  writeDiffPpm(compareSnapshotPath(compareSnapshotIndex, "diff"), primary,
                               secondary, renderWidth, renderHeight, compareDiffScale);
                }
                if (compareWriteSummary) {
                  appendCompareSummary(compareSummaryPath(), compareSnapshotIndex, primaryTag,
                                       secondaryTag, renderWidth, renderHeight, compareFullStats,
                                       compareDiffScale, compareWriteOutputs, compareWriteDiff,
                                       compareThreshold, compareLastExceeded, glfwGetTime(),
                                       kerrSpin, grbModulationEnabled, grbTimeSeconds,
                                       compareLastOutliers, compareLastOutlierLimit, outlierFrac);
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
        } /* end of GLSL fragment/compute else block */
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
        ZONE_SCOPED_N("Bloom Brightness");
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/bloom_brightness_pass.frag";
        rtti.textureUniforms["texture0"] = texBlackhole;
        rtti.targetTexture = texBrightness;
        rtti.width = renderWidth;
        rtti.height = renderHeight;
        renderToTexture(rtti);
      }

      // Post Processing panel moved to Main Settings

      {
        ZONE_SCOPED_N("Bloom Downsample");
        for (int level = 0; level < bloomIterations; level++) {
          auto const levelIndex = static_cast<std::size_t>(level);
          RenderToTextureInfo rtti;
          rtti.fragShader = "shader/bloom_downsample.frag";
          rtti.textureUniforms["texture0"] =
              level == 0 ? texBrightness : texDownsampled.at(static_cast<std::size_t>(level - 1));
          rtti.targetTexture = texDownsampled.at(levelIndex);
          int const downWidth = std::max(1, renderWidth >> (level + 1));
          int const downHeight = std::max(1, renderHeight >> (level + 1));
          rtti.width = downWidth;
          rtti.height = downHeight;
          renderToTexture(rtti);
        }
      }

      {
        ZONE_SCOPED_N("Bloom Upsample");
        for (int level = bloomIterations - 1; level >= 0; level--) {
          auto const levelIndex = static_cast<std::size_t>(level);
          RenderToTextureInfo rtti;
          rtti.fragShader = "shader/bloom_upsample.frag";
          rtti.textureUniforms["texture0"] =
              level == bloomIterations - 1 ? texDownsampled.at(levelIndex)
                                           : texUpsampled.at(static_cast<std::size_t>(level) + 1);
          rtti.textureUniforms["texture1"] =
              level == 0 ? texBrightness : texDownsampled.at(static_cast<std::size_t>(level - 1));
          rtti.targetTexture = texUpsampled.at(levelIndex);
          int const upWidth = std::max(1, renderWidth >> level);
          int const upHeight = std::max(1, renderHeight >> level);
          rtti.width = upWidth;
          rtti.height = upHeight;
          renderToTexture(rtti);
        }
      }

      {
        ZONE_SCOPED_N("Bloom Composite");
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/bloom_composite.frag";
        rtti.textureUniforms["texture0"] = texBlackhole;
        rtti.textureUniforms["texture1"] = texUpsampled.at(0);
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
        ZONE_SCOPED_N("Tonemap");
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/tonemapping.frag";
        rtti.textureUniforms["texture0"] = texBloomFinal;
        rtti.targetTexture = texTonemapped;
        rtti.width = renderWidth;
        rtti.height = renderHeight;

        if (input.isUIVisible()) {
          ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
          ImGui::Checkbox("tonemappingEnabled", &tonemappingEnabled);
          ImGui::SliderFloat("exposure", &toneExposure, 0.01f, 2.0f, "%.2f", ImGuiSliderFlags_Logarithmic);
          ImGui::SliderFloat("gamma", &gamma, 1.0f, 4.0f);
          settings.tonemappingEnabled = tonemappingEnabled;
          settings.gamma = gamma;
          ImGui::End();
        }
        rtti.floatUniforms["tonemappingEnabled"] = tonemappingEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["exposure"] = toneExposure;
        rtti.floatUniforms["gamma"] = gamma;
        rtti.floatUniforms["chromaticAberrationStrength"] = tonemapChromaticAberrationStrength;
        rtti.floatUniforms["vignetteStrength"] = tonemapVignetteStrength;
        rtti.floatUniforms["filmGrainStrength"] = tonemapFilmGrainStrength;

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
        fogStart = std::min(fogStart, fogEnd);
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
        dofFocusNear = std::min(dofFocusNear, dofFocusFar);
        ImGui::SliderFloat("DoF Max Radius", &dofMaxRadius, 0.0f, 12.0f);
        ImGui::SliderFloat("Depth Curve", &depthCurve, 0.5f, 2.0f);
        ImGui::End();
      }

      GLuint finalTexture = texTonemapped;
      if (depthEffectsEnabled) {
        ZONE_SCOPED_N("Depth Cues");
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
      ImGui::Begin("Viewport", nullptr,
                   ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse |
                       ImGuiWindowFlags_NoTitleBar);
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
        glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, finalTexture,
                               0);
        glViewport(0, 0, renderWidth, renderHeight);

        // 1. Wiregrid BL-coord overlay -- implemented in task A2 (fragment shader)

        // 2. GRMHD Slice
        if (grmhdSliceEnabled && grmhdReady) {
          ZONE_SCOPED_N("GRMHD Slice");
          grmhdSliceAxis = std::clamp(grmhdSliceAxis, 0, 2);
          grmhdSliceChannel = std::clamp(grmhdSliceChannel, 0, 3);
          grmhdSliceCoord = std::clamp(grmhdSliceCoord, 0.0f, 1.0f);
          grmhdSliceSize = std::clamp(grmhdSliceSize, 64, 1024);

          const auto channelIndex = static_cast<std::size_t>(grmhdSliceChannel);
          if (grmhdSliceAutoRange && channelIndex < grmhdTexture.minValues.size() &&
              channelIndex < grmhdTexture.maxValues.size()) {
            grmhdSliceMin = grmhdTexture.minValues.at(channelIndex);
            grmhdSliceMax = grmhdTexture.maxValues.at(channelIndex);
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
          sliceRtti.texture3DUniforms["grmhdTexture"] =
              (grmhdTimeSeriesLoaded && grmhdPboUploader.ready())
                  ? grmhdPboUploader.texture()
                  : grmhdTexture.texture;
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
          // The original code rendered the slice to a separate texture, then displayed it in ImGui
          // Image? "ImGui::Image(sliceId, ...)" in the UI panel. So we don't need to composite it
          // here.

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
          if (controlsOverlayReady) {
            controlsOverlay.render(renderWidth, renderHeight);
          }
          if (perfOverlayReady) {
            perfOverlay.render(renderWidth, renderHeight);
          }
        }

        glBindFramebuffer(GL_FRAMEBUFFER, 0);
      }

      // Draw Final Texture to Viewport
      ImGui::Image(
          reinterpret_cast<void *>(static_cast<intptr_t>(finalTexture)), viewportSize, ImVec2(0, 1),
          ImVec2(
              1,
              0)); // NOLINT(performance-no-int-to-ptr) -- ImGui API requires void* for texture IDs

      // Enable mouse/keyboard interaction when hovering the viewport
      bool const isViewportHovered = ImGui::IsItemHovered();
      InputManager::instance().setIgnoreGuiCapture(isViewportHovered);

      // Gizmo
      if (gizmoEnabled) {
        ImGuizmo::SetDrawlist();
        ImVec2 const windowPos = ImGui::GetWindowPos();
        ImGuizmo::SetRect(windowPos.x, windowPos.y, viewportSize.x, viewportSize.y);
        ImGuizmo::Manipulate(glm::value_ptr(gizmoViewMatrix), glm::value_ptr(projectionMatrix),
                             gizmoOperation, gizmoMode, glm::value_ptr(gizmoTransform));
      }

      ImGui::End();         // End Viewport
      ImGui::PopStyleVar(); // WindowPadding

      // Normal UI panels are hidden in record mode so they don't appear in the video.
      if (input.isUIVisible() && recordFramesDir.empty()) {
        renderControlsHelpPanel();
        renderControlsSettingsPanel(cameraModeIndex, orbitRadius, orbitSpeed);
        renderDisplaySettingsPanel(window, swapInterval, renderScale, windowWidth, windowHeight);
        renderBackgroundPanel(backgroundAssets, backgroundIndex,
                              settings.backgroundParallaxStrength, settings.backgroundDriftStrength,
                              backgroundLayerDepth, backgroundLayerScale, backgroundLayerIntensity,
                              backgroundLayerLodBias);
        renderWiregridPanel(wiregridEnabled, wiregridParams, wiregridColor);
        renderRmlUiPanel(rmluiEnabled);
        renderGizmoPanel(gizmoEnabled, gizmoOperation, gizmoMode, gizmoTransform);
        renderPerformancePanel(gpuTimingEnabled, gpuTimers, timingHistory, cpuFrameMs,
                               perfOverlayEnabled, perfOverlayScale, depthPrepassEnabled);
      }

      /* --export-frame: read tonemapped texture via glGetTexImage before ImGui. */
      if (!exportFramePath.empty()) {
        static int exportWarmup = 0;
        if (++exportWarmup >= 5 && texTonemapped != 0 && renderWidth > 0 && renderHeight > 0) {
          glBindTexture(GL_TEXTURE_2D, texTonemapped);
          GLint texW = 0, texH = 0;
          glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_WIDTH, &texW);
          glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_HEIGHT, &texH);
          int const w = (texW > 0) ? texW : renderWidth;
          int const h = (texH > 0) ? texH : renderHeight;
          std::vector<unsigned char> px(static_cast<size_t>(w) * static_cast<size_t>(h) * 3);
          glPixelStorei(GL_PACK_ALIGNMENT, 1);
          glGetTexImage(GL_TEXTURE_2D, 0, GL_RGB, GL_UNSIGNED_BYTE, px.data());
          glPixelStorei(GL_PACK_ALIGNMENT, 4);
          glBindTexture(GL_TEXTURE_2D, 0);
          /* glGetTexImage gives bottom-to-top; flip for PNG. */
          std::vector<unsigned char> flipped(px.size());
          for (int row = 0; row < h; ++row) {
            std::memcpy(
                flipped.data() + static_cast<size_t>(row) * static_cast<size_t>(w) * 3,
                px.data() + static_cast<size_t>(h - 1 - row) * static_cast<size_t>(w) * 3,
                static_cast<size_t>(w) * 3);
          }
          stbi_write_png(exportFramePath.c_str(), w, h, 3, flipped.data(), w * 3);
          std::printf("Exported frame: %s (%dx%d)\n", exportFramePath.c_str(), w, h);
        }
      }

      /* --record-frames: draw cinematic physics HUD via foreground draw list.
       * GetForegroundDrawList() adds to ImGui's draw list, so this must be called
       * before ImGui::Render().  The overlay is composited over the scene by the
       * ImGui backend when RenderDrawData() runs below. */
      if (!recordFramesDir.empty()) {
        ++recordWarmup;
      }
      if (!recordFramesDir.empty() && recordProfile == "cinematic" && recordWarmup >= 15) {
        renderCinematicOverlay(recordCinematic, recordCurrentKf,
                               glm::length(cameraPos),
                               recordCurRs, recordCurIsco,
                               recordFrameIndex, recordFramesTotal);
      }

      // ImGui Render
      ImGui::Render();
      ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());

      /* --record-frames: capture the tonemapped scene texture via glGetTexImage.
       * WHY: glReadPixels(0) reads the window's default framebuffer which is
       * mostly ImGui chrome (black panels).  texTonemapped holds the full
       * rendered scene at renderWidth x renderHeight, identical to the
       * --export-frame path that is known to work.  The cinematic HUD overlay
       * drawn via GetForegroundDrawList() is composited by ffmpeg drawtext later;
       * the overlay is still drawn above in the ImGui frame for live preview. */
      /* WHY: glfwSetWindowSize() is asynchronous; the resize callback fires in
       * glfwPollEvents().  Wait 15 warmup frames (~250ms) to let the window and
       * render targets settle at the requested size before starting capture.
       * If the WM caps the window smaller (e.g., in a desktop session), we accept
       * whatever size the window settled at after the warmup period. */
      if (!recordFramesDir.empty() && recordWarmup >= 15
          && texTonemapped != 0 && renderWidth > 0 && renderHeight > 0) {
        glBindTexture(GL_TEXTURE_2D, texTonemapped);
        // Query actual stored texture dimensions -- these may differ from
        // renderWidth/renderHeight if the texture was created at a different
        // resolution (e.g. before the window settled to its current size).
        // glGetTexImage writes texW*texH*channels bytes; a size mismatch would
        // corrupt the heap metadata of the next allocation.
        GLint texW = 0, texH = 0;
        glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_WIDTH, &texW);
        glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_HEIGHT, &texH);
        int const w = (texW > 0) ? texW : renderWidth;
        int const h = (texH > 0) ? texH : renderHeight;
        std::vector<unsigned char> px(static_cast<size_t>(w) * static_cast<size_t>(h) * 3);
        // GL_PACK_ALIGNMENT defaults to 4: each row is padded to a 4-byte boundary.
        // For widths like 1343, row bytes = 1343*3=4029 which rounds up to 4032,
        // overflowing our tightly-sized buffer by (4032-4029)*h = 3177 bytes and
        // corrupting the next heap chunk's malloc header (SIGABRT on free).
        // Setting alignment to 1 disables row padding for the download.
        glPixelStorei(GL_PACK_ALIGNMENT, 1);
        glGetTexImage(GL_TEXTURE_2D, 0, GL_RGB, GL_UNSIGNED_BYTE, px.data());
        glPixelStorei(GL_PACK_ALIGNMENT, 4);
        glBindTexture(GL_TEXTURE_2D, 0);
        /* glGetTexImage is bottom-to-top; flip vertically for correct PNG. */
        std::vector<unsigned char> flipped(px.size());
        for (int row = 0; row < h; ++row) {
          std::memcpy(
              flipped.data() + static_cast<size_t>(row) * static_cast<size_t>(w) * 3,
              px.data() + static_cast<size_t>(h - 1 - row) * static_cast<size_t>(w) * 3,
              static_cast<size_t>(w) * 3);
        }
        char framePath[1024];
        std::snprintf(framePath, sizeof(framePath), "%s/frame_%06d.png",
                      recordFramesDir.c_str(), recordFrameIndex);
        stbi_write_png(framePath, w, h, 3, flipped.data(), w * 3);
        if (recordFrameIndex % K_CINEMATIC_FPS == 0) {
          std::printf("Record: frame %d / %d  (t = %.1f s)  [%dx%d]\n",
                      recordFrameIndex, recordFramesTotal,
                      static_cast<double>(recordCinematic), w, h);
        }
        ++recordFrameIndex;
        recordCinematic = static_cast<float>(recordFrameIndex) / static_cast<float>(K_CINEMATIC_FPS);
      }

      // Update Platform Windows (Docking)
      if ((ImGui::GetIO().ConfigFlags & ImGuiConfigFlags_ViewportsEnable) != 0) {
        GLFWwindow *backupCurrentContext = glfwGetCurrentContext();
        ImGui::UpdatePlatformWindows();
        ImGui::RenderPlatformWindowsDefault();
        glfwMakeContextCurrent(backupCurrentContext);
      }

      if (gpuTimingLogEnabled && gpuTimers.initialized) {
        gpuTimingLogCounter++;
        if (gpuTimingLogCounter >= gpuTimingLogStride) {
          appendGpuTimingSample(gpuTimingPath(), gpuTimingLogIndex++, renderWidth, renderHeight,
                                cpuFrameMs, gpuTimers, computeActiveForLog, kerrSpin,
                                glfwGetTime());
          gpuTimingLogCounter = 0;
        }
      }

      if (gpuTimers.initialized) {
        gpuTimers.swap();
      }
      FRAME_MARK;
      glfwSwapBuffers(window);

      /* --export-frame: break after the frame was exported above. */
      if (!exportFramePath.empty()) {
        static int exportDone = 0;
        if (++exportDone >= 6) { /* 5 warmup + 1 export frame */
          break;
        }
      }

      /* --record-frames: break when all requested frames have been captured.
       * recordFrameIndex starts at recordStartFrame; terminate when we have
       * written recordFramesTotal frames (i.e. reached recordStartFrame+total). */
      if (!recordFramesDir.empty()
          && recordFrameIndex >= recordStartFrame + recordFramesTotal) {
        int const written = recordFrameIndex - recordStartFrame;
        std::printf("Record complete: %d frames written to %s\n",
                    written, recordFramesDir.c_str());
        break;
      }
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

#if BLACKHOLE_HAS_CUDA
    cudaManager.shutdown();
#endif
    cleanup(window);
    return 0;
#if BLACKHOLE_HAS_CPPTRACE
  } catch (const cpptrace::exception &err) {
    std::fprintf(stderr, "Unhandled cpptrace exception: %s\n",
                 err.what()); // NOLINT(cert-err33-c) -- diagnostic output, return unused
    err.trace().print();
    return 1;
  } catch (const std::exception &err) {
    std::fprintf(stderr, "Unhandled std::exception: %s\n",
                 err.what()); // NOLINT(cert-err33-c) -- diagnostic output, return unused
    cpptrace::generate_trace(1).print();
    return 1;
  } catch (...) {
    std::fprintf(stderr, "Unhandled non-standard exception\n"); // NOLINT(cert-err33-c) --
                                                                // diagnostic output, return unused
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
