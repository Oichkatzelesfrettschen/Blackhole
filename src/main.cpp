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
#include <cstdio>

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

// Third-party library headers
#include "gl_loader.h"
#include <GLFW/glfw3.h>
#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtc/type_ptr.hpp>
#include <imgui.h>
#include <ImGuizmo.h>
#include <implot.h>

// Local headers
#include "GLDebugMessageCallback.h"
#include "grmhd_packed_loader.h"
#include "imgui_impl_glfw.h"
#include "imgui_impl_opengl3.h"
#include "hud_overlay.h"
#include "input.h"
#include "physics/lut.h"
#include "physics/noise.h"
#include "rmlui_overlay.h"
#include "render.h"
#include "settings.h"
#include "shader.h"
#include "shader_manager.h"
#include "texture.h"
#include "tracy_support.h"

enum class CameraMode { Input = 0, Front, Top, Orbit };

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

static void appendCompareSummary(const std::string &path, int index,
                                 const std::string &primaryTag,
                                 const std::string &secondaryTag, int width, int height,
                                 const DiffStats &stats, float diffScale, bool wroteOutputs,
                                 bool wroteDiff, float threshold, bool exceeded,
                                 double timeSec, float kerrSpin) {
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
           "write_outputs,write_diff,time_sec,kerr_spin\n";
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << primaryTag << "," << secondaryTag << "," << width << "," << height << ","
      << stats.meanAbs << "," << stats.rms << "," << stats.maxAbs << "," << diffScale << ","
      << threshold << "," << (exceeded ? 1 : 0) << "," << (wroteOutputs ? 1 : 0) << ","
      << (wroteDiff ? 1 : 0) << "," << timeSec << "," << kerrSpin << "\n";
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

  return window;
}

// Initialize ImGui context and backends
static void initializeImGui(GLFWwindow *window) {
  const char *glsl_version = "#version 460";

  IMGUI_CHECKVERSION();
  ImGui::CreateContext();
  ImPlot::CreateContext();
  ImGuiIO &io = ImGui::GetIO();
  io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard; // Enable keyboard navigation
  ImGuizmo::SetImGuiContext(ImGui::GetCurrentContext());
  ImGuizmo::SetOrthographic(false);

  ImGui::StyleColorsDark();

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

  ImGui::SetNextWindowPos(ImVec2(320, 10), ImGuiCond_FirstUseEver);
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
      auto axisBar = [&](const char *label, float value) {
        float normalized = (value + 1.0f) * 0.5f;
        ImGui::Text("%s: %.2f", label, static_cast<double>(value));
        ImGui::ProgressBar(normalized, ImVec2(0.0f, 0.0f));
      };

      axisBar("Left X", input.getGamepadAxisFiltered(GLFW_GAMEPAD_AXIS_LEFT_X));
      axisBar("Left Y", input.getGamepadAxisFiltered(GLFW_GAMEPAD_AXIS_LEFT_Y));
      axisBar("Right X", input.getGamepadAxisFiltered(GLFW_GAMEPAD_AXIS_RIGHT_X));
      axisBar("Right Y", input.getGamepadAxisFiltered(GLFW_GAMEPAD_AXIS_RIGHT_Y));
      axisBar("Left Trigger", input.getGamepadAxisRaw(GLFW_GAMEPAD_AXIS_LEFT_TRIGGER));
      axisBar("Right Trigger", input.getGamepadAxisRaw(GLFW_GAMEPAD_AXIS_RIGHT_TRIGGER));
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

  ImGui::SetNextWindowPos(ImVec2(690, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(320, 220), ImGuiCond_FirstUseEver);

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
    this->program = createShaderProgram("shader/simple.vert", fragShader);

    glUseProgram(this->program);
    glUniform1i(glGetUniformLocation(program, "texture0"), 0);
    glUseProgram(0);
  }

  void render(GLuint inputColorTexture, int width, int height, GLuint destFramebuffer = 0) {
    glBindFramebuffer(GL_FRAMEBUFFER, destFramebuffer);

    glDisable(GL_DEPTH_TEST);

    glClearColor(1.0f, 0.0f, 0.0f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT);

    glUseProgram(this->program);

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
  int index = 0;
  double lastMs = 0.0;

  void init() { glGenQueries(2, queries); }
  void shutdown() {
    glDeleteQueries(2, queries);
    queries[0] = 0;
    queries[1] = 0;
  }
  void begin() { glBeginQuery(GL_TIME_ELAPSED, queries[index]); }
  void end() { glEndQuery(GL_TIME_ELAPSED); }
  void resolve() {
    int prev = 1 - index;
    GLuint available = 0;
    glGetQueryObjectuiv(queries[prev], GL_QUERY_RESULT_AVAILABLE, &available);
    if (available != 0u) {
      GLuint64 timeNs = 0;
      glGetQueryObjectui64v(queries[prev], GL_QUERY_RESULT, &timeNs);
      lastMs = static_cast<double>(timeNs) / 1.0e6;
    }
  }
  void swap() { index = 1 - index; }
};

struct GpuTimerSet {
  bool initialized = false;
  GpuTimer blackholeFragment;
  GpuTimer blackholeCompute;
  GpuTimer bloom;
  GpuTimer tonemap;
  GpuTimer depth;

  void init() {
    blackholeFragment.init();
    blackholeCompute.init();
    bloom.init();
    tonemap.init();
    depth.init();
    initialized = true;
  }

  void shutdown() {
    blackholeFragment.shutdown();
    blackholeCompute.shutdown();
    bloom.shutdown();
    tonemap.shutdown();
    depth.shutdown();
    initialized = false;
  }

  void resolve() {
    blackholeFragment.resolve();
    blackholeCompute.resolve();
    bloom.resolve();
    tonemap.resolve();
    depth.resolve();
  }

  void swap() {
    blackholeFragment.swap();
    blackholeCompute.swap();
    bloom.swap();
    tonemap.swap();
    depth.swap();
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
    } else {
      const float nan = std::numeric_limits<float>::quiet_NaN();
      gpuFragmentMs[index] = nan;
      gpuComputeMs[index] = nan;
      gpuBloomMs[index] = nan;
      gpuTonemapMs[index] = nan;
      gpuDepthMs[index] = nan;
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
           "gpu_tonemap_ms,gpu_depth_ms,compute_active,kerr_spin\n";
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << timeSec << "," << width << "," << height << "," << cpuFrameMs << ","
      << timers.blackholeFragment.lastMs << "," << timers.blackholeCompute.lastMs << ","
      << timers.bloom.lastMs << "," << timers.tonemap.lastMs << "," << timers.depth.lastMs << ","
      << (computeActive ? 1 : 0) << "," << kerrSpin << "\n";
}

static void writeTimingHistoryCsv(const TimingHistory &history, const std::string &path) {
  std::filesystem::create_directories("logs/perf");
  std::ofstream out(path);
  if (!out) {
    return;
  }
  out << "index,cpu_ms,gpu_fragment_ms,gpu_compute_ms,gpu_bloom_ms,gpu_tonemap_ms,gpu_depth_ms\n";
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
        << history.gpuTonemapMs[idx] << "," << history.gpuDepthMs[idx] << "\n";
  }
}

static void renderPerformancePanel(bool &gpuTimingEnabled, const GpuTimerSet &timers,
                                   const TimingHistory &history, float cpuFrameMs) {
  ImGui::SetNextWindowPos(ImVec2(1020, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 200), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Performance", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("GPU Timing", &gpuTimingEnabled);
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

int main(int, char **) {
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

  // Initialize input manager and sync with settings
  InputManager::instance().init(window);
  InputManager::instance().syncFromSettings();
  if (settings.fullscreen) {
    InputManager::instance().toggleFullscreen();
  }

  // Initialize ImGui
  initializeImGui(window);

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
  static bool gravatationalLensing = true;
  static bool renderBlackHole = true;
  static bool adiskEnabled = true;
  static bool adiskParticle = true;
  static float adiskDensityV = 2.0f;
  static float adiskDensityH = 4.0f;
  static float adiskHeight = 0.55f;
  static float adiskLit = 0.25f;
  static float adiskNoiseLOD = 5.0f;
  static float adiskNoiseScale = 0.8f;
  static bool useNoiseTexture = false;
  static float noiseTextureScale = 0.25f;
  static int noiseTextureSize = 32;
  static float adiskSpeed = 0.5f;
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
  static float blackHoleMass = 1.0f;
  static float kerrSpin = 0.0f;
  static bool enablePhotonSphere = false;
  static bool enableRedshift = false;
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
  static int compareFailureCount = 0;
  static bool compareLastExceeded = false;
  static int compareSnapshotIndex = 0;
  static bool compareAutoCapture = false;
  static int compareAutoCount = static_cast<int>(kComparePresets.size());
  static int compareAutoStride = 30;
  static int compareAutoRemaining = 0;
  static int compareAutoStrideCounter = 0;
  static bool comparePresetSweep = false;
  static bool comparePresetSaved = false;
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
  static ui::RmlUiOverlay rmluiOverlay;
  static bool rmluiEnabled = false;
  static bool rmluiReady = false;
  static int rmluiWidth = 0;
  static int rmluiHeight = 0;
  static int computeMaxSteps = 300;
  static float computeStepSize = 0.1f;
  static bool computeTiled = false;
  static int computeTileSize = 256;
  static bool lutAssetsTried = false;
  static bool lutAssetsLoaded = false;
  static bool lutFromAssets = false;
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
  static std::vector<float> spectralLutValues;
  static bool lutInitialized = false;
  static float lutSpin = 0.0f;
  static float lutRadiusMin = 0.0f;
  static float lutRadiusMax = 0.0f;
  static float redshiftRadiusMin = 0.0f;
  static float redshiftRadiusMax = 0.0f;
  static GLuint texEmissivityLUT = 0;
  static GLuint texRedshiftLUT = 0;
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
    }
    compareAutoInit = true;
  }

  if (!gpuTimingLogInit) {
    const char *logEnv = std::getenv("BLACKHOLE_GPU_TIMING_LOG");
    if (logEnv != nullptr && std::string(logEnv) == "1") {
      gpuTimingLogEnabled = true;
      const char *strideEnv = std::getenv("BLACKHOLE_GPU_TIMING_LOG_STRIDE");
      if (strideEnv != nullptr) {
        int stride = std::atoi(strideEnv);
        gpuTimingLogStride = std::max(1, stride);
      }
    }
    gpuTimingLogInit = true;
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

  auto updateLuts = [&](float spin) {
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
        if (texEmissivityLUT != 0) {
          glDeleteTextures(1, &texEmissivityLUT);
          texEmissivityLUT = 0;
        }
        if (texRedshiftLUT != 0) {
          glDeleteTextures(1, &texRedshiftLUT);
          texRedshiftLUT = 0;
        }

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

    if (!lutInitialized || std::abs(spin - lutSpin) > 1e-3f || lutFromAssets) {
      if (texEmissivityLUT != 0) {
        glDeleteTextures(1, &texEmissivityLUT);
        texEmissivityLUT = 0;
      }
      if (texRedshiftLUT != 0) {
        glDeleteTextures(1, &texRedshiftLUT);
        texRedshiftLUT = 0;
      }

      constexpr int kLutSize = 256;
      constexpr double kMassSolar = 4.0e6;
      constexpr double kMdotEdd = 0.1;

      auto emissivityLut =
          physics::generate_emissivity_lut(kLutSize, kMassSolar, spin, kMdotEdd, true);
      auto redshiftLut = physics::generate_redshift_lut(kLutSize, kMassSolar, spin);

      texEmissivityLUT = createFloatTexture2D(kLutSize, 1, emissivityLut.values);
      texRedshiftLUT = createFloatTexture2D(kLutSize, 1, redshiftLut.values);

      lutRadiusMin = emissivityLut.r_min;
      lutRadiusMax = emissivityLut.r_max;
      redshiftRadiusMin = redshiftLut.r_min;
      redshiftRadiusMax = redshiftLut.r_max;
      lutSpin = spin;
      lutFromAssets = false;
      lutInitialized = true;
    }
  };

  auto loadGrmhdPacked = [&](const std::string &path) {
    std::string error;
    if (!loadGrmhdPackedTexture(path, grmhdTexture, error)) {
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

  while (!glfwWindowShouldClose(window)) {
    ZoneScopedN("Frame");
    // Calculate delta time
    double currentTime = glfwGetTime();
    float deltaTime = static_cast<float>(currentTime - lastTime);
    lastTime = currentTime;
    const float cpuFrameMs = deltaTime * 1000.0f;

    glfwPollEvents();

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

    static GLuint galaxy = loadCubemap("assets/skybox_nebula_dark");
    static GLuint colorMap = loadTexture2D("assets/color_map.png");
    if (!noiseTextureReady) {
      auto volume = physics::generate_noise_volume(noiseTextureSize, 1337u);
      texNoiseVolume = createFloatTexture3D(volume.size, volume.size, volume.size, volume.values);
      noiseTextureReady = true;
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
    int targetWidth =
        std::max(1, static_cast<int>(static_cast<float>(windowWidth) * renderScale));
    int targetHeight =
        std::max(1, static_cast<int>(static_cast<float>(windowHeight) * renderScale));
    if (targetWidth != renderWidth || targetHeight != renderHeight) {
      recreateRenderTargets(targetWidth, targetHeight);
    }
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
          }
        }
      }
    }
    if (!comparePresetSweep && comparePresetSaved) {
      CameraState &camMutable = input.camera();
      camMutable = comparePresetSavedCamera;
      cameraModeIndex = comparePresetSavedMode;
      orbitRadius = comparePresetSavedOrbitRadius;
      orbitSpeed = comparePresetSavedOrbitSpeed;
      orbitTime = comparePresetSavedOrbitTime;
      kerrSpin = comparePresetSavedKerrSpin;
      comparePresetSaved = false;
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
    glm::mat4 viewRotation(1.0f);
    viewRotation[0] = glm::vec4(cameraBasis[0], 0.0f);
    viewRotation[1] = glm::vec4(cameraBasis[1], 0.0f);
    viewRotation[2] = glm::vec4(cameraBasis[2], 0.0f);

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

    if (gpuTimers.initialized) {
      gpuTimers.tonemap.begin();
    }
    {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/blackhole_main.frag";
      rtti.cubemapUniforms["galaxy"] = galaxy;
      rtti.textureUniforms["colorMap"] = colorMap;
      bool lutReady = texEmissivityLUT != 0 && texRedshiftLUT != 0;
      if (lutReady) {
        rtti.textureUniforms["emissivityLUT"] = texEmissivityLUT;
        rtti.textureUniforms["redshiftLUT"] = texRedshiftLUT;
      }
      if (spectralEnabled) {
        rtti.textureUniforms["spectralLUT"] = texSpectralLUT;
      }
      noiseTextureScale = std::max(noiseTextureScale, 0.01f);
      bool noiseReady = useNoiseTexture && texNoiseVolume != 0;
      if (noiseReady) {
        rtti.texture3DUniforms["noiseTexture"] = texNoiseVolume;
      }
      if (grmhdEnabled) {
        rtti.texture3DUniforms["grmhdTexture"] = grmhdTexture.texture;
      }

      // Pass camera state to shader
      rtti.vec3Uniforms["cameraPos"] = cameraPos;
      rtti.mat3Uniforms["cameraBasis"] = cameraBasis;
      rtti.floatUniforms["depthFar"] = depthFar;
      rtti.floatUniforms["useLUTs"] = lutReady ? 1.0f : 0.0f;
      rtti.floatUniforms["useNoiseTexture"] = noiseReady ? 1.0f : 0.0f;
      rtti.floatUniforms["useGrmhd"] = grmhdEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["useSpectralLUT"] = spectralEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["noiseTextureScale"] = noiseTextureScale;
      rtti.floatUniforms["lutRadiusMin"] = lutRadiusMin;
      rtti.floatUniforms["lutRadiusMax"] = lutRadiusMax;
      rtti.floatUniforms["redshiftRadiusMin"] = redshiftRadiusMin;
      rtti.floatUniforms["redshiftRadiusMax"] = redshiftRadiusMax;
      rtti.floatUniforms["spectralRadiusMin"] = spectralRadiusMin;
      rtti.floatUniforms["spectralRadiusMax"] = spectralRadiusMax;
      rtti.vec3Uniforms["grmhdBoundsMin"] = grmhdBoundsMin;
      rtti.vec3Uniforms["grmhdBoundsMax"] = grmhdBoundsMax;

      rtti.targetTexture = texBlackhole;
      rtti.width = renderWidth;
      rtti.height = renderHeight;

      // Render UI controls only if visible
      if (input.isUIVisible()) {
        ImGui::Begin("Black Hole Parameters", nullptr, ImGuiWindowFlags_NoCollapse);
        ImGui::Checkbox("gravatationalLensing", &gravatationalLensing);
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

        ImGui::Separator();
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

        ImGui::Separator();
        ImGui::Text("Physics Parameters");

        // Black hole mass in solar masses (scaled for visualization)
        ImGui::SliderFloat("blackHoleMass", &blackHoleMass, 0.1f, 10.0f);
        // Kerr spin parameter a (|a|<M)
        ImGui::SliderFloat("kerrSpin(a/M)", &kerrSpin, -0.99f, 0.99f);

        // Physics visualization toggles
        ImGui::Checkbox("enablePhotonSphere", &enablePhotonSphere);
        ImGui::Checkbox("enableRedshift", &enableRedshift);

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

        ImGui::Separator();
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
          ImGui::Text("Threshold failures: %d", compareFailureCount);
          if (compareFullStats.valid) {
            ImGui::Text("Last capture: %s", compareLastExceeded ? "FAIL" : "PASS");
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

        ImGui::End();
      }

      updateLuts(kerrSpin);
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
      rtti.floatUniforms["gravatationalLensing"] = gravatationalLensing ? 1.0f : 0.0f;
      rtti.floatUniforms["renderBlackHole"] = renderBlackHole ? 1.0f : 0.0f;
      rtti.floatUniforms["adiskEnabled"] = adiskEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["adiskParticle"] = adiskParticle ? 1.0f : 0.0f;
      rtti.floatUniforms["adiskDensityV"] = adiskDensityV;
      rtti.floatUniforms["adiskDensityH"] = adiskDensityH;
      rtti.floatUniforms["adiskHeight"] = adiskHeight;
      rtti.floatUniforms["adiskLit"] = adiskLit;
      rtti.floatUniforms["adiskNoiseLOD"] = adiskNoiseLOD;
      rtti.floatUniforms["adiskNoiseScale"] = adiskNoiseScale;
      rtti.floatUniforms["adiskSpeed"] = adiskSpeed;
      rtti.floatUniforms["schwarzschildRadius"] = schwarzschildRadius;
      rtti.floatUniforms["photonSphereRadius"] = photonSphereRadius;
      rtti.floatUniforms["iscoRadius"] = iscoRadius;
      rtti.floatUniforms["enablePhotonSphere"] = enablePhotonSphere ? 1.0f : 0.0f;
      rtti.floatUniforms["enableRedshift"] = enableRedshift ? 1.0f : 0.0f;

      bool computeSupported = ShaderManager::instance().canUseComputeShaders();
      bool computeActive = useComputeRaytracer && computeSupported;
      bool compareActive = compareComputeFragment && computeSupported;
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
          computeProgram = createComputeProgram("shader/geodesic_trace.comp");
        }

        computeMaxSteps = std::clamp(computeMaxSteps, 10, 1000);
        computeStepSize = std::clamp(computeStepSize, 0.001f, 2.0f);

        glUseProgram(computeProgram);
        glUniform2f(glGetUniformLocation(computeProgram, "resolution"),
                    static_cast<float>(renderWidth), static_cast<float>(renderHeight));
        glUniformMatrix4fv(glGetUniformLocation(computeProgram, "viewMatrix"), 1, GL_FALSE,
                           glm::value_ptr(viewRotation));
        glUniformMatrix4fv(glGetUniformLocation(computeProgram, "projectionMatrix"), 1, GL_FALSE,
                           glm::value_ptr(projectionMatrix));
        glUniform3f(glGetUniformLocation(computeProgram, "cameraPosition"), cameraPos.x, cameraPos.y,
                    cameraPos.z);
        glUniform1f(glGetUniformLocation(computeProgram, "schwarzschildRadius"),
                    schwarzschildRadius);
        glUniform1f(glGetUniformLocation(computeProgram, "kerrSpin"), kerrSpin);
        glUniform1f(glGetUniformLocation(computeProgram, "iscoRadius"), iscoRadius);
        glUniform1f(glGetUniformLocation(computeProgram, "photonSphereRadius"),
                    photonSphereRadius);
        glUniform1i(glGetUniformLocation(computeProgram, "maxSteps"), computeMaxSteps);
        glUniform1f(glGetUniformLocation(computeProgram, "stepSize"), computeStepSize);
        glUniform1f(glGetUniformLocation(computeProgram, "maxDistance"), depthFar);
        glUniform1i(glGetUniformLocation(computeProgram, "enableDisk"),
                    adiskEnabled ? 1 : 0);
        glUniform1i(glGetUniformLocation(computeProgram, "enableRedshift"),
                    enableRedshift ? 1 : 0);

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
            compareLastExceeded =
                compareFullStats.valid && compareFullStats.maxAbs > compareThreshold;
            if (compareLastExceeded) {
              ++compareFailureCount;
            }

            const bool computeIsPrimary = (computeTarget == texBlackhole);
            const std::string primaryTag = computeIsPrimary ? "compute" : "fragment";
            const std::string secondaryTag = computeIsPrimary ? "fragment" : "compute";

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
                                   compareThreshold, compareLastExceeded, glfwGetTime(), kerrSpin);
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
      }
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
    if (gpuTimers.initialized) {
      gpuTimers.tonemap.end();
    }

    if (input.isUIVisible()) {
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

    static bool depthEffectsEnabled = false;
    static bool fogEnabled = true;
  static float fogDensity = 0.12f;
  static float fogStart = 0.5f;
  static float fogEnd = 0.95f;
  static float fogColor[3] = {0.05f, 0.05f, 0.08f};
    static bool edgeOutlinesEnabled = false;
    static float edgeThreshold = 0.5f;
    static float edgeWidth = 1.0f;
    static float edgeColor[3] = {1.0f, 1.0f, 1.0f};
    static bool depthDesatEnabled = true;
  static float desatStrength = 0.15f;
    static bool chromaDepthEnabled = false;
    static bool motionParallaxHint = false;
    static bool dofEnabled = false;
    static float dofFocusNear = 0.3f;
    static float dofFocusFar = 0.9f;
  static float dofMaxRadius = 2.5f;
  static float depthCurve = 1.1f;

    if (input.isUIVisible()) {
      ImGui::Begin("Depth Effects", nullptr, ImGuiWindowFlags_NoCollapse);
      ImGui::Checkbox("Enable Depth Effects", &depthEffectsEnabled);
      ImGui::SliderFloat("Depth Far", &depthFar, 10.0f, 200.0f);
      if (ImGui::Button("Preset: Subtle")) {
        depthEffectsEnabled = true;
        fogEnabled = true;
        fogDensity = 0.12f;
        fogStart = 0.5f;
        fogEnd = 0.95f;
        fogColor[0] = 0.05f;
        fogColor[1] = 0.05f;
        fogColor[2] = 0.08f;
        edgeOutlinesEnabled = false;
        edgeThreshold = 0.5f;
        edgeWidth = 1.0f;
        depthDesatEnabled = true;
        desatStrength = 0.15f;
        chromaDepthEnabled = false;
        motionParallaxHint = false;
        dofEnabled = false;
        dofFocusNear = 0.3f;
        dofFocusFar = 0.9f;
        dofMaxRadius = 2.5f;
        depthCurve = 1.1f;
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

    // Final passthrough to screen
    passthrough.render(finalTexture, windowWidth, windowHeight);

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
      renderToTexture(sliceRtti);
    }

    if (rmluiReady) {
      rmluiOverlay.render();
    }

    if (controlsOverlayEnabled && !input.isUIVisible()) {
      if (!controlsOverlayReady) {
        controlsOverlay.init();
        controlsOverlayReady = true;
      }
      auto keyName = [&](KeyAction action) {
        return input.getKeyName(input.getKeyForAction(action));
      };
      const glm::vec4 headerColor(0.9f, 0.85f, 0.2f, 1.0f);
      const glm::vec4 textColor(0.9f, 0.9f, 0.9f, 1.0f);
      std::vector<HudOverlayLine> lines;
      lines.push_back({"OpenGL Controls", headerColor});
      lines.push_back({"Move: " + keyName(KeyAction::CameraMoveForward) + " " +
                           keyName(KeyAction::CameraMoveLeft) + " " +
                           keyName(KeyAction::CameraMoveBackward) + " " +
                           keyName(KeyAction::CameraMoveRight),
                       textColor});
      lines.push_back({"Elevate: " + keyName(KeyAction::CameraMoveUp) + " / " +
                           keyName(KeyAction::CameraMoveDown),
                       textColor});
      lines.push_back({"Roll: " + keyName(KeyAction::CameraRollLeft) + " / " +
                           keyName(KeyAction::CameraRollRight),
                       textColor});
      lines.push_back({"Zoom: Scroll / " + keyName(KeyAction::ZoomIn) + " / " +
                           keyName(KeyAction::ZoomOut),
                       textColor});
      lines.push_back({"Look: Mouse drag", textColor});
      lines.push_back({"UI: " + keyName(KeyAction::ToggleUI) + "  Fullscreen: " +
                           keyName(KeyAction::ToggleFullscreen),
                       textColor});
      lines.push_back({"Pause: " + keyName(KeyAction::Pause) + "  Reset: " +
                           keyName(KeyAction::ResetCamera),
                       textColor});
      lines.push_back({"Time: " + keyName(KeyAction::IncreaseTimeScale) + " / " +
                           keyName(KeyAction::DecreaseTimeScale),
                       textColor});
      controlsOverlay.render(windowWidth, windowHeight, controlsOverlayScale, 16.0f, lines);
    }

    // Render UI panels (before popup modal for proper window ordering)
    if (input.isUIVisible()) {
      renderControlsHelpPanel();
      renderControlsSettingsPanel(cameraModeIndex, orbitRadius, orbitSpeed);
      renderDisplaySettingsPanel(window, swapInterval, renderScale, windowWidth, windowHeight);
      renderRmlUiPanel(rmluiEnabled);
      renderGizmoPanel(gizmoEnabled, gizmoOperation, gizmoMode, gizmoTransform);
      renderPerformancePanel(gpuTimingEnabled, gpuTimers, timingHistory, cpuFrameMs);
    }

    if (input.isUIVisible() && gizmoEnabled) {
      ImGuizmo::SetDrawlist();
      ImGuizmo::SetRect(0.0f, 0.0f, static_cast<float>(windowWidth),
                        static_cast<float>(windowHeight));
      ImGuizmo::Manipulate(glm::value_ptr(gizmoViewMatrix), glm::value_ptr(projectionMatrix),
                           gizmoOperation, gizmoMode, glm::value_ptr(gizmoTransform));
    }

    ImGui::Render();
    ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());

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

  cleanup(window);
  return 0;
}
