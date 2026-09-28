#include <memory>

#include <gtest/gtest.h>
#include <imgui.h>
#include <imgui_internal.h>

#include "render/render_state.h"
#include "settings.h"
#include "ui/campaign_panels.h"
#include "ui/panels.h"
#include "ui/presentation_metadata.h"
#include "ui/settings_window.h"

namespace {

struct WindowRect {
  ImVec2 position;
  ImVec2 size;
  ImGuiID dockId;
};

WindowRect drawWindow(const char *name) {
  ImGui::Begin(name);
  const WindowRect rectangle{.position = ImGui::GetWindowPos(),
                             .size = ImGui::GetWindowSize(),
                             .dockId = ImGui::GetWindowDockID()};
  ImGui::End();
  return rectangle;
}

bool separated(const WindowRect &first, const WindowRect &second) {
  return first.position.x + first.size.x <= second.position.x + 1.0f ||
         second.position.x + second.size.x <= first.position.x + 1.0f ||
         first.position.y + first.size.y <= second.position.y + 1.0f ||
         second.position.y + second.size.y <= first.position.y + 1.0f;
}

void expectSame(const WindowRect &first, const WindowRect &second) {
  EXPECT_FLOAT_EQ(first.position.x, second.position.x);
  EXPECT_FLOAT_EQ(first.position.y, second.position.y);
  EXPECT_FLOAT_EQ(first.size.x, second.size.x);
  EXPECT_FLOAT_EQ(first.size.y, second.size.y);
}

struct WorkspaceRects {
  WindowRect viewport;
  WindowRect rail;
  WindowRect lower;
  WindowRect postProcessing;
  WindowRect curve;
  WindowRect intel;
  WindowRect objectives;
  WindowRect events;
  WindowRect physical;
};

WorkspaceRects drawWorkspaceWindows(ui::WorkspaceKind workspace) {
  return {.viewport = drawWindow("Viewport"),
          .rail =
              drawWindow(workspace == ui::WorkspaceKind::ProperTime ? "Operations" : "Settings"),
          .lower = drawWindow(workspace == ui::WorkspaceKind::ProperTime ? "System/Strategic Map"
                                                                         : "Controls"),
          .postProcessing = drawWindow("Post Processing"),
          .curve = drawWindow("Curve Overlay"),
          .intel = drawWindow(workspace == ui::WorkspaceKind::ProperTime ? "Intelligence"
                                                                         : "Campaign Intel"),
          .objectives = drawWindow("Objectives"),
          .events = drawWindow("Event Log"),
          .physical = drawWindow("Physical Viewport")};
}

WorkspaceRects runLayoutPass(ui::WorkspaceKind workspace) {
  WorkspaceRects rectangles{};
  for (int frame = 0; frame < 3; ++frame) {
    ImGui::NewFrame();
    const ImGuiID dockspaceId = ImGui::GetID("WorkspaceLayoutTest");
    ImGui::DockSpaceOverViewport(dockspaceId, ImGui::GetMainViewport());
    if (frame == 0) {
      ui::resetLayout(dockspaceId, workspace);
    }
    rectangles = drawWorkspaceWindows(workspace);
    ImGui::Render();
  }
  return rectangles;
}

void expectProtectedViewport(const WindowRect &viewport) {
  EXPECT_NE(viewport.dockId, 0U);
  const ImGuiDockNode *viewportNode = ImGui::DockBuilderGetNode(viewport.dockId);
  ASSERT_NE(viewportNode, nullptr);
  EXPECT_NE(viewportNode->LocalFlags & static_cast<int>(ImGuiDockNodeFlags_NoDockingOverMe), 0);
  EXPECT_NE(viewportNode->LocalFlags & static_cast<int>(ImGuiDockNodeFlags_NoDockingSplit), 0);
}

void expectProperTimePanels(const WorkspaceRects &rectangles) {
  EXPECT_NE(rectangles.objectives.dockId, 0U);
  EXPECT_NE(rectangles.events.dockId, 0U);
  EXPECT_NE(rectangles.physical.dockId, 0U);
}

void expectWorkspaceGeometry(const WorkspaceRects &rectangles, ImVec2 displaySize,
                             ui::WorkspaceKind workspace) {
  expectProtectedViewport(rectangles.viewport);
  EXPECT_NE(rectangles.rail.dockId, 0U);
  EXPECT_NE(rectangles.lower.dockId, 0U);
  EXPECT_NE(rectangles.postProcessing.dockId, 0U);
  EXPECT_NE(rectangles.curve.dockId, 0U);
  EXPECT_NE(rectangles.intel.dockId, 0U);
  if (workspace == ui::WorkspaceKind::ProperTime) {
    expectProperTimePanels(rectangles);
  }
  EXPECT_TRUE(separated(rectangles.viewport, rectangles.rail));
  EXPECT_TRUE(separated(rectangles.viewport, rectangles.lower));
  EXPECT_TRUE(separated(rectangles.rail, rectangles.lower));
  EXPECT_GE(rectangles.viewport.size.x, displaySize.x * 0.55f);
}

void expectSameWorkspace(const WorkspaceRects &first, const WorkspaceRects &second) {
  expectSame(first.viewport, second.viewport);
  expectSame(first.rail, second.rail);
  expectSame(first.lower, second.lower);
}

void checkWorkspace(const ImVec2 displaySize, const ImVec2 framebufferScale,
                    ui::WorkspaceKind workspace) {
  ImGui::CreateContext();
  ImGuiIO &io = ImGui::GetIO();
  io.IniFilename = nullptr;
  io.ConfigFlags |= ImGuiConfigFlags_DockingEnable;
  io.DisplaySize = displaySize;
  io.DisplayFramebufferScale = framebufferScale;
  io.DeltaTime = 1.0f / 60.0f;
  unsigned char *pixels = nullptr;
  int atlasWidth = 0;
  int atlasHeight = 0;
  io.Fonts->GetTexDataAsRGBA32(&pixels, &atlasWidth, &atlasHeight);
  ASSERT_NE(pixels, nullptr);
  ASSERT_GT(atlasWidth, 0);
  ASSERT_GT(atlasHeight, 0);

  const WorkspaceRects original = runLayoutPass(workspace);
  expectWorkspaceGeometry(original, displaySize, workspace);
  const WorkspaceRects repeated = runLayoutPass(workspace);
  expectWorkspaceGeometry(repeated, displaySize, workspace);
  expectSameWorkspace(original, repeated);
  ImGui::DestroyContext();
}

TEST(WorkspaceLayout, DeterministicAtCanonicalSizes) {
  for (const ImVec2 displaySize : {ImVec2(1280, 720), ImVec2(1920, 1080)}) {
    for (const ui::WorkspaceKind workspace :
         {ui::WorkspaceKind::Simulator, ui::WorkspaceKind::ProperTime,
          ui::WorkspaceKind::Diagnostics}) {
      checkWorkspace(displaySize, ImVec2(1, 1), workspace);
    }
  }
  checkWorkspace(ImVec2(1280, 720), ImVec2(2, 2), ui::WorkspaceKind::ProperTime);
}

TEST(WorkspacePresentation, BasicControlsUseStablePlayerLabels) {
  for (const ui::ControlPresentation &presentation : ui::K_DISK_PRESENTATION) {
    EXPECT_NE(presentation.key, presentation.label);
    EXPECT_EQ(presentation.key, presentation.persistenceKey);
    EXPECT_NE(presentation.label[0], '\0');
    EXPECT_NE(presentation.help[0], '\0');
    EXPECT_EQ(presentation.visibility, ui::ControlVisibility::Basic);
  }
  EXPECT_NE(ui::K_DOPPLER_PRESENTATION.key, ui::K_DOPPLER_PRESENTATION.label);
  EXPECT_TRUE(ui::K_DOPPLER_PRESENTATION.persistenceKey.empty());
}

TEST(WorkspacePresentation, FirstRunDepthProfileIsOptIn) {
  const auto state = std::make_unique<blackhole::RenderState>();
  const Settings settings;
  EXPECT_FALSE(state->depthFx.depthEffectsEnabled);
  EXPECT_FALSE(state->depthFx.fogEnabled);
  EXPECT_FALSE(state->depthFx.depthDesatEnabled);
  EXPECT_FALSE(settings.advancedControls);
  EXPECT_EQ(settings.workspaceSchemaVersion, 0);
  EXPECT_EQ(settings.workspaceKind, static_cast<int>(ui::WorkspaceKind::Simulator));
}

TEST(WorkspacePresentation, CampaignRailUsesReadableFleetCards) {
  EXPECT_FLOAT_EQ(ui::fleetTableMinimumWidth(), 1025.0f);
  EXPECT_TRUE(ui::fleetRosterUsesCards(1280.0f * 0.40f));
  EXPECT_TRUE(ui::fleetRosterUsesCards(1920.0f * 0.40f));
  EXPECT_FALSE(ui::fleetRosterUsesCards(1200.0f));
}

TEST(WorkspacePresentation, EmptyCurvePathCreatesNoWindow) {
  ImGui::CreateContext();
  ImGuiIO &io = ImGui::GetIO();
  io.IniFilename = nullptr;
  io.DisplaySize = ImVec2(1280, 720);
  io.DeltaTime = 1.0f / 60.0f;
  unsigned char *pixels = nullptr;
  int atlasWidth = 0;
  int atlasHeight = 0;
  io.Fonts->GetTexDataAsRGBA32(&pixels, &atlasWidth, &atlasHeight);
  ASSERT_NE(pixels, nullptr);
  ASSERT_GT(atlasWidth, 0);
  ASSERT_GT(atlasHeight, 0);
  auto state = std::make_unique<blackhole::RenderState>();
  ImGui::NewFrame();
  ui::renderCurveOverlayWindow(*state, "");
  EXPECT_EQ(ImGui::FindWindowByName("Curve Overlay"), nullptr);
  ImGui::Render();
  ImGui::DestroyContext();
}

} // namespace
