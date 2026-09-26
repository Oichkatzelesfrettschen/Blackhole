/**
 * @file input_key_edges_test.cpp
 * @brief InputManager::update reads key edges against the prior frame.
 *
 * update() computes isKeyJustPressed from keyState_ vs. prevKeyState_, so the
 * previous-state snapshot must be taken after the single-press action block
 * reads it, not before: a snapshot taken at entry makes keyState_ and
 * prevKeyState_ equal at every just-pressed check inside update, so a held
 * key never edges and every single-press action is dead. These cases run
 * GL-free (onKey does not touch the GLFWwindow pointer) and restore the
 * shared InputManager singleton's bindings and flags they change.
 */

#include <gtest/gtest.h>

#include <imgui.h>

#include "input.h"

namespace {

// Falsifier: reverting update() to copy keyState_ into prevKeyState_ before
// the single-press block makes isActionJustPressed(ToggleUI) read false on
// both calls below, so uiVisible_ never flips and this fails.
TEST(InputKeyEdges, SinglePressActionFiresOnceAcrossTwoHeldUpdates) {
  ImGuiContext *const context = ImGui::CreateContext();
  ImGui::GetIO().WantCaptureKeyboard = false;

  InputManager &input = InputManager::instance();
  const int savedBinding = input.getKeyForAction(KeyAction::ToggleUI);
  const bool savedVisible = input.isUIVisible();
  const bool savedGamepad = input.isGamepadEnabled();
  input.setGamepadEnabled(false);
  input.setIgnoreGuiCapture(false); // Exercise the default gate, not the bypass.

  constexpr int testKey = GLFW_KEY_T;
  input.setKeyForAction(KeyAction::ToggleUI, testKey);
  input.setUIVisible(false);

  input.onKey(testKey, 0, GLFW_PRESS, 0);
  input.update(1.0f / 60.0f);
  EXPECT_TRUE(input.isUIVisible()) << "held key's first update must fire the bound action once";

  input.update(1.0f / 60.0f); // Key is still held; must not fire again.
  EXPECT_TRUE(input.isUIVisible()) << "a held key must not re-fire on the next update";

  input.onKey(testKey, 0, GLFW_RELEASE, 0);
  input.update(1.0f / 60.0f);
  input.setUIVisible(savedVisible);
  input.setKeyForAction(KeyAction::ToggleUI, savedBinding);
  input.setGamepadEnabled(savedGamepad);
  ImGui::DestroyContext(context);
}

// Falsifier: letting the remapping press leave the key's previous state
// false makes the held key's GLFW_REPEAT read as a fresh press, so the action
// just bound fires immediately and this fails.
TEST(InputKeyEdges, RemappingPressDoesNotFireTheNewBinding) {
  ImGuiContext *const context = ImGui::CreateContext();
  ImGui::GetIO().WantCaptureKeyboard = false;

  InputManager &input = InputManager::instance();
  const int savedBinding = input.getKeyForAction(KeyAction::ToggleUI);
  const bool savedVisible = input.isUIVisible();
  const bool savedGamepad = input.isGamepadEnabled();
  input.setGamepadEnabled(false);
  input.setIgnoreGuiCapture(false);
  input.setUIVisible(false);

  constexpr int testKey = GLFW_KEY_Y;
  input.startKeyRemapping(KeyAction::ToggleUI);
  input.onKey(testKey, 0, GLFW_PRESS, 0);
  EXPECT_EQ(input.getKeyForAction(KeyAction::ToggleUI), testKey);
  input.onKey(testKey, 0, GLFW_REPEAT, 0);
  input.update(1.0f / 60.0f);
  EXPECT_FALSE(input.isUIVisible()) << "the remapping press must not fire the new binding";

  input.onKey(testKey, 0, GLFW_RELEASE, 0);
  input.update(1.0f / 60.0f);
  input.onKey(testKey, 0, GLFW_PRESS, 0);
  input.update(1.0f / 60.0f);
  EXPECT_TRUE(input.isUIVisible()) << "a later press fires the new binding";

  input.onKey(testKey, 0, GLFW_RELEASE, 0);
  input.update(1.0f / 60.0f);
  input.setUIVisible(savedVisible);
  input.setKeyForAction(KeyAction::ToggleUI, savedBinding);
  input.setGamepadEnabled(savedGamepad);
  ImGui::DestroyContext(context);
}

// Falsifier: removing the WantCaptureKeyboard gate on the single-press block
// (or routing it through the ignoreGuiCapture_ bypass) makes the bound
// action fire while an ImGui field owns the keyboard, and this fails.
TEST(InputKeyEdges, WantCaptureKeyboardSuppressesSinglePressAction) {
  ImGuiContext *const context = ImGui::CreateContext();
  ImGui::GetIO().WantCaptureKeyboard = true;

  InputManager &input = InputManager::instance();
  const int savedBinding = input.getKeyForAction(KeyAction::ToggleUI);
  const bool savedVisible = input.isUIVisible();
  const bool savedGamepad = input.isGamepadEnabled();
  input.setGamepadEnabled(false);
  input.setIgnoreGuiCapture(false); // Default: GUI capture is honored.

  constexpr int testKey = GLFW_KEY_T;
  input.setKeyForAction(KeyAction::ToggleUI, testKey);
  input.setUIVisible(false);

  input.onKey(testKey, 0, GLFW_PRESS, 0);
  input.update(1.0f / 60.0f);
  EXPECT_FALSE(input.isUIVisible()) << "WantCaptureKeyboard must suppress the single-press block";

  input.onKey(testKey, 0, GLFW_RELEASE, 0);
  input.update(1.0f / 60.0f);
  input.setUIVisible(savedVisible);
  input.setKeyForAction(KeyAction::ToggleUI, savedBinding);
  input.setGamepadEnabled(savedGamepad);
  ImGui::DestroyContext(context);
}

} // namespace
