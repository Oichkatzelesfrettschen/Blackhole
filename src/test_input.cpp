#include "input.h"
#include <imgui.h>
#include <cassert>
#include <cstring>

#include "input.h"
#include <imgui.h>
#include <cassert>
#include <cstring>
#include <iostream> // For potential debug output, but keep minimal

int main() {
    ImGui::CreateContext();

    auto &in = InputManager::instance();

    // Test singleton instance
    auto &in2 = InputManager::instance();
    assert(&in == &in2); // Ensure same instance

    // Test initialization (mock window, but since we can't create real GLFW, just call init with nullptr and check no crash)
    // Note: In real tests, use a test window or mock.
    in.init(nullptr);
    // After init, check default bindings
    assert(in.getKeyForAction(KeyAction::Quit) == GLFW_KEY_ESCAPE);
    assert(in.getKeyForAction(KeyAction::ToggleUI) == GLFW_KEY_H);

    // Test syncFromSettings and syncToSettings (assuming SettingsManager is testable)
    // For simplicity, assume settings are set; in real scenario, mock SettingsManager
    in.syncFromSettings();
    // Check if bindings are synced (depends on settings, but test structure)
    in.syncToSettings();
    // Verify round-trip if possible

    // Expanded key binding tests
    in.setKeyForAction(KeyAction::ZoomIn, GLFW_KEY_KP_ADD);
    assert(in.getKeyForAction(KeyAction::ZoomIn) == GLFW_KEY_KP_ADD);
    in.setKeyForAction(KeyAction::ZoomOut, GLFW_KEY_KP_SUBTRACT);
    assert(in.getKeyForAction(KeyAction::ZoomOut) == GLFW_KEY_KP_SUBTRACT);
    // Test invalid action
    in.setKeyForAction(KeyAction::COUNT, GLFW_KEY_A); // Should not crash, but check if ignored
    assert(in.getKeyForAction(KeyAction::COUNT) == GLFW_KEY_UNKNOWN);

    // Expanded action name lookup
    const char *zoomName = in.getActionName(KeyAction::ZoomIn);
    assert(zoomName && std::strcmp(zoomName, "Zoom In") == 0);
    const char *quitName = in.getActionName(KeyAction::Quit);
    assert(quitName && std::strcmp(quitName, "Quit") == 0);
    // Test all actions for completeness
    for (int i = 0; i < static_cast<int>(KeyAction::COUNT); ++i) {
        const char *name = in.getActionName(static_cast<KeyAction>(i));
        assert(name && std::strcmp(name, "Unknown") != 0); // Ensure no unknowns in valid range
    }

    // Expanded key name tests
    std::string escName = in.getKeyName(GLFW_KEY_ESCAPE);
    assert(escName == "ESC");
    std::string enterName = in.getKeyName(GLFW_KEY_ENTER);
    assert(enterName == "Enter");
    std::string spaceName = in.getKeyName(GLFW_KEY_SPACE);
    assert(spaceName == "Space");
    std::string f11Name = in.getKeyName(GLFW_KEY_F11);
    assert(f11Name == "F11");
    std::string bracketName = in.getKeyName(GLFW_KEY_LEFT_BRACKET);
    assert(bracketName == "[");
    // Test regular key
    std::string aName = in.getKeyName(GLFW_KEY_A);
    assert(aName == "a");
    // Test invalid key
    std::string invalidName = in.getKeyName(-1);
    assert(invalidName == "Unknown");

    // Expanded key press/just-pressed/just-released behavior
    const int testKey = GLFW_KEY_Z;
    // Initial state
    assert(!in.isKeyPressed(testKey));
    assert(!in.isKeyJustPressed(testKey));
    assert(!in.isKeyJustReleased(testKey));
    // Press
    in.onKey(testKey, 0, GLFW_PRESS, 0);
    assert(in.isKeyPressed(testKey));
    assert(in.isKeyJustPressed(testKey));
    assert(!in.isKeyJustReleased(testKey));
    // Update to set prev state
    in.update(0.016f);
    assert(in.isKeyPressed(testKey));
    assert(!in.isKeyJustPressed(testKey)); // No longer just pressed
    assert(!in.isKeyJustReleased(testKey));
    // Release
    in.onKey(testKey, 0, GLFW_RELEASE, 0);
    assert(!in.isKeyPressed(testKey));
    assert(!in.isKeyJustPressed(testKey));
    assert(in.isKeyJustReleased(testKey));
    // Update again
    in.update(0.016f);
    assert(!in.isKeyPressed(testKey));
    assert(!in.isKeyJustPressed(testKey));
    assert(!in.isKeyJustReleased(testKey)); // No longer just released

    // Test multiple keys simultaneously
    const int key1 = GLFW_KEY_W;
    const int key2 = GLFW_KEY_S;
    in.onKey(key1, 0, GLFW_PRESS, 0);
    in.onKey(key2, 0, GLFW_PRESS, 0);
    assert(in.isKeyPressed(key1) && in.isKeyPressed(key2));
    in.update(0.016f);
    in.onKey(key1, 0, GLFW_RELEASE, 0);
    assert(!in.isKeyPressed(key1) && in.isKeyPressed(key2));

    // Expanded mouse button tests
    const int mb = GLFW_MOUSE_BUTTON_LEFT;
    // Initial
    assert(!in.isMouseButtonPressed(mb));
    assert(!in.isMouseButtonJustPressed(mb));
    // Press
    in.onMouseButton(mb, GLFW_PRESS, 0);
    assert(in.isMouseButtonPressed(mb));
    assert(in.isMouseButtonJustPressed(mb));
    // Update
    in.update(0.016f);
    assert(in.isMouseButtonPressed(mb));
    assert(!in.isMouseButtonJustPressed(mb));
    // Release
    in.onMouseButton(mb, GLFW_RELEASE, 0);
    assert(!in.isMouseButtonPressed(mb));
    assert(!in.isMouseButtonJustPressed(mb)); // No just-released for mouse, but ensure state
    // Test multiple buttons
    const int mb2 = GLFW_MOUSE_BUTTON_RIGHT;
    in.onMouseButton(mb2, GLFW_PRESS, 0);
    assert(in.isMouseButtonPressed(mb2));
    in.update(0.016f);
    in.onMouseButton(mb2, GLFW_RELEASE, 0);
    assert(!in.isMouseButtonPressed(mb2));

    // Expanded action mapping tests
    const int actionKey = GLFW_KEY_X;
    in.setKeyForAction(KeyAction::ToggleUI, actionKey);
    // Initial
    assert(!in.isActionPressed(KeyAction::ToggleUI));
    assert(!in.isActionJustPressed(KeyAction::ToggleUI));
    // Press
    in.onKey(actionKey, 0, GLFW_PRESS, 0);
    assert(in.isActionPressed(KeyAction::ToggleUI));
    assert(in.isActionJustPressed(KeyAction::ToggleUI));
    // Update
    in.update(0.016f);
    assert(in.isActionPressed(KeyAction::ToggleUI));
    assert(!in.isActionJustPressed(KeyAction::ToggleUI));
    // Release
    in.onKey(actionKey, 0, GLFW_RELEASE, 0);
    assert(!in.isActionPressed(KeyAction::ToggleUI));
    assert(!in.isActionJustPressed(KeyAction::ToggleUI));
    // Test unbound action
    assert(!in.isActionPressed(KeyAction::COUNT));

    // Test mouse movement and delta
    in.onMouseMove(100.0, 200.0);
    in.update(0.016f); // Set prev
    in.onMouseMove(110.0, 210.0);
    in.update(0.016f);
    // Check deltas (assuming sensitivity 1.0, no inversion)
    // Note: mouseDeltaX_ and mouseDeltaY_ are private; in real tests, add getters or test indirectly via camera

    // Test scroll
    in.onScroll(0.0, 1.0);
    in.update(0.016f);
    // scrollDelta_ should be 1.0, then reset to 0

    // Test effective delta time
    in.togglePause(); // Assume paused_ starts false
    assert(in.getEffectiveDeltaTime(1.0f) == 0.0f); // Paused
    in.togglePause(); // Unpause
    assert(in.getEffectiveDeltaTime(1.0f) == 1.0f * in.timeScale_); // Assuming timeScale_ default

    // Test fullscreen toggle (mock, since no real window)
    in.toggleFullscreen();
    // Check fullscreen_ state if accessible, or just ensure no crash

    // Test hold-to-toggle (basic)
    in.holdToToggleCamera_ = true;
    in.handleHoldToToggle(KeyAction::CameraMoveForward, true, false);
    // Check holdToggleState_.forward toggled

    // Test camera update (basic, without full simulation)
    in.updateCamera(0.016f);
    // Check camera values clamped/normalized

    // Test gamepad functions (mock, assume no gamepad connected)
    assert(!in.isGamepadConnected());
    assert(in.getGamepadAxisRaw(0) == 0.0f);
    assert(in.getGamepadAxisFiltered(0) == 0.0f);
    assert(!in.isGamepadButtonJustPressed(0));

    // Test shutdown
    in.shutdown();
    assert(in.window_ == nullptr);

    ImGui::DestroyContext();
    return 0;
}