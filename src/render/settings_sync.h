#ifndef BLACKHOLE_RENDER_SETTINGS_SYNC_H
#define BLACKHOLE_RENDER_SETTINGS_SYNC_H

struct Settings;
class InputManager;

namespace blackhole {

struct RenderState;

// One-time hydration: each RenderState group copies from persisted Settings the
// first frame its *SettingsLoaded latch is clear, then latches so later user
// edits in the panels are not clobbered by the persisted values.
void loadSettingsIntoRenderState(RenderState &rs, const Settings &settings);

// Write-back: the live RenderState display/post values plus the window fullscreen
// state flow into Settings so SettingsManager::save() persists the session.
void syncRenderStateToSettings(const RenderState &rs, Settings &settings, InputManager &input);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_SETTINGS_SYNC_H
