#ifndef BLACKHOLE_RENDER_BACKGROUND_LOADER_H
#define BLACKHOLE_RENDER_BACKGROUND_LOADER_H

#include <string>

namespace blackhole {

struct RenderState;

// Resolves the persisted background id against the manifest and, when the
// selection changed, loads the base 2D texture and any skybox cubemap into the
// RenderState background group. The manifest is parsed once and cached on
// rs.background.backgroundAssets. A failed texture load leaves the prior
// binding in place.
void updateActiveBackground(RenderState &rs, const std::string &backgroundId);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_BACKGROUND_LOADER_H
