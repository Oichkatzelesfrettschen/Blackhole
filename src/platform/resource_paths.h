/**
 * @file resource_paths.h
 * @brief Repository-root detection and asset path resolution.
 *
 * The resource root is the nearest ancestor directory (of the working
 * directory or the executable) that contains the repository landmarks
 * shader/simple.vert, assets/backgrounds/manifest.json, and
 * src/main.cpp; falls back to the working directory when no ancestor
 * qualifies. initResourceRoot() runs the detection once at startup;
 * resourcePath() then resolves repository-relative asset paths against
 * it from any call site.
 */

#ifndef BLACKHOLE_PLATFORM_RESOURCE_PATHS_H
#define BLACKHOLE_PLATFORM_RESOURCE_PATHS_H

#include <filesystem>
#include <string>
#include <string_view>

namespace platform {

void initResourceRoot(const char *argv0);
[[nodiscard]] const std::filesystem::path &resourceRoot();
[[nodiscard]] std::string resourcePath(std::string_view relativePath);

} // namespace platform

#endif // BLACKHOLE_PLATFORM_RESOURCE_PATHS_H
