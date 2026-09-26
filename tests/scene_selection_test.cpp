/**
 * @file scene_selection_test.cpp
 * @brief BLACKHOLE_SCENE parsing and the startup rejection of exports the
 *        selected scene cannot honor.
 *
 * main calls exportConflictForScene(cli, startupSceneMode()) before opening a
 * window and exits with status 2 on a conflict, so these cases pin that
 * command-line contract without a GL context.
 */

#include <cstdlib>
#include <optional>
#include <string>

#include <gtest/gtest.h>
// POSIX declares setenv and unsetenv only in <stdlib.h>.
#include <stdlib.h> // NOLINT(modernize-deprecated-headers)

#include "platform/cli_options.h"
#include "render/env_config.h"
#include "render/record_mode.h"
#include "render/render_state.h"

namespace {

using blackhole::exportConflictForScene;
using blackhole::parseSceneName;
using blackhole::startupSceneMode;
using SceneMode = blackhole::RenderState::SceneMode;

/** Sets BLACKHOLE_SCENE for one scope and restores the prior environment. */
class ScopedSceneEnv {
public:
  explicit ScopedSceneEnv(const char *value) {
    if (const char *prior = std::getenv("BLACKHOLE_SCENE")) {
      prior_ = prior;
    }
    if (value == nullptr) {
      unsetenv("BLACKHOLE_SCENE");
    } else {
      setenv("BLACKHOLE_SCENE", value, 1);
    }
  }
  ~ScopedSceneEnv() {
    if (prior_.has_value()) {
      setenv("BLACKHOLE_SCENE", prior_->c_str(), 1);
    } else {
      unsetenv("BLACKHOLE_SCENE");
    }
  }
  ScopedSceneEnv(const ScopedSceneEnv &) = delete;
  ScopedSceneEnv &operator=(const ScopedSceneEnv &) = delete;
  ScopedSceneEnv(ScopedSceneEnv &&) = delete;
  ScopedSceneEnv &operator=(ScopedSceneEnv &&) = delete;

private:
  std::optional<std::string> prior_;
};

TEST(SceneSelection, ParsesTheTwoSceneNames) {
  EXPECT_EQ(parseSceneName("blackhole"), SceneMode::Blackhole);
  EXPECT_EQ(parseSceneName("tesseract"), SceneMode::Tesseract);
  EXPECT_FALSE(parseSceneName("Tesseract").has_value());
  EXPECT_FALSE(parseSceneName("").has_value());
}

TEST(SceneSelection, StartupSceneFollowsTheEnvironment) {
  {
    const ScopedSceneEnv env(nullptr);
    EXPECT_EQ(startupSceneMode(), SceneMode::Blackhole);
  }
  {
    const ScopedSceneEnv env("tesseract");
    EXPECT_EQ(startupSceneMode(), SceneMode::Tesseract);
  }
  {
    const ScopedSceneEnv env("not-a-scene");
    EXPECT_EQ(startupSceneMode(), SceneMode::Blackhole);
  }
}

TEST(SceneSelection, TesseractSceneRejectsRawExportAtStartup) {
  platform::CliOptions cli;
  cli.exportRawFramePath = "out.pfm";
  {
    const ScopedSceneEnv env("tesseract");
    const std::optional<std::string> conflict = exportConflictForScene(cli, startupSceneMode());
    ASSERT_TRUE(conflict.has_value());
    EXPECT_NE(conflict.value_or("").find("--export-raw-frame"), std::string::npos);
  }
  EXPECT_FALSE(exportConflictForScene(cli, SceneMode::Blackhole).has_value());
  // The labeled PNG export stays available in the tesseract scene.
  platform::CliOptions pngOnly;
  pngOnly.exportFramePath = "out.png";
  EXPECT_FALSE(exportConflictForScene(pngOnly, SceneMode::Tesseract).has_value());
}

} // namespace
