/**
 * @file observer_panels.cpp
 * @brief Observer-sky scene panels (see observer_panels.h).
 */

#include "ui/observer_panels.h"

#include <array>
#include <cmath>
#include <format>
#include <numbers>
#include <optional>
#include <string>

#include <imgui.h>

#include "physics/observer_sky_lut.h"
#include "physics/observer_sky_map.h"
#include "render/observer_sky_view.h"
#include "render/render_state.h"

namespace ui {

namespace {

using blackhole::ObserverKind;
using blackhole::RenderState;
namespace sky = physics::observer_sky;

constexpr double K_ARCSECONDS_PER_RADIAN = 180.0 * 3600.0 / std::numbers::pi;
constexpr double K_FILM_RENDER_SPIN = 0.6;

void renderObserverControls(RenderState::ObserverViewGroup &view) {
  ImGui::SeparatorText("Observer");
  const double epsilonMin = 1.0e-15;
  const double epsilonMax = 1.0;
  ImGui::SliderScalar("1 - a", ImGuiDataType_Double, &view.epsilon, &epsilonMin, &epsilonMax,
                      "%.3e", ImGuiSliderFlags_Logarithmic);
  if (ImGui::Button("Gargantua canon (1 - a = 1.33e-14, prograde ISCO)")) {
    view.epsilon = blackhole::K_GARGANTUA_SPIN_DEFICIT;
    view.atIsco = true;
    view.kind = ObserverKind::Prograde;
  }
  constexpr std::array<const char *, 4> kinds = {"Circular orbit, prograde",
                                                 "Circular orbit, retrograde", "ZAMO (hovering)",
                                                 "Static (hovering, outside ergoregion)"};
  int kindIndex = static_cast<int>(view.kind);
  if (ImGui::Combo("Observer", &kindIndex, kinds.data(), static_cast<int>(kinds.size()))) {
    view.kind = static_cast<ObserverKind>(kindIndex);
  }
  ImGui::Checkbox("At the ISCO", &view.atIsco);
  if (!view.atIsco) {
    const double xMin = 1.0e-8;
    const double xMax = 1.0e3;
    ImGui::SliderScalar("r - 1 (M)", ImGuiDataType_Double, &view.x, &xMin, &xMax, "%.6e",
                        ImGuiSliderFlags_Logarithmic);
  } else {
    ImGui::Text("r - 1 = %.6e M", view.x);
  }
  const double massMin = 1.0;
  const double massMax = 1.0e11;
  ImGui::SliderScalar("Mass (M_sun)", ImGuiDataType_Double, &view.massSolar, &massMin, &massMax,
                      "%.3e", ImGuiSliderFlags_Logarithmic);
}

void renderClockControls(RenderState::ObserverViewGroup &view) {
  ImGui::SeparatorText("Clock");
  const double scaleMin = 1.0e-6;
  const double scaleMax = 10.0;
  ImGui::SliderScalar("Sky time scale", ImGuiDataType_Double, &view.skyTimeScale, &scaleMin,
                      &scaleMax, "%.1e", ImGuiSliderFlags_Logarithmic);
  ImGui::TextDisabled("observer seconds per wall second; 1 = the observer's real time");
  if (ImGui::Button("1e-3 (default)")) {
    view.skyTimeScale = 1.0e-3;
  }
  ImGui::SameLine();
  if (ImGui::Button("1 (physical)")) {
    view.skyTimeScale = 1.0;
  }
  ImGui::SameLine();
  ImGui::Checkbox("Paused", &view.paused);
  ImGui::Checkbox("Motion blur (4 samples when the sky moves)", &view.motionBlur);
  const blackhole::ObserverClockModel &clock = view.lastClock;
  ImGui::Text("Observer clock: %.6f s", view.properSeconds);
  if (clock.secondsPerM > 0.0) {
    ImGui::Text("Outside (coordinate) time: %.4e s", view.properSeconds / clock.properTimeRate);
  }
}

void renderViewControls(RenderState::ObserverViewGroup &view) {
  ImGui::SeparatorText("View");
  ImGui::Checkbox("Steer with the orbit camera", &view.followCamera);
  ImGui::Checkbox("Center on the blueshift patch", &view.lookAtPatch);
  if (!view.followCamera && !view.lookAtPatch) {
    const double lonMin = -180.0;
    const double lonMax = 180.0;
    const double latMin = -89.0;
    const double latMax = 89.0;
    ImGui::SliderScalar("Longitude (deg)", ImGuiDataType_Double, &view.lookLongitudeDeg, &lonMin,
                        &lonMax, "%.4f");
    ImGui::SliderScalar("Latitude (deg)", ImGuiDataType_Double, &view.lookLatitudeDeg, &latMin,
                        &latMax, "%.4f");
    ImGui::TextDisabled("longitude 0 = the hole, 90 = direction of motion, 180 = straight out");
  }
  const double fovMin = 1.0e-4;
  const double fovMax = 170.0;
  ImGui::SliderScalar("Field of view (deg)", ImGuiDataType_Double, &view.fovDeg, &fovMin, &fovMax,
                      "%.5g", ImGuiSliderFlags_Logarithmic);
  ImGui::SeparatorText("Sources and exposure");
  ImGui::Checkbox("CMB (2.725 K blackbody)", &view.cmbEnabled);
  ImGui::SameLine();
  ImGui::Checkbox("Stars (cubemap)", &view.starsEnabled);
  ImGui::SliderFloat("Starfield luminance (cd/m^2)", &view.starSkyLuminance, 1.0e-6F, 1.0F, "%.1e",
                     ImGuiSliderFlags_Logarithmic);
  ImGui::DragFloatRange2("log10 luminance range", &view.logLuminanceMin, &view.logLuminanceMax,
                         0.1F, -12.0F, 20.0F, "%.1f");
  ImGui::TextDisabled("Star colors: RGB texels shifted as blackbodies (approximate).");
}

void renderStatistics(const RenderState::ObserverViewGroup &view) {
  ImGui::SeparatorText("Traced sky");
  const auto &lut = view.renderer.lut();
  if (!view.renderer.message().empty()) {
    ImGui::TextWrapped("%s", view.renderer.message().c_str());
  }
  if (!lut) {
    return;
  }
  const sky::LutStatistics &stats = lut->statistics;
  ImGui::Text("Observer v = %.9f c relative to the ZAMO", lut->key.velocity);
  ImGui::Text("Shadow: %.2f%% of the sky", 100.0 * stats.capturedFraction);
  ImGui::Text("g = nu_obs / nu_inf: %.4g .. %.4g", stats.gMin, stats.gMax);
  ImGui::Text("CMB: %.3g K .. %.3g K (energy-weighted %.3g K)", view.cmbTemperature * stats.gMin,
              view.cmbTemperature * stats.gMax, view.cmbTemperature * stats.energyWeightedG);
  ImGui::Text("99%% of the energy: %.2f x %.2f arcsec",
              stats.patch99LongitudeSpan * K_ARCSECONDS_PER_RADIAN,
              stats.patch99LatitudeSpan * K_ARCSECONDS_PER_RADIAN);
  const sky::SkyAngles peak = sky::lookAngles(lut->peak.look);
  ImGui::Text("Patch center: longitude %.6f deg, latitude %.6f deg",
              peak.longitude * 180.0 / std::numbers::pi, peak.latitude * 180.0 / std::numbers::pi);
}

} // namespace

std::string observerSpinDisclosure(const RenderState &rs) {
  const auto renderSpin = static_cast<double>(rs.physicsCore.kerrSpin);
  const bool filmSpin = std::fabs(renderSpin - K_FILM_RENDER_SPIN) < 1.0e-6;
  return std::format("physics spin 1-a = {:.3g} (this view); main render a = {:.2g} {}",
                     rs.observerView.epsilon, renderSpin,
                     filmSpin ? "(film choice)" : "(film choice: 0.6)");
}

void drawObserverDisclosure(const RenderState &rs, ImVec2 imageMin, ImVec2 imageMax) {
  const std::string text = observerSpinDisclosure(rs);
  ImDrawList *draw = ImGui::GetForegroundDrawList();
  const ImVec2 size = ImGui::CalcTextSize(text.c_str());
  const float pad = 6.0F;
  const ImVec2 origin(imageMin.x + pad, imageMax.y - size.y - (3.0F * pad));
  draw->AddRectFilled(ImVec2(origin.x - pad, origin.y - pad),
                      ImVec2(origin.x + size.x + pad, origin.y + size.y + pad),
                      IM_COL32(0, 0, 0, 170), 4.0F);
  draw->AddText(origin, IM_COL32(235, 235, 235, 255), text.c_str());
}

void renderObserverSkyPanel(RenderState &rs) {
  RenderState::ObserverViewGroup &view = rs.observerView;
  ImGui::SetNextWindowSize(ImVec2(460, 720), ImGuiCond_FirstUseEver);
  ImGui::Begin("Observer sky");
  ImGui::TextWrapped("%s", observerSpinDisclosure(rs).c_str());
  renderObserverControls(view);
  renderClockControls(view);
  renderViewControls(view);
  renderStatistics(view);
  ImGui::End();
}

} // namespace ui
