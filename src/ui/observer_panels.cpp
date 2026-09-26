/**
 * @file observer_panels.cpp
 * @brief Observer-sky scene panels (see observer_panels.h).
 */

#include "ui/observer_panels.h"

#include <array>
#include <cfloat>
#include <cmath>
#include <cstddef>
#include <format>
#include <numbers>
#include <optional>
#include <string>
#include <vector>

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

void renderObserverPhysicsNote(const RenderState &rs) {
  const RenderState::ObserverViewGroup &view = rs.observerView;
  const blackhole::ObserverClockModel &clock = view.lastClock;
  ImGui::SetNextWindowPos(ImVec2(1380, 40), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(520, 330), ImGuiCond_FirstUseEver);
  ImGui::Begin("Observer physics note");
  if (!(clock.secondsPerM > 0.0)) {
    ImGui::TextWrapped("The observer's sky is still being traced.");
    ImGui::End();
    return;
  }
  const double dilation = 1.0 / clock.properTimeRate;
  ImGui::Text("dtau/dt = %.5g: one observer second = %.5g outside seconds (%.3g h)",
              clock.properTimeRate, dilation, dilation / 3600.0);
  ImGui::Text("At sky time scale %.1e: one wall second = %.4g observer s = %.4g outside h",
              view.skyTimeScale, view.skyTimeScale, view.skyTimeScale * dilation / 3600.0);
  if (clock.coordinatePeriodSeconds > 0.0) {
    ImGui::Text(
        "Orbital period: %.4g s outside (%.4g h, 2 pi / Omega), %.4g s on the observer's clock",
        clock.coordinatePeriodSeconds, clock.coordinatePeriodSeconds / 3600.0,
        clock.properPeriodSeconds);
    const double turnsPerWallSecond = view.skyTimeScale / clock.properPeriodSeconds;
    ImGui::Text("Star field turns %.4g times per wall second (%.4g at scale 1)", turnsPerWallSecond,
                1.0 / clock.properPeriodSeconds);
  }
  ImGui::Text("M = %.3g M_sun: GM/c^3 = %.5g s", view.massSolar, clock.secondsPerM);
  ImGui::Separator();
  ImGui::TextWrapped(
      "A tidally locked observer keeps the same face to the hole, so its local sky is fixed in "
      "its own frame: the shadow and the blueshift patch are functions of the look direction "
      "alone and never move. Only the source content scrolls -- the whole sky at infinity turns "
      "about the spin axis once per orbit, about ten times a second of the observer's own time at "
      "Miller's orbit. At sky time scale 1 each frame samples four sub-frame positions (motion "
      "blur); the default 1e-3 slows the sky a thousandfold so the star field can be followed.");
  ImGui::End();
}

namespace {

/** @brief Screen schematic: extremal shadow edge, NHEKline, and the two
 *         images, with alpha to the right and beta up (units of M). */
void drawDistantScreen(double inclination) {
  const ImVec2 size(ImGui::GetContentRegionAvail().x, 240.0F);
  const ImVec2 origin = ImGui::GetCursorScreenPos();
  ImGui::InvisibleButton("distant-screen", size);
  ImDrawList *draw = ImGui::GetWindowDrawList();
  draw->AddRectFilled(origin, ImVec2(origin.x + size.x, origin.y + size.y),
                      IM_COL32(8, 8, 14, 255));
  const float scale = size.y / 14.0F;
  const ImVec2 center(origin.x + (0.45F * size.x), origin.y + (0.5F * size.y));
  const auto toScreen = [&](double alpha, double beta) {
    return ImVec2(center.x + (static_cast<float>(alpha) * scale),
                  center.y - (static_cast<float>(beta) * scale));
  };
  const std::vector<std::array<double, 2>> edge = blackhole::extremalShadowEdge(inclination, 400);
  for (std::size_t index = 1; index < edge.size(); ++index) {
    for (const double sign : {1.0, -1.0}) {
      draw->AddLine(toScreen(edge.at(index - 1).at(0), sign * edge.at(index - 1).at(1)),
                    toScreen(edge.at(index).at(0), sign * edge.at(index).at(1)),
                    IM_COL32(150, 150, 170, 255), 1.5F);
    }
  }
  const std::optional<blackhole::NhekLine> line = blackhole::nhekLine(inclination);
  if (line) {
    draw->AddLine(toScreen(line->alpha, -line->halfLength), toScreen(line->alpha, line->halfLength),
                  IM_COL32(255, 170, 60, 255), 3.0F);
    draw->AddCircleFilled(toScreen(line->alpha, 0.0), 5.0F, IM_COL32(255, 220, 120, 255));
    draw->AddText(ImVec2(toScreen(line->alpha, 0.0).x + 8.0F, toScreen(line->alpha, 0.0).y - 7.0F),
                  IM_COL32(255, 220, 120, 255), "Miller on the NHEKline");
  }
  draw->AddCircle(toScreen(0.0, 0.0), 4.0F, IM_COL32(120, 60, 60, 255));
  draw->AddText(ImVec2(toScreen(0.0, 0.0).x - 40.0F, toScreen(0.0, 0.0).y + 14.0F),
                IM_COL32(150, 90, 90, 255), "direct image (g = dtau/dt)");
  draw->AddText(ImVec2(origin.x + 6.0F, origin.y + 4.0F), IM_COL32(200, 200, 200, 255),
                "schematic: extremal Kerr screen (GLS 2017 Eqs. A.5, A.12), M = 1");
  if (!line) {
    draw->AddText(ImVec2(origin.x + 6.0F, origin.y + size.y - 20.0F), IM_COL32(200, 120, 120, 255),
                  "no NHEKline below 47 deg inclination");
  }
}

} // namespace

void renderObserverDistantView(RenderState &rs) {
  RenderState::ObserverViewGroup &view = rs.observerView;
  ImGui::SetNextWindowPos(ImVec2(1380, 380), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(520, 660), ImGuiCond_FirstUseEver);
  ImGui::Begin("Observer from far away (schematic)");
  const auto &lut = view.renderer.lut();
  const blackhole::ObserverClockModel &clock = view.lastClock;
  if (!lut || !(clock.secondsPerM > 0.0)) {
    ImGui::TextWrapped("The observer's sky is still being traced.");
    ImGui::End();
    return;
  }
  ImGui::TextWrapped("Not traced: the geometry is extremal Kerr and the main render uses a = %.2g.",
                     static_cast<double>(rs.physicsCore.kerrSpin));
  const double inclinationMin = 5.0;
  const double inclinationMax = 90.0;
  ImGui::SliderScalar("Viewer inclination (deg)", ImGuiDataType_Double, &view.distantInclinationDeg,
                      &inclinationMin, &inclinationMax, "%.1f");
  drawDistantScreen(view.distantInclinationDeg * std::numbers::pi / 180.0);

  const blackhole::EmissionSummary &emission = view.renderer.emission();
  const double rate = clock.properTimeRate;
  ImGui::SeparatorText("Redshift of the observer's light, g_emit = (dtau/dt) / (1 - Omega lambda)");
  ImGui::Text("Direct image, lambda ~ 0: g_emit ~ dtau/dt = %.4g (1/%.0f); g^4 = %.2g", rate,
              1.0 / rate, rate * rate * rate * rate);
  ImGui::Text("NHEKline image, lambda -> 1/Omega: g_emit up to %.4g (GLS bound sqrt(3) = 1.732)",
              emission.gEmitMax);
  ImGui::Text("Emission sphere: %.1f%% escapes; %.2g%% direct (g_emit < 1e-3), %.1f%% NHEK "
              "(g_emit > 0.1)",
              100.0 * emission.escapingFraction, 100.0 * emission.directFraction,
              100.0 * emission.nhekFraction);
  if (!emission.histogram.empty()) {
    ImGui::PlotHistogram("##gEmit", emission.histogram.data(),
                         static_cast<int>(emission.histogram.size()), 0, nullptr, 0.0F, FLT_MAX,
                         ImVec2(ImGui::GetContentRegionAvail().x, 80.0F));
    ImGui::TextDisabled(
        "emission-sphere fraction per 0.1 dex of g_emit, from 1e%.0f to 1e%.0f", emission.log10Min,
        emission.log10Min + (emission.log10Step * static_cast<double>(emission.histogram.size())));
  }
  ImGui::TextWrapped(
      "The received sky's winding (about 1e2 rad of azimuth per degree of look direction) "
      "scrambles "
      "which emission direction reaches a given viewer at a given orbital phase, so the "
      "phase-resolved light curve is not computed here; the distribution above follows from the "
      "traced sky.");

  ImGui::SeparatorText("Clock seen from far away");
  ImGui::Text("Apparent tick rate (orbit average): %.4g -- one observer second per %.3g outside h",
              rate, 1.0 / rate / 3600.0);
  const double radiusMin = 2.0;
  const double radiusMax = 1.0e6;
  ImGui::SliderScalar("Viewer radius (M)", ImGuiDataType_Double, &view.distantRadius, &radiusMin,
                      &radiusMax, "%.4g", ImGuiSliderFlags_Logarithmic);
  const double delay = blackhole::signalDelaySeconds(lut->key, clock, view.distantRadius - 1.0);
  const double outside = view.properSeconds / rate;
  const double received = std::fmax(0.0, outside - delay) * rate;
  ImGui::Text("Radial light delay to r = %.4g M: %.4g s (%.3g days)", view.distantRadius, delay,
              delay / 86400.0);
  ImGui::Text("Observer clock %.6g s; latest received there: %.6g s", view.properSeconds, received);
  ImGui::End();
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
