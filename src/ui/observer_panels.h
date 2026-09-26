/**
 * @file observer_panels.h
 * @brief ImGui panels of the observer-sky scene: the observer and view
 *        controls with the measured sky statistics, and the spin disclosure
 *        drawn over the viewport.
 */

#ifndef BLACKHOLE_UI_OBSERVER_PANELS_H
#define BLACKHOLE_UI_OBSERVER_PANELS_H

#include <string>

#include <imgui.h>

#include "render/render_state.h"

namespace ui {

/** @brief Observer (spin deficit, radius, kind, mass), clock, view, sources,
 *         exposure, and the traced sky's statistics. */
void renderObserverSkyPanel(blackhole::RenderState &rs);

/**
 * @brief What the observer's clock means for what it sees: dtau/dt and its
 *        inverse, the outside time one wall second covers at the chosen sky
 *        time scale, the orbital period on both clocks, and how fast the star
 *        field turns while the shadow and the patch, fixed in the tidally
 *        locked observer's frame, stay put.
 */
void renderObserverPhysicsNote(const blackhole::RenderState &rs);

/**
 * @brief The observer seen from far away, as a heads-up overlay rather than a
 *        trace: the redshift g_emit = (dtau/dt) / (1 - Omega lambda) of its
 *        light over the emission sphere, the g^4 dimming, the apparent tick
 *        rate, the latest observer time a distant radius has received, and a
 *        schematic of where its images sit on an extremal hole's screen (the
 *        NHEKline of Gralla, Lupsasca & Strominger 2017).
 */
void renderObserverDistantView(blackhole::RenderState &rs);

/**
 * @brief The disclosure line drawn on the viewport image in the observer-sky
 *        scene: the view's physics spin against the black-hole scene's render
 *        spin. The film itself separated them (James et al. 2015,
 *        arXiv:1502.03808: physics a/M ~= 1, render a/M = 0.6).
 */
[[nodiscard]] std::string observerSpinDisclosure(const blackhole::RenderState &rs);
void drawObserverDisclosure(const blackhole::RenderState &rs, ImVec2 imageMin, ImVec2 imageMax);

} // namespace ui

#endif // BLACKHOLE_UI_OBSERVER_PANELS_H
