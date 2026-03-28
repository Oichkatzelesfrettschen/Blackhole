/**
 * @file cinematic.h
 * @brief Keyframe camera path and physics HUD overlay for the cinematic render mode.
 *
 * CinematicPath stores 9 control-point keyframes spanning 180 seconds (3 min at
 * 60 fps = 10 800 frames) and evaluates them at any time t via a Catmull-Rom
 * spline.  All float fields (yaw, pitch, roll, distance, fov, kerrSpin) are
 * interpolated independently; the caption is taken from the nearest P1 keyframe.
 *
 * renderCinematicOverlay() draws a full-screen ImGui foreground-list overlay:
 *   - top-left  panel: live physics values (a*, r+, r_ISCO, r_ph, z, T_H)
 *   - top-right panel: Kerr geodesic equations (E, Lz, Q, R, Theta)
 *   - right col:       time-dilation table at 7 canonical radii
 *   - bottom bar:      ticker with dist-to-horizon / redshift / dilation / progress
 */

#pragma once

#include "input.h"   // CameraState

#include <imgui.h>

#include <array>
#include <cmath>
#include <cstddef>
#include <cstdio>

// ---------------------------------------------------------------------------
// Duration constants
// ---------------------------------------------------------------------------

inline constexpr float K_CINEMATIC_DURATION_S = 180.0f;          ///< 3 minutes.
inline constexpr int   K_CINEMATIC_FPS        = 60;
inline constexpr int   K_CINEMATIC_FRAMES     =
    static_cast<int>(K_CINEMATIC_DURATION_S) * K_CINEMATIC_FPS;  ///< 10 800

// ---------------------------------------------------------------------------
// Keyframe definition
// ---------------------------------------------------------------------------

struct CamKeyframe {
    float       t_sec;    ///< Absolute time in seconds [0, 180].
    CameraState cam;      ///< {yaw, pitch, roll, distance, fov}.
    float       kerrSpin; ///< Dimensionless spin a* in [0, 1).
    const char *caption;  ///< HUD caption (not interpolated; taken from P1).
};

// ---------------------------------------------------------------------------
// 9 keyframes -- 3-minute cinematic sweep around a near-extremal Kerr BH
//
// All camera positions are in scene units where r_s = 2*M = 2.0.
// At a* = 0.998 the key BL radii are (M = 1):
//   r_+    ~ 1.063  (outer event horizon)
//   r_ph   ~ 1.070  (prograde photon sphere)
//   r_ISCO ~ 1.237  (prograde innermost stable orbit)
// Camera distances are always >= 5.2, well outside these radii.
// ---------------------------------------------------------------------------

inline constexpr std::array<CamKeyframe, 9> K_CINEMATIC_KEYFRAMES = {{

    /* t=0s -- Vast establishing shot: BH + disk as compact ring against the Milky Way.
     * Camera ABOVE the equatorial plane (pitch=+30) looking down at the disk.
     * WHY positive pitch: cameraPositionFromYawPitch(+30) places the camera at
     *   y = radius * sin(+30) > 0 -- above the disk.  Negative pitch = below disk
     *   which was causing the disk to fill the upper half of the frame (wrong). */
    {
        0.0f,
        CameraState{.yaw = 0.0f, .pitch = 30.0f, .roll = 0.0f,
                    .distance = 120.0f, .fov = 40.0f},
        0.998f,
        "Near-extremal Kerr black hole  |  a* = 0.998  |  Mass M = 1  |  r_s = 2M"
    },

    /* t=28s -- Begin approach from above; disk ring expands, Doppler asymmetry visible */
    {
        28.0f,
        CameraState{.yaw = 20.0f, .pitch = 25.0f, .roll = 0.0f,
                    .distance = 70.0f, .fov = 42.0f},
        0.998f,
        "Accretion disk  |  r_ISCO (prograde) = 1.24 M  |  T_disk ~ 10^7 K"
    },

    /* t=55s -- Mid-range from above; lensed photon ring clearly visible around shadow */
    {
        55.0f,
        CameraState{.yaw = 45.0f, .pitch = 22.0f, .roll = 0.0f,
                    .distance = 20.0f, .fov = 34.0f},
        0.998f,
        "Gravitational lensing  |  Delta-phi = 4GM/rc^2  |"
        "  Photon-capture sigma = 27 pi G^2 M^2 / c^4"
    },

    /* t=78s -- Low-angle close pass; Doppler crescent asymmetry maximised */
    {
        78.0f,
        CameraState{.yaw = 88.0f, .pitch = 16.0f, .roll = 0.0f,
                    .distance = 18.0f, .fov = 36.0f},
        0.998f,
        "Gravitational redshift  |  z = 1/sqrt(1 - r_s/r) - 1  |"
        "  Doppler beaming  kappa = (1-beta)/(1+beta)"
    },

    /* t=100s -- Very close, near equatorial; frame-dragging distorts shadow teardrop */
    {
        100.0f,
        CameraState{.yaw = 140.0f, .pitch = 18.0f, .roll = 0.0f,
                    .distance = 35.0f, .fov = 36.0f},
        0.998f,
        "Frame dragging  |  Omega_LT = a*M r / (r^4 + a^2 r^2 + 2 a^2 M r)  |"
        "  Ergosphere r_ergo = M + sqrt(M^2 - a^2 cos^2 theta)"
    },

    /* t=120s -- Just below equatorial; stacked Einstein rings at shadow edge */
    {
        120.0f,
        CameraState{.yaw = 195.0f, .pitch = 14.0f, .roll = 0.0f,
                    .distance = 32.0f, .fov = 34.0f},
        0.998f,
        "Photon sphere  |  r_ph = 1.07 M (prograde)  |"
        "  Critical impact parameter  b_crit = sqrt(27) M"
    },

    /* t=142s -- Pull up to polar view; ring seen from above in full symmetry */
    {
        142.0f,
        CameraState{.yaw = 242.0f, .pitch = 28.0f, .roll = 0.0f,
                    .distance = 40.0f, .fov = 36.0f},
        0.998f,
        "Hawking radiation  |  T_H = hbar c^3 / (8 pi G M k_B)  |"
        "  Bekenstein-Hawking  S = k_B A / (4 l_P^2)"
    },

    /* t=162s -- Long pullback; disk ring visible as thin ellipse against star field */
    {
        162.0f,
        CameraState{.yaw = 280.0f, .pitch = 22.0f, .roll = 0.0f,
                    .distance = 70.0f, .fov = 42.0f},
        0.998f,
        "Gravitational waves  |  h = 4G/c^4 * I''(t) / r  |"
        "  f_ISCO ~ c^3 / (6 sqrt(6) pi G M)"
    },

    /* t=180s -- Final vast shot: BH as jewel against the Milky Way */
    {
        180.0f,
        CameraState{.yaw = 318.0f, .pitch = 20.0f, .roll = 0.0f,
                    .distance = 140.0f, .fov = 45.0f},
        0.998f,
        "Singularity at r = 0  |  Weyl curvature psi_2 ~ M/r^3  |"
        "  Kretschner  K = 48 G^2 M^2 / (c^4 r^6)"
    },

}};

// ---------------------------------------------------------------------------
// CinematicPath: Catmull-Rom spline over K_CINEMATIC_KEYFRAMES
// ---------------------------------------------------------------------------

class CinematicPath {
public:
    /**
     * @brief Evaluate the camera path at absolute time t_sec.
     *
     * Uses a standard Catmull-Rom spline with clamp-at-endpoint boundary
     * conditions.  All CameraState floats and kerrSpin are interpolated.
     * The caption is taken from the P1 control point (not interpolated).
     *
     * @param t_sec  Time in seconds, clamped to [0, K_CINEMATIC_DURATION_S].
     * @return Interpolated CamKeyframe.
     */
    [[nodiscard]] CamKeyframe evaluate(float t_sec) const noexcept {
        static constexpr std::size_t N = K_CINEMATIC_KEYFRAMES.size();

        t_sec = std::fmaxf(0.0f, std::fminf(t_sec, K_CINEMATIC_DURATION_S));

        // Find segment index i: kf[i].t_sec <= t_sec < kf[i+1].t_sec
        std::size_t i = 0;
        for (std::size_t k = 0; k + 1 < N; ++k) {
            if (t_sec < K_CINEMATIC_KEYFRAMES[k + 1].t_sec) {
                i = k;
                break;
            }
            i = k;
        }
        if (t_sec >= K_CINEMATIC_KEYFRAMES[N - 1].t_sec) {
            return K_CINEMATIC_KEYFRAMES[N - 1];
        }

        // Clamp-at-endpoints 4-point stencil
        auto const &k0 = K_CINEMATIC_KEYFRAMES[(i > 0)       ? i - 1 : 0    ];
        auto const &k1 = K_CINEMATIC_KEYFRAMES[i                             ];
        auto const &k2 = K_CINEMATIC_KEYFRAMES[i + 1                        ];
        auto const &k3 = K_CINEMATIC_KEYFRAMES[(i + 2 < N) ? i + 2 : N - 1 ];

        float const span = k2.t_sec - k1.t_sec;
        float const u    = (span > 0.0f) ? (t_sec - k1.t_sec) / span : 0.0f;

        CamKeyframe out{};
        out.t_sec        = t_sec;
        out.cam.yaw      = cr(k0.cam.yaw,      k1.cam.yaw,      k2.cam.yaw,      k3.cam.yaw,      u);
        out.cam.pitch    = cr(k0.cam.pitch,    k1.cam.pitch,    k2.cam.pitch,    k3.cam.pitch,    u);
        out.cam.roll     = cr(k0.cam.roll,     k1.cam.roll,     k2.cam.roll,     k3.cam.roll,     u);
        out.cam.distance = cr(k0.cam.distance, k1.cam.distance, k2.cam.distance, k3.cam.distance, u);
        out.cam.fov      = cr(k0.cam.fov,      k1.cam.fov,      k2.cam.fov,      k3.cam.fov,      u);
        out.kerrSpin     = cr(k0.kerrSpin,     k1.kerrSpin,     k2.kerrSpin,     k3.kerrSpin,     u);
        out.caption      = k1.caption;  // caption is not interpolated
        return out;
    }

private:
    /** @brief Standard Catmull-Rom basis at local parameter u in [0, 1]. */
    static float cr(float p0, float p1, float p2, float p3, float u) noexcept {
        float const u2 = u * u;
        float const u3 = u2 * u;
        return 0.5f * (
              (2.0f * p1)
            + (-p0 + p2)                            * u
            + (2.0f*p0 - 5.0f*p1 + 4.0f*p2 - p3)  * u2
            + (-p0 + 3.0f*p1 - 3.0f*p2 + p3)       * u3
        );
    }
};

// ---------------------------------------------------------------------------
// renderCinematicOverlay -- full-screen ImGui foreground-list physics HUD
// ---------------------------------------------------------------------------

/**
 * @brief Draw the cinematic physics HUD on top of the rendered frame.
 *
 * Uses ImGui::GetForegroundDrawList() so it composites over the scene and all
 * normal ImGui windows.  Must be called inside an active ImGui frame (between
 * NewFrame and Render).
 *
 * @param t_sec       Current cinematic time [0, 180].
 * @param kf          Current interpolated keyframe (caption and spin).
 * @param camDist     Camera radial distance from origin in scene units.
 * @param rs          Schwarzschild radius = 2*M in scene units.
 * @param isco_r      ISCO radius in scene units.
 * @param frameIndex  Current 0-based frame index.
 * @param totalFrames Total frames to record (for progress bar).
 */
inline void renderCinematicOverlay(float t_sec, const CamKeyframe &kf,
                                   float camDist, float rs, float isco_r,
                                   int frameIndex, int totalFrames) noexcept {
    ImDrawList *dl     = ImGui::GetForegroundDrawList();
    ImVec2 const disp  = ImGui::GetIO().DisplaySize;
    float const W      = disp.x;
    float const H      = disp.y;

    // ---- Derived physics -------------------------------------------------
    float const M       = rs * 0.5f;
    float const aStar   = kf.kerrSpin;
    float const a       = aStar * M;
    // Outer horizon: r+ = M + sqrt(M^2 - a^2)
    float const rPlus   = M + std::sqrtf(std::fmaxf(0.0f, M*M - a*a));
    // Prograde photon sphere approximation (exact for Schwarzschild at a=0)
    float const cosFac  = std::cosf((2.0f / 3.0f) * std::acosf(-aStar));
    float const rPh     = M * (1.0f + cosFac) * 2.0f;  // prograde ph orbit
    (void)rPh;

    // Gravitational redshift at camera (Schwarzschild approximation)
    float const rCam    = camDist;
    float const zCam    = (rCam > rs)
                        ? (1.0f / std::sqrtf(1.0f - rs / rCam) - 1.0f)
                        : 9999.0f;
    float const dilCam  = 1.0f + zCam;

    // Hawking temperature in natural units (hbar = G = c = k_B = 1): T_H = 1/(8*pi*M)
    float const tHawking = (M > 1e-9f) ? (1.0f / (8.0f * 3.14159265f * M)) : 0.0f;

    // Frame-dragging angular velocity at r = isco_r (equatorial, BL)
    float const r3      = isco_r * isco_r * isco_r;
    float const omegaFF = (r3 + a*a*isco_r + 2.0f*a*a*M > 1e-9f)
                        ? (a / (r3 + a*a*isco_r + 2.0f*a*a*M))
                        : 0.0f;

    // ---- Layout constants ------------------------------------------------
    float const pad     = 12.0f;
    float const lineH   = 18.0f;
    float const panelW  = 315.0f;
    float const eqW     = 358.0f;

    // ---- Colors ----------------------------------------------------------
    ImU32 const colBg      = IM_COL32(  0,   0,   0, 160);
    ImU32 const colBgBar   = IM_COL32(  0,   0,   0, 200);
    ImU32 const colBorder  = IM_COL32(180, 140,  60, 220);
    ImU32 const colTitle   = IM_COL32(255, 200,  80, 255);
    ImU32 const colValue   = IM_COL32(200, 240, 200, 255);
    ImU32 const colEq      = IM_COL32(180, 210, 255, 255);
    ImU32 const colCaption = IM_COL32(255, 255, 255, 220);
    ImU32 const colProg    = IM_COL32(100, 200, 120, 220);
    ImU32 const colWarn    = IM_COL32(255, 120,  80, 255);
    ImU32 const colBarBg   = IM_COL32( 30,  30,  30, 160);

    // ---- Helpers ---------------------------------------------------------
    char buf[256];

    auto drawPanel = [&](float x, float y, float w, float h) {
        dl->AddRectFilled(ImVec2(x, y), ImVec2(x+w, y+h), colBg, 4.0f);
        dl->AddRect      (ImVec2(x, y), ImVec2(x+w, y+h), colBorder, 4.0f, 0, 1.5f);
    };
    auto text = [&](float x, float y, ImU32 col, const char *s) {
        dl->AddText(ImVec2(x, y), col, s);
    };

    // =========================================================================
    // TOP-LEFT: Live physics values
    // =========================================================================
    {
        float const px = pad;
        float const py = pad;
        float const ph = pad*2.0f + lineH * 10.0f + 4.0f;
        drawPanel(px, py, panelW, ph);

        float tx = px + pad;
        float ty = py + pad;

        text(tx, ty, colTitle, "BLACK HOLE PHYSICS");
        ty += lineH + 4.0f;

        std::snprintf(buf, sizeof(buf), "  Spin        a* = %.4f",
                      static_cast<double>(aStar));
        text(tx, ty, colValue, buf); ty += lineH;

        std::snprintf(buf, sizeof(buf), "  Mass         M = %.2f   (r_s = %.2f)",
                      static_cast<double>(M), static_cast<double>(rs));
        text(tx, ty, colValue, buf); ty += lineH;

        std::snprintf(buf, sizeof(buf), "  Horizon     r+ = %.4f M",
                      static_cast<double>(rPlus / M));
        text(tx, ty, colValue, buf); ty += lineH;

        std::snprintf(buf, sizeof(buf), "  ISCO    r_ISCO = %.4f M",
                      static_cast<double>(isco_r / M));
        text(tx, ty, colValue, buf); ty += lineH;

        std::snprintf(buf, sizeof(buf), "  Camera        r = %.3f M",
                      static_cast<double>(rCam / M));
        ImU32 const rCol = (rCam < isco_r * 1.05f) ? colWarn : colValue;
        text(tx, ty, rCol, buf); ty += lineH;

        std::snprintf(buf, sizeof(buf), "  Redshift      z = %.5f",
                      static_cast<double>(zCam));
        text(tx, ty, colValue, buf); ty += lineH;

        std::snprintf(buf, sizeof(buf), "  Time dilation   = %.5f x",
                      static_cast<double>(dilCam));
        text(tx, ty, colValue, buf); ty += lineH;

        std::snprintf(buf, sizeof(buf), "  Omega_ff        = %.5f M^-1",
                      static_cast<double>(omegaFF));
        text(tx, ty, colValue, buf); ty += lineH;

        std::snprintf(buf, sizeof(buf), "  T_Hawking       = %.3e M^-1",
                      static_cast<double>(tHawking));
        text(tx, ty, colValue, buf);
    }

    // =========================================================================
    // TOP-RIGHT: Kerr geodesic equations
    // =========================================================================
    {
        float const px = W - eqW - pad;
        float const py = pad;
        float const ph = pad*2.0f + lineH * 12.0f + 4.0f;
        drawPanel(px, py, eqW, ph);

        float tx = px + pad;
        float ty = py + pad;

        text(tx, ty, colTitle, "KERR GEODESIC EQUATIONS");
        ty += lineH + 4.0f;

        text(tx, ty, colEq, "  Sigma = r^2 + a^2 cos^2(theta)");   ty += lineH;
        text(tx, ty, colEq, "  Delta = r^2 - r_s*r + a^2");         ty += lineH;
        ty += 3.0f;
        text(tx, ty, colEq, "  E  = -(g_tt k^t + g_tphi k^phi)");   ty += lineH;
        text(tx, ty, colEq, "  Lz =   g_tphi k^t + g_pp k^phi");    ty += lineH;
        text(tx, ty, colEq, "  Q  = Sigma^2 (k^theta)^2");           ty += lineH;
        text(tx, ty, colEq, "          - a^2 cos^2 + Lz^2/sin^2");   ty += lineH;
        ty += 3.0f;
        text(tx, ty, colEq, "  R(r)  = [E(r^2+a^2) - aLz]^2");      ty += lineH;
        text(tx, ty, colEq, "            - Delta[Q + (Lz - aE)^2]"); ty += lineH;
        text(tx, ty, colEq, "  T(th) = Q + a^2 E^2 cos^2");          ty += lineH;
        text(tx, ty, colEq, "                - Lz^2 / sin^2(theta)");
    }

    // =========================================================================
    // RIGHT COLUMN: Time-dilation table at 7 canonical radii
    // =========================================================================
    {
        // Rows: label + r in units of M
        struct TDRow { const char *label; float rM; };
        static constexpr std::array<TDRow, 7> rows = {{
            {"  r = infinity", 1e8f  },
            {"  r = 100 M",    100.0f},
            {"  r =  10 M",     10.0f},
            {"  r =   6 M",      6.0f},
            {"  r =   3 M",      3.0f},
            {"  r = r_ISCO",     0.0f},   // overridden below
            {"  r = camera",     0.0f},   // overridden below
        }};

        float const tw  = 262.0f;
        float const px  = W - tw - pad;
        float const py  = pad*2.0f + lineH*12.0f + 4.0f + pad*2.0f;
        float const ph  = pad*2.0f + lineH * (static_cast<float>(rows.size()) + 2.0f);
        drawPanel(px, py, tw, ph);

        float tx = px + pad;
        float ty = py + pad;

        text(tx, ty, colTitle, "TIME DILATION  1/sqrt(1-r_s/r)");
        ty += lineH + 4.0f;

        for (std::size_t row = 0; row < rows.size(); ++row) {
            float rM = rows[row].rM;
            if (row == rows.size() - 2) { rM = isco_r / M; }  // r_ISCO
            if (row == rows.size() - 1) { rM = rCam   / M; }  // camera

            float const rGeom = rM * M;
            float td = 1.0f;
            if (rGeom > rs) {
                td = 1.0f / std::sqrtf(1.0f - rs / rGeom);
            } else {
                td = 9999.0f;
            }

            if (td > 999.0f) {
                std::snprintf(buf, sizeof(buf), " -> inside horizon");
            } else {
                std::snprintf(buf, sizeof(buf), " -> %.5f x",
                              static_cast<double>(td));
            }
            text(tx,          ty, colValue, rows[row].label);
            text(tx + 148.0f, ty, colEq,   buf);
            ty += lineH;
        }
    }

    // =========================================================================
    // BOTTOM BAR: Caption ticker + progress
    // =========================================================================
    {
        float const bh  = lineH * 3.0f + pad * 2.5f;
        float const by  = H - bh - pad;
        float const bx  = pad;
        float const bw  = W - pad * 2.0f;
        dl->AddRectFilled(ImVec2(bx, by), ImVec2(bx+bw, by+bh), colBgBar, 4.0f);
        dl->AddRect      (ImVec2(bx, by), ImVec2(bx+bw, by+bh), colBorder, 4.0f, 0, 1.5f);

        float tx = bx + pad;
        float ty = by + pad;

        // Caption from current keyframe P1
        text(tx, ty, colCaption, kf.caption);
        ty += lineH + 3.0f;

        // Live ticker
        int const tMin = static_cast<int>(t_sec) / 60;
        int const tSec = static_cast<int>(t_sec) % 60;
        std::snprintf(buf, sizeof(buf),
                      "  T %d:%02d  |  Frame %d / %d  |  "
                      "Dist-to-horizon: %.3f M  |  "
                      "Redshift z: %.4f  |  "
                      "Time dilation: %.4f x  |  "
                      "T_Hawking: %.3e M^-1",
                      tMin, tSec, frameIndex, totalFrames,
                      static_cast<double>((rCam - rPlus) / M),
                      static_cast<double>(zCam),
                      static_cast<double>(dilCam),
                      static_cast<double>(tHawking));
        text(tx, ty, colValue, buf);
        ty += lineH + 3.0f;

        // Progress bar
        float const barH  = 7.0f;
        float const barX0 = tx;
        float const barX1 = bx + bw - pad;
        float const frac  = (totalFrames > 0)
                          ? static_cast<float>(frameIndex) / static_cast<float>(totalFrames)
                          : 0.0f;
        dl->AddRectFilled(ImVec2(barX0, ty),
                          ImVec2(barX1, ty + barH), colBarBg, 2.0f);
        if (frac > 0.0f) {
            dl->AddRectFilled(ImVec2(barX0, ty),
                              ImVec2(barX0 + frac*(barX1-barX0), ty + barH),
                              colProg, 2.0f);
        }
    }
}
