/**
 * @file stokes_transport.glsl
 * @brief Polarized radiative transfer: Stokes I,Q,U,V transport for GLSL.
 *
 * WHY: Scalar intensity transport (rte_step.glsl) cannot model the polarization
 * that EHT directly measures.  The 2021 M87* polarized image (EHT Paper VII)
 * and Sgr A* polarization (Paper VIII, 2022) are the primary validation targets.
 * This shader module ports the CPU stokesStep() from src/physics/stokes_transport.h
 * to GLSL so the fragment and compute paths produce polarized output without a
 * separate CPU readback.
 *
 * WHAT: Four functions:
 *   stokesStep()                  -- exact formal solution for simplified K matrix
 *   synchrotronPolarizedEmission() -- (jI, jQ, jU, jV) from B-field geometry
 *   faradayRotCoeff()             -- cold-plasma rho_V [rad / (same units as ds)]
 *   stokesDisplayColor()          -- map Stokes (I,Q,U,V) to display RGB
 *
 * POLARIZED RTE (simplified K: alpha_I + rho_V only):
 *   dS/ds = J - K_simp * S
 *   K_simp: alpha_I for I and V (scalar RTE), rho_V couples Q <-> U (Faraday).
 *   This is the primary approximation for EHT frequencies (230 GHz, Theta_e >> 1)
 *   where Faraday rotation >> dichroism.
 *
 * EXACT SOLUTION FOR (Q,U):
 *   Homogeneous part:  Q_hom = E*(Q0*cos(phi) - U0*sin(phi))
 *                      U_hom = E*(Q0*sin(phi) + U0*cos(phi))
 *   Particular (emission integrals Ic, Is):
 *     D = A^2 + R^2   (A=alphaI, R=rhoV)
 *     Ic = [A*(1-E*C) + R*E*S] / D
 *     Is = [R*(1-E*C) - A*E*S] / D
 *     Q_emit = jQ*Ic - jU*Is
 *     U_emit = jQ*Is + jU*Ic
 *
 * STOKES CONVENTIONS:
 *   vec4 state: (I, Q, U, V)
 *     I >= 0 total intensity
 *     Q, U linear polarization; EVPA = 0.5*atan(U,Q) [rad]
 *     V > 0: right-circular (IAU convention)
 *   vec4 emission: (jI, jQ, jU, jV)
 *
 * References:
 *   - Hamaker & Bregman (1996), A&AS 117, 137
 *   - Shcherbakov & Huang (2011), MNRAS 410, 1052
 *   - EHT Collaboration Paper VII (2021), ApJL 910, L13
 */

#ifndef STOKES_TRANSPORT_GLSL
#define STOKES_TRANSPORT_GLSL

// ---------------------------------------------------------------------------
// stokesStep
//
// Exact analytic solution of the simplified polarized RTE over one segment.
// Simplified K: only total absorption (alphaI) and Faraday rotation (rhoV).
//
// Parameters:
//   state   -- current Stokes vector (I, Q, U, V)
//   em      -- emission vector (jI, jQ, jU, jV)
//   alphaI  -- total absorption [1/path-unit]
//   rhoV    -- Faraday rotation coefficient [rad/path-unit]
//   ds      -- segment length [same units as alphaI denominator]
//
// Returns: updated Stokes state after segment.
// ---------------------------------------------------------------------------
vec4 stokesStep(vec4 state, vec4 em, float alphaI, float rhoV, float ds) {
    if (ds <= 0.0) { return state; }

    float A   = max(alphaI, 0.0);
    float R   = rhoV;
    float L   = ds;

    float tauL = A * L;
    float E    = (tauL < 700.0) ? exp(-tauL) : 0.0;  // exp(-alpha*ds)
    float phi  = R * L;                                 // Faraday rotation angle [rad]
    float Cp   = cos(phi);
    float Sp   = sin(phi);

    // -----------------------------------------------------------------------
    // I channel: standard scalar RTE (same as rteStepVec3 in rte_step.glsl)
    // -----------------------------------------------------------------------
    float iNew;
    if (tauL < 1.0e-4) {
        iNew = state.x * (1.0 - tauL) + em.x * L;
    } else {
        iNew = state.x * E + (em.x / A) * (1.0 - E);
    }
    if (A < 1.0e-30) { iNew = state.x + em.x * L; }

    // -----------------------------------------------------------------------
    // V channel: scalar RTE (decoupled in simplified K)
    // -----------------------------------------------------------------------
    float vNew;
    if (tauL < 1.0e-4) {
        vNew = state.w * (1.0 - tauL) + em.w * L;
    } else {
        vNew = state.w * E + (em.w / A) * (1.0 - E);
    }
    if (A < 1.0e-30) { vNew = state.w + em.w * L; }

    // -----------------------------------------------------------------------
    // (Q, U) system: absorption + Faraday rotation
    // Homogeneous solution (initial state decayed and rotated):
    //   Q_hom = E * (Q0*cos(phi) - U0*sin(phi))
    //   U_hom = E * (Q0*sin(phi) + U0*cos(phi))
    // -----------------------------------------------------------------------
    float qHom = E * (state.y * Cp - state.z * Sp);
    float uHom = E * (state.y * Sp + state.z * Cp);

    float qNew, uNew;
    float D = A * A + R * R;

    if (D < 1.0e-60) {
        // Neither absorption nor rotation: pure emission
        qNew = state.y + em.y * L;
        uNew = state.z + em.z * L;
    } else if (A < 1.0e-15 * abs(R)) {
        // Rotation-dominated (A ~ 0): Ic = sin(phi)/R, Is = (1-cos(phi))/R
        float ic  =  Sp / R;
        float is_ = (1.0 - Cp) / R;
        qNew = qHom + em.y * ic  - em.z * is_;
        uNew = uHom + em.y * is_ + em.z * ic;
    } else if (abs(R) < 1.0e-15 * A) {
        // Absorption-dominated (R ~ 0): Ic = (1-E)/A, Is = 0
        float oneME = (tauL < 1.0e-4) ? L - 0.5 * tauL * L : (1.0 - E) / A;
        qNew = qHom + em.y * oneME;
        uNew = uHom + em.z * oneME;
    } else {
        float ec  = E * Cp;
        float es  = E * Sp;
        float ic  = (A * (1.0 - ec) + R * es) / D;
        float is_ = (R * (1.0 - ec) - A * es) / D;
        qNew = qHom + em.y * ic  - em.z * is_;
        uNew = uHom + em.y * is_ + em.z * ic;
    }

    return vec4(iNew, qNew, uNew, vNew);
}

// ---------------------------------------------------------------------------
// synchrotronPolarizedEmission
//
// Compute the polarized emission vector from total emissivity jI, intrinsic
// linear polarization fraction piLin, and projected B-field EVPA chiBRad.
//
// The E-vector is perpendicular to B: chi_E = chi_B + pi/2, so:
//   jQ = -jI * piLin * cos(2*chi_B)
//   jU = -jI * piLin * sin(2*chi_B)
//   jV = 0  (thermal synchrotron has negligible circular polarization)
//
// Parameters:
//   jI      -- total intensity emissivity [same units as stokesStep emission]
//   piLin   -- intrinsic linear polarization fraction in [0,1]
//   chiBRad -- EVPA of the projected B field on the sky [rad]
//
// Returns: emission vec4 (jI, jQ, jU, jV=0)
// ---------------------------------------------------------------------------
vec4 synchrotronPolarizedEmission(float jI, float piLin, float chiBRad) {
    float cos2 = cos(2.0 * chiBRad);
    float sin2 = sin(2.0 * chiBRad);
    return vec4(jI, -jI * piLin * cos2, -jI * piLin * sin2, 0.0);
}

// ---------------------------------------------------------------------------
// faradayRotCoeff
//
// Cold-plasma Faraday rotation coefficient (Shcherbakov & Huang 2011, Eq B11):
//   rho_V = PREFAC * nE * bParallel / nu^2   [rad / (same length units as ds)]
//
// PREFAC = e^3 / (2*pi * m_e^2 * c^4) = 1.049e-8 in CGS (rad cm / G / cm^-3 / Hz^2)
//
// For dimensionless rendering units: provide nE in normalised density,
// bParallel in normalised B, and treat the prefactor as a tuneable coefficient.
//
// Parameters:
//   nE         -- electron density (normalised; multiply by prefac externally)
//   bParallel  -- B-field component along LOS (normalised)
//   prefac     -- calibration factor (set to 1.049e-8 for CGS)
//
// Returns: rho_V [rad/length-unit]
// ---------------------------------------------------------------------------
float faradayRotCoeff(float nE, float bParallel, float prefac) {
    if (nE <= 0.0 || prefac <= 0.0) { return 0.0; }
    return prefac * nE * bParallel;
}

// ---------------------------------------------------------------------------
// stokesDisplayColor
//
// Map Stokes (I, Q, U, V) to a display RGB.
//
// Encoding:
//   - Luminance: I (total intensity, same as scalar RTE output)
//   - Linear polarization fraction: P_lin = sqrt(Q^2 + U^2) / I
//   - EVPA angle: chi = 0.5 * atan(U, Q)
//   - Hue tint: rotate the intensity color by 2*chi in the RG-plane so that
//     0 deg EVPA is reddish, 90 deg is greenish (artistic, not physical)
//   - V modulates blue slightly for circular polarization indicator
//
// WHY: Stokes output needs to be visually interpretable in the framebuffer
// before a dedicated polarization-map rendering pass exists.  This tint is
// removed when the polarimetric renderer is in place.
// ---------------------------------------------------------------------------
vec3 stokesDisplayColor(vec4 stokes, vec3 baseColor) {
    float I = max(stokes.x, 0.0);
    if (I < 1.0e-10) { return baseColor * 0.0; }

    float P_lin = sqrt(stokes.y * stokes.y + stokes.z * stokes.z) / I;
    P_lin = clamp(P_lin, 0.0, 1.0);

    // EVPA: angle [rad] in (-pi/2, pi/2]
    float chi = 0.5 * atan(stokes.z, stokes.y);

    // Hue tint: modulate R and G by cos/sin of 2*chi, weighted by P_lin
    float tintR = 1.0 + P_lin * 0.4 * cos(2.0 * chi);
    float tintG = 1.0 + P_lin * 0.4 * sin(2.0 * chi);
    float tintB = 1.0 + clamp(stokes.w / I, -0.5, 0.5) * 0.2;

    vec3 color = baseColor * I / max(baseColor.x + baseColor.y + baseColor.z, 1.0e-10);
    return clamp(color * vec3(tintR, tintG, tintB), 0.0, 10.0);
}

#endif // STOKES_TRANSPORT_GLSL
