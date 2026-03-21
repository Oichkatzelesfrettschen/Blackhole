/**
 * @file rte_step.glsl
 * @brief Volumetric Radiative Transfer Equation (RTE) step helpers for GLSL.
 *
 * WHY: Implements the formal solution of the scalar RTE along a single path
 * segment for use in the Kerr geodesic tracer.  The CPU equivalent lives in
 * src/physics/rte_integrator.h (D1).  This shader version uses the same
 * analytic step formula but operates on vec3 (RGB) intensities for rendering.
 *
 * WHAT: Single-function API:
 *   rteStepVec3()  -- apply one RTE step to an RGB intensity accumulator
 *   rteComposit()  -- front-to-back compositing update (transmittance form)
 *
 * The formal RTE solution over a uniform segment of length ds:
 *   I_new = I_old * exp(-alpha * ds) + (j / alpha) * (1 - exp(-alpha * ds))
 * where S = j/alpha is the source function (emission / absorption).
 *
 * For the front-to-back compositing form used in volume rendering:
 *   accumI += transmittance * S * (1 - exp(-alpha * ds))
 *   transmittance *= exp(-alpha * ds)
 *
 * Taylor fallback for thin segments (tau = alpha * ds < 1e-5):
 *   1 - exp(-tau) ~= tau          (avoids (1-exp(-tau)) cancellation)
 *   exp(-tau)     ~= 1 - tau
 */

#ifndef RTE_STEP_GLSL
#define RTE_STEP_GLSL

// ---------------------------------------------------------------------------
// rteStepVec3
//
// Apply one RTE segment to a running accumulator using front-to-back
// compositing.  Returns the segment emission contribution; the caller is
// responsible for updating transmittance.
//
// Parameters:
//   emitColor   -- emission color (temperature-mapped RGB, pre-Doppler)
//   jEff        -- effective emission coefficient (already includes boost, g^3)
//   alphaNu     -- absorption coefficient [inverse step units]
//   stepSize    -- segment path length [same units as alphaNu denominator]
//   transmit    -- current path transmittance [0,1]; updated in place
//
// Returns: segment contribution to add to accumI (= transmit * S * (1-exp(-tau))
//          before transmit is updated).
// ---------------------------------------------------------------------------
vec3 rteStepVec3(vec3 emitColor, float jEff, float alphaNu, float stepSize,
                 inout float transmit) {
    float tau = max(alphaNu * stepSize, 0.0);

    float oneMexpTau;
    float expTau;
    if (tau < 1.0e-5) {
        // Taylor: avoid (1 - exp(-tau)) cancellation for tiny tau
        oneMexpTau = tau * (1.0 - 0.5 * tau);
        expTau     = 1.0 - tau;
    } else {
        expTau     = exp(-tau);
        oneMexpTau = 1.0 - expTau;
    }

    // Source function: S = emitColor * jEff / alphaNu
    // Segment emission: S * (1 - exp(-tau))
    vec3 segEmit;
    if (alphaNu < 1.0e-30) {
        // No absorption -- pure emission: I += j * ds
        segEmit = emitColor * jEff * stepSize;
    } else {
        float srcScale = jEff / alphaNu;
        segEmit = emitColor * (srcScale * oneMexpTau);
    }

    // Front-to-back contribution (weighted by current transmittance)
    vec3 contribution = transmit * segEmit;

    // Update transmittance
    transmit *= max(expTau, 0.0);

    return contribution;
}

#endif // RTE_STEP_GLSL
