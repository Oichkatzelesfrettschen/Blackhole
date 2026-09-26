#ifndef INTEROP_TRACE_GLSL
#define INTEROP_TRACE_GLSL

// Use include/ prefix for shader loader compatibility
#include "include/physics_constants.glsl"
#include "include/rte_step.glsl"
#include "include/stokes_transport.glsl"
#include "include/disk_profile.glsl"

const float BH_EPSILON = 1e-6;
const float BH_DEBUG_MAX_RADIUS_MULT = 4.0;
const int BH_DEBUG_FLAG_NAN = 1;
const int BH_DEBUG_FLAG_RANGE = 2;
// Set when the integrator returns because it exhausted its step budget rather
// than because the ray reached maxDistance. A true escape (r > maxDistance)
// leaves this clear; budget exhaustion sets it, so the two terminal states stay
// distinct instead of both reading as escaped. Classification is unconditional;
// bhShadeHit masks debugFlags by the enabled debug bits, so the flag surfaces as
// a color only when its bit is enabled and the default (mask 0) path is
// unaffected.
const int BH_DEBUG_FLAG_MAXSTEPS = 4;

uniform float bhDebugFlags = 0.0;

struct Ray {
  vec3 position;
  vec3 velocity;
  float affineParameter;
};

struct HitResult {
  // Camera position in the tracer's chart (kerrChartPosition); hit and
  // closest-approach points are in the same chart.
  vec3 origin;
  bool hitDisk;
  bool hitHorizon;
  bool escaped;
  vec3 hitPoint;
  vec3 closestApproachPoint;
  vec3 escapedDir;
  float phi;
  float redshiftFactor;
  float minRadius;
  int closestApproachUpdateCount;
  int firstClosestApproachStep;
  int lastClosestApproachStep;
  int debugFlags;
};

const int BH_BACKGROUND_LAYERS = 3;

int bhDebugMask() { return int(bhDebugFlags + 0.5); }

// Frames. The world frame is y-up: the camera orbit (camera_math.cpp), the
// sky's equirect pole (bhDirToUv), and the legacy tracer's spin axis. The
// physics frame carries the Kerr spin along +z with the disk in the xy plane,
// the Boyer-Lindquist convention of kerr.glsl. The rotation about x by -90
// degrees maps world +y to physics +z; camera rays enter the tracer through
// bhWorldToPhysics and escaped directions reach the sky through
// bhPhysicsToWorld, so a camera orbiting the world xz plane views the disk
// near edge-on instead of sitting inside the disk plane.
vec3 bhWorldToPhysics(vec3 v) { return vec3(v.x, -v.z, v.y); }
vec3 bhPhysicsToWorld(vec3 v) { return vec3(v.x, v.z, -v.y); }

bool bhIsInvalidFloat(float v) { return isnan(v) || isinf(v); }

bool bhIsInvalidVec3(vec3 v) { return any(isnan(v)) || any(isinf(v)); }

int bhDebugEvaluate(vec3 pos, vec3 vel, float maxDistance) {
  int mask = bhDebugMask();
  if (mask == 0) {
    return 0;
  }
  int flags = 0;
  if ((mask & BH_DEBUG_FLAG_NAN) != 0) {
    if (bhIsInvalidVec3(pos) || bhIsInvalidVec3(vel)) {
      flags |= BH_DEBUG_FLAG_NAN;
    }
  }
  if ((mask & BH_DEBUG_FLAG_RANGE) != 0) {
    float r = length(pos);
    if (r > maxDistance * BH_DEBUG_MAX_RADIUS_MULT) {
      flags |= BH_DEBUG_FLAG_RANGE;
    }
  }
  return flags;
}

// ---------------------------------------------------------------------------
// bhAdaptiveStep (D10: AMR geodesic refinement near critical surfaces)
//
// Returns a scaled step based on three refinement zones:
//   1. Horizon proximity: scale ~ (r - r_horizon) / r_s, min 0.1
//   2. Photon-sphere proximity: at r_ph ~ 1.5*r_s, scale is halved and
//      recovers to 1.0 at |r - r_ph| = 0.5*r_s.
//   3. Far-field overshoot prevention: in Mino time sqrt(R) ~ r^2 for large r,
//      so dr ~ r^2 * dlam per step.  At r=350, dlam=0.08 gives dr=9800,
//      skipping the BH entirely.  scale_far = min(1, 0.5/r) limits each step
//      to at most 0.5*r in radial distance.  Mirrors d_adaptive_step Zone 3
//      in src/cuda/device_physics.cuh for GLSL/CUDA parity.
//
// WHY: Fixed Mino-time steps overshoot near the horizon (missing the termination
// check) and accumulate angular error for photon-sphere-grazing orbits.
// ---------------------------------------------------------------------------
float bhAdaptiveStep(float r, float r_s, float r_horizon, float stepSize) {
  float d_horiz  = r - r_horizon;
  float scale_h  = clamp(d_horiz / max(r_s, BH_EPSILON), 0.1, 1.0);

  float r_ph     = 1.5 * r_s;
  float d_ph     = abs(r - r_ph) / max(r_s, BH_EPSILON);
  float scale_ph = min(1.0, 0.5 + d_ph);

  // Zone 3: far-field step limiting -- see d_adaptive_step in device_physics.cuh
  float scale_far = min(1.0, 0.5 / max(r, BH_EPSILON));

  return stepSize * min(scale_far, min(scale_h, scale_ph));
}

vec3 bhSchwarzschildAccel(vec3 pos, vec3 vel, float r_s) {
  float r = length(pos);
  if (r < BH_EPSILON) {
    return vec3(0.0);
  }

  vec3 h = cross(pos, vel);
  float h2 = dot(h, h);

  float r5 = r * r * r * r * r;
  return -1.5 * r_s * h2 * pos / r5;
}

void bhStepRK4(inout Ray ray, float r_s, float dt) {
  vec3 x0 = ray.position;
  vec3 v0 = ray.velocity;

  vec3 accel = bhSchwarzschildAccel(x0, v0, r_s);

  vec3 k1_x = v0;
  vec3 k1_v = accel;

  vec3 x1 = x0 + 0.5 * dt * k1_x;
  vec3 v1 = v0 + 0.5 * dt * k1_v;
  accel = bhSchwarzschildAccel(x1, v1, r_s);
  vec3 k2_x = v1;
  vec3 k2_v = accel;

  vec3 x2 = x0 + 0.5 * dt * k2_x;
  vec3 v2 = v0 + 0.5 * dt * k2_v;
  accel = bhSchwarzschildAccel(x2, v2, r_s);
  vec3 k3_x = v2;
  vec3 k3_v = accel;

  vec3 x3 = x0 + dt * k3_x;
  vec3 v3 = v0 + dt * k3_v;
  accel = bhSchwarzschildAccel(x3, v3, r_s);
  vec3 k4_x = v3;
  vec3 k4_v = accel;

  ray.position = x0 + (dt / 6.0) * (k1_x + 2.0 * k2_x + 2.0 * k3_x + k4_x);
  ray.velocity = v0 + (dt / 6.0) * (k1_v + 2.0 * k2_v + 2.0 * k3_v + k4_v);
  ray.affineParameter += dt;
}

// Crossing of the zero-thickness disk plane z = 0 by the step oldPos -> newPos
// inside the annulus [r_in, r_out]. A step that starts on the plane leaves it
// rather than crossing it: its start is the observer (a camera in the disk
// plane, where every tilted ray would otherwise hit the disk at t = 0) or the
// end of a previous step that landed on the plane and was counted there.
bool bhCheckDiskIntersection(vec3 oldPos, vec3 newPos, float r_in, float r_out,
                             out vec3 hitPoint) {
  hitPoint = oldPos;
  if (oldPos.z == 0.0 || oldPos.z * newPos.z > 0.0) {
    return false;
  }

  float t = -oldPos.z / (newPos.z - oldPos.z);
  hitPoint = mix(oldPos, newPos, t);

  float r = length(hitPoint.xy);
  return r >= r_in && r <= r_out;
}

float bhComputeRedshiftFactor(float r, float r_s) {
  if (r <= r_s) {
    return 0.0;
  }

  float factor = 1.0 - r_s / r;
  if (factor <= 0.0) {
    return 0.0;
  }
  return sqrt(factor);
}

vec3 bhPackShaperInputs(float minRadiusReached, vec3 closestApproachPos, vec3 origin, float r_s) {
  float alignedFlow = 0.5;
  float nearHoleWeight = 0.0;
  if (minRadiusReached < r_s * 5.0) {
    vec3 approachDir = normalize(origin - closestApproachPos);
    // Physics frame: the spin axis is +z (bhWorldToPhysics).
    vec3 spinAxis = vec3(0.0, 0.0, kerrSpin >= 0.0 ? 1.0 : -1.0);
    vec3 flowDir = normalize(cross(spinAxis, normalize(closestApproachPos)));
    alignedFlow = 0.5 + 0.5 * dot(flowDir, approachDir);
    nearHoleWeight =
        pow(clamp(1.0 - (minRadiusReached - r_s) / max(r_s * 3.0, BH_EPSILON), 0.0, 1.0), 1.55);
  }
  float minRadiusNorm = clamp(minRadiusReached / max(r_s * 5.0, BH_EPSILON), 0.0, 1.0);
  return vec3(minRadiusNorm, clamp(alignedFlow, 0.0, 1.0), clamp(nearHoleWeight, 0.0, 1.0));
}

vec3 bhEncodeUnitVector(vec3 v) {
  vec3 n = normalize(v);
  return 0.5 * (n + vec3(1.0));
}

void bhRecordClosestApproach(inout HitResult result, float radius, vec3 point, int step) {
  if (radius < result.minRadius) {
    result.minRadius = radius;
    result.closestApproachPoint = point;
    if (result.closestApproachUpdateCount == 0) {
      result.firstClosestApproachStep = step;
    }
    result.lastClosestApproachStep = step;
    result.closestApproachUpdateCount += 1;
  }
}

vec3 bhPackClosestApproachState(float minRadiusReached, vec3 closestApproachPos, float r_s) {
  float radiusScale = max(r_s * 5.0, BH_EPSILON);
  float minRadiusNorm = clamp(minRadiusReached / radiusScale, 0.0, 1.0);
  float closestRadius = length(closestApproachPos);
  float closestRadiusNorm = clamp(closestRadius / radiusScale, 0.0, 1.0);
  float mismatchNorm = clamp(abs(closestRadius - minRadiusReached) / radiusScale, 0.0, 1.0);
  return vec3(minRadiusNorm, closestRadiusNorm, mismatchNorm);
}

vec3 bhPackClosestApproachTimeline(int firstStep, int lastStep, int updateCount, int maxSteps) {
  float denom = max(float(maxSteps - 1), 1.0);
  float firstNorm = updateCount > 0 ? clamp(float(firstStep) / denom, 0.0, 1.0) : 0.0;
  float lastNorm = updateCount > 0 ? clamp(float(lastStep) / denom, 0.0, 1.0) : 0.0;
  float countNorm = clamp(float(updateCount) / 16.0, 0.0, 1.0);
  return vec3(firstNorm, lastNorm, countNorm);
}

// Accretion-disk inner edge at the spin-dependent ISCO. isco_radius() returns
// the innermost stable circular orbit in units of M (BPT 1972); with r_s = 2 M
// the value in the shader's r_s-scaled coordinates is 0.5 * isco_radius(a_star)
// * r_s. At a_star = 0 this is 3 r_s, so the Schwarzschild disk is unchanged;
// prograde spin (a_star > 0) draws the inner edge inward, retrograde spin pushes
// it outward. The dimensionless spin a_star is the kerrSpin uniform; r_s comes
// from the caller so the disk edge tracks the same Schwarzschild radius the
// geodesic integrates, with no hidden global dependency.
float bhDiskInnerRadius(float r_s) {
  return 0.5 * isco_radius(kerrSpin) * r_s;
}

// Escape radius for a ray starting at pos. A ray escapes only once it is
// outside both the scene radius and the camera's own radius and moving
// outward; a camera placed beyond maxDistance otherwise escapes every ray at
// step 0 and draws the unlensed sky.
float bhEscapeRadius(vec3 pos, float maxDistance) {
  return max(maxDistance, 1.01 * length(pos));
}

// Scene toggles read by the three interop traces. renderBlackHole = 0 removes
// the hole and, as in the legacy tracer, its disk: each ray reaches the sky
// along the camera direction without integration. gravitationalLensing = 0
// keeps the horizon and the disk but traces straight rays: flat space is the
// r_s = 0, a = 0 member of the Kerr family, where the Mino-time leapfrog moves
// along straight lines, so the same integrator runs with bhMetricRadius and
// bhMetricSpin in place of the hole's r_s and spin while capture, disk radii,
// and step sizing keep the physical values.
bool bhHoleRendered() { return renderBlackHole > 0.5; }

float bhMetricRadius(float r_s) { return gravitationalLensing > 0.5 ? r_s : 0.0; }

float bhMetricSpin(float aTrace) { return gravitationalLensing > 0.5 ? aTrace : 0.0; }

// Boyer-Lindquist position of a point in the tracer's chart: undoes
// kerrChartPosition by rotating through -F(|p|) with the traced metric, so
// consumers defined on Boyer-Lindquist phi (the wiregrid overlay) read the
// azimuth the photon actually has there. Chart-space shading and depth keep
// the chart position. With renderBlackHole = 0 the traces return the straight
// camera ray's end point, which was never rotated, so it passes unchanged.
vec3 bhChartToBoyerLindquist(vec3 p, float r_s) {
  if (!bhHoleRendered()) {
    return p;
  }
  float aTrace = bhMetricSpin(kerrTraceSpin(0.5 * kerrSpin * r_s));
  return kerrRotateZ(p, -kerrKsAzimuthOffset(length(p), bhMetricRadius(r_s), aTrace));
}

// Closest-approach radius reported for a ray that meets no hole; above every
// near-hole threshold (redshift, shaping) the shading helpers apply.
const float BH_NO_HOLE_RADIUS = 1.0e30;

HitResult bhTraceGeodesic(Ray ray, float r_s, float maxDistance, int maxSteps,
                          float stepSize) {
  float escapeRadius = bhEscapeRadius(ray.position, maxDistance);
  HitResult result;
  result.hitDisk = false;
  result.hitHorizon = false;
  result.escaped = false;
  result.hitPoint = vec3(0.0);
  result.origin = ray.position;
  result.closestApproachPoint = ray.position;
  result.escapedDir = normalize(ray.velocity);
  result.phi = 0.0;
  result.redshiftFactor = 1.0;
  result.minRadius = length(ray.position);
  result.closestApproachUpdateCount = 0;
  result.firstClosestApproachStep = -1;
  result.lastClosestApproachStep = -1;
  result.debugFlags = 0;

  if (!bhHoleRendered()) {
    result.escaped = true;
    result.hitPoint = ray.position + escapeRadius * result.escapedDir;
    result.minRadius = BH_NO_HOLE_RADIUS;
    return result;
  }

  // One integrator for every spin: Schwarzschild is the a = 0 member of the
  // Kerr family and kerr.glsl's Mino-time leapfrog is exact there, so the
  // image is continuous in spin by construction.
  float a = 0.5 * kerrSpin * r_s;
  float r_horizon = kerrOuterHorizon(r_s, a);
  if (r_horizon <= BH_EPSILON) {
    r_horizon = r_s;
  }

  float r_disk_in = bhDiskInnerRadius(r_s);
  float r_disk_out = 100.0 * r_s;

  float rsMetric = bhMetricRadius(r_s);
  float aTrace = bhMetricSpin(kerrTraceSpin(a));
  KerrConsts c;
  KerrRay kerrRay;
  kerrInitGeodesic(ray.position, ray.velocity, rsMetric, aTrace, c, kerrRay);
  result.origin = kerrChartPosition(ray.position, rsMetric, aTrace);
  result.closestApproachPoint = result.origin;

  vec3 oldPos;
  float dt = stepSize;

  for (int step = 0; step < maxSteps; ++step) {
    oldPos = kerrRayPosition(kerrRay);
    bhRecordClosestApproach(result, kerrRay.r, oldPos, step);

    if (kerrRay.r <= r_horizon) {
      result.hitHorizon = true;
      result.hitPoint = oldPos;
      return result;
    }

    /* D10: AMR step refinement near horizon and photon sphere */
    float stepDt = bhAdaptiveStep(kerrRay.r, r_s, r_horizon, dt);
    kerrStep(kerrRay, rsMetric, aTrace, c, stepDt);
    vec3 newPos = kerrRayPosition(kerrRay);
    result.debugFlags |= bhDebugEvaluate(newPos, newPos - oldPos, escapeRadius);
    if ((bhDebugMask() & BH_DEBUG_FLAG_RANGE) != 0 && kerrRay.r < 0.0) {
      result.debugFlags |= BH_DEBUG_FLAG_RANGE;
    }

    if (adiskEnabled > 0.5) {
      vec3 diskHit;
      if (bhCheckDiskIntersection(oldPos, newPos, r_disk_in, r_disk_out, diskHit)) {
        result.hitDisk = true;
        result.hitPoint = diskHit;
        result.phi = atan(diskHit.y, diskHit.x);
        result.redshiftFactor = bhComputeRedshiftFactor(length(diskHit), r_s);
        return result;
      }
    }

    if (kerrRay.r > escapeRadius && kerrRay.vr > 0.0) {
      result.escaped = true;
      result.hitPoint = newPos;
      result.escapedDir = normalize(newPos - oldPos);
      return result;
    }
  }

  result.debugFlags |= BH_DEBUG_FLAG_MAXSTEPS;
  result.escaped = true;
  result.hitPoint = kerrRayPosition(kerrRay);
  result.escapedDir = normalize(result.hitPoint - oldPos);
  return result;
}

vec4 bhHorizonColor() {
  return vec4(0.0, 0.0, 0.0, 1.0);
}

// Color a ray captured at radius r brings back: the black horizon plus the
// Hawking thermal glow (hawking_glow.glsl), which the legacy tracer adds at
// the same capture point.
vec3 bhHorizonShade(float r, float r_s) {
  return applyHawkingGlow(bhHorizonColor().rgb, blackHoleMass, r, r_s, hawkingGlowEnabled,
                          hawkingTempScale, hawkingGlowIntensity, hawkingTempLUT,
                          hawkingSpectrumLUT, useHawkingLUTs);
}

vec4 bhDiskColorFromHit(HitResult hit, float r_s) {
  float r = length(hit.hitPoint.xy);

  float flux = 0.0;
  if (useLUTs > 0.5) {
    float rNorm = r / max(r_s, BH_EPSILON);
    float denom = max(lutRadiusMax - lutRadiusMin, 0.0001);
    float u = clamp((rNorm - lutRadiusMin) / denom, 0.0, 1.0);
    flux = max(0.0, texture(emissivityLUT, vec2(u, 0.5)).r);
  } else {
    float r_in = bhDiskInnerRadius(r_s);
    float x = r_in / r;
    flux = pow(x, 3.0) * (1.0 - sqrt(x));
    flux = max(0.0, flux);
  }

  float T_norm = pow(flux, 0.25);

  vec3 color;
  if (T_norm > 0.6) {
    color = vec3(1.0, 0.9, 0.8);
  } else if (T_norm > 0.3) {
    color = vec3(1.0, 0.6, 0.2);
  } else {
    color = vec3(0.8, 0.2, 0.1);
  }

  float spectral = 1.0;
  if (useSpectralLUT > 0.5) {
    float rNorm = r / max(r_s, BH_EPSILON);
    float denom = max(spectralRadiusMax - spectralRadiusMin, 0.0001);
    float u = clamp((rNorm - spectralRadiusMin) / denom, 0.0, 1.0);
    spectral = max(0.0, texture(spectralLUT, vec2(u, 0.5)).r);
  }

  float intensity = flux * 2.0 * spectral;

  float v = sqrt(0.5 * r_s / r);
  float cos_phi = cos(hit.phi);
  float doppler = 1.0 + 0.3 * v * cos_phi;
  intensity *= doppler * doppler * doppler;

  if (useGrbModulation > 0.5) {
    float denom = max(grbTimeMax - grbTimeMin, 0.0001);
    float u = clamp((grbTime - grbTimeMin) / denom, 0.0, 1.0);
    float modulation = texture(grbModulationLUT, vec2(u, 0.5)).r;
    intensity *= max(modulation, 0.0);
  }

  if (enableRedshift > 0.5) {
    float z = 1.0 / max(hit.redshiftFactor, BH_EPSILON) - 1.0;
    if (useLUTs > 0.5) {
      float rNorm = r / max(r_s, BH_EPSILON);
      float denom = max(redshiftRadiusMax - redshiftRadiusMin, 0.0001);
      float u = clamp((rNorm - redshiftRadiusMin) / denom, 0.0, 1.0);
      z = texture(redshiftLUT, vec2(u, 0.5)).r;
    }
    color = applyGravitationalRedshift(color, z);
  }

  return vec4(color * intensity, 1.0);
}

vec3 bhRotateY(vec3 v, float angleDegrees) {
  float angle = radians(angleDegrees);
  float c = cos(angle);
  float s = sin(angle);
  return vec3(c * v.x + s * v.z, v.y, -s * v.x + c * v.z);
}

vec2 bhDirToUv(vec3 dir) {
  vec3 n = normalize(dir);
  float u = atan(n.z, n.x) / TWO_PI + 0.5;
  float v = asin(clamp(n.y, -1.0, 1.0)) * INV_PI + 0.5;
  return vec2(u, v);
}

vec3 bhSampleBackgroundLayers(vec3 dir, out float weight) {
  vec2 uv = bhDirToUv(dir);
  vec3 accum = vec3(0.0);
  weight = 0.0;
  for (int i = 0; i < BH_BACKGROUND_LAYERS; ++i) {
    vec4 params = backgroundLayerParams[i];
    if (params.w <= 0.0) {
      continue;
    }
    vec2 layerUv = fract(uv * params.z + params.xy);
    float lodBias = max(backgroundLayerLodBias[i], 0.0);
    vec3 layerColor = textureLod(backgroundLayers[i], layerUv, lodBias).rgb;
    accum += layerColor * params.w;
    weight += params.w;
  }
  if (weight > 0.0) {
    accum /= weight;
  }
  return accum;
}

// dir is a physics-frame direction; the sky textures are world-frame.
vec4 bhBackgroundColorFromDir(vec3 dir, float minRadius, float r_s) {
  vec3 n = normalize(bhPhysicsToWorld(dir));
  vec3 skyDir = bhRotateY(n, time);
  vec3 color = texture(galaxy, skyDir).rgb;
  if (backgroundEnabled > 0.5) {
    float layerWeight = 0.0;
    vec3 layerColor = bhSampleBackgroundLayers(skyDir, layerWeight);
    if (layerWeight > 0.0) {
      color = layerColor * backgroundIntensity;
    }
  }

  if (enableRedshift > 0.5 && minRadius < r_s * 10.0) {
    float z = 1.0 / max(bhComputeRedshiftFactor(minRadius, r_s), BH_EPSILON) - 1.0;
    if (useLUTs > 0.5) {
      float rNorm = minRadius / max(r_s, BH_EPSILON);
      float denom = max(redshiftRadiusMax - redshiftRadiusMin, 0.0001);
      float u = clamp((rNorm - redshiftRadiusMin) / denom, 0.0, 1.0);
      z = texture(redshiftLUT, vec2(u, 0.5)).r;
    }
    color = applySimpleRedshift(color, z);
  }

  return vec4(color, 1.0);
}

vec4 bhShadeHit(HitResult hit, vec3 cameraPos, float r_s) {
  // Show only the debug conditions the mask enables. Masking debugFlags here
  // (rather than gating each flag's assignment) lets the integrator classify
  // unconditionally while an exhausted ray under an unrelated mask bit still
  // falls through to normal shading instead of being swallowed to black.
  int displayFlags = hit.debugFlags & bhDebugMask();
  if (displayFlags != 0) {
    vec3 debugColor = vec3(0.0);
    if ((displayFlags & BH_DEBUG_FLAG_NAN) != 0) {
      debugColor += vec3(1.0, 0.0, 1.0);
    }
    if ((displayFlags & BH_DEBUG_FLAG_RANGE) != 0) {
      debugColor += vec3(1.0, 1.0, 0.0);
    }
    if ((displayFlags & BH_DEBUG_FLAG_MAXSTEPS) != 0) {
      debugColor += vec3(0.0, 1.0, 1.0);
    }
    return vec4(clamp(debugColor, 0.0, 1.0), 1.0);
  }
  if (hit.hitHorizon) {
    return vec4(bhHorizonShade(length(hit.hitPoint), r_s), 1.0);
  }
  if (hit.hitDisk) {
    return bhDiskColorFromHit(hit, r_s);
  }
  if (debugShaperInputs > 0.5) {
    return vec4(bhPackShaperInputs(hit.minRadius, hit.closestApproachPoint, cameraPos, r_s), 1.0);
  }
  if (debugClosestApproachState > 0.5) {
    return vec4(bhPackClosestApproachState(hit.minRadius, hit.closestApproachPoint, r_s), 1.0);
  }
  if (debugClosestApproachTimeline > 0.5) {
    return vec4(
        bhPackClosestApproachTimeline(hit.firstClosestApproachStep, hit.lastClosestApproachStep,
                                      hit.closestApproachUpdateCount, int(interopMaxSteps)),
        1.0);
  }
  if (debugClosestApproachDirection > 0.5) {
    return vec4(bhEncodeUnitVector(hit.closestApproachPoint), 1.0);
  }
  if (debugEscapedDirection > 0.5) {
    return vec4(bhEncodeUnitVector(hit.escapedDir), 1.0);
  }
  return bhBackgroundColorFromDir(normalize(hit.escapedDir), hit.minRadius, r_s);
}

// ---------------------------------------------------------------------------
// Volumetric disk segment
//
// The RTE and Stokes traces model the disk as a Gaussian layer, density
// exp(-z^2 / 2h^2) with h = 0.1 r_s, over the annulus rIn <= rho <= rOut
// (rho the cylindrical radius) under the Novikov-Thorne flux profile. A
// far-field step spans ~0.05 r, many scale heights, so a coefficient read at
// one point misses a midplane crossed mid-step, applies the peak density to
// the whole step, or keeps or drops the whole step by one radius.
// bhDiskSegment intersects the step's straight chord with the annulus
// (rho^2 is quadratic along the chord, so the emitting part is at most two
// intervals), integrates the density exactly over each interval, and reads
// the slowly varying radial factors (flux, color, Doppler) at each
// interval's density-weighted centroid, which is exact for factors linear
// along the chord. With every coefficient proportional to the density and
// the source function constant over the segment, the formal solution depends
// only on the column, so the mean coefficients over the step's path length
// give the exact segment when the radial factors are constant across it and
// converge as the step shrinks otherwise.
// ---------------------------------------------------------------------------

// erf(x) by Abramowitz & Stegun 7.1.26, |error| <= 1.5e-7.
float bhErf(float x) {
  float t = 1.0 / (1.0 + 0.3275911 * abs(x));
  float poly = t * (0.254829592 + t * (-0.284496736 + t * (1.421413741 +
               t * (-1.453152027 + t * 1.061405429))));
  float y = 1.0 - poly * exp(-x * x);
  return x < 0.0 ? -y : y;
}

// Mean and centroid of the density exp(-z^2 / 2h^2) along a chord whose
// height runs linearly from z0 to z1, sharing one erf pair (s = 1 / (sqrt(2) h)):
//   mean     = h sqrt(pi/2) (erf(z1 s) - erf(z0 s)) / (z1 - z0),
//   centroid = fraction along the chord of the weighted mean height
//              -h^2 (exp(-z1^2 / 2h^2) - exp(-z0^2 / 2h^2)) / (mean (z1 - z0)).
// Below |z1 - z0| = 0.01 sqrt(2) h the midpoint value (relative error < 1e-5)
// and the midpoint; a chord too far in the tail to resolve its centroid also
// takes the midpoint.
vec2 bhGaussianChordMoments(float z0, float z1, float h) {
  float s = 0.70710678 / h;
  float dz = z1 - z0;
  if (abs(dz) * s < 0.01) {
    float zm = 0.5 * (z0 + z1) / h;
    return vec2(exp(-0.5 * zm * zm), 0.5);
  }
  float mass = 1.25331414 * h * (bhErf(z1 * s) - bhErf(z0 * s));
  float frac = 0.5;
  if (abs(mass) >= 1e-6 * abs(dz)) {
    float zBar = -h * h * (exp(-z1 * z1 * s * s) - exp(-z0 * z0 * s * s)) / mass;
    frac = clamp((zBar - z0) / dz, 0.0, 1.0);
  }
  return vec2(mass / dz, frac);
}

// Parameter interval [t0, t1] (clipped to [0, 1]) of the chord a + b t,
// t in [0, 1], on which |a + b t| <= radius; empty when t0 > t1.
vec2 bhChordInsideRadius(vec2 a, vec2 b, float radius) {
  float qa = dot(b, b);
  float qb = dot(a, b);
  float qc = dot(a, a) - radius * radius;
  if (qa < 1e-12 * max(qc + radius * radius, 1.0)) {
    return qc <= 0.0 ? vec2(0.0, 1.0) : vec2(1.0, 0.0);
  }
  float disc = qb * qb - qa * qc;
  if (disc < 0.0) {
    return vec2(1.0, 0.0);
  }
  float root = sqrt(disc);
  return vec2(max((-qb - root) / qa, 0.0), min((-qb + root) / qa, 1.0));
}

// Radial factors of the disk at cylindrical radius rho and azimuth angle phi.
float bhDiskRadialEmission(float rho, float phi, float rIn, float r_s, out vec3 emitColor) {
  // Novikov-Thorne surface flux profile
  float x    = rIn / max(rho, BH_EPSILON);
  float flux = max(0.0, x * x * x * (1.0 - sqrt(x)));

  // Temperature-to-color mapping (three bands)
  float T_norm = sqrt(sqrt(flux));
  if (T_norm > 0.6) {
    emitColor = vec3(1.0, 0.9, 0.8);
  } else if (T_norm > 0.3) {
    emitColor = vec3(1.0, 0.6, 0.2);
  } else {
    emitColor = vec3(0.8, 0.2, 0.1);
  }

  // Doppler beaming (Keplerian v ~ sqrt(r_s / 2r))
  float v       = sqrt(0.5 * r_s / max(rho, BH_EPSILON));
  float doppler = 1.0 + 0.3 * v * cos(phi);
  return flux * doppler * doppler * doppler;
}

// Adds the part of the chord p0 -> p1 between parameters ta and tb (inside
// the annulus) to the running column, emissivity, and color sums.
void bhDiskPiece(vec3 p0, vec3 p1, float ta, float tb, float rIn, float h, float r_s,
                 inout float rhoSum, inout float jSum, inout vec3 colorSum) {
  if (tb <= ta) {
    return;
  }
  float za = mix(p0.z, p1.z, ta);
  float zb = mix(p0.z, p1.z, tb);
  vec2 moments = bhGaussianChordMoments(za, zb, h);
  float column = (tb - ta) * moments.x;
  if (column <= 0.0) {
    return;
  }
  vec3 weighted = mix(p0, p1, mix(ta, tb, moments.y));
  vec3 color;
  float radial = bhDiskRadialEmission(length(weighted.xy), atan(weighted.y, weighted.x), rIn,
                                      r_s, color);
  rhoSum += column;
  jSum += radial * column;
  colorSum += color * (radial * column);
}

// Disk emission over the chord p0 -> p1 (physics frame, disk in xy). Returns
// false when no part of the chord inside the annulus carries density;
// otherwise the emission-weighted band color, the mean emissivity
// jEff = <flux g^3 rho> over the whole chord, and the mean density <rho>
// over the whole chord (zero outside the annulus).
bool bhDiskSegment(vec3 p0, vec3 p1, float rIn, float rOut, float h, float r_s,
                   out vec3 emitColor, out float jEff, out float rhoMean) {
  emitColor = vec3(0.0);
  jEff = 0.0;
  rhoMean = 0.0;
  // A chord on one side of the midplane and more than 8 h from it carries
  // density below exp(-32) ~ 1e-14 everywhere.
  if (p0.z * p1.z > 0.0 && min(abs(p0.z), abs(p1.z)) > 8.0 * h) {
    return false;
  }
  // Inside rOut is one interval; inside rIn is one interval to exclude.
  // rho^2 is convex along the chord, so end points inside rOut keep the
  // whole chord and a closest approach outside rIn excludes nothing; only a
  // chord across an edge solves the quadratic.
  vec2 a = p0.xy;
  vec2 b = p1.xy - p0.xy;
  vec2 outer = max(dot(a, a), dot(p1.xy, p1.xy)) <= rOut * rOut
                   ? vec2(0.0, 1.0)
                   : bhChordInsideRadius(a, b, rOut);
  float tClosest = clamp(-dot(a, b) / max(dot(b, b), 1e-30), 0.0, 1.0);
  vec2 closest = a + tClosest * b;
  vec2 inner = dot(closest, closest) >= rIn * rIn ? vec2(1.0, 0.0)
                                                   : bhChordInsideRadius(a, b, rIn);
  vec3 colorSum = vec3(0.0);
  if (inner.x > inner.y) {
    bhDiskPiece(p0, p1, outer.x, outer.y, rIn, h, r_s, rhoMean, jEff, colorSum);
  } else {
    bhDiskPiece(p0, p1, outer.x, min(outer.y, inner.x), rIn, h, r_s, rhoMean, jEff, colorSum);
    bhDiskPiece(p0, p1, max(outer.x, inner.y), outer.y, rIn, h, r_s, rhoMean, jEff, colorSum);
  }
  if (!(rhoMean > 0.0)) {
    return false;
  }
  emitColor = jEff > 0.0 ? colorSum / jEff : vec3(0.8, 0.2, 0.1);
  return true;
}

// ---------------------------------------------------------------------------
// bhTraceGeodesicRTE
//
// Volumetric radiative transfer along a Kerr geodesic using front-to-back
// compositing.  Each step inside the disk volume accumulates emission via
// rteStepVec3(); background and horizon contributions are weighted by the
// surviving transmittance at escape.
//
// opacityScale: alpha_nu = opacityScale * j_eff  (tune in ImGui); j_eff and
// alpha_nu are per unit affine length (kerrAffineStep).
// ---------------------------------------------------------------------------
vec4 bhTraceGeodesicRTE(Ray ray, float r_s, float maxDistance, int maxSteps,
                        float stepSize, float opacityScale, out vec3 terminalPos) {
  float a = 0.5 * kerrSpin * r_s;
  float r_horizon = kerrOuterHorizon(r_s, a);
  if (r_horizon <= BH_EPSILON) { r_horizon = r_s; }

  float r_disk_in  = bhDiskInnerRadius(r_s);
  float r_disk_out = 100.0 * r_s;
  // Gaussian vertical scale height for thin-disk density model (H/r ~ 0.1)
  float h_disk = max(0.1 * r_s, BH_EPSILON);

  float escapeRadius = bhEscapeRadius(ray.position, maxDistance);
  if (!bhHoleRendered()) {
    vec3 dir = normalize(ray.velocity);
    terminalPos = ray.position + escapeRadius * dir;
    return vec4(bhBackgroundColorFromDir(dir, BH_NO_HOLE_RADIUS, r_s).rgb, 1.0);
  }

  float rsMetric = bhMetricRadius(r_s);
  float aTrace = bhMetricSpin(kerrTraceSpin(a));
  KerrConsts c;
  KerrRay    kRay;
  kerrInitGeodesic(ray.position, ray.velocity, rsMetric, aTrace, c, kRay);
  vec3 origin = kerrChartPosition(ray.position, rsMetric, aTrace);

  vec3  accumI   = vec3(0.0);
  float transmit = 1.0;
  float minR     = kRay.r;

  for (int step = 0; step < maxSteps; ++step) {
    vec3 curPos = kerrRayPosition(kRay);
    minR = min(minR, kRay.r);

    if (kRay.r <= r_horizon) {
      terminalPos = curPos;
      accumI += transmit * bhHorizonShade(kRay.r, r_s);
      return vec4(accumI, 1.0);
    }

    /* D10: AMR step refinement near horizon and photon sphere */
    float rteStepDt = bhAdaptiveStep(kRay.r, r_s, r_horizon, stepSize);
    KerrRay before = kRay;
    kerrStep(kRay, rsMetric, aTrace, c, rteStepDt);
    vec3 newPos = kerrRayPosition(kRay);
    // rteStepDt is a Mino-time increment; transfer integrates over affine
    // length (kerrAffineStep), the unit of jEff and alphaNu.
    float pathStep = kerrAffineStep(before, kRay, aTrace, rteStepDt);

    vec3 emitColor;
    float jEff;
    float rhoNorm;
    if (adiskEnabled > 0.5 &&
        bhDiskSegment(curPos, newPos, r_disk_in, r_disk_out, h_disk, r_s, emitColor, jEff,
                      rhoNorm)) {
      float alphaNu = opacityScale * max(jEff, 0.0);

      accumI += rteStepVec3(emitColor, jEff, alphaNu, pathStep, transmit);

      // Early exit when medium becomes opaque
      if (transmit < 0.005) {
        terminalPos = newPos;
        return vec4(accumI, 1.0);
      }
    }

    if (kRay.r > escapeRadius && kRay.vr > 0.0) {
      vec3 escDir = newPos - curPos;
      terminalPos = newPos;
      if (dot(escDir, escDir) > BH_EPSILON * BH_EPSILON) {
        accumI += transmit * bhBackgroundColorFromDir(normalize(escDir),
                                                      minR, r_s).rgb;
      }
      return vec4(accumI, 1.0);
    }
  }

  // Max steps exhausted -- treat as escaped toward last known direction
  vec3 finalPos = kerrRayPosition(kRay);
  terminalPos = finalPos;
  vec3 escDir   = finalPos - origin;
  if (dot(escDir, escDir) > BH_EPSILON * BH_EPSILON) {
    accumI += transmit * bhBackgroundColorFromDir(normalize(escDir),
                                                  minR, r_s).rgb;
  }
  return vec4(accumI, 1.0);
}

// ---------------------------------------------------------------------------
// bhTraceGeodesicStokes
//
// Polarized radiative transfer along a Kerr geodesic.  Extends
// bhTraceGeodesicRTE() to track Stokes Q, U, V alongside the scalar
// intensity accumulator.
//
// The I channel uses the same front-to-back compositing as bhTraceGeodesicRTE()
// (vec3 color-accurate accumulation).  The Q, U, V channels take each disk
// step's stokesStep() exact solution (simplified K: alpha_I + rho_V) and
// composite it front to back through the nearer steps (stokesCompositeStep),
// with the same alphaI and path length as the intensity path so the
// polarimetric and photometric results remain consistent.
//
// Polarization model:
//   - Intrinsic linear polarization fraction: PI_LIN = 0.75 (thermal synchrotron
//     at Theta_e >> 1, Mahadevan 1996, matches thermalSynchLinearPolarFrac)
//   - B-field EVPA on sky: bFieldAngle [rad] (uniform field, tuned via ImGui)
//   - Faraday rotation rate: rhoV = neScale * rhoNorm (neScale tunable)
//
// At exit: stokesDisplayColor() tints the accumulated intensity by EVPA and
// linear polarization fraction so the result is visually informative.
//
// Parameters:
//   bFieldAngle -- projected B-field EVPA on sky [rad]
//   neScale     -- Faraday rotation strength multiplier (0 = no Faraday)
// ---------------------------------------------------------------------------
vec4 bhTraceGeodesicStokes(Ray ray, float r_s, float maxDistance, int maxSteps,
                            float stepSize, float opacityScale,
                            float bFieldAngle, float neScale,
                            out vec3 terminalPos) {
  float a = 0.5 * kerrSpin * r_s;
  float r_horizon = kerrOuterHorizon(r_s, a);
  if (r_horizon <= BH_EPSILON) { r_horizon = r_s; }

  float r_disk_in  = bhDiskInnerRadius(r_s);
  float r_disk_out = 100.0 * r_s;
  float h_disk     = max(0.1 * r_s, BH_EPSILON);

  // Thermal synchrotron intrinsic linear polarization fraction (~0.75 at Theta_e >> 1)
  const float PI_LIN = 0.75;

  float escapeRadius = bhEscapeRadius(ray.position, maxDistance);
  if (!bhHoleRendered()) {
    vec3 dir = normalize(ray.velocity);
    terminalPos = ray.position + escapeRadius * dir;
    vec3 sky = bhBackgroundColorFromDir(dir, BH_NO_HOLE_RADIUS, r_s).rgb;
    float skyI = (sky.r + sky.g + sky.b) / 3.0;
    return vec4(stokesDisplayColor(vec4(skyI, 0.0, 0.0, 0.0), sky), 1.0);
  }

  float rsMetric = bhMetricRadius(r_s);
  float aTrace = bhMetricSpin(kerrTraceSpin(a));
  KerrConsts c;
  KerrRay    kRay;
  kerrInitGeodesic(ray.position, ray.velocity, rsMetric, aTrace, c, kRay);
  vec3 origin = kerrChartPosition(ray.position, rsMetric, aTrace);
  // Set when the ray escapes or the medium turns opaque; otherwise the step
  // budget ran out and the ray is shaded as escaping along its last
  // direction, as bhTraceGeodesicRTE does.
  bool finished = false;

  vec3  accumI   = vec3(0.0);   // Color-accurate intensity (same as RTE path)
  // Observed polarization, composited front to back (stokesCompositeStep):
  // (unused I, Q, U, V), the nearer segments' transmittance and Faraday angle.
  vec4  polObserved = vec4(0.0);
  float polTransmit = 1.0;
  float polFaraday  = 0.0;
  float transmit = 1.0;
  float minR     = kRay.r;

  for (int step = 0; step < maxSteps; ++step) {
    vec3 curPos = kerrRayPosition(kRay);
    minR = min(minR, kRay.r);

    if (kRay.r <= r_horizon) {
      terminalPos = curPos;
      accumI += transmit * bhHorizonShade(kRay.r, r_s);
      float I = (accumI.r + accumI.g + accumI.b) / 3.0;
      vec4 stokes = vec4(I, polObserved.y, polObserved.z, polObserved.w);
      return vec4(stokesDisplayColor(stokes, accumI), 1.0);
    }

    float stepDt = bhAdaptiveStep(kRay.r, r_s, r_horizon, stepSize);
    KerrRay before = kRay;
    kerrStep(kRay, rsMetric, aTrace, c, stepDt);
    vec3 newPos = kerrRayPosition(kRay);
    // Affine path length of the Mino step (kerrAffineStep), the unit of
    // alphaNu and rhoV.
    float pathStep = kerrAffineStep(before, kRay, aTrace, stepDt);

    vec3 emitColor;
    float jEff;
    float rhoNorm;
    if (adiskEnabled > 0.5 &&
        bhDiskSegment(curPos, newPos, r_disk_in, r_disk_out, h_disk, r_s, emitColor, jEff,
                      rhoNorm)) {
      float alphaNu = opacityScale * max(jEff, 0.0);

      // Intensity path (front-to-back compositing identical to RTE path)
      accumI += rteStepVec3(emitColor, jEff, alphaNu, pathStep, transmit);

      // Polarization path: stokesStep() for Q, U, V
      // jI_scalar: mean color intensity for the emission vector
      float jI_scalar = jEff * (emitColor.r + emitColor.g + emitColor.b) / 3.0;
      // Polarized emission: j_Q, j_U from B-field EVPA; j_V = 0
      vec4 emStokes = synchrotronPolarizedEmission(jI_scalar, PI_LIN, bFieldAngle);

      // Faraday rotation rate: rhoV = neScale * rhoNorm (density-modulated)
      float rhoV = neScale * rhoNorm;

      // Q, U, V under simplified K (alpha_I + rho_V), composited front to
      // back: this segment's emission passes through the nearer segments.
      stokesCompositeStep(polObserved, polTransmit, polFaraday, emStokes, alphaNu, rhoV,
                          pathStep);

      if (transmit < 0.005) {
        finished = true;
        break;
      }
    }

    if (kRay.r > escapeRadius && kRay.vr > 0.0) {
      vec3 escDir = newPos - curPos;
      terminalPos = newPos;
      if (dot(escDir, escDir) > BH_EPSILON * BH_EPSILON) {
        accumI += transmit * bhBackgroundColorFromDir(normalize(escDir),
                                                      minR, r_s).rgb;
      }
      finished = true;
      break;
    }
  }

  // Map accumulated Stokes state to display color
  terminalPos = kerrRayPosition(kRay);
  vec3 budgetDir = terminalPos - origin;
  if (!finished && dot(budgetDir, budgetDir) > BH_EPSILON * BH_EPSILON) {
    accumI += transmit * bhBackgroundColorFromDir(normalize(budgetDir), minR, r_s).rgb;
  }
  float I = (accumI.r + accumI.g + accumI.b) / 3.0;
  vec4 stokes = vec4(I, polObserved.y, polObserved.z, polObserved.w);
  return vec4(stokesDisplayColor(stokes, accumI), 1.0);
}

#endif // INTEROP_TRACE_GLSL
