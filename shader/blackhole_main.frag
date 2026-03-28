/**
 * @file blackhole_main.frag
 * @brief Primary black hole ray-tracing fragment shader.
 *
 * Marches rays through Schwarzschild/Kerr spacetime, samples the accretion
 * disk with noise and LUTs, applies gravitational lensing, Doppler beaming,
 * gravitational redshift, photon-sphere glow, and optional Hawking thermal glow.
 * Key uniforms: resolution, cameraPos, cameraBasis, schwarzschildRadius, kerrSpin,
 *   adisk*, hawking*, backgroundLayers[3], grmhdTexture, noiseTexture.
 * Inputs: gl_FragCoord.
 * Outputs: fragColor (RGB = HDR color, A = normalized depth).
 */
#version 460 core
#extension GL_GOOGLE_include_directive : enable

// Mathematical and physical constants
#include "include/physics_constants.glsl"

// Physics library includes - Phase 7: Verified from Rocq formalization
#include "include/verified/physics.glsl"

// Legacy includes (maintained for compatibility)
#include "include/redshift.glsl"
#include "include/kerr.glsl"
#include "include/interop_raygen.glsl"

// Phase 10.1: Hawking radiation thermal glow
#include "hawking_glow.glsl"
#include "include/wiregrid.glsl"

const float EPSILON = 0.0001;
const float INFINITY = 1000000.0;

out vec4 fragColor;

uniform vec2 resolution; // viewport resolution in pixels
uniform float time; // time elapsed in seconds
uniform sampler2D uSynchLUT;
uniform sampler2D colorMap;
uniform sampler2D emissivityLUT;
uniform sampler2D redshiftLUT;
uniform sampler2D spectralLUT;
uniform sampler2D grbModulationLUT;
uniform sampler2D photonGlowLUT; // Phase 8.2: LUT for exp(-distance*4.0)
uniform sampler2D diskDensityLUT; // Phase 8.2: Disk density profile LUT
uniform sampler3D noiseTexture;
uniform sampler3D grmhdTexture;
uniform samplerCube galaxy;
uniform sampler2D backgroundLayers[3];
uniform vec4 backgroundLayerParams[3];
uniform float backgroundLayerLodBias[3];
uniform float backgroundEnabled = 0.0;
uniform float backgroundIntensity = 1.0;
uniform float backgroundYawRad = 0.0;
uniform float backgroundPitchRad = 0.0;
uniform float kerrSpin = 0.0;
uniform float useLUTs = 0.0;
uniform float useNoiseTexture = 0.0;
uniform float useGrmhd = 0.0;
uniform float useSpectralLUT = 0.0;
uniform float noiseTextureScale = 0.25;
uniform float lutRadiusMin = 0.0;
uniform float lutRadiusMax = 1.0;
uniform float redshiftRadiusMin = 0.0;
uniform float redshiftRadiusMax = 1.0;
uniform float spectralRadiusMin = 0.0;
uniform float spectralRadiusMax = 1.0;
uniform float useGrbModulation = 0.0;
uniform float grbTime = 0.0;
uniform float grbTimeMin = 0.0;
uniform float grbTimeMax = 1.0;
uniform vec3 grmhdBoundsMin = vec3(-10.0);
uniform vec3 grmhdBoundsMax = vec3(10.0);

uniform vec3 cameraPos;
uniform mat3 cameraBasis;
uniform float depthFar = 50.0;

uniform float gravitationalLensing = 1.0;
uniform float renderBlackHole = 1.0;
uniform float fovScale = 1.0;
uniform float interopParityMode = 0.0;
uniform float interopMaxSteps = 48.0;  // Balanced quality/performance (was 300, ultra-fast=20)
uniform float interopStepSize = 0.2;   // Balanced (was 0.1, ultra-fast=0.25)
// D2: Volumetric RTE path -- accumulates emission/absorption through disk volume
uniform float rteEnabled      = 0.0;   // 0=single-scatter (legacy), 1=volumetric RTE
uniform float rteOpacityScale = 0.5;   // alpha_nu = rteOpacityScale * j_nu

// D4: Polarized Stokes I,Q,U,V transport (supersedes rteEnabled when on)
uniform float stokesEnabled    = 0.0;  // 1 = track Stokes IQUV alongside intensity
uniform float stokesBFieldAngle = 0.0; // EVPA of projected B field on sky [rad]
uniform float stokesNeScale    = 0.0;  // Faraday rotation strength (0 = no Faraday)

uniform float adiskEnabled = 1.0;
uniform float adiskParticle = 1.0;
uniform float adiskHeight = 0.2;
uniform float adiskLit = 0.5;
uniform float adiskDensityV = 1.0;
uniform float adiskDensityH = 1.0;
uniform float adiskNoiseScale = 1.0;
uniform float adiskNoiseLOD = 5.0;
uniform float adiskSpeed = 0.5;
uniform float dopplerStrength = 1.0;

// Physics parameters
uniform float schwarzschildRadius = 2.0; // r_s = 2GM/c² (default = 2 in geometric units)
// Derived radii computed from schwarzschildRadius using physics functions:
// - photonSphereRadius = 1.5 * r_s via sch_photonSphereRadius()
// - iscoRadius = 3.0 * r_s via sch_iscoRadius()
// These are now computed in adiskColor() and traceColor() to avoid redundant uniforms
uniform float enableRedshift = 0.0;      // Toggle gravitational redshift
uniform float enablePhotonSphere = 0.0;  // Toggle photon sphere glow
uniform float photonSphereGlowStrength = 1.0;

// Phase 10.1: Hawking radiation parameters
uniform float hawkingGlowEnabled = 0.0;  // Toggle Hawking thermal glow
uniform float hawkingTempScale = 1.0;    // Temperature scaling (1.0=physical, 1e6=primordial, 1e9=extreme)
uniform float hawkingGlowIntensity = 1.0; // Glow intensity multiplier [0, 5]
uniform sampler2D hawkingTempLUT;        // Temperature T_H(M) LUT
uniform sampler2D hawkingSpectrumLUT;    // Blackbody RGB spectrum LUT
uniform float useHawkingLUTs = 1.0;      // Use LUTs (1.0) vs direct calculation (0.0)
uniform float blackHoleMass = 1.989e33;  // Black hole mass [g] (default: 1 solar mass)

// Wiregrid BL-coordinate overlay uniforms (task A2)
uniform float wiregridEnabled  = 0.0; // 1.0 = overlay active
uniform float wiregridShowErgo = 1.0; // 1.0 = show ergosphere boundary
uniform float wiregridGridScale = 0.92; // Grid density multiplier
uniform float wiregridMotionScale = 0.62; // Frame-dragging advection strength
uniform float wiregridInfallScale = 0.24; // Inward shell motion strength
uniform float wiregridStrength = 0.84; // Post-attenuation alpha multiplier
uniform float wiregridScenePreserve = 1.0; // 1 = yield to scene luminance, 0 = diagnostic
uniform vec4 wiregridColor = vec4(0.21, 0.62, 0.92, 0.16); // Base grid RGBA

// Derived physics quantities: use sch_* functions from schwarzschild.glsl
// These macros ensure iscoRadius and photonSphereRadius are computed from schwarzschildRadius
// rather than being redundant uniforms (eliminates parameter synchronization issues)
// Define the sch_* functions inline to avoid include conflicts with redshift.glsl
float sch_photonSphereRadius(float r_s) { return 1.5 * r_s; }
float sch_iscoRadius(float r_s) { return 3.0 * r_s; }
#define iscoRadius sch_iscoRadius(schwarzschildRadius)
#define photonSphereRadius sch_photonSphereRadius(schwarzschildRadius)

#include "include/interop_trace.glsl"

///----
/// Noise is sampled from a 3D texture (offline/precomputed).
///----

vec3 panoramaColor(sampler2D tex, vec3 dir) {
  vec2 uv = vec2(0.5 - atan(dir.z, dir.x) / PI * 0.5, 0.5 - asin(dir.y) / PI);
  return texture(tex, uv).rgb;
}

float luminance(vec3 color) {
  return dot(color, vec3(0.2126, 0.7152, 0.0722));
}

// Inlined accel() computation (Phase 8.2 optimization: eliminates function call overhead)
// a = -1.5 * r_s * h² * pos / r⁵ where r = |pos|

vec4 quadFromAxisAngle(vec3 axis, float angle) {
  vec4 qr;
  float half_angle = (angle * 0.5) * 3.14159 / 180.0;
  qr.x = axis.x * sin(half_angle);
  qr.y = axis.y * sin(half_angle);
  qr.z = axis.z * sin(half_angle);
  qr.w = cos(half_angle);
  return qr;
}

vec4 quadConj(vec4 q) { return vec4(-q.x, -q.y, -q.z, q.w); }

vec4 quat_mult(vec4 q1, vec4 q2) {
  vec4 qr;
  qr.x = (q1.w * q2.x) + (q1.x * q2.w) + (q1.y * q2.z) - (q1.z * q2.y);
  qr.y = (q1.w * q2.y) - (q1.x * q2.z) + (q1.y * q2.w) + (q1.z * q2.x);
  qr.z = (q1.w * q2.z) + (q1.x * q2.y) - (q1.y * q2.x) + (q1.z * q2.w);
  qr.w = (q1.w * q2.w) - (q1.x * q2.x) - (q1.y * q2.y) - (q1.z * q2.z);
  return qr;
}

vec3 rotateVector(vec3 position, vec3 axis, float angle) {
  vec4 qr = quadFromAxisAngle(axis, angle);
  vec4 qr_conj = quadConj(qr);
  vec4 q_pos = vec4(position.x, position.y, position.z, 0);

  vec4 q_tmp = quat_mult(qr, q_pos);
  qr = quat_mult(q_tmp, qr_conj);

  return vec3(qr.x, qr.y, qr.z);
}

#define IN_RANGE(x, a, b) (((x) > (a)) && ((x) < (b)))

void cartesianToSpherical(in vec3 xyz, out float rho, out float phi,
                          out float theta) {
  rho = sqrt((xyz.x * xyz.x) + (xyz.y * xyz.y) + (xyz.z * xyz.z));
  phi = asin(xyz.y / rho);
  theta = atan(xyz.z, xyz.x);
}

// Convert from Cartesian to spherical coord (rho, phi, theta)
// https://en.wikipedia.org/wiki/Spherical_coordinate_system
vec3 toSpherical(vec3 p) {
  float rho = sqrt((p.x * p.x) + (p.y * p.y) + (p.z * p.z));
  float theta = atan(p.z, p.x);
  float phi = asin(p.y / rho);
  return vec3(rho, theta, phi);
}

vec3 toSpherical2(vec3 pos) {
  vec3 radialCoords;
  radialCoords.x = length(pos) * 1.5 + 0.55;
  radialCoords.y = atan(-pos.x, -pos.z) * 1.5;
  radialCoords.z = abs(pos.y);
  return radialCoords;
}

float sqrLength(vec3 a) { return dot(a, a); }

bool adiskColor(vec3 pos, vec3 rayDir, inout vec3 color, inout float alpha) {
  // Inner radius at ISCO (innermost stable circular orbit)
  // For Schwarzschild: r_ISCO = 3 * r_s where r_s = 2GM/c²
  // iscoRadius is already in the same coordinate units as positions
  float innerRadius = iscoRadius;
  float outerRadius = iscoRadius * 4.0; // Outer edge at ~12 r_s for typical thin disk

  // Phase 8.2 Priority 3: Cache Cartesian radius to avoid recomputation
  float r = length(pos);

  // Density linearly decreases as the distance to the blackhole center
  // increases.
  float density = max(
      0.0, 1.0 - length(pos.xyz / vec3(outerRadius, adiskHeight, outerRadius)));
  if (density < 0.001) {
    return false;
  }

  // Phase 8.2 Priority 2: Use precomputed disk density LUT instead of pow()
  // Map vertical coordinate to [0, 1] and lookup density profile
  float normalizedV = abs(pos.y) / adiskHeight;
  float verticalDensity = texture(diskDensityLUT, vec2(clamp(normalizedV, 0.0, 1.0), 0.5)).r;
  density *= verticalDensity;

  // Set particle density to 0 when radius is below the innermost stable
  // circular orbit (ISCO). Matter spirals in rapidly below this radius.
  density *= smoothstep(innerRadius, innerRadius * 1.1, r);  // Use cached radius

  // Avoid the shader computation when density is very small.
  if (density < 0.001) {
    return false;
  }

  vec3 sphericalCoord = toSpherical(pos);
  float radial01 = clamp((r - innerRadius) / max(outerRadius - innerRadius, EPSILON), 0.0, 1.0);

  // Scale the rho and phi so that the particales appear to be at the correct
  // scale visually.
  sphericalCoord.y *= 2.0;
  sphericalCoord.z *= 4.0;

  density *= 1.0 / pow(sphericalCoord.x, adiskDensityH);
  density *= 16000.0;

  if (useGrmhd > 0.5) {
    vec3 boundsSize = max(grmhdBoundsMax - grmhdBoundsMin, vec3(EPSILON));
    vec3 grmhdCoord = clamp((pos - grmhdBoundsMin) / boundsSize, 0.0, 1.0);
    vec4 grmhdSample = texture(grmhdTexture, grmhdCoord);
    /* Synchrotron emissivity: j_nu ~ rho * B^2.
     * Approximate B^2 ~ u (internal energy; plasma beta ~ 1).
     * Both channels are pre-normalised to [0,1] by nubhlight_pack min/max. */
    float rho = max(grmhdSample.r, 0.0);
    float uu  = max(grmhdSample.g, 0.0);
    density *= rho * uu;
  }

  if (adiskParticle < 0.5) {
    color += vec3(0.0, 1.0, 0.0) * density * 0.02;
    return true;
  }

  float noise = 1.0;
  bool useNoiseTex = useNoiseTexture > 0.5;
  for (int i = 0; i < int(adiskNoiseLOD); i++) {
    float noiseSample = 1.0;
    if (useNoiseTex) {
      vec3 noiseCoord = fract(sphericalCoord * noiseTextureScale * adiskNoiseScale);
      noiseSample = texture(noiseTexture, noiseCoord).r;
    }
    noise *= noiseSample;
    if (i % 2 == 0) {
      sphericalCoord.y += time * adiskSpeed;
    } else {
      sphericalCoord.y -= time * adiskSpeed;
    }
  }

  vec3 dustColor =
      texture(colorMap, vec2(sphericalCoord.x / outerRadius, 0.5)).rgb;

  // Give the inner disk a hotter, brighter thermal character so the accretion
  // structure reads as a scene element instead of a uniformly tinted slab.
  vec3 thermalInner = vec3(1.35, 0.78, 0.28);
  vec3 thermalOuter = vec3(0.92, 0.86, 0.78);
  vec3 thermalTint = mix(thermalInner, thermalOuter, sqrt(radial01));
  dustColor *= thermalTint;

  // Relativistic Doppler beaming (boosts the approaching side of the disk)
  vec3 velDir = normalize(vec3(-pos.z, 0.0, pos.x));
  float doppler = 1.0 + dot(velDir, normalize(rayDir)) * 0.65 * dopplerStrength;
  float beaming = pow(max(0.18, doppler), 1.35);
  dustColor *= beaming;

  // Kerr showcase shots need asymmetric energy placement, not a globally
  // brighter disk. Bias the inner emission toward the approaching/prograde side.
  vec3 spinAxis = vec3(0.0, kerrSpin >= 0.0 ? 1.0 : -1.0, 0.0);
  float spinView = 0.5 + 0.5 * dot(normalize(cross(spinAxis, normalize(pos))), -normalize(rayDir));
  float anisotropicBoost = mix(1.0, mix(0.82, 1.55, spinView), smoothstep(0.05, 0.85, abs(kerrSpin)));
  dustColor *= anisotropicBoost;

  // Viewing the thin disk closer to edge-on should increase its visual force.
  float grazingBoost = pow(clamp(1.0 - abs(rayDir.y), 0.0, 1.0), 1.5);
  dustColor *= mix(1.0, 1.55, grazingBoost);

  // Emphasize the inner-crescent read where the disk is both hot and seen as a
  // thin luminous sheet near the hole.
  float midplaneBoost = pow(clamp(1.0 - normalizedV, 0.0, 1.0), 0.45);
  float crescentBoost = mix(1.0, 1.8, midplaneBoost * (1.0 - radial01));
  dustColor *= crescentBoost;

  // Phase 8.2 Priority 3: Conditional texture batching with mix() to avoid branch divergence
  float rNorm = r / max(schwarzschildRadius, EPSILON);  // Use cached radius

  // Emissivity LUT: use mix() instead of if/else to eliminate branch divergence
  float lutEmissivity = 1.0;
  float denom = max(lutRadiusMax - lutRadiusMin, 0.0001);
  float u = clamp((rNorm - lutRadiusMin) / denom, 0.0, 1.0);
  lutEmissivity = max(0.0, texture(emissivityLUT, vec2(u, 0.5)).r);
  float emissivity = mix(1.0, lutEmissivity, step(0.5, useLUTs));
  density *= emissivity;

  // Spectral LUT: use mix() instead of if/else
  float spectralValue = 1.0;
  denom = max(spectralRadiusMax - spectralRadiusMin, 0.0001);
  u = clamp((rNorm - spectralRadiusMin) / denom, 0.0, 1.0);
  spectralValue = max(0.0, texture(spectralLUT, vec2(u, 0.5)).r);
  density *= mix(1.0, spectralValue, step(0.5, useSpectralLUT));

  // GRB modulation: use mix() instead of if/else
  float grbValue = 1.0;
  denom = max(grbTimeMax - grbTimeMin, 0.0001);
  u = clamp((grbTime - grbTimeMin) / denom, 0.0, 1.0);
  grbValue = max(0.0, texture(grbModulationLUT, vec2(u, 0.5)).r);
  density *= mix(1.0, grbValue, step(0.5, useGrbModulation));

  // Apply gravitational redshift to disk emission
  if (enableRedshift > 0.5) {
    float z = gravitationalRedshift(r, schwarzschildRadius);  // Use cached radius r
    if (useLUTs > 0.5) {
      float rNorm = r / max(schwarzschildRadius, EPSILON);
      float denom = max(redshiftRadiusMax - redshiftRadiusMin, 0.0001);
      float u = clamp((rNorm - redshiftRadiusMin) / denom, 0.0, 1.0);
      z = texture(redshiftLUT, vec2(u, 0.5)).r;
    }
    // Apply full wavelength shift for physically accurate color
    dustColor = applyGravitationalRedshift(dustColor, z);
  }

  // Push more emissive structure toward the near-ISCO region so the disk has a
  // brighter asymmetric crescent rather than reading as a faint halo.
  float innerBoost = mix(1.8, 0.85, pow(radial01, 0.65));
  float emission = density * adiskLit * alpha * abs(noise) * innerBoost;
  color += emission * dustColor;
  return true;
}

vec3 traceColor(vec3 pos, vec3 dir, out float depthDistance, out vec3 lastPos) {
  vec3 color = vec3(0.0);
  float alpha = 1.0;
  vec3 origin = pos;
  lastPos = pos; // updated at each early-return; final pos = ray endpoint

  depthDistance = depthFar;

  float STEP_SIZE = 0.1;
  dir *= STEP_SIZE;

  // Initial values for geodesic integration
  vec3 h = cross(pos, dir);
  float h2 = dot(h, h);

  // Track closest approach to photon sphere
  float minRadiusReached = length(pos);
  vec3 closestApproachPos = pos;
  float r_ph = photonSphereRadius; // 1.5 * r_s

  for (int i = 0; i < 300; i++) {
    lastPos = pos;
    float r = length(pos);
    if (r < minRadiusReached) {
      minRadiusReached = r;
      closestApproachPos = pos;
    }

    if (renderBlackHole > 0.5) {
      // Apply gravitational lensing (geodesic bending)
      if (gravitationalLensing > 0.5) {
        // Inlined accel: a = -1.5 * r_s * h² * pos / r⁵
        float r2 = dot(pos, pos);
        float r5 = r2 * r2 * r;
        vec3 acc = -1.5 * schwarzschildRadius * h2 * pos / r5;
        dir += acc;
      }

      // Event horizon detection: r < r_s (Schwarzschild radius IS the event horizon)
      // Note: r_s = 2GM/c² is the coordinate radius where g_tt = 0
      // The factor of 2 was already included in the definition of schwarzschildRadius
      if (r < schwarzschildRadius) {
        // Ray captured by black hole - return accumulated color (mostly black)
        depthDistance = min(depthDistance, length(pos - origin));

        // Phase 10.1: Apply Hawking thermal glow near event horizon
        if (hawkingGlowEnabled > 0.5) {
          color = applyHawkingGlow(
            color,
            blackHoleMass,
            r,
            schwarzschildRadius,
            hawkingGlowEnabled,
            hawkingTempScale,
            hawkingGlowIntensity,
            hawkingTempLUT,
            hawkingSpectrumLUT,
            useHawkingLUTs
          );
        }

        return color;
      }

      // Photon sphere glow effect (rays grazing r_ph = 1.5 * r_s)
      if (enablePhotonSphere > 0.5) {
        float photonSphereDistance = abs(r - r_ph);
        if (photonSphereDistance < 0.5) {
          // Phase 8.2 optimization: LUT for exp(-distance*4.0) avoids transcendental
          float u = photonSphereDistance / 0.5;  // Normalize to [0,1]
          float glowIntensity =
              texture(photonGlowLUT, vec2(u, 0.5)).r * 0.22 * photonSphereGlowStrength;
          glowIntensity = pow(glowIntensity, 1.08);
          vec3 spinAxis = vec3(0.0, kerrSpin >= 0.0 ? 1.0 : -1.0, 0.0);
          vec3 flowDir = normalize(cross(spinAxis, normalize(pos)));
          float anisotropicRing =
              mix(1.0,
                  mix(0.72, 1.65, 0.5 + 0.5 * dot(flowDir, normalize(origin - pos))),
                  smoothstep(0.05, 0.85, abs(kerrSpin)));
          glowIntensity *= anisotropicRing;
          // A brighter warm-white core with amber shoulders reads more like a
          // concentrated photon ring than a generic orange haze.
          const vec3 GLOW_COLOR = vec3(1.06, 0.86, 0.58);
          const vec3 RIM_COLOR = vec3(1.22, 1.0, 0.78);
          float rimMix = smoothstep(0.09, 0.0, photonSphereDistance);
          color += mix(GLOW_COLOR, RIM_COLOR, rimMix) * glowIntensity * alpha;
          // Phase 8.2 Priority 3: Cache distance computation
          depthDistance = min(depthDistance, length(pos - origin));
        }
      }

      if (adiskEnabled > 0.5) {
        if (adiskColor(pos, dir, color, alpha)) {
          // Phase 8.2 Priority 3: Cache distance computation
          depthDistance = min(depthDistance, length(pos - origin));
        }
      }
    }

    pos += dir;
  }

  // Sample background with parallax layers or fallback to cubemap
  dir = rotateVector(dir, vec3(0.0, 1.0, 0.0), time);
  vec3 skyColor = vec3(0.0);

  if (backgroundEnabled > 0.5) {
    // Convert 3D direction to equirectangular UV coordinates
    vec3 d = normalize(dir);
    if (abs(backgroundYawRad) > EPSILON) {
      d = rotateVector(d, vec3(0.0, 1.0, 0.0), backgroundYawRad);
    }
    if (abs(backgroundPitchRad) > EPSILON) {
      d = rotateVector(d, normalize(cameraBasis[0]), backgroundPitchRad);
    }
    float u = atan(d.z, d.x) / (2.0 * 3.14159265359) + 0.5;
    float v = asin(clamp(d.y, -1.0, 1.0)) / 3.14159265359 + 0.5;
    vec2 baseUV = vec2(u, v);

    // Sample and blend all parallax layers
    for (int i = 0; i < 3; i++) {
      vec4 params = backgroundLayerParams[i];
      vec2 offset = params.xy;
      float scale = params.z;
      float intensity = params.w;
      float lodBias = backgroundLayerLodBias[i];

      // Apply parallax offset and scale
      vec2 uv = (baseUV - 0.5) * scale + 0.5 + offset;

      // Sample layer with LOD bias
      vec3 layerColor = textureLod(backgroundLayers[i], uv, lodBias).rgb;

      // Accumulate with intensity weighting
      skyColor += layerColor * intensity;
    }

    // Normalize by total intensity and apply global intensity
    float totalIntensity = backgroundLayerParams[0].w + backgroundLayerParams[1].w + backgroundLayerParams[2].w;
    skyColor = (skyColor / max(totalIntensity, 0.01)) * backgroundIntensity;
  } else {
    // Fallback to cubemap galaxy texture
    skyColor = texture(galaxy, dir).rgb;
  }

  // Apply gravitational redshift to background light
  if (enableRedshift > 0.5 && minRadiusReached < schwarzschildRadius * 10.0) {
    float z = gravitationalRedshift(minRadiusReached, schwarzschildRadius);
    if (useLUTs > 0.5) {
      float rNorm = minRadiusReached / max(schwarzschildRadius, EPSILON);
      float denom = max(redshiftRadiusMax - redshiftRadiusMin, 0.0001);
      float u = clamp((rNorm - redshiftRadiusMin) / denom, 0.0, 1.0);
      z = texture(redshiftLUT, vec2(u, 0.5)).r;
    }
    skyColor = applySimpleRedshift(skyColor, z);
  }

  if (minRadiusReached < schwarzschildRadius * 5.0) {
    vec3 approachDir = normalize(origin - closestApproachPos);
    vec3 spinAxis = vec3(0.0, kerrSpin >= 0.0 ? 1.0 : -1.0, 0.0);
    vec3 flowDir = normalize(cross(spinAxis, normalize(closestApproachPos)));
    float alignedFlow = 0.5 + 0.5 * dot(flowDir, approachDir);
    float nearHoleWeight =
        pow(clamp(1.0 - (minRadiusReached - schwarzschildRadius) /
                              max(schwarzschildRadius * 3.0, EPSILON),
                  0.0, 1.0),
            1.55);

    // The compute/desktop path wins because it concentrates contrast into a
    // narrow bright sector and lets the rest of the lensed field stay dark.
    // Reproduce that here with local, anisotropic escaped-background shaping
    // rather than more global bloom or ring lift.
    float brightSector = smoothstep(0.74, 0.972, alignedFlow);
    float counterSector = smoothstep(0.24, 0.54, alignedFlow);
    float localShadow = mix(1.0, 0.18, nearHoleWeight * (1.0 - brightSector * 0.94));
    float localLift = 1.0 + nearHoleWeight * (0.78 * brightSector + 0.04 * counterSector);
    skyColor *= localShadow * localLift;

    float skyLuma = luminance(skyColor);
    float sectorContrast = nearHoleWeight * mix(-0.36, 0.28, brightSector);
    skyColor += skyColor * sectorContrast * clamp(skyLuma - 0.03, 0.0, 1.0);

    vec3 arcTint = mix(vec3(0.84, 0.80, 0.96), vec3(1.06, 0.98, 0.88), brightSector);
    skyColor = mix(skyColor, skyColor * arcTint, nearHoleWeight * (0.06 + 0.12 * brightSector));

    float exclusion = nearHoleWeight * (1.0 - brightSector) * smoothstep(0.04, 0.26, skyLuma);
    skyColor *= 1.0 - 0.14 * exclusion;
  }

  color += skyColor * alpha;
  return color;
}

// Compute approximate Boyer-Lindquist (r, theta, phi) from Cartesian hit position.
// WHY: The geodesic integrator tracks Cartesian-space pos; BL coords are recovered by
//      the spherical-coordinates transform, valid as an approximation for the overlay.
void applyWiregridOverlay(inout vec3 color, vec3 hitPos) {
  if (wiregridEnabled < 0.5) return;
  float r = length(hitPos);
  if (r < 1e-5) return;
  float theta = acos(clamp(hitPos.z / r, -1.0, 1.0));
  float phi   = atan(hitPos.y, hitPos.x);
  bool  showErgo = wiregridShowErgo > 0.5;
  vec4  wg = wiregridOverlay(r, theta, phi, kerrSpin, showErgo, wiregridGridScale,
                             wiregridMotionScale, wiregridInfallScale,
                             wiregridColor, time);
  float scenePreserve = clamp(wiregridScenePreserve, 0.0, 1.0);
  float alpha = wg.a * mix(1.0, wg_overlayAttenuation(color), scenePreserve) *
                max(wiregridStrength, 0.0);
  alpha = clamp(alpha, 0.0, 1.0);
  color = mix(color, wg.rgb, alpha);
}

void main() {
  vec3 dir = bhRayDir(gl_FragCoord.xy, resolution, fovScale, cameraBasis);
  vec3 pos = cameraPos;

  if (interopParityMode > 0.5) {
    Ray ray;
    ray.position = pos;
    ray.velocity = dir;
    ray.affineParameter = 0.0;

    int steps = int(max(1.0, interopMaxSteps + 0.5));

    if (stokesEnabled > 0.5) {
      // D4: Polarized Stokes IQUV transport (supersedes scalar RTE)
      vec3 terminalPos;
      vec4 stokesColor = bhTraceGeodesicStokes(ray, schwarzschildRadius, depthFar, steps,
                                               interopStepSize, rteOpacityScale,
                                               stokesBFieldAngle, stokesNeScale,
                                               terminalPos);
      vec3 interopColor = stokesColor.rgb;
      applyWiregridOverlay(interopColor, terminalPos);
      fragColor = vec4(interopColor, 1.0);
      return;
    }

    if (rteEnabled > 0.5) {
      // D2: Volumetric RTE path -- accumulates emission/absorption through disk
      vec3 terminalPos;
      vec4 rteColor = bhTraceGeodesicRTE(ray, schwarzschildRadius, depthFar, steps,
                                         interopStepSize, rteOpacityScale,
                                         terminalPos);
      vec3 interopColor = rteColor.rgb;
      applyWiregridOverlay(interopColor, terminalPos);
      fragColor = vec4(interopColor, 1.0);
      return;
    }

    HitResult hit =
        bhTraceGeodesic(ray, schwarzschildRadius, depthFar, steps, interopStepSize);
    vec4 shaded = bhShadeHit(hit, cameraPos, schwarzschildRadius);
    float depthNormalized =
        clamp(length(hit.hitPoint - cameraPos) / max(depthFar, 0.0001), 0.0, 1.0);
    vec3 interopColor = shaded.rgb;
    applyWiregridOverlay(interopColor, hit.hitPoint);
    fragColor = vec4(interopColor, depthNormalized);
    return;
  }

  float depthDistance = depthFar;
  vec3 lastPos;
  vec3 color = traceColor(pos, dir, depthDistance, lastPos);
  applyWiregridOverlay(color, lastPos);
  float depthNormalized = clamp(depthDistance / depthFar, 0.0, 1.0);
  fragColor = vec4(color, depthNormalized);
}
