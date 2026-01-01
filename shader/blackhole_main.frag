#version 460 core
#extension GL_GOOGLE_include_directive : enable

// Physics library includes
#include "include/physics_constants.glsl"
#include "include/schwarzschild.glsl"
#include "include/geodesics.glsl"
#include "include/redshift.glsl"
#include "include/kerr.glsl"
#include "include/interop_raygen.glsl"

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
uniform sampler3D noiseTexture;
uniform sampler3D grmhdTexture;
uniform samplerCube galaxy;
uniform sampler2D backgroundLayers[3];
uniform vec4 backgroundLayerParams[3];
uniform float backgroundLayerLodBias[3];
uniform float backgroundEnabled = 0.0;
uniform float backgroundIntensity = 1.0;
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
uniform float interopMaxSteps = 300.0;
uniform float interopStepSize = 0.1;

uniform float adiskEnabled = 1.0;
uniform float adiskParticle = 1.0;
uniform float adiskHeight = 0.2;
uniform float adiskLit = 0.5;
uniform float adiskDensityV = 1.0;
uniform float adiskDensityH = 1.0;
uniform float adiskNoiseScale = 1.0;
uniform float adiskNoiseLOD = 5.0;
uniform float adiskSpeed = 0.5;

// Physics parameters
uniform float schwarzschildRadius = 2.0; // r_s = 2GM/c² (default = 2 in geometric units)
uniform float photonSphereRadius = 3.0;  // r_ph = 1.5 * r_s
uniform float iscoRadius = 6.0;          // r_ISCO = 3 * r_s (Schwarzschild)
uniform float enableRedshift = 0.0;      // Toggle gravitational redshift
uniform float enablePhotonSphere = 0.0;  // Toggle photon sphere glow

#include "include/interop_trace.glsl"

///----
/// Noise is sampled from a 3D texture (offline/precomputed).
///----

vec3 panoramaColor(sampler2D tex, vec3 dir) {
  vec2 uv = vec2(0.5 - atan(dir.z, dir.x) / PI * 0.5, 0.5 - asin(dir.y) / PI);
  return texture(tex, uv).rgb;
}

/**
 * Compute geodesic acceleration for null rays (photons).
 *
 * Derived from the Schwarzschild effective potential for photons:
 * V_eff(r) = h²/r² * (1 - r_s/r)
 *
 * The radial acceleration in coordinate time is:
 * d²r/dt² = -∂V_eff/∂r = -h²(r_s - 2r)/r⁴
 *
 * For the full 3D vector equation in Cartesian coordinates:
 * a = -1.5 * r_s * h² * r̂ / r⁴
 *
 * This is equivalent to: a = -(3/2) * r_s * h² * pos / r⁵
 */
vec3 accel(float h2, vec3 pos) {
  float r2 = dot(pos, pos);
  // More numerically stable than pow(r2, 2.5)
  float r = sqrt(r2);
  float r5 = r2 * r2 * r;
  // Geodesic equation: a = -1.5 * r_s * h² / r⁵ * r̂
  vec3 acc = -1.5 * schwarzschildRadius * h2 * pos / r5;
  return acc;
}

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

bool adiskColor(vec3 pos, inout vec3 color, inout float alpha) {
  // Inner radius at ISCO (innermost stable circular orbit)
  // For Schwarzschild: r_ISCO = 3 * r_s where r_s = 2GM/c²
  // iscoRadius is already in the same coordinate units as positions
  float innerRadius = iscoRadius;
  float outerRadius = iscoRadius * 4.0; // Outer edge at ~12 r_s for typical thin disk

  // Density linearly decreases as the distance to the blackhole center
  // increases.
  float density = max(
      0.0, 1.0 - length(pos.xyz / vec3(outerRadius, adiskHeight, outerRadius)));
  if (density < 0.001) {
    return false;
  }

  density *= pow(1.0 - abs(pos.y) / adiskHeight, adiskDensityV);

  // Set particle density to 0 when radius is below the innermost stable
  // circular orbit (ISCO). Matter spirals in rapidly below this radius.
  density *= smoothstep(innerRadius, innerRadius * 1.1, length(pos));

  // Avoid the shader computation when density is very small.
  if (density < 0.001) {
    return false;
  }

  vec3 sphericalCoord = toSpherical(pos);

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
    density *= max(grmhdSample.r, 0.0);
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

  float emissivity = 1.0;
  if (useLUTs > 0.5) {
    float rNorm = length(pos) / max(schwarzschildRadius, EPSILON);
    float denom = max(lutRadiusMax - lutRadiusMin, 0.0001);
    float u = clamp((rNorm - lutRadiusMin) / denom, 0.0, 1.0);
    emissivity = max(0.0, texture(emissivityLUT, vec2(u, 0.5)).r);
  }
  density *= emissivity;

  if (useSpectralLUT > 0.5) {
    float rNorm = length(pos) / max(schwarzschildRadius, EPSILON);
    float denom = max(spectralRadiusMax - spectralRadiusMin, 0.0001);
    float u = clamp((rNorm - spectralRadiusMin) / denom, 0.0, 1.0);
    float spectral = texture(spectralLUT, vec2(u, 0.5)).r;
    density *= max(spectral, 0.0);
  }

  if (useGrbModulation > 0.5) {
    float denom = max(grbTimeMax - grbTimeMin, 0.0001);
    float u = clamp((grbTime - grbTimeMin) / denom, 0.0, 1.0);
    float modulation = texture(grbModulationLUT, vec2(u, 0.5)).r;
    density *= max(modulation, 0.0);
  }

  // Apply gravitational redshift to disk emission
  if (enableRedshift > 0.5) {
    float r = length(pos);
    float z = gravitationalRedshift(r, schwarzschildRadius);
    if (useLUTs > 0.5) {
      float rNorm = r / max(schwarzschildRadius, EPSILON);
      float denom = max(redshiftRadiusMax - redshiftRadiusMin, 0.0001);
      float u = clamp((rNorm - redshiftRadiusMin) / denom, 0.0, 1.0);
      z = texture(redshiftLUT, vec2(u, 0.5)).r;
    }
    // Apply full wavelength shift for physically accurate color
    dustColor = applyGravitationalRedshift(dustColor, z);
  }

  color += density * adiskLit * dustColor * alpha * abs(noise);
  return true;
}

vec3 traceColor(vec3 pos, vec3 dir, out float depthDistance) {
  vec3 color = vec3(0.0);
  float alpha = 1.0;
  vec3 origin = pos;

  depthDistance = depthFar;

  float STEP_SIZE = 0.1;
  dir *= STEP_SIZE;

  // Initial values for geodesic integration
  vec3 h = cross(pos, dir);
  float h2 = dot(h, h);

  // Compute impact parameter: b = |r × v| / |v|
  float impactParameter = length(cross(pos, normalize(dir)));

  // Critical impact parameter for photon capture: b_crit ≈ sqrt(27) * r_s/2
  float criticalImpact = sqrt(27.0) * schwarzschildRadius / 2.0;

  // Track closest approach to photon sphere
  float minRadiusReached = length(pos);
  float r_ph = photonSphereRadius; // 1.5 * r_s

  for (int i = 0; i < 300; i++) {
    float r = length(pos);
    minRadiusReached = min(minRadiusReached, r);

    if (renderBlackHole > 0.5) {
      // Apply gravitational lensing (geodesic bending)
      if (gravitationalLensing > 0.5) {
        vec3 acc = accel(h2, pos);
        dir += acc;
      }

      // Event horizon detection: r < r_s (Schwarzschild radius IS the event horizon)
      // Note: r_s = 2GM/c² is the coordinate radius where g_tt = 0
      // The factor of 2 was already included in the definition of schwarzschildRadius
      if (r < schwarzschildRadius) {
        // Ray captured by black hole - return accumulated color (mostly black)
        depthDistance = min(depthDistance, length(pos - origin));
        return color;
      }

      // Photon sphere glow effect (rays grazing r_ph = 1.5 * r_s)
      if (enablePhotonSphere > 0.5) {
        float photonSphereDistance = abs(r - r_ph);
        if (photonSphereDistance < 0.5) {
          // Glow intensity peaks at photon sphere
          float glowIntensity = exp(-photonSphereDistance * 4.0) * 0.3;
          // Orange-yellow glow color for photon ring
          vec3 glowColor = vec3(1.0, 0.7, 0.3) * glowIntensity;
          color += glowColor * alpha;
          depthDistance = min(depthDistance, length(pos - origin));
        }
      }

      if (adiskEnabled > 0.5) {
        if (adiskColor(pos, color, alpha)) {
          depthDistance = min(depthDistance, length(pos - origin));
        }
      }
    }

    pos += dir;
  }

  // Sample skybox color with optional gravitational redshift
  dir = rotateVector(dir, vec3(0.0, 1.0, 0.0), time);
  vec3 skyColor = texture(galaxy, dir).rgb;

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

  color += skyColor * alpha;
  return color;
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
    HitResult hit =
        bhTraceGeodesic(ray, schwarzschildRadius, depthFar, steps, interopStepSize);
    vec4 shaded = bhShadeHit(hit, cameraPos, schwarzschildRadius);
    float depthNormalized =
        clamp(length(hit.hitPoint - cameraPos) / max(depthFar, 0.0001), 0.0, 1.0);
    fragColor = vec4(shaded.rgb, depthNormalized);
    return;
  }

  float depthDistance = depthFar;
  vec3 color = traceColor(pos, dir, depthDistance);
  float depthNormalized = clamp(depthDistance / depthFar, 0.0, 1.0);
  fragColor = vec4(color, depthNormalized);
}
