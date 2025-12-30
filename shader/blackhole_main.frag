#version 460 core
#extension GL_GOOGLE_include_directive : enable

// Physics library includes
#include "include/physics_constants.glsl"
#include "include/schwarzschild.glsl"
#include "include/geodesics.glsl"
#include "include/redshift.glsl"

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
uniform sampler3D noiseTexture;
uniform sampler3D grmhdTexture;
uniform samplerCube galaxy;
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
uniform vec3 grmhdBoundsMin = vec3(-10.0);
uniform vec3 grmhdBoundsMax = vec3(10.0);

uniform vec3 cameraPos;
uniform mat3 cameraBasis;
uniform float depthFar = 50.0;

uniform float gravatationalLensing = 1.0;
uniform float renderBlackHole = 1.0;
uniform float fovScale = 1.0;

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

///----
/// Simplex 3D Noise
/// by Ian McEwan, Ashima Arts
vec4 permute(vec4 x) { return mod(((x * 34.0) + 1.0) * x, 289.0); }
vec4 taylorInvSqrt(vec4 r) { return 1.79284291400159 - 0.85373472095314 * r; }

float snoise(vec3 v) {
  const vec2 C = vec2(1.0 / 6.0, 1.0 / 3.0);
  const vec4 D = vec4(0.0, 0.5, 1.0, 2.0);

  // First corner
  vec3 i = floor(v + dot(v, C.yyy));
  vec3 x0 = v - i + dot(i, C.xxx);

  // Other corners
  vec3 g = step(x0.yzx, x0.xyz);
  vec3 l = 1.0 - g;
  vec3 i1 = min(g.xyz, l.zxy);
  vec3 i2 = max(g.xyz, l.zxy);

  //  x0 = x0 - 0. + 0.0 * C
  vec3 x1 = x0 - i1 + 1.0 * C.xxx;
  vec3 x2 = x0 - i2 + 2.0 * C.xxx;
  vec3 x3 = x0 - 1. + 3.0 * C.xxx;

  // Permutations
  i = mod(i, 289.0);
  vec4 p = permute(permute(permute(i.z + vec4(0.0, i1.z, i2.z, 1.0)) + i.y +
                           vec4(0.0, i1.y, i2.y, 1.0)) +
                   i.x + vec4(0.0, i1.x, i2.x, 1.0));

  // Gradients
  // ( N*N points uniformly over a square, mapped onto an octahedron.)
  float n_ = 1.0 / 7.0; // N=7
  vec3 ns = n_ * D.wyz - D.xzx;

  vec4 j = p - 49.0 * floor(p * ns.z * ns.z); //  mod(p,N*N)

  vec4 x_ = floor(j * ns.z);
  vec4 y_ = floor(j - 7.0 * x_); // mod(j,N)

  vec4 x = x_ * ns.x + ns.yyyy;
  vec4 y = y_ * ns.x + ns.yyyy;
  vec4 h = 1.0 - abs(x) - abs(y);

  vec4 b0 = vec4(x.xy, y.xy);
  vec4 b1 = vec4(x.zw, y.zw);

  vec4 s0 = floor(b0) * 2.0 + 1.0;
  vec4 s1 = floor(b1) * 2.0 + 1.0;
  vec4 sh = -step(h, vec4(0.0));

  vec4 a0 = b0.xzyw + s0.xzyw * sh.xxyy;
  vec4 a1 = b1.xzyw + s1.xzyw * sh.zzww;

  vec3 p0 = vec3(a0.xy, h.x);
  vec3 p1 = vec3(a0.zw, h.y);
  vec3 p2 = vec3(a1.xy, h.z);
  vec3 p3 = vec3(a1.zw, h.w);

  // Normalise gradients
  vec4 norm =
      taylorInvSqrt(vec4(dot(p0, p0), dot(p1, p1), dot(p2, p2), dot(p3, p3)));
  p0 *= norm.x;
  p1 *= norm.y;
  p2 *= norm.z;
  p3 *= norm.w;

  // Mix final noise value
  vec4 m =
      max(0.6 - vec4(dot(x0, x0), dot(x1, x1), dot(x2, x2), dot(x3, x3)), 0.0);
  m = m * m;
  return 42.0 *
         dot(m * m, vec4(dot(p0, x0), dot(p1, x1), dot(p2, x2), dot(p3, x3)));
}
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
    float noiseSample = 0.5 * snoise(sphericalCoord * pow(i, 2) * adiskNoiseScale) + 0.5;
    if (useNoiseTex) {
      vec3 noiseCoord = fract(sphericalCoord * noiseTextureScale);
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
      if (gravatationalLensing > 0.5) {
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
  vec2 uv = gl_FragCoord.xy / resolution.xy - vec2(0.5);
  uv.x *= resolution.x / resolution.y;

  vec3 dir = normalize(vec3(-uv.x * fovScale, uv.y * fovScale, 1.0));
  vec3 pos = cameraPos;
  dir = cameraBasis * dir;

  float depthDistance = depthFar;
  vec3 color = traceColor(pos, dir, depthDistance);
  float depthNormalized = clamp(depthDistance / depthFar, 0.0, 1.0);
  fragColor = vec4(color, depthNormalized);
}
