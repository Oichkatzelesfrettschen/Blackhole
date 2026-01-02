#ifndef INTEROP_TRACE_GLSL
#define INTEROP_TRACE_GLSL

#include "include/physics_constants.glsl"

const float BH_EPSILON = 1e-6;
const float BH_DEBUG_MAX_RADIUS_MULT = 4.0;
const int BH_DEBUG_FLAG_NAN = 1;
const int BH_DEBUG_FLAG_RANGE = 2;

uniform float bhDebugFlags = 0.0;

struct Ray {
  vec3 position;
  vec3 velocity;
  float affineParameter;
};

struct HitResult {
  bool hitDisk;
  bool hitHorizon;
  bool escaped;
  vec3 hitPoint;
  float phi;
  float redshiftFactor;
  float minRadius;
  int debugFlags;
};

const int BH_BACKGROUND_LAYERS = 3;

int bhDebugMask() { return int(bhDebugFlags + 0.5); }

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

bool bhCheckDiskIntersection(vec3 oldPos, vec3 newPos, float r_in, float r_out,
                             out vec3 hitPoint) {
  if (oldPos.z * newPos.z > 0.0) {
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

HitResult bhTraceGeodesic(Ray ray, float r_s, float maxDistance, int maxSteps,
                          float stepSize) {
  HitResult result;
  result.hitDisk = false;
  result.hitHorizon = false;
  result.escaped = false;
  result.hitPoint = vec3(0.0);
  result.phi = 0.0;
  result.redshiftFactor = 1.0;
  result.minRadius = length(ray.position);
  result.debugFlags = 0;

  float a = 0.5 * kerrSpin * r_s;
  if (abs(a) > BH_EPSILON) {
    float r_horizon = kerrOuterHorizon(r_s, a);
    if (r_horizon <= BH_EPSILON) {
      r_horizon = r_s;
    }

    float r_disk_in = iscoRadius;
    float r_disk_out = 100.0 * r_s;

    KerrConsts c = kerrInitConsts(ray.position, ray.velocity);
    KerrRay kerrRay = kerrInitRay(ray.position, ray.velocity);

    vec3 oldPos;
    float dt = stepSize;

    for (int step = 0; step < maxSteps; ++step) {
      oldPos = kerrToCartesian(kerrRay.r, kerrRay.theta, kerrRay.phi);
      result.minRadius = min(result.minRadius, kerrRay.r);

      if (kerrRay.r <= r_horizon) {
        result.hitHorizon = true;
        result.hitPoint = oldPos;
        return result;
      }

      kerrStep(kerrRay, r_s, a, c, dt);
      vec3 newPos = kerrToCartesian(kerrRay.r, kerrRay.theta, kerrRay.phi);
      result.debugFlags |= bhDebugEvaluate(newPos, newPos - oldPos, maxDistance);
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

      if (kerrRay.r > maxDistance) {
        result.escaped = true;
        result.hitPoint = newPos;
        return result;
      }
    }

    result.escaped = true;
    result.hitPoint = kerrToCartesian(kerrRay.r, kerrRay.theta, kerrRay.phi);
    return result;
  }

  float r_disk_in = iscoRadius;
  float r_disk_out = 100.0 * r_s;

  vec3 oldPos;
  float dt = stepSize;

  for (int step = 0; step < maxSteps; ++step) {
    oldPos = ray.position;
    bhStepRK4(ray, r_s, dt);
    result.debugFlags |= bhDebugEvaluate(ray.position, ray.velocity, maxDistance);

    float r = length(ray.position);
    result.minRadius = min(result.minRadius, r);
    if (r <= r_s) {
      result.hitHorizon = true;
      result.hitPoint = ray.position;
      return result;
    }

    if (adiskEnabled > 0.5) {
      vec3 diskHit;
      if (bhCheckDiskIntersection(oldPos, ray.position, r_disk_in, r_disk_out, diskHit)) {
        result.hitDisk = true;
        result.hitPoint = diskHit;
        result.phi = atan(diskHit.y, diskHit.x);
        result.redshiftFactor = bhComputeRedshiftFactor(length(diskHit), r_s);
        return result;
      }
    }

    if (r > maxDistance) {
      result.escaped = true;
      result.hitPoint = ray.position;
      return result;
    }
  }

  result.escaped = true;
  result.hitPoint = ray.position;
  return result;
}

vec4 bhHorizonColor() {
  return vec4(0.0, 0.0, 0.0, 1.0);
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
    float r_in = iscoRadius;
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

vec4 bhBackgroundColorFromDir(vec3 dir, float minRadius, float r_s) {
  vec3 n = normalize(dir);
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
  if (bhDebugMask() != 0 && hit.debugFlags != 0) {
    vec3 debugColor = vec3(0.0);
    if ((hit.debugFlags & BH_DEBUG_FLAG_NAN) != 0) {
      debugColor += vec3(1.0, 0.0, 1.0);
    }
    if ((hit.debugFlags & BH_DEBUG_FLAG_RANGE) != 0) {
      debugColor += vec3(1.0, 1.0, 0.0);
    }
    return vec4(clamp(debugColor, 0.0, 1.0), 1.0);
  }
  if (hit.hitHorizon) {
    return bhHorizonColor();
  }
  if (hit.hitDisk) {
    return bhDiskColorFromHit(hit, r_s);
  }
  return bhBackgroundColorFromDir(normalize(hit.hitPoint - cameraPos),
                                  hit.minRadius, r_s);
}

#endif // INTEROP_TRACE_GLSL
