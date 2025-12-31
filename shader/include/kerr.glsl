#ifndef KERR_GLSL
#define KERR_GLSL

struct KerrConsts {
  float E;
  float Lz;
  float Q;
};

struct KerrRay {
  float r;
  float theta;
  float phi;
  float t;
  float sign_r;
  float sign_theta;
};

const float KERR_EPSILON = 1e-6;

float kerrSigma(float r, float a, float cosTheta) {
  return r * r + a * a * cosTheta * cosTheta;
}

float kerrDelta(float r, float a, float r_s) {
  return r * r - r_s * r + a * a;
}

float kerrOuterHorizon(float r_s, float a) {
  float M = 0.5 * r_s;
  float disc = M * M - a * a;
  if (disc < 0.0) {
    return r_s;
  }
  return M + sqrt(disc);
}

vec3 kerrToCartesian(float r, float theta, float phi) {
  float sinTheta = sin(theta);
  return vec3(r * sinTheta * cos(phi),
              r * sinTheta * sin(phi),
              r * cos(theta));
}

// Approximate Carter constants from flat-space angular momentum.
KerrConsts kerrInitConsts(vec3 pos, vec3 dir) {
  KerrConsts c;
  c.E = 1.0;
  vec3 L = cross(pos, dir);
  c.Lz = L.z;
  float L2 = dot(L, L);
  c.Q = max(0.0, L2 - c.Lz * c.Lz);
  return c;
}

KerrRay kerrInitRay(vec3 pos, vec3 dir) {
  KerrRay ray;
  ray.r = length(pos);
  float invR = ray.r > KERR_EPSILON ? 1.0 / ray.r : 0.0;
  float cosTheta = clamp(pos.z * invR, -1.0, 1.0);
  ray.theta = acos(cosTheta);
  ray.phi = atan(pos.y, pos.x);
  ray.t = 0.0;

  vec3 e_r = normalize(pos);
  vec3 e_theta = normalize(vec3(cos(ray.theta) * cos(ray.phi),
                                cos(ray.theta) * sin(ray.phi),
                                -sin(ray.theta)));
  float dr = dot(dir, e_r);
  float dtheta = dot(dir, e_theta);
  ray.sign_r = dr >= 0.0 ? 1.0 : -1.0;
  ray.sign_theta = dtheta >= 0.0 ? 1.0 : -1.0;
  return ray;
}

void kerrStep(inout KerrRay ray, float r_s, float a, KerrConsts c, float dlam) {
  float r = ray.r;
  float theta = ray.theta;
  float sinTheta = sin(theta);
  float cosTheta = cos(theta);
  float sin2 = max(sinTheta * sinTheta, 1e-6);

  float Delta = kerrDelta(r, a, r_s);
  float A = (r * r + a * a) * c.E - a * c.Lz;
  float Lz_minus_aE = c.Lz - a * c.E;

  float R = A * A - Delta * (c.Q + Lz_minus_aE * Lz_minus_aE);
  float Theta = c.Q + (a * a * c.E * c.E * cosTheta * cosTheta) -
                (c.Lz * c.Lz / sin2);

  if (R < 0.0) {
    ray.sign_r *= -1.0;
  }
  if (Theta < 0.0) {
    ray.sign_theta *= -1.0;
  }

  float sqrtR = sqrt(max(R, 0.0));
  float sqrtTheta = sqrt(max(Theta, 0.0));
  float deltaSafe = max(Delta, 1e-6);

  float dr_dlam = ray.sign_r * sqrtR;
  float dtheta_dlam = ray.sign_theta * sqrtTheta;
  float dphi_dlam = (c.Lz / sin2) - a * c.E + (a * A / deltaSafe);
  float dt_dlam = ((r * r + a * a) * A / deltaSafe) +
                  a * (c.Lz - a * c.E * sin2);

  ray.r += dlam * dr_dlam;
  ray.theta += dlam * dtheta_dlam;
  ray.phi += dlam * dphi_dlam;
  ray.t += dlam * dt_dlam;

  ray.theta = clamp(ray.theta, 1e-6, PI - 1e-6);
}

#endif // KERR_GLSL
