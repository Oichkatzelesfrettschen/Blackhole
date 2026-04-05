#ifndef KERR_GLSL
#define KERR_GLSL

// Use include/ prefix for shader loader compatibility
#include "include/physics_constants.glsl"

// ============================================================================
// Kerr Metric Utilities
// ============================================================================

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

// Exact Carter constants from the Kerr metric at the initial position.
//
// Projects the Cartesian direction `dir` onto Boyer-Lindquist coordinates,
// solves the null condition g_mu_nu k^mu k^nu = 0 for k^t, then reads off
// E = -k_t and Lz = k_phi from the covariant components.  Q is derived from
// the code convention Theta = Q + a^2 cos^2 - Lz^2/sin^2 = (Sigma k^theta)^2.
// Result is normalized to E = 1 to preserve the existing step-size calibration.
//
// WHY this beats the old flat-space approx (c.E=1, Q=|L|^2-Lz^2):
//   For a tangential ray at radius r, the old code gives R > 0 (non-zero radial
//   velocity) even though the ray has no radial component.  The exact formula
//   gives R <= 0, correctly anchoring the ray at its turning point and matching
//   the geodesic impact parameters b = Lz/E and q = Q/E^2 to the local metric.
KerrConsts kerrInitConsts(vec3 pos, vec3 dir, float r_s, float a) {
  KerrConsts c;

  float r = length(pos);
  if (r < KERR_EPSILON) {
    c.E = 1.0; c.Lz = 0.0; c.Q = 0.0;
    return c;
  }

  float invR  = 1.0 / r;
  float cosT  = clamp(pos.z * invR, -1.0, 1.0);
  float sinT  = sqrt(max(1.0 - cosT * cosT, 0.0));
  float sin2  = sinT * sinT;
  float phi   = atan(pos.y, pos.x);
  float cosP  = cos(phi);
  float sinP  = sin(phi);

  // Spherical basis at pos (same orientation as kerrInitRay).
  vec3 e_r     = vec3(sinT * cosP,  sinT * sinP,  cosT);
  vec3 e_theta = vec3(cosT * cosP,  cosT * sinP, -sinT);
  vec3 e_phi   = vec3(-sinP,         cosP,         0.0);

  // BL contravariant spatial components of the null direction.
  float kr     = dot(dir, e_r);
  float ktheta = dot(dir, e_theta) * invR;
  float kphi   = (sinT > KERR_EPSILON) ? dot(dir, e_phi) / (r * sinT) : 0.0;

  // Kerr metric at (r, theta); r_s = 2M convention.
  float sigma  = r * r + a * a * cosT * cosT;
  float delta  = r * r - r_s * r + a * a;
  float f      = (sigma > KERR_EPSILON) ? (r_s * r / sigma) : 0.0;
  float gtt    = -(1.0 - f);
  float gtphi  = -f * a * sin2;
  float grr    = sigma / max(abs(delta), KERR_EPSILON);
  float gthth  = sigma;
  float gphph  = (r * r + a * a + f * a * a * sin2) * sin2;

  // Solve null condition gtt*(k^t)^2 + 2*gtphi*kphi*(k^t) + spatial = 0
  // for the future-directed root (k^t > 0).
  float spatial = grr * kr * kr + gthth * ktheta * ktheta + gphph * kphi * kphi;
  float hb      = gtphi * kphi;
  float disc    = hb * hb - gtt * spatial;
  float kt;
  if (disc >= 0.0 && abs(gtt) > KERR_EPSILON) {
    float sqD  = sqrt(disc);
    float kt_a = (-hb + sqD) / gtt;
    float kt_b = (-hb - sqD) / gtt;
    kt = (kt_a > 0.0) ? kt_a : kt_b;
    if (kt <= 0.0) kt = max(kt_a, kt_b);  // ergosphere: pick less-negative root
  } else {
    kt = 1.0;  // degenerate or inside ergosphere: flat-space fallback
  }

  // Conserved quantities: E = -(g_tt k^t + g_tphi k^phi),
  //                       Lz = g_tphi k^t + g_phph k^phi.
  float E_raw  = -(gtt * kt + gtphi * kphi);
  float Lz_raw = gtphi * kt + gphph * kphi;

  // Normalize to E = 1 to preserve existing step-size calibration.
  float invE = (E_raw > KERR_EPSILON) ? (1.0 / E_raw) : 1.0;
  c.E  = 1.0;
  c.Lz = Lz_raw * invE;

  // Carter Q (code convention: Theta = Q + a^2 cos^2 - Lz^2/sin^2 = (Sigma k^theta)^2).
  // Q can be negative for radial photons near the poles (e.g. Q = -a^2 at theta=0).
  float ptheta = sigma * ktheta * invE;  // p_theta = Sigma * k^theta (E-normalized)
  if (sinT > KERR_EPSILON) {
    c.Q = ptheta * ptheta - a * a * cosT * cosT + c.Lz * c.Lz / sin2;
  } else {
    // Pole: kphi = 0, so Lz = 0.  Q = ptheta^2 - a^2 (exact at theta = 0 or pi).
    c.Q = ptheta * ptheta - a * a;
  }

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

  /* Issue-009: FMA contraction can reorder the subtract in R and Theta,
   * changing the sign at turning points differently between compute and
   * fragment shaders.  'precise' forces IEEE-754 sequential evaluation
   * of each expression, making sign detection deterministic across paths. */
  precise float R = A * A - Delta * (c.Q + Lz_minus_aE * Lz_minus_aE);
  precise float Theta = c.Q + (a * a * c.E * c.E * cosTheta * cosTheta) -
                        (c.Lz * c.Lz / sin2);

  if (R < 0.0) {
    ray.sign_r *= -1.0;
  }
  if (Theta < 0.0) {
    ray.sign_theta *= -1.0;
  }

  float sqrtR = sqrt(max(R, 0.0));
  float sqrtTheta = sqrt(max(Theta, 0.0));

  float dr_dlam     = ray.sign_r     * sqrtR;
  float dtheta_dlam = ray.sign_theta * sqrtTheta;

  /* Rationalized outgoing KS formulas -- no deltaSafe in denominator.
   *
   * BL singularity: dphi/dt both diverge as Delta -> 0 at the outer horizon.
   *
   * KS cancellation identity (ingoing ray, sign_r = -1):
   *   A + dr_dlam = A - sqrtR = (A^2 - R) / (A + sqrtR)
   *                           = Delta * Q_eff / (A + sqrtR)
   * so (A - sqrtR)/Delta = Q_eff/(A+sqrtR)  -- Delta cancels exactly.
   * Similarly, using r^2+a^2-rs*r = Delta:
   *   [(r^2+a^2)*A - rs*r*sqrtR] / Delta = A + rs*r*Q_eff/(A+sqrtR)
   * Both are finite as Delta -> 0 without any clamping.
   *
   * Outgoing ray (sign_r = +1): at any turning point sqrtR = 0 and
   * R = 0 => A^2 = Delta*Q_eff, so Q_eff/A = A/Delta (same as BL).
   * Away from the turning point Delta is bounded away from 0, making
   * the standard KS form a*(A+sqrtR)/Delta numerically safe.
   *
   * Continuity: both branches give identical values when sqrtR = 0,
   * because Q_eff/(A+sqrtR) = Q_eff/A = A/Delta when R = 0.
   *
   * Reference: src/cuda/device_physics.cuh d_kerr_step() (CUDA parity). */
  float Q_eff = c.Q + Lz_minus_aE * Lz_minus_aE;
  float dphi_dlam, dt_dlam;
  if (ray.sign_r < 0.0) {
    /* Ingoing: rationalized form, Delta-free. */
    float inv_Aps = 1.0 / max(A + sqrtR, 1e-30);
    dphi_dlam = (c.Lz / sin2) - a * c.E + a * Q_eff * inv_Aps;
    dt_dlam   = A + r_s * r * Q_eff * inv_Aps + a * (c.Lz - a * c.E * sin2);
  } else {
    /* Outgoing (post-turning-point): Delta bounded away from 0. */
    float invD = 1.0 / max(Delta, 1e-6);
    dphi_dlam  = (c.Lz / sin2) - a * c.E + a * (A + sqrtR) * invD;
    dt_dlam    = ((r * r + a * a) * A + r_s * r * sqrtR) * invD
                 + a * (c.Lz - a * c.E * sin2);
  }

  ray.r += dlam * dr_dlam;
  ray.theta += dlam * dtheta_dlam;
  ray.phi += dlam * dphi_dlam;
  ray.t += dlam * dt_dlam;

  ray.theta = clamp(ray.theta, 1e-6, PI - 1e-6);
}

#endif // KERR_GLSL
