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

// Mino-time state. The polar motion runs in mu = cos(theta), where Carter's
// polar potential is the polynomial
//   Theta_mu(mu) = (dmu/dlambda)^2 = Q (1 - mu^2) + a^2 E^2 mu^2 (1 - mu^2) - Lz^2 mu^2,
// free of the Lz^2 cot^2 pole singularity of the theta form. vr = dr/dlambda
// and vmu = dmu/dlambda follow d^2r/dlambda^2 = R'(r)/2 and d^2mu/dlambda^2 =
// Theta_mu'(mu)/2; accR and accMu cache those accelerations so each leapfrog
// step evaluates the forces once. theta = acos(mu) is kept for callers.
struct KerrRay {
  float r;
  float theta;
  float phi;
  float t;
  float vr;
  float mu;
  float vmu;
  float accR;
  float accMu;
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

// Spin passed to kerrInitGeodesic and kerrStep. The camera pixel gives the
// direction the arriving photon travelled from; its past history is the
// time reverse of its path. Time reversal t -> -t is an isometry from Kerr
// with spin a to Kerr with spin -a, so the arriving photon's past path is,
// point for point in (r, theta, phi), the future path of a photon emitted
// along the pixel direction in Kerr with spin -a. The physical photon's
// constants are then E = c.E, Lz = -c.Lz, Q = c.Q (James et al. 2015,
// arXiv:1502.03808, App. A traces the same backward ray).
float kerrTraceSpin(float a) {
  return -a;
}

// Radial and polar accelerations R'(r)/2 and Theta_mu'(mu)/2 of the Mino
// system: Theta_mu'/2 = -(Q + Lz^2) mu + a^2 E^2 (mu - 2 mu^3).
void kerrAccelerations(float r, float mu, float r_s, float a, KerrConsts c,
                       out float accR, out float accMu) {
  float P = (r * r + a * a) * c.E - a * c.Lz;
  float Lz_minus_aE = c.Lz - a * c.E;
  float Q_eff = c.Q + Lz_minus_aE * Lz_minus_aE;
  accR = 2.0 * r * c.E * P - (r - 0.5 * r_s) * Q_eff;
  float a2E2 = a * a * c.E * c.E;
  accMu = -(c.Q + c.Lz * c.Lz) * mu + a2E2 * (mu - 2.0 * mu * mu * mu);
}

float kerrPolarPotentialMu(float mu, float a, KerrConsts c) {
  float mu2 = mu * mu;
  return c.Q * (1.0 - mu2) + a * a * c.E * c.E * mu2 * (1.0 - mu2) - c.Lz * c.Lz * mu2;
}

// Null geodesic through pos with Cartesian direction dir in Kerr spin a
// (r_s = 2M). Projects dir onto the Boyer-Lindquist basis, solves the null
// condition for the future root k^t, reads E = -k_t and Lz = k_phi, and
// normalizes to E = 1. Q is Carter's constant p_theta^2 - a^2 cos^2 +
// Lz^2 cot^2 with p_theta = Sigma k^theta / E, so R(r0) = vr^2 and
// Theta_mu(mu0) = vmu^2 at the start (physics::kerrNullGeodesicFromBL is the
// CPU twin, pinned by tests/kerr_null_geodesic_test.cpp; the GPU init is
// pinned by tests/kerr_shader_capture_test.cpp).
void kerrInitGeodesic(vec3 pos, vec3 dir, float r_s, float a,
                      out KerrConsts c, out KerrRay ray) {
  float r = length(pos);
  ray.r = r;
  ray.t = 0.0;
  ray.phi = atan(pos.y, pos.x);
  c.E = 1.0;
  c.Lz = 0.0;
  c.Q = 0.0;
  ray.vr = 0.0;
  ray.mu = 0.0;
  ray.vmu = 0.0;
  if (r < KERR_EPSILON) {
    ray.theta = 0.5 * PI;
    ray.accR = 0.0;
    ray.accMu = 0.0;
    return;
  }

  float invR  = 1.0 / r;
  float cosT  = clamp(pos.z * invR, -1.0, 1.0);
  float sinT  = sqrt(max(1.0 - cosT * cosT, 0.0));
  float sin2  = sinT * sinT;
  float cosP  = cos(ray.phi);
  float sinP  = sin(ray.phi);
  ray.theta   = acos(cosT);

  vec3 e_r     = vec3(sinT * cosP,  sinT * sinP,  cosT);
  vec3 e_theta = vec3(cosT * cosP,  cosT * sinP, -sinT);
  vec3 e_phi   = vec3(-sinP,         cosP,         0.0);

  // BL contravariant spatial components of the null direction.
  float kr     = dot(dir, e_r);
  float ktheta = dot(dir, e_theta) * invR;
  float kphi   = (sinT > KERR_EPSILON) ? dot(dir, e_phi) / (r * sinT) : 0.0;

  float sigma  = r * r + a * a * cosT * cosT;
  float delta  = r * r - r_s * r + a * a;
  float f      = (sigma > KERR_EPSILON) ? (r_s * r / sigma) : 0.0;
  float gtt    = -(1.0 - f);
  float gtphi  = -f * a * sin2;
  float grr    = sigma / max(abs(delta), KERR_EPSILON);
  float gthth  = sigma;
  float gphph  = (r * r + a * a + f * a * a * sin2) * sin2;

  // gtt (k^t)^2 + 2 gtphi kphi k^t + spatial = 0. Outside the ergoregion the
  // roots have opposite signs; the future-directed root is the larger one.
  float spatial = grr * kr * kr + gthth * ktheta * ktheta + gphph * kphi * kphi;
  float hb      = gtphi * kphi;
  float disc    = hb * hb - gtt * spatial;
  float kt = 1.0;
  if (disc >= 0.0 && abs(gtt) > KERR_EPSILON) {
    float sqD = sqrt(disc);
    kt = max((-hb + sqD) / gtt, (-hb - sqD) / gtt);
  }

  float E_raw  = -(gtt * kt + gtphi * kphi);
  float Lz_raw = gtphi * kt + gphph * kphi;
  float invE = (E_raw > KERR_EPSILON) ? (1.0 / E_raw) : 1.0;
  c.Lz = Lz_raw * invE;

  float ptheta = sigma * ktheta * invE;
  float cot2 = (sin2 > KERR_EPSILON) ? (cosT * cosT / sin2) : 0.0;
  c.Q = ptheta * ptheta - a * a * cosT * cosT + c.Lz * c.Lz * cot2;

  ray.vr = sigma * kr * invE;
  ray.mu = cosT;
  ray.vmu = -sinT * ptheta;  // dmu/dlambda = -sin(theta) dtheta/dlambda
  kerrAccelerations(ray.r, ray.mu, r_s, a, c, ray.accR, ray.accMu);
}

// Ingoing Kerr-Schild phi and t rates in Mino time for radial velocity vr:
//   dphi/dlambda = Lz/sin^2 - aE + a (P + vr)/Delta
//   dt/dlambda   = ((r^2+a^2) P + r_s r vr)/Delta + a (Lz - aE sin^2)
// with P = (r^2+a^2)E - a Lz. Both are regular on the future horizon. For an
// ingoing ray (vr < 0), P + vr = (P^2 - vr^2)/(P - vr) = Delta Q_eff/(P - vr)
// on shell (vr^2 = R), which removes the 0/0 at Delta -> 0.
void kerrAngularRates(float r, float theta, float vr, float r_s, float a,
                      KerrConsts c, out float dphi, out float dt) {
  float sinTheta = sin(theta);
  float sin2 = max(sinTheta * sinTheta, 1e-6);
  float P = (r * r + a * a) * c.E - a * c.Lz;
  float Lz_minus_aE = c.Lz - a * c.E;
  float Q_eff = c.Q + Lz_minus_aE * Lz_minus_aE;
  float tail = a * (c.Lz - a * c.E * sin2);
  if (vr < 0.0) {
    float inv = 1.0 / max(P - vr, 1e-30);
    dphi = (c.Lz / sin2) - a * c.E + a * Q_eff * inv;
    dt   = P + r_s * r * Q_eff * inv + tail;
  } else {
    float invD = 1.0 / max(kerrDelta(r, a, r_s), 1e-6);
    dphi = (c.Lz / sin2) - a * c.E + a * (P + vr) * invD;
    dt   = ((r * r + a * a) * P + r_s * r * vr) * invD + tail;
  }
}

// Null-constraint projection. The second-order system carries vr^2 = R(r)
// and vmu^2 = Theta_mu(mu) only as first integrals; in float32 the rounding
// of |vr| ~ P ~ r^2 far out accumulates over the r^2 dynamic range until a
// near-radial ray reverses at a few r_s. Away from turning points (potential
// above 1% of its scale) the magnitude is reset to the exact root; near a
// turning point the leapfrog alone carries the sign change, where the
// magnitudes are small and float32 resolves them.
void kerrProjectOnShell(inout KerrRay ray, float r_s, float a, KerrConsts c) {
  float P = (ray.r * ray.r + a * a) * c.E - a * c.Lz;
  float Lz_minus_aE = c.Lz - a * c.E;
  float R = P * P - kerrDelta(ray.r, a, r_s) * (c.Q + Lz_minus_aE * Lz_minus_aE);
  if (R > 0.01 * P * P) {
    ray.vr = (ray.vr >= 0.0 ? 1.0 : -1.0) * sqrt(R);
  }
  float thetaMu = kerrPolarPotentialMu(ray.mu, a, c);
  float muScale = abs(c.Q) + a * a * c.E * c.E + c.Lz * c.Lz;
  if (muScale > 0.0 && thetaMu > 0.01 * muScale) {
    ray.vmu = (ray.vmu >= 0.0 ? 1.0 : -1.0) * sqrt(thetaMu);
  }
}

// One kick-drift-kick (Stormer-Verlet) step of the second-order Mino system.
// r and mu decouple in Mino time, each with a separable Hamiltonian
// v^2/2 - R/2 (resp. Theta_mu/2), so the step is symplectic: the on-shell
// error stays bounded and the ray passes radial and polar turning points
// continuously. phi and t advance with midpoint rates. Near the axis
// dphi/dlambda ~ Lz/sin^2 grows large for small Lz, so the step shrinks to
// keep each phi increment below 0.25 rad.
// Cost: one force and one rate evaluation per step (forces carried in ray),
// plus the on-shell projection.
void kerrStep(inout KerrRay ray, float r_s, float a, KerrConsts c, float dlam) {
  float sin2Now = max(1.0 - ray.mu * ray.mu, 1e-8);
  float phiRate = abs(c.Lz) / sin2Now + abs(a) * (1.0 + abs(c.Lz)) + 1e-6;
  dlam = sign(dlam) * min(abs(dlam), 0.25 / phiRate);

  precise float vrHalf = ray.vr + 0.5 * dlam * ray.accR;
  precise float vmuHalf = ray.vmu + 0.5 * dlam * ray.accMu;

  float rMid = ray.r + 0.5 * dlam * vrHalf;
  float muMid = clamp(ray.mu + 0.5 * dlam * vmuHalf, -1.0, 1.0);
  float dphi;
  float dt;
  kerrAngularRates(rMid, acos(muMid), vrHalf, r_s, a, c, dphi, dt);

  precise float rNew = ray.r + dlam * vrHalf;
  precise float muNew = ray.mu + dlam * vmuHalf;
  ray.phi += dlam * dphi;
  ray.t += dlam * dt;

  // A ray with Lz = 0 turns in mu exactly at the axis (Theta_mu(+-1) = -Lz^2);
  // overshooting mu = +-1 is a pass over the pole, which continues the
  // geodesic on the far side: mu -> +-2 - mu with phi -> phi + pi.
  if (muNew > 1.0) {
    muNew = 2.0 - muNew;
    vmuHalf = -vmuHalf;
    ray.phi += PI;
  } else if (muNew < -1.0) {
    muNew = -2.0 - muNew;
    vmuHalf = -vmuHalf;
    ray.phi += PI;
  }

  ray.r = rNew;
  ray.mu = muNew;
  ray.theta = acos(clamp(muNew, -1.0, 1.0));
  kerrAccelerations(ray.r, ray.mu, r_s, a, c, ray.accR, ray.accMu);
  ray.vr = vrHalf + 0.5 * dlam * ray.accR;
  ray.vmu = vmuHalf + 0.5 * dlam * ray.accMu;
  kerrProjectOnShell(ray, r_s, a, c);
}

#endif // KERR_GLSL
