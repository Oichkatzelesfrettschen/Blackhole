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

// Mino-time state. The radial motion carries vr = dr/dlambda through
// d^2r/dlambda^2 = R'(r)/2 (accR caches R'/2). The angular motion carries the
// unit direction n and its tangent velocity w = dn/dlambda without the frame
// dragging part: in Mino time Carter's polar equation is a particle on the unit
// sphere with potential -a^2 E^2 n_z^2 / 2, so
//   |w|^2 = p_theta^2 + Lz^2 / sin^2 = Q + Lz^2 + a^2 E^2 n_z^2,
//   (n x w) . z = Lz,
// and neither contains a 1/sin(theta) factor: the axis is a regular point, so
// rays with any Lz, including 0, cross it continuously. Frame dragging rotates
// n and w together about z. Positions are r * n; the azimuth of n is the
// ingoing Kerr-Schild azimuth, offset at the start so it equals the
// Boyer-Lindquist azimuth at infinity.
struct KerrRay {
  float r;
  float t;
  float vr;
  float accR;
  vec3 n;
  vec3 w;
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

vec3 kerrRayPosition(KerrRay ray) {
  return ray.r * ray.n;
}

// Rotation of v about +z by angle.
vec3 kerrRotateZ(vec3 v, float angle) {
  float c = cos(angle);
  float s = sin(angle);
  return vec3(c * v.x - s * v.y, s * v.x + c * v.y, v.z);
}

// Ingoing Kerr-Schild azimuth offset F(r) = phi_KS - phi_BL along a ray,
// F(r) = a / (r+ - r-) ln((r - r+)/(r - r-)), with F -> 0 at infinity
// (r_s = 2M). Zero at a = 0 and inside the outer horizon.
float kerrKsAzimuthOffset(float r, float r_s, float a) {
  float M = 0.5 * r_s;
  float disc = M * M - a * a;
  if (abs(a) < KERR_EPSILON || disc <= 0.0) {
    return 0.0;
  }
  float root = sqrt(disc);
  float rPlus = M + root;
  float rMinus = M - root;
  if (r <= rPlus) {
    return 0.0;
  }
  return a / (rPlus - rMinus) * log((r - rPlus) / (r - rMinus));
}

// Position pos in the chart the ray state lives in: kerrInitGeodesic rotates
// the state by the Kerr-Schild azimuth offset F(|pos|) (r_s and a as passed
// to it), so every position along the ray is in this chart, and a scene
// position such as the camera must be rotated alike before it is compared
// with one.
vec3 kerrChartPosition(vec3 pos, float r_s, float a) {
  return kerrRotateZ(pos, kerrKsAzimuthOffset(length(pos), r_s, a));
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

// Radial acceleration R'(r)/2 = 2 r E P - (r - r_s/2) Q_eff with
// P = (r^2 + a^2) E - a Lz and Q_eff = Q + (Lz - aE)^2.
float kerrRadialAcceleration(float r, float r_s, float a, KerrConsts c) {
  float P = (r * r + a * a) * c.E - a * c.Lz;
  float Lz_minus_aE = c.Lz - a * c.E;
  float Q_eff = c.Q + Lz_minus_aE * Lz_minus_aE;
  return 2.0 * r * c.E * P - (r - 0.5 * r_s) * Q_eff;
}

// Tangential acceleration of n on the unit sphere from the potential
// -a^2 E^2 n_z^2 / 2 (Carter's a^2 E^2 cos^2 term).
vec3 kerrSphereAcceleration(vec3 n, float a, KerrConsts c) {
  float k = a * a * c.E * c.E * n.z;
  return k * (vec3(0.0, 0.0, 1.0) - n.z * n);
}

// On-shell angular speed |w| = sqrt(Q + Lz^2 + a^2 E^2 n_z^2).
float kerrAngularSpeed(vec3 n, float a, KerrConsts c) {
  return sqrt(max(c.Q + c.Lz * c.Lz + a * a * c.E * c.E * n.z * n.z, 0.0));
}

// Null geodesic through pos with Cartesian direction dir in Kerr spin a
// (r_s = 2M). Projects dir onto the Boyer-Lindquist basis, solves the null
// condition for the future root k^t, reads E = -k_t and Lz = k_phi, and
// normalizes to E = 1. Q is Carter's constant p_theta^2 - a^2 cos^2 +
// Lz^2 cot^2 with p_theta = Sigma k^theta / E, so R(r0) = vr^2 and
// |w|^2 = p_theta^2 + Lz^2 / sin^2 = Q + Lz^2 + a^2 cos^2 at the start
// (physics::kerrNullGeodesicFromBL is the CPU twin, pinned by
// tests/kerr_null_geodesic_test.cpp; the GPU init is pinned by
// tests/kerr_shader_capture_test.cpp). The state starts rotated by the
// Kerr-Schild azimuth offset F(r0) so the traced azimuth is Boyer-Lindquist at
// infinity.
void kerrInitGeodesic(vec3 pos, vec3 dir, float r_s, float a,
                      out KerrConsts c, out KerrRay ray) {
  float r = length(pos);
  ray.r = r;
  ray.t = 0.0;
  c.E = 1.0;
  c.Lz = 0.0;
  c.Q = 0.0;
  ray.vr = 0.0;
  ray.n = vec3(0.0, 0.0, 1.0);
  ray.w = vec3(0.0);
  ray.accR = 0.0;
  if (r < KERR_EPSILON) {
    return;
  }

  // sin(theta) from the cylindrical radius: sqrt(1 - cos^2) cancels to zero
  // or to a rounding residue near the axis in float32.
  float invR  = 1.0 / r;
  float cosT  = clamp(pos.z * invR, -1.0, 1.0);
  float sinT  = min(length(pos.xy) * invR, 1.0);
  float sin2  = sinT * sinT;
  // On the axis the Boyer-Lindquist azimuth is free. Choosing it along the
  // transverse part of dir puts that part in e_theta = sign(cos) (cos phi,
  // sin phi, 0), so k^theta = |dir_perp| / r carries it with k^phi = 0 and
  // Lz = 0; atan(0, 0) at the axis would otherwise leave e_theta arbitrary
  // and drop any transverse component outside it.
  bool onAxis = sinT <= KERR_EPSILON;
  vec2 azimuthDir = onAxis ? cosT * dir.xy : pos.xy;
  float phi   = dot(azimuthDir, azimuthDir) > 0.0 ? atan(azimuthDir.y, azimuthDir.x) : 0.0;
  float cosP  = cos(phi);
  float sinP  = sin(phi);

  vec3 e_r     = vec3(sinT * cosP,  sinT * sinP,  cosT);
  vec3 e_theta = vec3(cosT * cosP,  cosT * sinP, -sinT);
  vec3 e_phi   = vec3(-sinP,         cosP,         0.0);

  // BL contravariant spatial components of the null direction.
  float kr     = dot(dir, e_r);
  float ktheta = dot(dir, e_theta) * invR;
  float kphi   = onAxis ? 0.0 : dot(dir, e_phi) / (r * sinT);

  float sigma  = r * r + a * a * cosT * cosT;
  float delta  = r * r - r_s * r + a * a;
  float f      = (sigma > KERR_EPSILON) ? (r_s * r / sigma) : 0.0;
  float gtt    = -(1.0 - f);
  float gtphi  = -f * a * sin2;
  float grr    = sigma / max(abs(delta), KERR_EPSILON);
  float gthth  = sigma;
  float gphph  = (r * r + a * a + f * a * a * sin2) * sin2;

  // gtt (k^t)^2 + 2 hb k^t + spatial = 0 with hb = gtphi kphi. The roots
  // have E = -(gtt k^t + hb) = +-sqrt(D), D = hb^2 - gtt spatial, and in
  // conjugate form k^t(E > 0) = spatial / (sqrt(D) - hb) and
  // k^t(E < 0) = -spatial / (sqrt(D) + hb), which divide by gtt nowhere: on
  // the stationary limit (gtt = 0) the equation is linear and the first form
  // is its root -spatial / (2 hb), finite for hb < 0. A denominator within
  // float rounding of sqrt(D) + |hb| marks a root at infinity. Outside the
  // ergoregion the E > 0 root is the future-directed one; inside it both can
  // be future-directed and the E > 0 root, the one that can connect to
  // infinity, is preferred (physics::kerrNullGeodesicFromBL applies the same
  // rule). D < 0 has no null completion.
  float spatial = grr * kr * kr + gthth * ktheta * ktheta + gphph * kphi * kphi;
  float hb      = gtphi * kphi;
  float disc    = hb * hb - gtt * spatial;
  float sqD     = sqrt(max(disc, 0.0));
  float rootTol = 1e-6 * (sqD + abs(hb));
  bool finitePos = disc >= 0.0 && (sqD - hb) > rootTol;
  bool finiteNeg = disc >= 0.0 && (sqD + hb) > rootTol;
  float ktPos = finitePos ? spatial / (sqD - hb) : 0.0;
  float ktNeg = finiteNeg ? -spatial / (sqD + hb) : 0.0;
  bool useNeg = finiteNeg && ktNeg > 0.0 && (!finitePos || ktPos <= 0.0);
  float kt = useNeg ? ktNeg : ktPos;

  float E_raw  = useNeg ? -sqD : sqD;
  float Lz_raw = gtphi * kt + gphph * kphi;
  // No finite null completion, or a photon with E <= 0 (possible only inside
  // the ergoregion), which cannot reach infinity and so cannot bring the sky
  // to the camera: start it at r = 0, which every trace loop treats as
  // captured.
  if (!(finitePos || useNeg) || !(E_raw > KERR_EPSILON)) {
    ray.r = 0.0;
    return;
  }
  float invE = 1.0 / E_raw;
  c.Lz = Lz_raw * invE;

  float ptheta = sigma * ktheta * invE;
  float cot2 = onAxis ? 0.0 : (cosT * cosT / sin2);
  c.Q = ptheta * ptheta - a * a * cosT * cosT + c.Lz * c.Lz * cot2;

  ray.vr = sigma * kr * invE;
  ray.accR = kerrRadialAcceleration(r, r_s, a, c);

  // Angular state: w = p_theta e_theta + (Lz / sin) e_phi, tangent to the
  // sphere at n = pos / r, rescaled to the on-shell speed.
  vec3 n = pos * invR;
  float lzOverSin = onAxis ? 0.0 : c.Lz / sinT;
  vec3 w = ptheta * e_theta + lzOverSin * e_phi;
  w -= dot(w, n) * n;
  float wLen = length(w);
  float speed = kerrAngularSpeed(n, a, c);
  if (wLen > 0.0) {
    w *= speed / wLen;
  }
  float offset = kerrKsAzimuthOffset(r, r_s, a);
  ray.n = kerrRotateZ(n, offset);
  ray.w = kerrRotateZ(w, offset);
}

// Frame-dragging azimuth rate and coordinate-time rate in Mino time (ingoing
// Kerr-Schild), without the Lz / sin^2 term that the sphere motion carries:
//   dphi_drag/dlambda = -aE + a (P + vr)/Delta
//   dt/dlambda        = ((r^2+a^2) P + r_s r vr)/Delta + a (Lz - aE sin^2)
// with P = (r^2+a^2)E - a Lz. Both are regular on the future horizon: for an
// ingoing ray (vr < 0), P + vr = (P^2 - vr^2)/(P - vr) = Delta Q_eff/(P - vr)
// on shell (vr^2 = R), which removes the 0/0 at Delta -> 0.
void kerrDragAndTimeRates(float r, float sin2, float vr, float r_s, float a,
                          KerrConsts c, out float dphiDrag, out float dt) {
  float P = (r * r + a * a) * c.E - a * c.Lz;
  float Lz_minus_aE = c.Lz - a * c.E;
  float Q_eff = c.Q + Lz_minus_aE * Lz_minus_aE;
  float tail = a * (c.Lz - a * c.E * sin2);
  if (vr < 0.0) {
    float inv = 1.0 / max(P - vr, 1e-30);
    dphiDrag = -a * c.E + a * Q_eff * inv;
    dt       = P + r_s * r * Q_eff * inv + tail;
  } else {
    // abs(Delta): a step that overshoots r_+ before the horizon check fires
    // must not flip the sign of the rates (d_kerr_drag_and_time_rates twin).
    float invD = 1.0 / max(abs(kerrDelta(r, a, r_s)), 1e-6);
    dphiDrag = -a * c.E + a * (P + vr) * invD;
    dt       = ((r * r + a * a) * P + r_s * r * vr) * invD + tail;
  }
}

// Affine length of a Mino step, the path length radiative transfer
// integrates over: d(lambda_affine) = Sigma d(lambda_Mino) at E = 1, so it is
// the length a distant observer assigns to the photon path. Far from the hole
// it is the Euclidean length (on the spin axis dr/d(lambda_affine) = 1
// exactly). Trapezoid rule over the step's end states; the error falls as the
// square of the step, so sums over a fixed stretch of path converge as the
// step shrinks.
float kerrAffineStep(KerrRay before, KerrRay after, float a, float dlam) {
  float sigma0 = kerrSigma(before.r, a, before.n.z);
  float sigma1 = kerrSigma(after.r, a, after.n.z);
  return 0.5 * (sigma0 + sigma1) * abs(dlam);
}

// Null-constraint projection. The leapfrog carries vr^2 = R(r) only as a first
// integral; in float32 the rounding of |vr| ~ P ~ r^2 far out accumulates over
// the r^2 dynamic range until a near-radial ray reverses at a few r_s. Away
// from turning points (R above 1% of P^2) |vr| is reset to sqrt(R); near a
// turning point the leapfrog alone carries the sign change, where the
// magnitudes are small and float32 resolves them. The angular state is
// projected onto |n| = 1, w . n = 0, and |w| = sqrt(Q + Lz^2 + a^2 n_z^2).
void kerrProjectOnShell(inout KerrRay ray, float r_s, float a, KerrConsts c) {
  float P = (ray.r * ray.r + a * a) * c.E - a * c.Lz;
  float Lz_minus_aE = c.Lz - a * c.E;
  float R = P * P - kerrDelta(ray.r, a, r_s) * (c.Q + Lz_minus_aE * Lz_minus_aE);
  if (R > 0.01 * P * P) {
    ray.vr = (ray.vr >= 0.0 ? 1.0 : -1.0) * sqrt(R);
  }
  ray.n = normalize(ray.n);
  ray.w -= dot(ray.w, ray.n) * ray.n;
  float wLen = length(ray.w);
  if (wLen > 0.0) {
    ray.w *= kerrAngularSpeed(ray.n, a, c) / wLen;
  }
}

// One kick-drift-kick (Stormer-Verlet) step of the Mino-time system. r follows
// the separable Hamiltonian vr^2/2 - R/2; n moves on the unit sphere as a free
// great-circle rotation (exact Rodrigues drift) kicked by the a^2 n_z^2
// potential, and frame dragging rotates n and w about z by the midpoint rate.
// The step is symplectic in r and in n, conserves Lz = (n x w) . z exactly
// (kicks point in the (z, n) plane; drift and drag are rotations), and has no
// coordinate singularity on the spin axis. Cost: one radial force, one sphere
// force, one rate evaluation, and one sin/cos pair per step.
void kerrStep(inout KerrRay ray, float r_s, float a, KerrConsts c, float dlam) {
  precise float vrHalf = ray.vr + 0.5 * dlam * ray.accR;
  vec3 wHalf = ray.w + 0.5 * dlam * kerrSphereAcceleration(ray.n, a, c);
  wHalf -= dot(wHalf, ray.n) * ray.n;

  float rMid = ray.r + 0.5 * dlam * vrHalf;
  precise float rNew = ray.r + dlam * vrHalf;

  // Frame dragging at the midpoint rate, split in two half rotations about z
  // around the great-circle drift so the step stays symmetric.
  float dphiDrag;
  float dt;
  kerrDragAndTimeRates(rMid, max(1.0 - ray.n.z * ray.n.z, 0.0), vrHalf, r_s, a, c,
                       dphiDrag, dt);
  float halfDrag = 0.5 * dlam * dphiDrag;
  vec3 nNew = kerrRotateZ(ray.n, halfDrag);
  vec3 wNew = kerrRotateZ(wHalf, halfDrag);

  // Great-circle drift of (n, w) through angle |w| dlam.
  float speed = length(wNew);
  if (speed > 0.0) {
    vec3 u = wNew / speed;
    float ang = speed * dlam;
    float ca = cos(ang);
    float sa = sin(ang);
    vec3 nDrift = nNew * ca + u * sa;
    wNew = speed * (u * ca - nNew * sa);
    nNew = nDrift;
  }
  nNew = kerrRotateZ(nNew, halfDrag);
  wNew = kerrRotateZ(wNew, halfDrag);
  ray.t += dlam * dt;

  ray.r = rNew;
  ray.accR = kerrRadialAcceleration(ray.r, r_s, a, c);
  ray.vr = vrHalf + 0.5 * dlam * ray.accR;
  ray.n = normalize(nNew);
  ray.w = wNew + 0.5 * dlam * kerrSphereAcceleration(ray.n, a, c);
  kerrProjectOnShell(ray, r_s, a, c);
}

#endif // KERR_GLSL
