#ifndef BH_DISK_TURBULENCE_GLSL
#define BH_DISK_TURBULENCE_GLSL

// Log-normal turbulence on the accretion-disk emissivity.
//
// The factor exp(sigma * n - sigma^2 / 2) multiplies the Page-Thorne
// emissivity, with n a four-octave value-noise field scaled to about unit
// variance, so its mean over the disk is 1 to within about 1% and the
// azimuthally averaged flux stays the Page-Thorne profile. The pattern is a
// texture, not a transport solution: it stands in for the MRI-driven density
// fluctuations the thin-disk model averages away. sigma = 0 returns 1 exactly
// and restores the smooth disk.
//
// Each feature orbits at the prograde Keplerian angular velocity
// Omega = 1 / (r^(3/2) + a) (BPT 1972, M = 1, time in GM/c^3), so the
// differential rotation shears it into a trailing spiral. Unbounded shear
// winds every feature into a sub-pixel azimuthal stripe, so two copies of the
// pattern, offset by half of K_DTB_WINDING_PERIOD, each age only through one
// period and cross-fade; the blend keeps the pitch of the spirals bounded
// while the pattern keeps rotating.

const float K_DTB_WINDING_PERIOD = 240.0;
// Azimuth embedded on a circle of this radius in noise space: about 19
// first-octave features around the disk.
const float K_DTB_AZIMUTH_SCALE = 3.0;
// Noise-space units per unit of ln r: about 6 first-octave features per
// e-fold in radius, so features are elongated along the orbit.
const float K_DTB_RADIAL_SCALE = 6.0;
// Inverse standard deviation of the four-octave sum below, 0.213 over 4e5
// uniform samples, which scales it to unit variance; the sum is near Gaussian,
// so the factor's mean is 0.997 at sigma 0.6 and 0.989 at sigma 0.9.
const float K_DTB_NOISE_NORM = 1.0 / 0.213;

float dtbHash(vec3 p) {
  p = fract(p * 0.3183099 + vec3(0.1, 0.2, 0.3));
  p *= 17.0;
  return fract(p.x * p.y * p.z * (p.x + p.y + p.z));
}

// Trilinear value noise with smoothstep weights, range [0, 1].
float dtbValueNoise(vec3 x) {
  vec3 cell = floor(x);
  vec3 f = fract(x);
  vec3 w = f * f * (3.0 - (2.0 * f));
  float n000 = dtbHash(cell);
  float n100 = dtbHash(cell + vec3(1.0, 0.0, 0.0));
  float n010 = dtbHash(cell + vec3(0.0, 1.0, 0.0));
  float n110 = dtbHash(cell + vec3(1.0, 1.0, 0.0));
  float n001 = dtbHash(cell + vec3(0.0, 0.0, 1.0));
  float n101 = dtbHash(cell + vec3(1.0, 0.0, 1.0));
  float n011 = dtbHash(cell + vec3(0.0, 1.0, 1.0));
  float n111 = dtbHash(cell + vec3(1.0, 1.0, 1.0));
  float nx00 = mix(n000, n100, w.x);
  float nx10 = mix(n010, n110, w.x);
  float nx01 = mix(n001, n101, w.x);
  float nx11 = mix(n011, n111, w.x);
  return mix(mix(nx00, nx10, w.y), mix(nx01, nx11, w.y), w.z);
}

// Zero-mean four-octave sum.
float dtbFbm(vec3 q) {
  float sum = 0.0;
  float amplitude = 0.5;
  for (int octave = 0; octave < 4; ++octave) {
    sum += amplitude * ((2.0 * dtbValueNoise(q)) - 1.0);
    q = (q * 2.03) + vec3(17.1, 5.3, 11.7);
    amplitude *= 0.5;
  }
  return sum;
}

// Noise sample of the pattern whose features have aged `age` since they were
// laid down; `seed` separates the two cross-faded copies.
float dtbPattern(float rM, float phi, float omega, float age, float seed) {
  float phase = phi - (omega * age);
  vec3 q = vec3(cos(phase) * K_DTB_AZIMUTH_SCALE, sin(phase) * K_DTB_AZIMUTH_SCALE,
                (log(rM) * K_DTB_RADIAL_SCALE) + seed);
  return dtbFbm(q);
}

// Emissivity factor at radius rM (units of M), azimuth phi, spin a (M = 1),
// coordinate time tM (GM/c^3), and log-normal width sigma.
float bhDiskTurbulenceFactor(float rM, float phi, float a, float tM, float sigma) {
  if (sigma <= 0.0 || rM <= 0.0) {
    return 1.0;
  }
  float omega = 1.0 / ((rM * sqrt(rM)) + a);
  float cycle = tM / K_DTB_WINDING_PERIOD;
  float ageA = fract(cycle) * K_DTB_WINDING_PERIOD;
  float ageB = fract(cycle + 0.5) * K_DTB_WINDING_PERIOD;
  float epochA = floor(cycle);
  float epochB = floor(cycle + 0.5);
  // Triangle weights: each copy fades in and out over its own period, and the
  // two weights sum to 1.
  float weightA = 1.0 - abs((2.0 * fract(cycle)) - 1.0);
  float nA = dtbPattern(rM, phi, omega, ageA, 37.0 * epochA);
  float nB = dtbPattern(rM, phi, omega, ageB, (37.0 * epochB) + 101.0);
  float n = (weightA * nA) + ((1.0 - weightA) * nB);
  // Blending two independent fields shrinks the variance by
  // w^2 + (1 - w)^2; dividing by its square root keeps unit variance.
  float spread = sqrt((weightA * weightA) + ((1.0 - weightA) * (1.0 - weightA)));
  float g = (n * K_DTB_NOISE_NORM) / spread;
  return exp((sigma * g) - (0.5 * sigma * sigma));
}

#endif
