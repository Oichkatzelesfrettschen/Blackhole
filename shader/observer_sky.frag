/**
 * @file observer_sky.frag
 * @brief The sky seen by an equatorial Kerr observer, from the precomputed
 *        observer-sky maps (src/physics/observer_sky_lut.h).
 *
 * Each pixel's look direction, on the observer's (r, theta, phi) tetrad legs,
 * indexes a map built by backward null-geodesic tracing in double precision
 * on the CPU: rgb holds the direction of the pixel's source at infinity
 * relative to the observer's azimuth, a holds ln g (g = nu_obs / nu_inf) or a
 * shadow sentinel below -5e3. Float GLSL cannot trace these rays itself: at
 * the canon Miller orbit the horizon offset is 1.6e-7 and the lapse squared
 * 3.5e-10. A log-polar tile resolves the arcsecond patch where the distant
 * universe converges; the equirectangular map covers the rest.
 *
 * Radiance. A blueshift g maps a Planck spectrum at T onto one at g T
 * (I_nu / nu^3 is invariant: I_obs(nu) = g^3 I_sky(nu / g)), so both sources
 * are blackbodies looked up at g T in blackbodyLut (row k: log10 T = 0.01 k;
 * rgb = linear sRGB at unit luminance, a = log10 luminance in cd/m^2):
 *   - CMB: an undiluted blackbody at cmbTemperature g;
 *   - stars: each galaxy-cubemap texel is read as a diluted blackbody whose
 *     temperature is the one with the texel's blue/red ratio (an RGB texel
 *     does not carry a spectrum, so this shift is approximate) and whose
 *     luminance at g = 1 is the texel luminance times starSkyLuminance.
 * Luminance spans about 19 decades (a 1e-3 cd/m^2 starfield to the 1e13
 * cd/m^2 patch), so the output is a log-luminance exposure: luminance maps to
 * displayPeak * (log10 L - logLuminanceMin) / (logLuminanceMax -
 * logLuminanceMin) with the chromaticity kept, before bloom and ACES.
 *
 * Unresolved patch. Wherever a pixel is wider than the patch, the patch's
 * CMB flux inside rhoSplit of the tile center (tileFluxLut: cumulative
 * integral of luminance dOmega over rings) is deposited into the single
 * pixel that contains the center (splatPixel), divided by that pixel's solid
 * angle, instead of being point-sampled and missed. Starlight inside that
 * disk is omitted: blueshifted starlight in the patch is about 1e-10 of the
 * CMB there (dilution 1e-13 times T_star / T_cmb, both on the Rayleigh-Jeans
 * tail).
 *
 * Key uniforms: viewBasis (columns right, up, forward on the tetrad legs),
 * tanHalfFov, skyPhiOffset / skyPhiBlurSpan / blurSamples (rotation of the
 * sky about the spin axis, in radians, and its motion-blur span), tile*.
 * Outputs: fragColor (rgb = display radiance, a = 1: the sky is at the far
 * plane for depth_cues.frag).
 */
#version 460 core

layout(location = 0) in vec2 uv;

out vec4 fragColor;

uniform vec2 resolution;

uniform sampler2D skyMap;
uniform sampler2D skyTile;
uniform sampler2D tileFluxLut;
uniform sampler2D blackbodyLut;
uniform samplerCube galaxy;

uniform mat3 viewBasis;
uniform float tanHalfFov = 1.0;

uniform vec3 tileCenter;
uniform vec3 tileEast;
uniform vec3 tileNorth;
uniform float tileLogRhoMin;
uniform float tileLogRhoMax;
uniform float useTile = 1.0;

uniform float skyPhiOffset = 0.0;
uniform float skyPhiBlurSpan = 0.0;
uniform float blurSamples = 1.0;

uniform float cmbEnabled = 1.0;
uniform float cmbTemperature = 2.725;
uniform float starsEnabled = 1.0;
uniform float starSkyLuminance = 1.0e-3;

uniform float logLuminanceMin = -5.0;
uniform float logLuminanceMax = 14.0;
uniform float displayPeak = 4.0;

uniform float splatEnabled = 1.0;
uniform vec2 splatPixel = vec2(-1.0);
uniform float pixelSolidAngle = 1.0e-6;

const float PI = 3.14159265358979;
const float NO_SKY_THRESHOLD = -5.0e3;
const float LUT_LOG10_STEP = 0.01;
const vec3 REC709 = vec3(0.2126, 0.7152, 0.0722);

// ---------------------------------------------------------------------------
// Blackbody table
// ---------------------------------------------------------------------------

vec4 blackbodyAt(float log10T) {
  float rows = float(textureSize(blackbodyLut, 0).x);
  float index = clamp(log10T / LUT_LOG10_STEP, 0.0, rows - 1.0);
  return texture(blackbodyLut, vec2((index + 0.5) / rows, 0.5));
}

float blueRedRatio(int row) {
  vec3 rgb = texelFetch(blackbodyLut, ivec2(row, 0), 0).rgb;
  return rgb.b / max(rgb.r, 1.0e-6);
}

/** @brief log10 of the blackbody temperature whose linear-sRGB blue/red ratio
 *         matches `ratio`, searched over 1000 K .. 50,000 K (rows 300..470). */
float temperatureFromRatio(float ratio) {
  int low = 300;
  int high = 470;
  float target = clamp(ratio, blueRedRatio(low), blueRedRatio(high));
  for (int step = 0; step < 8; ++step) {
    int middle = (low + high) / 2;
    if (blueRedRatio(middle) < target) {
      low = middle;
    } else {
      high = middle;
    }
  }
  return float(high) * LUT_LOG10_STEP;
}

// ---------------------------------------------------------------------------
// Sources at infinity
// ---------------------------------------------------------------------------

/** @brief Cubemap direction of a source direction in the (X to phi, Z spin)
 *         frame after the sky has turned by `phi` about Z. */
vec3 galaxyDirection(vec3 source, float phi) {
  float c = cos(phi);
  float s = sin(phi);
  vec3 turned = vec3(c * source.x - s * source.y, s * source.x + c * source.y, source.z);
  return vec3(turned.x, turned.z, -turned.y);
}

/** @brief Linear-sRGB luminance-weighted radiance (cd/m^2) of one sky sample. */
vec3 skyRadiance(vec3 source, float logG) {
  float log10G = logG / log(10.0);
  vec3 radiance = vec3(0.0);
  if (cmbEnabled > 0.5) {
    vec4 cmb = blackbodyAt(log(cmbTemperature) / log(10.0) + log10G);
    radiance += cmb.rgb * pow(10.0, cmb.a);
  }
  if (starsEnabled > 0.5) {
    int samples = blurSamples > 1.5 ? 4 : 1;
    vec3 stars = vec3(0.0);
    for (int i = 0; i < samples; ++i) {
      float phi = skyPhiOffset + skyPhiBlurSpan * (float(i) + 0.5) / float(samples);
      vec3 texel = texture(galaxy, galaxyDirection(source, phi)).rgb;
      float luminance = dot(texel, REC709);
      if (luminance <= 0.0) {
        continue;
      }
      float log10T = temperatureFromRatio(texel.b / max(texel.r, 1.0e-6));
      vec4 rest = blackbodyAt(log10T);
      vec4 shifted = blackbodyAt(log10T + log10G);
      stars += shifted.rgb * luminance * pow(10.0, shifted.a - rest.a);
    }
    radiance += stars * (starSkyLuminance / float(samples));
  }
  return radiance;
}

// ---------------------------------------------------------------------------
// Map lookups
// ---------------------------------------------------------------------------

/**
 * @brief Bilinear read of a direction map at texel coordinate `st` (texel
 *        units). Directions interpolate only where all four texels show sky
 *        and agree to 0.1 rad; across a lensing fold or the shadow edge the
 *        nearest texel wins, so no pixel shows a blend of unrelated sources.
 */
vec4 readDirectionMap(sampler2D map, vec2 st, bool wrapX) {
  ivec2 size = textureSize(map, 0);
  vec2 base = floor(st - 0.5);
  vec2 f = st - 0.5 - base;
  ivec2 i0 = ivec2(base);
  vec4 texels[4];
  for (int k = 0; k < 4; ++k) {
    ivec2 at = i0 + ivec2(k & 1, k >> 1);
    at.x = wrapX ? (at.x + size.x) % size.x : clamp(at.x, 0, size.x - 1);
    at.y = clamp(at.y, 0, size.y - 1);
    texels[k] = texelFetch(map, at, 0);
  }
  vec4 nearest = texels[(f.x < 0.5 ? 0 : 1) + (f.y < 0.5 ? 0 : 2)];
  bool allSky = min(min(texels[0].a, texels[1].a), min(texels[2].a, texels[3].a)) > NO_SKY_THRESHOLD;
  if (!allSky) {
    return nearest;
  }
  float agreement = min(min(dot(texels[0].rgb, texels[1].rgb), dot(texels[0].rgb, texels[2].rgb)),
                        dot(texels[0].rgb, texels[3].rgb));
  if (agreement < cos(0.1)) {
    return nearest;
  }
  vec4 top = mix(texels[0], texels[1], f.x);
  vec4 bottom = mix(texels[2], texels[3], f.x);
  vec4 blended = mix(top, bottom, f.y);
  return vec4(normalize(blended.rgb), blended.a);
}

vec4 equirectSample(vec3 look) {
  float longitude = atan(look.z, -look.x);
  float latitude = asin(clamp(-look.y, -1.0, 1.0));
  vec2 size = vec2(textureSize(skyMap, 0));
  vec2 st = vec2((longitude + PI) / (2.0 * PI), (0.5 * PI - latitude) / PI) * size;
  return readDirectionMap(skyMap, st, true);
}

/** @brief Tile coordinates of `look`: x = ln rho, y = azimuth psi in [0, 2 pi). */
vec2 tileCoordinates(vec3 look) {
  float east = dot(look, tileEast);
  float north = dot(look, tileNorth);
  float rho = atan(length(vec2(east, north)), dot(look, tileCenter));
  float psi = atan(north, east);
  return vec2(log(max(rho, 1.0e-30)), psi < 0.0 ? psi + 2.0 * PI : psi);
}

vec4 tileSample(vec2 coordinates) {
  vec2 size = vec2(textureSize(skyTile, 0));
  float radial = (coordinates.x - tileLogRhoMin) / (tileLogRhoMax - tileLogRhoMin);
  vec2 st = vec2(coordinates.y / (2.0 * PI), radial) * size;
  return readDirectionMap(skyTile, st, true);
}

/** @brief Cumulative CMB flux (luminance x sr) inside ln rho = `logRho`. */
vec3 tileFluxInside(float logRho) {
  float rings = float(textureSize(tileFluxLut, 0).x);
  float ring = (logRho - tileLogRhoMin) / (tileLogRhoMax - tileLogRhoMin) * rings;
  int index = clamp(int(ring), 0, int(rings) - 1);
  return texelFetch(tileFluxLut, ivec2(index, 0), 0).rgb;
}

vec3 displayMapped(vec3 radiance) {
  float luminance = dot(radiance, REC709);
  if (!(luminance > 0.0)) {
    return vec3(0.0);
  }
  float level = (log(luminance) / log(10.0) - logLuminanceMin) / (logLuminanceMax - logLuminanceMin);
  return radiance / luminance * displayPeak * clamp(level, 0.0, 1.0);
}

void main() {
  vec2 ndc = uv * 2.0 - 1.0;
  float aspect = resolution.x / max(resolution.y, 1.0);
  vec3 look = normalize(viewBasis * vec3(ndc.x * aspect * tanHalfFov, ndc.y * tanHalfFov, 1.0));
  float pixelAngle = 2.0 * tanHalfFov / max(resolution.y, 1.0);

  vec3 radiance = vec3(0.0);
  bool fromTile = false;
  if (useTile > 0.5) {
    vec2 coordinates = tileCoordinates(look);
    if (coordinates.x < tileLogRhoMax) {
      fromTile = true;
      float rhoSplit = 0.75 * pixelAngle;
      if (splatEnabled > 0.5 && coordinates.x < log(rhoSplit)) {
        // Inside the unresolved disk: its whole CMB flux lands on one pixel.
        if (all(equal(floor(gl_FragCoord.xy), floor(splatPixel)))) {
          radiance = tileFluxInside(log(rhoSplit)) / pixelSolidAngle;
        }
      } else {
        vec4 texel = tileSample(coordinates);
        if (texel.a > NO_SKY_THRESHOLD) {
          radiance = skyRadiance(texel.rgb, texel.a);
        }
      }
    }
  }
  if (!fromTile) {
    vec4 texel = equirectSample(look);
    if (texel.a > NO_SKY_THRESHOLD) {
      radiance = skyRadiance(texel.rgb, texel.a);
    }
  }
  fragColor = vec4(displayMapped(radiance), 1.0);
}
