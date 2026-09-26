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
 * Luminance spans about 19 decades (a 1e-4 cd/m^2 starfield to the 1e13
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
 * sky about the spin axis, in radians, and its motion-blur span), tile*,
 * splatPixelX/Y and pixelSolidAngle (the pixel holding the tile center and
 * its solid angle, from the CPU in double), skyReady.
 * Outputs: fragColor (rgb = display radiance, a = 1: the sky is at the far
 * plane for depth_cues.frag).
 */
#version 460 core

layout(location = 0) in vec2 uv;

out vec4 fragColor;

uniform vec2 resolution;

uniform sampler2D skyMap;
uniform sampler2D skySpan;
uniform sampler2D skyTile;
uniform sampler2D tileSpan;
uniform sampler2D tileFluxLut;
uniform sampler2D blackbodyLut;
uniform samplerCube galaxy;
uniform float skyReady = 0.0;

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

uniform float logLuminanceMin = -7.0;
uniform float logLuminanceMax = 13.5;
uniform float displayPeak = 4.0;

uniform float splatEnabled = 1.0;
uniform float splatPixelX = -1.0;
uniform float splatPixelY = -1.0;
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

/**
 * @brief Linear-sRGB luminance-weighted radiance (cd/m^2) of one sky sample.
 *        `footprint` is the (azimuthal, polar) extent the pixel covers on the
 *        sky at infinity. Azimuth about the spin axis is sampled explicitly,
 *        together with the motion-blur turn, since both rotate the source
 *        about Z; the remaining extent picks the cubemap mip level. A strongly
 *        demagnified region thus shows the average starlight of its footprint
 *        -- near an extremal horizon, whole rings of source latitude --
 *        instead of aliasing onto single stars.
 */
vec3 skyRadiance(vec3 source, float logG, vec2 footprint) {
  float log10G = logG / log(10.0);
  vec3 radiance = vec3(0.0);
  if (cmbEnabled > 0.5) {
    vec4 cmb = blackbodyAt(log(cmbTemperature) / log(10.0) + log10G);
    radiance += cmb.rgb * pow(10.0, cmb.a);
  }
  if (starsEnabled > 0.5) {
    float blurTurn = blurSamples > 1.5 ? skyPhiBlurSpan : 0.0;
    float turn = min(footprint.x + abs(blurTurn), 2.0 * PI);
    float spacing = max(footprint.y, 0.05);
    int samples = clamp(int(ceil(turn / spacing)), blurSamples > 1.5 ? 4 : 1, 16);
    float cubeTexelAngle = 0.5 * PI / float(textureSize(galaxy, 0).x);
    float extent = max(footprint.y, turn / float(samples));
    float lod = max(log2(max(extent, 1.0e-12) / cubeTexelAngle), 0.0);
    // The pixel's azimuth range, centered on its source, trailed by the turn.
    float start = skyPhiOffset - 0.5 * footprint.x;
    vec3 stars = vec3(0.0);
    for (int i = 0; i < samples; ++i) {
      float phi = start + turn * (float(i) + 0.5) / float(samples);
      vec3 texel = textureLod(galaxy, galaxyDirection(source, phi), lod).rgb;
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
 *        and agree to 0.5 rad; across a lensing fold or the shadow edge the
 *        nearest texel wins, so no pixel shows a blend of unrelated sources.
 *        `span` returns the sky at infinity one map texel spans: x the widest
 *        azimuthal step from `spanMap` (the unwrapped swept azimuth), y the
 *        widest polar step or chord between the sky texels. ln g is a smooth function
 *        of the look direction alone (g = 1/E is fixed at the observer), so
 *        it interpolates over whichever of the four texels show sky even
 *        where the directions do not.
 */
vec4 readDirectionMap(sampler2D map, sampler2D spanMap, vec2 st, bool wrapX, out vec2 span) {
  ivec2 size = textureSize(map, 0);
  vec2 base = floor(st - 0.5);
  vec2 f = st - 0.5 - base;
  ivec2 i0 = ivec2(base);
  vec4 texels[4];
  span = vec2(0.0);
  for (int k = 0; k < 4; ++k) {
    ivec2 at = i0 + ivec2(k & 1, k >> 1);
    at.x = wrapX ? (at.x + size.x) % size.x : clamp(at.x, 0, size.x - 1);
    at.y = clamp(at.y, 0, size.y - 1);
    texels[k] = texelFetch(map, at, 0);
    if (texels[k].a > NO_SKY_THRESHOLD) {
      span = max(span, texelFetch(spanMap, at, 0).rg);
    }
  }
  vec4 nearest = texels[(f.x < 0.5 ? 0 : 1) + (f.y < 0.5 ? 0 : 2)];
  float spread = 0.0;
  float polarSpread = 0.0;
  for (int a = 0; a < 4; ++a) {
    for (int b = a + 1; b < 4; ++b) {
      if (texels[a].a > NO_SKY_THRESHOLD && texels[b].a > NO_SKY_THRESHOLD) {
        spread = max(spread, distance(texels[a].rgb, texels[b].rgb));
        polarSpread = max(polarSpread, abs(texels[a].z - texels[b].z));
      }
    }
  }
  // Where whole turns separate the texels, their chord says nothing about
  // the polar extent; the z steps do.
  span.y = max(span.y, span.x > 0.5 ? polarSpread : spread);
  vec4 weights = vec4((1.0 - f.x) * (1.0 - f.y), f.x * (1.0 - f.y), (1.0 - f.x) * f.y, f.x * f.y);
  float skyWeight = 0.0;
  float logG = 0.0;
  for (int k = 0; k < 4; ++k) {
    if (texels[k].a > NO_SKY_THRESHOLD) {
      skyWeight += weights[k];
      logG += weights[k] * texels[k].a;
    }
  }
  if (nearest.a > NO_SKY_THRESHOLD) {
    nearest.a = logG / skyWeight;
  }
  bool allSky = skyWeight > 0.9999;
  if (allSky && span.x > 0.5 && span.y < 0.5) {
    // The texels wind through different azimuths but share a source
    // latitude band: interpolate the polar component alone and keep the
    // nearest azimuth, which the renderer averages over anyway.
    float z = mix(mix(texels[0].z, texels[1].z, f.x), mix(texels[2].z, texels[3].z, f.x), f.y);
    vec2 xy = nearest.xy * (sqrt(max(1.0 - z * z, 0.0)) / max(length(nearest.xy), 1.0e-6));
    return vec4(xy, z, nearest.a);
  }
  if (!allSky || spread > 0.5 || span.x > 0.5) {
    return nearest;
  }
  vec4 top = mix(texels[0], texels[1], f.x);
  vec4 bottom = mix(texels[2], texels[3], f.x);
  vec4 blended = mix(top, bottom, f.y);
  return vec4(normalize(blended.rgb), blended.a);
}

/** @brief Equirectangular read; `texelAngle` returns the map's pitch. */
vec4 equirectSample(vec3 look, out vec2 span, out float texelAngle) {
  float longitude = atan(look.z, -look.x);
  float latitude = asin(clamp(-look.y, -1.0, 1.0));
  vec2 size = vec2(textureSize(skyMap, 0));
  vec2 st = vec2((longitude + PI) / (2.0 * PI), (0.5 * PI - latitude) / PI) * size;
  texelAngle = PI / size.y;
  return readDirectionMap(skyMap, skySpan, st, true, span);
}

/** @brief Tile coordinates of `look`: x = ln rho, y = azimuth psi in [0, 2 pi). */
vec2 tileCoordinates(vec3 look) {
  float east = dot(look, tileEast);
  float north = dot(look, tileNorth);
  float rho = atan(length(vec2(east, north)), dot(look, tileCenter));
  float psi = atan(north, east);
  return vec2(log(max(rho, 1.0e-30)), psi < 0.0 ? psi + 2.0 * PI : psi);
}

/** @brief Log-polar read; `texelAngle` returns the local texel size. */
vec4 tileSample(vec2 coordinates, out vec2 span, out float texelAngle) {
  vec2 size = vec2(textureSize(skyTile, 0));
  float radial = (coordinates.x - tileLogRhoMin) / (tileLogRhoMax - tileLogRhoMin);
  vec2 st = vec2(coordinates.y / (2.0 * PI), radial) * size;
  float rho = exp(coordinates.x);
  texelAngle = rho * max((tileLogRhoMax - tileLogRhoMin) / size.y, 2.0 * PI / size.x);
  return readDirectionMap(skyTile, tileSpan, st, true, span);
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
  if (skyReady < 0.5) {
    // The maps are still being traced: draw the far plane black.
    fragColor = vec4(0.0, 0.0, 0.0, 1.0);
    return;
  }
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
        if (cmbEnabled > 0.5 &&
            all(equal(floor(gl_FragCoord.xy), floor(vec2(splatPixelX, splatPixelY))))) {
          radiance = tileFluxInside(log(rhoSplit)) / pixelSolidAngle;
        }
      } else {
        vec2 span;
        float texelAngle;
        vec4 texel = tileSample(coordinates, span, texelAngle);
        if (texel.a > NO_SKY_THRESHOLD) {
          radiance = skyRadiance(texel.rgb, texel.a, span * (pixelAngle / texelAngle));
        }
      }
    }
  }
  if (!fromTile) {
    vec2 span;
    float texelAngle;
    vec4 texel = equirectSample(look, span, texelAngle);
    if (texel.a > NO_SKY_THRESHOLD) {
      radiance = skyRadiance(texel.rgb, texel.a, span * (pixelAngle / texelAngle));
    }
  }
  fragColor = vec4(displayMapped(radiance), 1.0);
}
