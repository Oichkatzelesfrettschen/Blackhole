/**
 * @file tonemapping.frag
 * @brief Post-process tonemapping with luminance ACES, chromatic aberration, vignette, and film grain.
 *
 * When tonemappingEnabled > 0.5: applies edge-weighted chromatic aberration,
 * vignette, ACES filmic tone mapping (Narkowicz 2015) applied to luminance
 * with a saturation-only gamut map, animated film grain,
 * and gamma correction.  Otherwise passes texture0 through unchanged.
 * Key uniforms: texture0 (HDR scene), resolution, time, gamma, tonemappingEnabled.
 * Inputs: uv (interpolated texture coordinates).
 * Outputs: fragColor (gamma-corrected LDR output).
 */
#version 460 core

layout(location = 0) in vec2 uv;

out vec4 fragColor;

uniform float gamma = 2.2;
uniform float exposure = 1.0;
uniform float tonemappingEnabled;
uniform sampler2D texture0;
uniform vec2 resolution;
uniform float time;
uniform float chromaticAberrationStrength = 0.002;
uniform float vignetteStrength = 1.0;
uniform float filmGrainStrength = 0.005;

///----
/// Narkowicz 2015, "ACES Filmic Tone Mapping Curve"
float aces(float x) {
  const float a = 2.51;
  const float b = 0.03;
  const float c = 2.43;
  const float d = 0.59;
  const float e = 0.14;
  return clamp((x * (a * x + b)) / (x * (c * x + d) + e), 0.0, 1.0);
}
///----

// Hue-preserving tone map. The ACES curve maps Rec. 709 luminance, and the
// color is scaled by the ratio, so a bright warm pixel stays warm instead of
// every channel reaching the per-channel curve's shoulder and meeting at
// white. A scaled color with a channel above 1 is out of gamut; it is mixed
// toward the gray of the same mapped luminance by the smallest amount that
// brings its largest channel to 1, which keeps luminance and gives up only
// saturation. A gray input maps exactly as the per-channel curve does.
vec3 toneMapLuminance(vec3 x) {
  x = max(x, vec3(0.0));
  float lumIn = dot(x, vec3(0.2126, 0.7152, 0.0722));
  if (lumIn <= 0.0) {
    return vec3(0.0);
  }
  float lumOut = aces(lumIn);
  vec3 mapped = x * (lumOut / lumIn);
  float peak = max(mapped.r, max(mapped.g, mapped.b));
  if (peak > 1.0) {
    float t = (peak - 1.0) / max(peak - lumOut, 1e-6);
    mapped = mix(mapped, vec3(lumOut), clamp(t, 0.0, 1.0));
  }
  return clamp(mapped, 0.0, 1.0);
}

// Pseudo-random number generator
float random(vec2 st) {
    return fract(sin(dot(st.xy, vec2(12.9898,78.233))) * 43758.5453123);
}

void main() {
  vec2 texCoord = uv;
  vec3 color;

  if (tonemappingEnabled > 0.5) {
    // Chromatic Aberration (Simulate lens dispersion)
    // Stronger at edges
    float dist = distance(texCoord, vec2(0.5));
    float caStrength = chromaticAberrationStrength * dist;
    vec2 dir = texCoord - 0.5;
    
    float r = texture(texture0, texCoord - dir * caStrength).r;
    float g = texture(texture0, texCoord).g;
    float b = texture(texture0, texCoord + dir * caStrength).b;
    color = vec3(r, g, b);

    // Vignette (Subtle)
    float vignette = mix(1.0, smoothstep(1.0, 0.2, dist), clamp(vignetteStrength, 0.0, 1.0));
    color *= vignette;

    // Exposure trim before ACES tone mapping
    color *= exposure;

    // Film Grain: applied in linear HDR space BEFORE tonemapping so amplitude
    // scales with the scene's exposure and is perceptually visible.
    // Old position (after ACES clamp to [0,1]) gave only 0.25% modulation.
    float noise = random(texCoord + mod(time, 10.0));
    color += (noise - 0.5) * filmGrainStrength;

    // ACES tone mapping on luminance
    color = toneMapLuminance(color);

    // Gamma Correction
    color = pow(color, vec3(1.0 / gamma));
  } else {
    color = texture(texture0, texCoord).rgb;
  }

  fragColor = vec4(color, 1.0);
}
