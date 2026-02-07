#version 460 core

layout(location = 0) in vec2 uv;

out vec4 fragColor;

uniform float gamma = 2.2;
uniform float tonemappingEnabled;
uniform sampler2D texture0;
uniform vec2 resolution;
uniform float time;

///----
/// Narkowicz 2015, "ACES Filmic Tone Mapping Curve"
vec3 aces(vec3 x) {
  const float a = 2.51;
  const float b = 0.03;
  const float c = 2.43;
  const float d = 0.59;
  const float e = 0.14;
  return clamp((x * (a * x + b)) / (x * (c * x + d) + e), 0.0, 1.0);
}
///----

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
    float caStrength = 0.002 * dist; // Reduced strength
    vec2 dir = texCoord - 0.5;
    
    float r = texture(texture0, texCoord - dir * caStrength).r;
    float g = texture(texture0, texCoord).g;
    float b = texture(texture0, texCoord + dir * caStrength).b;
    color = vec3(r, g, b);

    // Vignette (Subtle)
    float vignette = smoothstep(1.0, 0.2, dist);
    color *= vignette;

    // ACES Tone Mapping
    color = aces(color);

    // Film Grain (Animated, Subtle)
    float grainStrength = 0.005;
    float noise = random(texCoord + mod(time, 10.0));
    color += (noise - 0.5) * grainStrength;

    // Gamma Correction
    color = pow(color, vec3(1.0 / gamma));
  } else {
    color = texture(texture0, texCoord).rgb;
  }

  fragColor = vec4(color, 1.0);
}
