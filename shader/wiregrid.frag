#version 460 core

in vec3 worldPos;
out vec4 fragColor;

layout(location = 4) uniform vec4 color;
uniform float time;
uniform vec3 cameraPos;

void main() {
  float dist = distance(worldPos, cameraPos);
  
  // Distance fade (fog)
  // Increased range to 200.0 for better visibility of outer grid
  float fade = clamp(1.0 - (dist / 200.0), 0.0, 1.0);
  fade = pow(fade, 1.5); // Soft falloff

  // Energy pulse effect moving outwards from the singularity
  float r = length(worldPos.xz);
  float pulseSpeed = 1.0; // Slower, more majestic
  float pulseFreq = 0.2;
  float pulse = sin(r * pulseFreq - time * pulseSpeed) * 0.5 + 0.5;
  pulse = pow(pulse, 4.0); // Softer pulse

  vec4 finalColor = color;
  
  // Add pulse glow (subtle)
  vec3 glowColor = vec3(0.4, 0.7, 1.0); // Cyan-blue
  finalColor.rgb = mix(finalColor.rgb, glowColor, pulse * 0.5);
  finalColor.a = max(finalColor.a, pulse * 0.8); 

  // Apply fog
  finalColor.a *= fade;

  fragColor = finalColor;
}
