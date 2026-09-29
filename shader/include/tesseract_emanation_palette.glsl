#ifndef TESSERACT_EMANATION_PALETTE_GLSL
#define TESSERACT_EMANATION_PALETTE_GLSL

/**
 * @file tesseract_emanation_palette.glsl
 * @brief Glow color of an emanation-table value, shared by the pane pass and
 *        the lattice pass (the traveling pulse takes the walk's hue).
 */

const vec3 EMANATION_WARM_LOW = vec3(1.0, 0.34, 0.08);
const vec3 EMANATION_WARM_HIGH = vec3(1.0, 0.78, 0.40);
const vec3 EMANATION_COOL_LOW = vec3(0.06, 0.20, 0.33);
const vec3 EMANATION_COOL_HIGH = vec3(0.21, 0.39, 0.54);

// Glow color of a table value at @p level. The high bits of |v| = a ^ b name
// the table sub-block the cell lies in (the nesting of successive doublings),
// so the hue steps by block, and the low bits modulate brightness; a positive
// edge sign glows warm amber, a negative one muted cool blue.
vec3 emanationColor(int v, int level) {
  int magnitude = abs(v);
  float block = float(magnitude >> max(level - 4, 0)) / 7.0;
  float detail = 0.75 + (0.25 * float(magnitude & 7) / 7.0);
  vec3 color = v >= 0 ? mix(EMANATION_WARM_LOW, EMANATION_WARM_HIGH, block)
                      : mix(EMANATION_COOL_LOW, EMANATION_COOL_HIGH, block);
  return color * detail;
}

#endif // TESSERACT_EMANATION_PALETTE_GLSL
