# Wiregrid Best Practices

## Scope
- Visualize spacetime curvature with a clean, stable wiregrid that aligns with
  the simulation geometry and preserves detail near the horizon.
- Keep the wiregrid predictable across compute/fragment paths and avoid
  Z-fighting artifacts in post effects.

## Geometry modeling
- Use an embedding surface for the equatorial slice when a full 3D curvature
  surface is not required. The canonical Schwarzschild embedding is the
  Flamm paraboloid (good for intuition and grid topology).
- For Kerr, prefer an equatorial slice visualization or a parametric
  approximation; full embeddings are not globally Euclidean and are usually
  shown as partial patches.
- Keep a clear separation between visual embedding geometry and the physics
  integrator to avoid mixing coordinate artifacts into the simulation.

## Grid parameterization
- Use log or hybrid radial spacing to maintain detail near the horizon while
  keeping outer regions readable.
- Define grid lines in parametric space (r, phi) and map them into world space
  via the embedding function, so line spacing is stable under camera motion.
- Store per-vertex attributes for proper length and coordinate radius if you
  want UI readouts and debug overlays to match the wiregrid.

## Rendering strategies
- Prefer a two-pass overlay: render filled geometry, then render wiregrid with
  polygon offset or depth bias to prevent Z-fighting.
- For stable line thickness, use a barycentric-coordinate wireframe in the
  fragment shader rather than relying on `glLineWidth`.
- If you must use line primitives, keep width at 1.0 and lean on MSAA; wide
  lines are inconsistently supported across drivers.

## Quality and stability
- Use MSAA and smoothstep on edge distances for anti-aliased wire edges.
- Clamp near-horizon vertex spacing to avoid degenerate triangles that can
  explode wire thickness in screen space.
- Update the grid mesh only when curvature parameters change; avoid per-frame
  rebuilds when the camera moves.

## References (starting points)
- Schwarzschild embedding intuition: https://en.wikipedia.org/wiki/Flamm%27s_paraboloid
- Curvature embedding diagrams: https://en.wikipedia.org/wiki/Embedding_diagram
- OpenGL polygon offset guidance: https://www.khronos.org/opengl/wiki/Polygon_Offset
- Wireframe overlay pitfalls: https://registry.khronos.org/OpenGL-Refpages/gl4/html/glPolygonMode.xhtml
