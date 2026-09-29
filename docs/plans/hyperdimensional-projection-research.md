# Projection and Rendering of Four- and Higher-Dimensional Structures

Status: research note for the tesseract scene (`src/render/tesseract/`). No
code is changed by this note. Provenance labels used throughout:

- **[math]** established mathematics, checkable by proof or the oracle in
  section 3.
- **[pub]** a published technique; the source is in the references.
- **[design]** this note's own inference; it carries a falsifier and is not
  published fact.

Verification status of every citation is in the references. A source marked
"snippet only" was seen in a search result, not fetched in full.

## 1. Findings

1. A 2D screen cannot show a 4D perspective image directly. A 4D eye looking
   through a viewport produces a 3D image (Hollasch 1991 ray-traces a "gridded
   3D volume of RGB triples"). Every real-time 4D renderer therefore takes one
   of two paths: render a 3D hyperplane slice (ten Bosch 2020, Miegakure,
   4D Toys) or project 4D geometry to 3D and then draw that (the existing
   `tesseract_geometry` perspective and stereographic paths). [pub]
2. The Interstellar tesseract is a rendered 3D structure with no 4D
   mathematics behind its look. Press accounts describe a large physical set
   plus a Double Negative digital extension of extra timelines and fine light
   threads. No DNEG or SIGGRAPH paper on the tesseract turned up in this
   search. Its look decomposes into components that a 3D ray marcher can
   produce (section 2). [pub, press accounts, snippet only]
3. The strongest fit to that look is a hyperplane slice of a periodic 4D
   field of thickened 2-planes ("beams"), warped by a unit-quaternion twist
   that varies along the fourth coordinate to weave strands. It costs a few
   ALU operations per march step and reuses `so4.h` unchanged. [design]
4. Cayley-Dickson arithmetic beyond the quaternions (octonions, sedenions)
   adds no visual value for the lattice look. The quaternion layer is already
   in the codebase and is the only layer that has a rotation group acting on
   R^4. Octonion and sedenion products have a place only as an optional
   fractal or warp generator that looks different from Interstellar
   (section 4). [design]
5. A branch-light sign function for the basis product `e_i e_j = s(i,j)
   e_{i xor j}` exists in O(log n) steps, and a verified oracle for it is in
   section 3. It reproduces the recursive formula `(a,b)(c,d) = (ac - d*b,
   da + bc*)` for every n up to 32 and matches the Hamilton product in
   `so4.h` bit for bit. [math, checked by script]

## 2. The Interstellar look and its components

Sources: Thorne, *The Science of Interstellar* (2014), chapters 29-31, cited
by the existing plan; page-level claims are not re-verified here. Press:
IndieWire, Colossal, fxguide, Art of VFX (search snippets only; the IndieWire
page returned a paywall on fetch).

What the accounts state: a physical set with light-print textured "world
line" tubes, digital additions of "additional timelines and the fine threads
of light that wove through the scene", and a digital model layered on the set
to extend it "into infinity". Thorne's construction: the tesseract is a
5D-bulk object whose time axis is unfolded into a third spatial direction, so
a rectilinear lattice of world-lines carries "slices" of the bedroom at
successive times, joined by gravity-carried strands. [pub, snippets; the
physics is Thorne's speculation, as the existing plan already labels it]

Decomposition into renderable components [design]:

| Component | What the viewer sees | Renderable form |
| --- | --- | --- |
| Bulk void | near-black space, no horizon | background near 0, no sky |
| Lattice | straight rectilinear beams in three orthogonal families receding in perspective | periodic distance field of tubes |
| Woven strands | fine bright filaments that braid around and between beams | twisted thin tubes, many per beam |
| Slices | rectangular glimpses of the room at fixed times | quads or textured patches at lattice nodes (deferred) |
| Fog | depth-graded haze; distant beams dissolve to warm-white | exponential extinction along the ray |
| Glow | additive halo, mostly on strands | analytic bloom from march minimum distance |

The user rules out books, rear windows, and wireframes. Wireframe is a line
list drawn over an empty background; the tube field below has thickness,
extinction, and emission, and no line list exists in it.

## 3. Cayley-Dickson arithmetic

### 3.1 Conventions [math]

Dimension n = 2^k. Elements are arrays of n reals; index 0 is the real unit.
The doubling of an algebra of dimension h = n/2 is

    (a, b)(c, d) = (a c - conj(d) b,  d a + b conj(c)),
    conj((a, b)) = (conj(a), -b).

Check against `so4.h`: with the array order (w, x, y, z) = indices 0..3 the
recursion reproduces the Hamilton product coded in `operator*` exactly (50
random integer pairs, script below). The `so4.h` point order (x, y, z, w)
differs only by a permutation of storage.

Other conventions exist: `(a,b)(c,d) = (ac - d*b, da + bc*)` is the one used
here; `(ac - db*, a*d + cb)` and sign-flipped variants give isomorphic
algebras with relabeled units. A test must state its convention.

Structure [math, Baez 2002; Wilmot 2025]: n=2 complex, n=4 quaternions
(associative), n=8 octonions (alternative, non-associative, normed division
algebra), n=16 sedenions (not alternative, contains zero divisors, norm not
multiplicative). Hurwitz's theorem limits normed division algebras to
n = 1, 2, 4, 8.

### 3.2 Basis product as signed XOR [math]

Every basis product is `e_i e_j = s(i,j) e_{i xor j}`, `s = +-1`. The sign
follows from the doubling rule by splitting the top bit `h`. With `i`, `j`
the low parts (below `h`) and `cj = (j == 0) ? +1 : -1`:

| top bits of (i, j) | product sign factor | next call |
| --- | --- | --- |
| (0, 0) | +1 | s(i, j) |
| (0, 1) | +1 | s(j, i) |
| (1, 0) | cj | s(i, j) |
| (1, 1) | -cj | s(j, i) |

Iterating from the top bit down gives an O(log n) loop with no table:

```
int sgn(uint i, uint j, uint n) {        // n = 2^k, returns +1 or -1
  int s = 1;
  for (uint h = n >> 1; h != 0u; h >>= 1) {
    bool bi = (i & h) != 0u, bj = (j & h) != 0u;
    i &= h - 1u;  j &= h - 1u;            // low parts
    if (!bi && bj)      { swap(i, j); }
    else if (bi && !bj) { if (j != 0u) s = -s; }
    else if (bi && bj)  { if (j == 0u) s = -s; swap(i, j); }
  }
  return s;
}
```

Product: `r[i ^ j] += sgn(i, j, n) * a[i] * b[j]` over all i, j: n^2
multiply-adds, the O(n^2) direct method. Structure-exploiting alternatives:
Cariow-Cariowa reduced-multiplication formulas and Lemley (arXiv:2609.11588,
Sept 2026), who reports O(N log N) arithmetic, faster than direct at N >= 16
and about 16x faster at N = 1024 (abstract only; the paper does not address
sign computation in its abstract). For n <= 8 these are irrelevant: direct
products of 16 and 64 multiply-adds are cheaper than any restructuring.

Constant masks for GLSL [math, generated from the loop above]: bit
`i * n + j` set means `s(i,j) = -1`.

- n = 4: `0xC6A0`.
- n = 8: 64 bits, low word `0xACC66A00`, high word `0xB2D8741E`
  (`bit = (i*8+j) < 32 ? lo >> ... : hi >> ...`).

```
// octonion basis sign in GLSL: no branches, two constants
const uint OCT_LO = 0xACC66A00u, OCT_HI = 0xB2D8741Eu;
float octSign(uint i, uint j) {
  uint b = i * 8u + j;
  uint w = (b < 32u) ? OCT_LO : OCT_HI;
  return 1.0 - 2.0 * float((w >> (b & 31u)) & 1u);
}
```

A sedenion mask is 256 bits (eight `uint`); the loop form is preferable there.

### 3.3 Test oracle [math; run result recorded below]

A Python reference (recursive product, the `sgn` loop, and the checks) was
run in the session scratchpad and passed every assertion:

1. Sign loop equals the recursion for every (i, j) with n in
   {2, 4, 8, 16, 32}, and each basis product has exactly one nonzero entry at
   index `i xor j`.
2. Table product equals recursive product on random 16-vectors.
3. n = 4: `i j = k`, `j k = i`, `k i = j`, `i i = -1`, and the full product
   equals the Hamilton formula of `so4.h` on 50 random integer pairs.
4. n = 8: alternativity `x(xy) = (xx)y`, flexibility `(xy)x = x(yx)`, and
   the middle Moufang identity `(zx)(yz) = (z(xy))z` hold on 100 random
   integer triples; a random triple fails associativity.
5. Norm: `|xy|^2 = |x|^2 |y|^2` had 0 violations in 200 random pairs for
   n = 4 and n = 8, and 200 of 200 violations for n = 16.
6. Sedenion zero divisor: `(e1 + e10)(e4 - e15) = 0`. An exhaustive search over
   pairs of two-term imaginary units found 336 such pairs at n = 16 and none
   at n = 8.

The C++ test in the repo should embed items 1, 3, 5 (n = 4, 8, 16), and 6 as
gtest cases in double, with integer inputs so equality is exact. The GLSL
port is tested by running the same cases in a compute shader and comparing
against the C++ product (`gpu_cpu_parity` pattern).

Falsifier for the sign loop: any (i, j, n) where the loop disagrees with the
recursion. Falsifier for the convention: `i j != k` at n = 4.

## 4. How Cayley-Dickson structures produce a visual effect

| Technique | Source | Look | Fit to Interstellar |
| --- | --- | --- | --- |
| Quaternion Julia set, ray-marched distance estimator (3D slice of a 4D set) | Hart, Sandin, Kauffman 1989 [pub]; Quilez notes [pub] | organic blobs, coral, shelled bulbs | poor: fractal surface, no rectilinear lattice |
| Dual-quaternion Julia | Kenwright 2023, arXiv:2303.14827 [pub] | same class as above | poor |
| Octonion Julia / Mandelbrot slices | no verified primary source found; treat as unpublished folklore | similar to quaternion, with 4D slice choices richer | poor |
| Quaternion sandwich `q p q^-1` as domain warp | Hamilton product [math]; use is [design] | smooth helical twist of space | good, for strands |
| SO(4) pair `qL p conj(qR)` as animation | `so4.h` | rigid 4D rotation | good, for slice motion |
| Octonion Fano-plane structure, sedenion box-kites (arXiv math/0011260, title only) | [math] | discrete symmetric structure, no continuous rotation group on R^8 beyond SO(8) | none |
| E8 / Gosset polytope projection to 3D | Coxeter [math] | dense point clouds | none |

Quilez's distance estimator for the quadratic iteration `z -> z^2 + c`
tracks `z` and its derivative `dz` and returns
`d = 0.5 * |z| * log|z| / |dz|` [pub]. For a quaternion Julia set the
derivative recurrence is `dz -> 2 z dz`, one full Hamilton product (16
multiply-adds) plus one square (`z^2 = (w^2 - |v|^2, 2 w v)`, 7 operations)
per iteration. Cost estimate [design, not measured]: 8-12 iterations x about
25 flops x 80-150 march steps x 2.07 M pixels at 1080p is 3-8 GFlop per frame,
1-3 ms on a 20-40 TFLOP/s card at full occupancy and realistically 3-10 ms
once divergence and bandwidth are counted. The estimate needs a measurement
on the target GPU before any budget decision.

Conclusion for octonions: the octonion Julia surface is a 4D slice of an 8D
set, so its look is another bulbous fractal. No source connects octonion
structure to rectilinear lattices. Octonions in shaders would be decoration
unless a specific fractal pass is wanted as a separate scene.

## 5. Techniques for viewing 4D objects

### 5.1 Projections [math, pub]

- Perspective: `p = xyz * d / (d - w)`; implemented in
  `tesseract_geometry`. Cells nearest the 4D eye become large nested cubes.
- Stereographic from the pole `w = 1`: `p = xyz / (1 - w)`; conformal, maps
  great circles on S^3 to circles or lines. Fits Hopf and Clifford-torus
  images; Hanson (2006) uses these for quaternion visualization. Implemented.
- Orthographic: drop `w`. Schlegel diagram: perspective with the eye just
  outside one cell so it contains the rest; the standard image of the 120-cell
  and 600-cell (Coxeter).
- Kageyama (2016, arXiv:1607.01102) shows parallel hyperplane slices of a
  polytope arranged in an oval, with simple and double rotations
  controlled from the keyboard. [pub]

### 5.2 Slicing and 4D ray marching [pub, design]

Slice: the 3D hyperplane `H = { p in R^4 : n . p = c }`, parameterized by an
orthonormal frame `(u, v, s)`. A 3D ray `o + t r` in the frame is the 4D ray
`o4 + t r4` with `o4 = O + M o`, `r4 = M r`, where `M = [u v s]` is the 4x3
frame matrix (columns are frame vectors) and `O` is the hyperplane origin.
Sphere tracing needs a 4D distance field `f(p4)`; the 3D slice's distance
is bounded below by the 4D distance, so step size `f(o4 + t r4)` never
overshoots. [math] Ten Bosch (2020, DOI 10.1145/3386569.3392483) displays
4D rigid bodies "by taking a three-dimensional slice through them", and
Miegakure and 4D Toys use the same. [pub]

Cost: one 4x3 matrix-vector product per ray (setup) plus the 4D field
evaluation per step; the marching loop is otherwise identical to 3D.

Because `M` is any orthonormal frame, an SO(4) rotation `R` of the world equals
the inverse rotation of the frame: `M' = R^-1 M`. So animating the object
under SO(4) and animating the slice frame are one operation, and `so4.h`
already gives `R` from a `(qL, qR)` pair.

### 5.3 4D lighting and depth cues [pub, design]

- 4D lighting: surface normal is the 3-dimensional normal of the sliced
  surface; use the gradient of `f` projected onto `H` (`n3 = M^T grad f`,
  renormalized). Ordinary Lambert plus a point light in the slice works.
  [design; Hollasch 1991 discusses 4D shading in the ray-tracing setting]
- W-depth cue: Hollasch cues wireframe brightness by 4D depth of each
  vertex. Fog keyed to `|w|` (distance of the sampled point from the slice's
  own `w`) generalizes it. [pub]
- Color by the fourth coordinate: hue proportional to `w` on the surface.
  [pub concept, Hanson and Ma; design for the mapping]
- Motion is the dominant cue. He et al. (2023, DOI 10.3389/fpsyg.2023.1180561)
  found that observers distinguish rigid from non-rigid motion of
  hypercubes in VR almost as well as cubes, more so with active head
  movement, and describe a "3 1/2 D perception". No study found ranks
  shading against fog for 4D. [pub]

### 5.4 Rotations in SO(4) [math]

Every rotation is `x -> qL x conj(qR)`. Cases:

| Type | (qL, qR) | Fixed set | Visual reading |
| --- | --- | --- | --- |
| Simple | rotation planes: one angle | a plane pointwise | flat object turns with two axes; a cube "turns inside out" through w |
| Double | two angles | origin only | two slice-scale motions superimposed; tori under stereographic projection roll |
| Isoclinic left | `qR = 1` | none | all points move along parallel Hopf great circles; motion looks uniform, no preferred axis |
| Isoclinic right | `qL = 1` | none | same, opposite chirality |

Isoclinic rotation moves every point at the same rate along Hopf fibers
(each fiber is a great circle of S^3), so stereographic images of fibers are
linked circles (Clifford tori nest), and the motion reads as a smooth
twisting of space. That fits "strands weaving through the void" better than
a simple rotation, whose fixed plane gives a visible axis. [math for the
statement; the reading is design]

Hopf-fibration and Clifford-torus visualizations: Hanson (2006), *Visualizing
Quaternions*; Johnson (2011, popular stereographic Hopf images); arXiv:2003.09236
(double orthogonal projection construction; authors not verified here).

## 6. Recommendations for this renderer

Ranked. Each item: what, why, cost, falsifier.

### R1. Render the scene as a ray-marched hyperplane slice of a periodic 4D beam field [design over pub]

Field: a lattice of thickened 2-planes in R^4. A plane spanned by
`(a_axis, b_axis)` thickened by radius `r` slices to a 1D line in `H`, seen
as a tube. In lattice coordinates `q = fract(p4 / L) - 0.5` with cell size
`L`, the distance to the plane family that omits axes `i, j` is

    d_ij(p) = L * length(vec2(q[k], q[l]))  - r         (k, l = the two omitted axes)

Six pairings of four axes give six families. Keep three or four, chosen so the
slice of a generic `H` shows crossing beams in several directions. Slice
frame `M` comes from the SO(4) rotation of R2; because families are
axis-aligned in R^4 but not in `H`, beams in the 3D image tilt and cross
without being axis-aligned, which is the woven-lattice feel.
Distance is exact per family (lower bound after the `fract` fold), a valid
sphere-tracing bound.

Cost: one `fract`, three `length(vec2)`, and one `min` per family per step;
about 20 ALU ops per step; 60-100 steps at 1080p is in the low
single-digit ms. [design estimate, unmeasured]

Falsifier: render a static `H` with an identity frame and check that a beam
family becomes a regular 3D grid of tubes with radius `r` (the analytic
cross-section); an off-axis `H` must show a different crossing angle,
measured in the captured image. A field that looks like a wireframe (thin
uniform lines on black, no fog gradient) fails the brief.

### R2. Animate an isoclinic rotation of the slice frame, with a slow simple rotation as accent [math, design]

Drive `qL(t) = exp(t * omega_L)` and `qR = 1` (left isoclinic) via `quatExp`
in `so4.h`. Add a second small `qR` term only to break perfect symmetry.
Simple rotations in one plane become a rare event that reads as the slice
passing a beam junction.

Cost: zero per pixel; one 4x4 matrix uniform per frame.

Falsifier: log `|R^T R - I|` per frame (already testable in `so4.h`) and
confirm every point of a probe set moves at equal speed (isoclinic
invariant): the speed spread must be zero to float tolerance.

### R3. Weave strands by a quaternion twist warp of the transverse coordinates [design]

For each beam, replace the transverse offset `(qk, ql)` by a rotation
through angle `phi = k_w * w + k_s * s` (where `w` is the local 4D
coordinate along the omitted direction and `s` the arc length along the
beam), and place `N` thin strands at angular phases `2 pi m / N`:

    // strands: N thin tubes around the beam axis, each a helix
    vec2 t = rot2(k_w * p4.w + k_s * s) * vec2(qk, ql);
    float m = round(atan(t.y, t.x) * N / 6.2831853);         // strand index
    vec2 c = R_h * vec2(cos(6.2831853 * m / N), sin(6.2831853 * m / N));
    float d = length(t - c) - r_strand;                        // helical strand SDF

The quaternion form of the twist is the sandwich `q(w) p conj(q(w))`
with `q(w) = exp(w * axis * k)` for the 3D rotation about the beam axis,
which a shader may write as the 2D rotation above (identical on the
transverse plane). The `round`/`atan` fold is exact only for
`r_strand << R_h`; the resulting distance is a lower-bound estimate that
under-steps near strands, so multiply the step by 0.6-0.8 for safety
[design].

Cost: one `atan`, one `sincos`, one `length` per beam per step; 3-4x the
beam-only field. Restrict the strand evaluation to steps where the beam
distance is below `R_h + margin`, which cuts it to a small fraction of steps.

Falsifier: strands must be continuous (no seam) as `phi` passes `pi`;
sample the SDF across the branch cut of `atan` and require the gap to be zero
to tolerance. A count of strands per cross-section must equal `N` at any `s`.

### R4. Depth cues: fog on the ray and on `|w - w_slice|`, emissive strands, no shadows [pub, design]

- Extinction `T = exp(-sigma * t)` along the ray, with the far color graded
  toward warm white (a look choice; the film's grading is not verified).
- 4D cue: dim by `exp(-kappa * |p4.w|)`, the world-frame w coordinate of the
  sampled point. Under the slice-frame rotation of R2, `p4.w` changes along
  a fixed 3D ray, so strands brighten and fade as the slice turns, the
  4D-depth reading of Hollasch's depth-cued wireframe.
- Glow: accumulate `exp(-d_min / r_glow)` over the march (analytic bloom)
  with no extra pass.

Cost: a few ALU ops per step. Falsifier: a captured frame pair at two `H`
angles must differ in fog structure at unchanged camera pose (else the cue
carries no 4D information); a luminance-only test at fixed `t` must show
monotone decay.

### R5. Keep the existing projected-geometry path for the rare "structure" shot [design]

Stereographic projection of the tesseract's cell structure or a 24-cell,
drawn as thick tubes (not lines), is the best way to show the SO(4) rotation
as an object. Use it as a short interstitial or as the campaign-facing
explanatory view, not as the primary look.

Falsifier: the existing test of `tesseract_geometry` projection continues to
pass unchanged; no shader edit is needed.

### R6. Cayley-Dickson beyond quaternions: not recommended for the primary scene [design]

- Keep `Quat` in `so4.h` as the only algebra in the render path.
- Add the sign-loop product (section 3) to `src/render/tesseract/` only if a
  separate feature needs it, for example a quaternion-Julia or octonion
  scene. The 16 to 64 multiply-add product is not a bottleneck.
- If an octonion feature is built, gate it with the section 3.3 oracle before
  any visual review, and use it for a domain warp only as a debugging
  differentiator: non-associativity (`(xy)z != x(yz)`) makes a
  warp order-dependent, which would break the determinism law of the campaign
  for any state that reaches the game (the visualization stays render-only,
  so this is a caution, not a defect).

Falsifier: if a blind A/B of the R1-R4 look with and without an octonion warp
shows no viewer-detectable difference, the arithmetic is decoration.

## 7. Uncertainty

- The tesseract look description rests on press snippets and Thorne's book,
  not a DNEG technical paper. Confidence in the component table: medium.
  A DNEG or Franklin talk that describes the shading would raise it.
- All cost numbers are estimates from operation counts. No GPU measurement
  was made. They fall to measured values with a timing capture on the target
  card.
- R1 and R3 are this note's design; no published implementation of "slice of
  a lattice of thickened 2-planes" was found. Confidence that it produces a
  lattice with tilting beams: high (it follows from the geometry). Confidence
  that it matches the film's look: medium; a render comparison against film
  stills is the check.

## 8. References

Fetched and read (abstract or page summary):

- Marc ten Bosch, "N-dimensional rigid body dynamics", ACM Trans. Graph.
  39(4), SIGGRAPH 2020. DOI 10.1145/3386569.3392483.
  https://marctenbosch.com/ndphysics/
- Steven R. Hollasch, "Four-Space Visualization of 4D Objects", MS thesis,
  Arizona State University, 1991.
  https://hollasch.github.io/ray4/Four-Space_Visualization_of_4D_Objects.html
- Akira Kageyama, "A Visualization Method of Four Dimensional Polytopes by
  Oval Display of Parallel Hyperplane Slices", arXiv:1607.01102, 2016.
- Marco Cavallo, "Higher Dimensional Graphics: Conceiving Worlds in Four
  Spatial Dimensions and Beyond", arXiv:2103.14627, 2021 (abstract read;
  survey contents not verified).
- Z. He, J. Nguyen, H. Ogmen, S. Nishina, A. Yazdanbakhsh, "Perception of
  rigidity in three- and four-dimensional spaces", Front. Psychol. 2023.
  DOI 10.3389/fpsyg.2023.1180561.
- Harrison Lemley, "Quasilinear multiplication in the real Cayley-Dickson
  tower", arXiv:2609.11588, Sept 2026 (abstract only).
- G. P. Wilmot, "Structure of the Cayley-Dickson algebras", arXiv:2505.11747,
  2025 (abstract only; the sign function is not confirmed to be in it).
- Ben Kenwright, "Dual-Quaternion Julia Fractals", arXiv:2303.14827, 2023.
- Inigo Quilez, "Computing distance to Julia and Mandelbrot sets".
  https://iquilezles.org/articles/distancefractals/

Seen in search results only (not fetched in full; treat as unverified
detail):

- J. C. Hart, D. J. Sandin, L. H. Kauffman, "Ray tracing deterministic 3-D
  fractals", SIGGRAPH 1989, pp. 289-296.
  https://dl.acm.org/doi/10.1145/74334.74363 (a search result quoted the DOI
  as 10.1145/74333.74363; the fetched ACM link uses 74334.74363, use that).
- A. J. Hanson, *Visualizing Quaternions*, Morgan Kaufmann, 2006; A. J.
  Hanson and H. Ma, "Meshview" (Indiana University), for screen-door
  transparency and 4D color cues.
- arXiv:2003.09236, "Synthetic construction of the Hopf fibration in a
  double orthogonal projection of 4-space" (authors not verified).
- O. James, E. von Tunzelmann, P. Franklin, K. S. Thorne, "Gravitational
  lensing by spinning black holes in astrophysics, and in the movie
  Interstellar", arXiv:1502.03808, 2015 (black hole only; no tesseract
  content expected; not re-read here). Also "Building Interstellar's black
  hole: the gravitational renderer", ACM SIGGRAPH 2015 talk,
  DOI 10.1145/2775280.2792510 (title seen only).
- Kip Thorne, *The Science of Interstellar*, W. W. Norton, 2014, chapters
  29-31 (not re-read for page-level claims).
- IndieWire, "Inside the Making of the Spectacular Tesseract in Interstellar"
  (paywalled on fetch); Colossal, "The Visually Stunning Tesseract Scene in
  Interstellar was Filmed on a Physically Constructed Set" (2015); fxguide
  "Interstellar: inside the black art"; Art of VFX interview with Paul
  Franklin. Snippets only.
- J. C. Baez, "The Octonions", Bull. Amer. Math. Soc. 39 (2002), for the
  Hurwitz statement (from memory of the literature; not fetched).
- Cariow-Cariowa reduced-multiplication method for Cayley-Dickson algebras,
  cited via Lemley's abstract; original not located.
- Johnson (2011) Hopf fibration images; Coxeter, *Regular Polytopes*
  (Schlegel diagrams); Moreno and box-kite zero-divisor papers (arXiv
  math/0011260 title seen in search results; not read).
