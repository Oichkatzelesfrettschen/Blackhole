# Tesseract: one Z^4 lattice carrying the 4096-D algebra, its quasicrystal walls, and its zero divisors

Status: design, ahead of implementation. The scene stays labeled SPECULATIVE
(Thorne, The Science of Interstellar ch. 29-31): nothing here claims that
physical space is a quasicrystal or a Cayley-Dickson algebra.

Sources: docs/audits/open-gororoba-port/02-cd-algebra-crates.md (strand
lattice, box-kite octahedra, Theorem 11 copies), 04-papers.md section 4.1
(Boyle and Mygdalas, Spacetime Quasicrystals, arXiv:2601.07769, Ammann-Beenker
from Z^4), and src/render/tesseract/emanation_table.h (closed-form DMZ
predicate).

## 1. The one lattice

The scene is a section of R^4 by a slowly rotating 3D hyperplane (the slice
frame F of tesseractSliceFrame). Every structure below lives on the same
integer lattice Z^4 (cell units), so the slice rotation and the camera move
all of it together.

Three readings of one lattice point n = (n0, n1, n2, n3):

1. **Algebra (exact given the chosen embedding).** n names the basis unit
   e_i of the 4096-dimensional Cayley-Dickson algebra (level N = 12) with
   i = gm(n mod 8), the Gray-Morton index of section 2.
2. **Volume (exact).** The slice shows n where the hyperplane passes near it;
   beams run along the unit steps e_x, e_y, e_z between lattice points.
3. **Walls (exact).** Projected by the Ammann-Beenker projection, n is a
   vertex of the wall tiling when its perpendicular projection falls in the
   octagon window (section 3).

The consequence that makes the parts one structure: a unit lattice step
n -> n + e_j is simultaneously a beam segment in the volume, an edge of the
Ammann-Beenker tiling on the walls, and a single-bit XOR i -> i ^ 2^b in the
algebra, and that XOR is a candidate zero-divisor (DMZ) edge of the strutted
emanation graph. The strand on a beam and the lit edge on a wall are the same
algebraic fact seen through two projections.

## 2. Embedding: Gray-Morton, chosen

Index of n at level 12: per axis a in {0, 1, 2, 3} take k_a = n_a mod 8 and
its reflected Gray code g_a = k_a ^ (k_a >> 1); bit d of g_a becomes bit
4d + a of i.

Chosen over plain Morton because a unit step k -> k + 1 changes exactly one
Gray digit (including the cyclic wrap 7 -> 0, which flips digit 2), so every
unit lattice step is a single-bit XOR. Plain Morton makes 1 -> 2 a two-bit
flip and would leave some beams and tiling edges with no algebraic meaning.

Properties (each gets a test):

- Every unit step along any axis, from every k in 0..7, has
  popcount(i ^ i') = 1, and the flipped bit is 4 d + a.
- Gray codes map each block [0, 2^m) onto itself, so the subalgebra of level
  L < 12 (indices below 2^L) is a sub-box of the 8^4 box: the doubling tower
  32D, 64D, ..., 4096D is a nest of boxes. Hue by level L(i) =
  bit_length(i) makes the nest visible.
- Theorem 11 under this embedding: the primary copy of the level-(n-1)
  structure sits in the level-n box unchanged, and the shifted copy (labels
  with bit n-1 set) is its mirror image across the box's midplane on axis
  (n-1) mod 4 (reflected Gray code), not a translation. The doubling reads as
  a mirror tiling. This replaces candidate 3 of the crates report, which
  assumed plain Morton.
- Bit 11 lies on axis 3 (w), top digit: the lower cell of the strutted table
  (assessor labels lo < 2048) is the half box k_w < 4, and every assessor's
  partner hi = lo ^ X (X = 2048 + S) lies in the other half. Each basis
  unit's zero-divisor partner sits across the fourth dimension, and only a
  tilted slice brings it into view.

## 3. Walls: Ammann-Beenker cut-and-project from the same Z^4

Fixed plane (the octagonal plane of Boyle and Mygdalas section 2): e_j
projects to E_par direction (cos(j pi/4), sin(j pi/4)) and to E_perp
direction (cos(3 j pi/4), sin(3 j pi/4)), j = 0..3. The acceptance window is
the regular octagon pi_perp([0, 1]^4). The wall plane stays at this plane;
only the phason offset moves. A wall plane built from the rotating F instead
would, for the near-identity F the scene spends most time in, project two of
the four e_j to almost zero and draw a square grid with slivers.

Walls occupy the planes the pages used (p4.z = m cell, a sparse hashed subset
of tiles), inset from the beams. On a wall, a point x in E_par shows:

- tiling edges pi_par(n) -> pi_par(n + e_j) for accepted n and n + e_j;
- each edge lit when its single-bit link is a DMZ edge of strut S, warm for
  positive and cool for negative edge sign (the sign of dmzValueByClosedForm),
  a faint unlit line otherwise;
- steps along e_3 that flip bit 11 are the assessor-chord direction and get
  their own color.

Tile lookup: de Bruijn's dual method for the tetragrid: K_j = floor(x .
e_j^par + gamma_j) names a candidate lattice point; the fragment tests the
candidate and its grid neighbors for acceptance (octagon test, 8 dot
products) and draws the edges among the accepted ones. The prototype
measures cost against a 1.5 ms budget for the wall pass.

Phason offset gamma: computed on the CPU in double from the unwrapped eye
position (drift plus camera placement) relative to an integer origin, and
uploaded as the small residual; the wrapped eyeSlice would jump by
pi_perp(v) at every wrap by a lattice vector v, since that projection has no
period. Flying moves gamma, so tiles flip (phason flips) as the eye travels:
the walls change while their local rules stay exact.

Exact: the tiling, the octagon window, self-similarity under 1 + sqrt(2).
Chosen: wall placement and colors. The 1 + sqrt(2) inflation of the tiling
and the factor-2 Cayley-Dickson doubling are different self-similarities and
stay separate.

## 4. Volume: strands are the zero-divisor edges

Today a beam carries a strand when a hash says so. In this design the beam
segment between n and n + e_a (a in x, y, z; the w layer from the slice)
carries a strand exactly when its single-bit link is a DMZ edge of strut S;
the edge sign sets the helix handedness, and the level of the endpoints sets
the hue. Endpoints 0 and S, and pairs (lo, lo ^ S) (the blank strut
opposites), carry none.

DMZ mask: one 16-bit word per index (bit b set when the edge i -> i ^ 2^b is
DMZ, plus a sign bit per b in a second word), 4096 entries, built on the CPU
from dmzValueByClosedForm per strut change (about 49,000 predicate calls) and
read with one texelFetch per beam family per march step. The full table
texture is never needed.

Every drawn strand is one cell long. Under Gray-Morton every unit step is a
single-bit edge, but not conversely: per axis the 8-step Gray cycle uses 8 of
the 12 edges of that axis's 3-cube of digits, so a third of the single-bit
edges join lattice points 3 cells apart and are not drawn, nor are the
multi-bit DMZ edges (most of a full-fill strut), which are chords across the
lattice.

## 5. Box-kites: glyphs anchored at a vertex

A box-kite is the octahedron of one present projective line through vertex
a; its six true vertices a, a ^ S, 2^k, 2^k ^ S, a ^ 2^k, a ^ 2^k ^ S are
non-local in the lattice when S is large. The scene draws a small emissive
octahedron glyph at lattice point a (inset from the beam crossing) when a has
at least one present local octahedron (a, k), its brightness scaled by that
count (N - 2 = 10 possible) and its four sail faces lit. This is decoration
anchored at a vertex; the text of the scene's help says so.

## 6. Dynamics

- SO(4) slice rotation (existing): brings other w layers, and so other
  index bits and the assessor partners, into the section.
- Flight (navigation PR): moves the section through the lattice and the
  phason offset of the walls.
- Strut ride (optional, dwell in seconds): changes S, which rewires which
  beams carry strands and which wall edges light; sky struts give sparse fans,
  mandala struts dense webs.

## 7. Acceptance

Reused from the emanation-lattice work, measured with hidden-window captures
on NVIDIA GL:

- Dark fraction (pixels under 20/255) at record frames 0, 360 and 600 at
  least 85% of main's; guards against the wash the owner rejected.
- Motion: mean consecutive-frame MAE at 10 s within 20% of main's (0.0223 on
  the earlier measurement).
- Long session: LongSessionKeepsTheLatticeLit coverage floor.
- Frame time: gpu_tesseract_ms at 2560x1440 within 2 ms of the 13.95 ms
  baseline.

Tests:

- Gray-Morton: every unit step has a popcount-1 XOR at the documented bit;
  sub-boxes hold exactly the indices below 2^L.
- DMZ mask equals dmzValueByClosedForm exhaustively at N = 5..10 and against
  the closed-form predicate at N = 11 and 12 (the full table build takes 17
  minutes at N = 12 and stays out of CI).
- Ammann-Beenker: acceptance window equals the octagon; accepted points near
  the origin form the known vertex configurations (8-fold star at the
  origin for gamma = 0); inflation by 1 + sqrt(2) maps accepted points to
  accepted points under the Z^4 automorphism.
- Box-kites: for every strut tested, each present line has all 12 edges and
  6 positive, 6 negative (the crates report's N = 5..8 observations become
  assertions).
- Phason offset: continuous across the lattice wrap (no jump when the eye
  crosses a period boundary).

## 8. Order of work

1. Shader-only wall prototype, stills to the owner before any C++.
2. Strip of the page pass lands with the slice-frame and long-session fixes.
3. Navigation: free-fly and 4D slice-rotation keys.
4. This structure: Gray-Morton, DMZ mask, strands, walls, box-kite glyphs.
