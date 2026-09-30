# Audit 02: Cayley-Dickson algebra crates of open_gororoba

Scope: open_gororoba/crates (cd_kernel, algebra_experimental, de_marrais_2000,
gororoba_algebra, pathion_ellip, sign_imbalance, surreal_algebra, fwht,
moreno_1997, cd_spin_bridge, gororoba_view_core, gororoba_view_raster,
algebra_analysis, gororoba_structurable, lattice_filtration, and the crates
found by grep). Compared against the Blackhole port in
src/render/tesseract/emanation_table.h and shader/tesseract_panes.frag.

## Summary: three candidates to replace the flat pages

1. Assessor-strand lattice: Morton-embed the 2^N units in R^4 (N = 12 is an 8x8x8x8 grid); draw assessor chords and single-bit DMZ edges as strands (5.1).
2. Box-kite octahedra: each strutted table is an edge-disjoint union of DMZ/24 octahedra, one per PG(N-3,2) line; draw the local ones with lit sails (5.2).
3. Theorem 11 tiling: the level-n table occurs twice in level n+1 (primary and shifted, both exact); Morton turns that into lattice translation (5.3).
4. Rejected: any 2D table or sign wall, the hyper-fractal and PCA images (not algebra), gororoba_view_* (frame contracts only, Section 3).
5. Correction: the strutted table is K = 2^(N-1) - 2 square, so 2048D is 1022 x 1022 and 4096D is 2046 x 2046 (not 2046 and 4094); emanation_table(dim) is (dim-1) square.
6. Closed form: tone row (O(1) bit surgery) plus four N-iteration sign loops per cell; zero mismatches against the full test at N = 4..12 (1.3).
7. Build time, C++ port, one thread: all 1,023 struts at N = 11 in 120 s; all 2,047 at N = 12 in 17 min (1.4); 256 regimes, 15 full-fill struts at N = 12.
8. de Marrais's M (cdp_signed_product) equals the kernel sign for every pair to N = 8 and 4M random pairs at N = 9..12; the port needs no transliteration.
9. Not run: all Rust code (read only), visual quality of any embedding; hazards H1..H12 in Section 6.
10. Licensing: crates GPL-2.0-or-later (fwht MIT OR Apache-2.0); only third-party origin is de Marrais's published algorithm (Section 6).

## 0. Method and evidence labels

Observed means a program ran in this audit. Inferred means read from code.
Not run means the check was skipped, with the reason.

Observed runs used the Blackhole port header (emanation_table.h) compiled with
g++ (GCC) 16.2.1 -O2 -std=c++23, single thread, 12 logical CPUs present, plus
Python 3 reference code that ports the Rust functions line by line. Scratch
programs live outside the repository and are not committed.

The Rust crates were read, not executed: the emanation tests take minutes in
debug and the audit leaves the tree untouched; the C++ port implements the same
algorithm and was cross-checked (1.3). No de Marrais paper was read; comparisons
use only the numbers the repo transcribes (24 DMZ per box-kite, 168/72 at
pathions, 840/456/168/552 at chingons, Trip counts).

## 1. Strutted emanation table generator

### 1.1 Where it lives

| Function | File (open_gororoba/crates/algebra_experimental/src/emanation/) | Cost | Dimension range |
| --- | --- | --- | --- |
| cd_basis_mul_sign_iter | cd_kernel/src/cayley_dickson/signs.rs | O(log dim) integer ops | any power of two |
| cdp_signed_product (de Marrais M) | cdp.rs | O(log dim) | any; tested against the kernel only at 16, 32, 64 |
| generate_tone_row(n, s) | strutted_et.rs | O(K) | n >= 4, 1 <= s < 2^(n-1) |
| create_strutted_et(n, s) | strutted_et.rs | O(K^2 log dim), 4 sign calls per cell | n >= 4 |
| et_sparsity_spectroscopy / et_regimes(n) | strut_spectroscopy.rs | G-1 tables per level | n >= 4 |
| regime_address(n, s) | regime_address.rs | O(n) | n >= 4 |
| verify_theorem11(n, s) | theorem11.rs | two tables | n >= 4 |
| create_skybox(n, s) | skybox.rs | one table plus 4K label cells | n >= 4 |
| balloon_ride(s, n0, n1) | balloon_ride.rs | tables per level | n >= min level of s |
| emanation_table(dim) (unstrutted) | table_builder.rs | dominated by motif_components_for_cross_assessors | dim >= 16 |
| motif_components_for_cross_assessors(dim) | algebra_analysis/src/boxkites.rs | pairwise within XOR-key buckets | any; see 1.4 |

The strutted generator has no dependence on the graph code: it needs only the
sign function. The unstrutted emanation_table marks a cell as a zero divisor
when the pair sits in a motif component, which requires the O(dim^3)-class
component search; it is not a runtime path above 512.

### 1.2 Sizes and fill counts (observed, C++ port)

K = 2^(N-1) - 2 labels per side; cells off the diagonal and off the
strut-opposite anti-diagonal number K(K-2) (total possible). A full-fill strut
fills all of them. Edges E = K(K-2)/2 (each DMZ cell pair is one undirected
edge). Box-kites are counted per full-fill strut and equal
Trip_{N-2} = (2^(N-2) - 1)(2^(N-2) - 2)/6, which equals DMZ/24.

| N | dim | K | K^2 cells | K(K-2) | E (full fill) | box-kites (full fill) | regimes 2^(N-4) | full-fill struts | box-kites summed over all struts |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 5 | 32 | 14 | 196 | 168 | 84 | 7 | 2 | 8 | 77 |
| 6 | 64 | 30 | 900 | 840 | 420 | 35 | 4 | 9 | 665 |
| 7 | 128 | 62 | 3,844 | 3,720 | 1,860 | 155 | 8 | 10 | 5,425 |
| 8 | 256 | 126 | 15,876 | 15,624 | 7,812 | 651 | 16 | 11 | 43,617 |
| 9 | 512 | 254 | 64,516 | 64,008 | 32,004 | 2,667 | 32 | 12 | 349,377 |
| 10 | 1024 | 510 | 260,100 | 259,080 | 129,540 | 10,795 | 64 | 13 | 2,795,905 |
| 11 | 2048 | 1022 | 1,044,484 | 1,042,440 | 521,220 | 43,435 | 128 | 14 | 22,369,025 |
| 12 | 4096 | 2046 | 4,186,116 | 4,182,024 | 2,091,012 | 174,251 | 256 | 15 | 178,955,777 |

Observed for every strut of every level 4..12: each DMZ count is divisible
by 24, and the number of distinct DMZ counts equals 2^(N-4). The number of
full-fill struts is N+3 (S = 1..7 and every power of two from 8 to G/2).
Fill fraction of the sparsest regime: 0.0118 at N = 10 (S = 257, DMZ 3,048) and
0.0059 at N = 11 (S = 519, DMZ 6,120), and 0.0029 at N = 12 (DMZ 12,264). The Blackhole regimeAddress(n, s)
partitions the struts into exactly the DMZ-count classes at N = 10, 11 and 12
(zero addresses with two counts, zero counts with two addresses).

Memory: the Rust StruttedEtCell (four i32 products, eight usize fields, flags)
is about 100 B per cell, so one N = 12 table is about 400 MB (estimate, from
field sizes; not measured). The port stores int16 values: 8.4 MB at N = 12.
|value| = lo_r ^ lo_c < G <= 2048, so int16 holds every level to 15.

### 1.3 Closed-form GPU evaluation of one cell

The port evaluates dmzValueByClosedForm(dim, x, a, b) from four sign calls
of cdBasisMulSign, an N-iteration integer loop each (48 iterations at
N = 12). The magnitude conditions of the full test hold identically because
hi = lo ^ X, so the decision is the sign condition alone.

Observed: closed form equals the full magnitude test in every cell of every
strut at N = 4..9 (zero mismatches) and in 200,000 random cells at each of
three struts at N = 10, 11, 12 (zero mismatches).

The tone row is also closed form (observed: 236,150 positions at N = 5..12,
zero mismatches), which removes the last table lookup. With h the index of
the highest set bit of S, K/2 = G/2 - 1, and position i:

    j = (i < K/2) ? i : K - 1 - i
    v = j + 1
    c = ((v >> h) << (h + 1)) | (v & ((1 << h) - 1))     // insert a 0 at bit h
    lo(i) = (i < K/2) ? c : (c ^ S),   hi(i) = lo(i) ^ X, X = G + S

Position of a label lo (inverse) is the same bit surgery in reverse. A cell
(r, c) is then evaluated in about 100 integer operations with no texture.
The mirror position K-1-r holds lo ^ S (the strut opposite), and the row and
column pair (r, K-1-r) is the blank anti-diagonal.

The port's texture bake is unaffected by level: R16I of 2046 x 2046 is 8.4 MB
at N = 12. Only EMANATION_RENDER_LEVEL and the density-mip size (512 pad at
level 10; 2048 pad at level 12) change.

### 1.4 Build time and the N = 12 run

Observed, C++ port, every strut of the level, single thread:

| N | time all struts | per strut |
| --- | --- | --- |
| 8 | 0.5 s | 0.004 s |
| 9 | 4.1 s | 0.016 s |
| 10 | 16 s | 0.030 s |
| 11 | 120.5 s | 0.118 s |
| 12 | 1,023 s (17 min, with other load on the machine) | 0.5 s |

The N = 12 run (all 2,047 struts) finished: 256 regimes, 15 full-fill struts,
every DMZ count divisible by 24, closed form equal to the full test on 200,000
random cells at each of three struts, and each of the 256 DMZ counts belongs to
exactly one regime address. Box-kites summed over all struts: 178,955,777.

Rust path: not run at N >= 8. The algorithm scales identically (the same
O(K^2 log dim)); the limit is memory (about 400 MB per table at N = 12,
estimate) and the Option cell layout, not correctness. The unstrutted
motif_components_for_cross_assessors is the wall: it tests pairs inside
XOR-key buckets, so the pair count grows about 8x per level; the repo marks
its own dim-256 diagnostic test as "O(256^3): 15-30s" and ignores it in the
default run. Scaling from that note gives on the order of a day at 4096
(estimate). Use the strutted path only.

## 2. Inventory of every CD-structure module

Legend: max dim = largest dimension the code supports without redesign;
L2048 / L4096 = whether it scales there (Y, N, or partial).

### 2.1 cd_kernel (GPL-2.0-or-later)

| Module | What it computes | Cost | Max dim | L2048 | L4096 |
| --- | --- | --- | --- | --- | --- |
| signs.rs cd_basis_mul_sign (recursive) and _iter | sign of e_p e_q = s e_(p^q) | O(log dim) | any | Y | Y |
| signs.rs SignTable | bit-packed dim x dim sign table | O(dim^2 log dim) build, dim^2 bits | any | Y (0.5 MB) | Y (2 MB) |
| signs.rs sparse_multiply | sparse products by sign lookup | O(nnz_a nnz_b) | any | Y | Y |
| arith.rs cd_multiply / _into | dense product by doubling recursion | O(dim^2), allocating | any | slow | slow |
| simd.rs | specialized products | O(dim^2) | 256 | N | N |
| associator.rs, fast_associator.rs, soa_cache.rs | associator norms, workspace reuse | 4 products per triple | any | Y | Y (about 48 KB workspace) |
| zero_divisors.rs | find_zero_divisors (dense), sign-table search, 3-blade search | O(dim^3) or worse | practical <= 64 | N | N |
| predicates.rs | Moreno structural predicates | O(dim) each | any | Y | Y |
| signature.rs | split-signature sign variants | O(log dim) | any | Y | Y |
| sedenion.rs, trigintaduonion.rs, cariow_factorization.rs, turboquant/ | fixed 16D/32D products, multiplication counts, quantization | O(dim^2) | 16, 32 | N | N |

The sign function is the scalable primitive. It has a recursive and an
iterative form; both were checked equal to the explicit doubling product
(hazard H1).

### 2.2 algebra_analysis (GPL-2.0-or-later)

| Module | What it computes | Max dim | L2048 | L4096 |
| --- | --- | --- | --- | --- |
| boxkites.rs find_box_kites | 42 assessors, 7 box-kites | 16 only (returns empty otherwise) | N | N |
| boxkites/cross_assessors.rs | cross pairs (lo, hi), integer-exact diagonal zero products | any | pair count 1.05M | 4.2M |
| boxkites.rs motif_components_for_cross_assessors | ZD graph components, XOR-bucket pruning, rayon | tested to 256 | N (impractical) | N |
| boxkites/strut_table.rs | canonical A..F octahedron labeling | 16 | N | N |
| boxkites/face_sign_census.rs, imbalance.rs | face sign patterns, frustration ratio | tested to 256 | N | N |
| projective_geometry.rs | PG(m,2) points and lines; components <-> points bijection | 64, 128 tested (31 and 63 components) | Y for the geometry, N for the component side | same |
| graph_projections.rs | invariant suite; P_ZD_hypothesis is refuted at 64+ by its own header | 64+ | N | N |
| sky_mapping.rs | project_sky_to_basis (a 3D sky vector onto lattice vectors) | 1024 | Y | Y (not de Marrais's Sky) |
| codebook/, spectral_dimension.rs, ... | lattice codebooks, spectra | dense linear algebra | N | N |

### 2.3 algebra_experimental (GPL-2.0-or-later), emanation/

All of Section 1 plus, at the levels the code was built for (n = 4, 5, in
tests to n = 7 or 8): trip_sync.rs, sail_classification.rs, sail_loop.rs,
tray_racks.rs, twist_transitions.rs, delta_transition.rs, brocade.rs,
lanyard*.rs, quincunx.rs, three_viziers.rs, semiotic.rs, ss_kernel.rs,
fano_duality.rs, ct_boundary.rs. These operate on the 7 sedenion box-kites
(dim 16) and do not generalize as written: they consume BoxKite from
find_box_kites. Their content (octahedra, faces, sails, PSL(2,7) twist graph)
is recovered at every level from the strutted table by Section 4.2.

Other CD-dimension modules: cd_tower_violations.rs (alternator counts, 2^4 to
2^13), leech_pathion.rs (24D Leech lattice into 32D and up), voudon_stabilizer.rs
(256D GPU search for ZD cycles), sedenion_subalgebras, and physics lanes
(quark_sector, neutrino_sector, e10_octonion). novel_algorithms/ holds
speculative code (sedenion_raytracer, spin_emanation_routing); none is reusable
for the scene.

### 2.4 The other listed crates

| Crate | Content | Use for the scene |
| --- | --- | --- |
| de_marrais_2000 | 7 O-trips, 28 S-trips, 42 assessors, Production Rule 1, 168 = 42 x 4 (Rocq-mirrored constants) | hazard H8: oriented triples only |
| gororoba_algebra | re-export of cd_kernel; construction/ (Clifford, octonion geometry, Leech, E8 roots, chingon); gpu/dimensional.rs Monte Carlo APT census at 2048-4096 | dimensional.rs samples triangles of ZD graphs at 2048-4096 (CUDA feature); no geometry output |
| pathion_ellip | Kerr shadow modulated by 32D pathion ZD spectrum (Carlson integrals) | physics coupling of interest to the black-hole renderer, dim 32 only; not part of the lattice |
| sign_imbalance | signed graph from psi signs, Harary-Zaslavsky imbalance, 16D field on a 3D lattice, algebraic lensing | 3/8 imbalance attractor is a 16D claim; not a level-12 structure |
| surreal_algebra | CD algebra over surreal dyadics (exact i128 arithmetic) | control lane; none |
| fwht | Walsh-Hadamard transform, structured rotations (MIT OR Apache-2.0) | Walsh characters are the natural 4D projection of GF(2)^N labels (Section 5.2 alternative) |
| moreno_1997 | Moreno's theorems as dense matrices (T operator, annihilator decomposition) | O(dim^3) and worse; none |
| cd_spin_bridge | 16D imbalance to qubit decoherence | none |
| lattice_filtration | 16D fields on a 3D lattice, collision storms, "Lambda_2048 to 256" survival depth | narrative only; no CD generator |
| gororoba_structurable | Jordan-pair scaffolding | none |
| gororoba_view_core, gororoba_view_raster | see Section 3 | none |

## 3. gororoba_view_core and gororoba_view_raster

view_core (210 lines) holds frame contracts (GridShape3d, VolumeFrameF32,
SliceFrameRgba8, ParticleFrame, ViewerFrameSource) with no CD content.
view_raster (300 lines) rasterizes CPU frames to ARGB: volume slices with
Viridis/Inferno/Turbo tables, RGBA blits, autofit-XY particles, and
render_hyper_fractal_to_argb, a log-scaled |sum_{n=1..7} exp(i n pi/4)/(z^n + 0.1)|
map that contains no CD algebra. gororoba_cli vis_hyper_artifacts calls it and
draws "sedenion_zd_pca" from 1000 random disk points; neither depicts the
algebra. Reusable for a raymarched 4D field: nothing. Do not port.

## 4. Geometric and graph structures, per dimension

Notation: m = K/2 = 2^(N-2) - 1 strut-opposite pairs; X = G + S. Every
count below for the ET graph is observed at N = 5..11 in the table of 1.2 or
derived from it.

### 4.1 Assessors, strut pairs, the XOR lattice

Basis index i in [0, 2^N) is a vertex of the N-cube; the product index is the
XOR, i.e. vector addition over GF(2)^N. At N = 4 this is the tesseract itself:
the 16 sedenion units are its 16 vertices. An assessor (lo, hi) is a chord
from a vertex of the lower cell (lo < G) to a vertex of the upper cell. In
strut S all K assessors share the displacement label X = G + S (hi = lo ^ X),
so the K assessors of a strut are K parallel chords of the N-cube.

Vertices per strut: K assessors in m antipodal pairs (lo, lo ^ S). Zero-divisor
planes are spanned by e_lo and e_hi; the diagonals e_lo +- e_hi are the unit
zero divisors (4 per assessor: 24 per box-kite).

### 4.2 The table as a graph: cross-polytopes and octahedra

Observed, N = 5..8, several struts each (edge sets exhaustive):

- The DMZ relation is symmetric; each nonblank cell pair is one undirected edge.
- Full fill: degree K-2, E = K(K-2)/2, triangles 8 C(m,3): the 1-skeleton
  of the m-dimensional cross-polytope (orthoplex) K_{2,2,...,2}, with the strut
  opposites as antipodes. Repo code names the same graph (k2_multipartite_part_count,
  cosmology_core orthoplex_crystal). m = 7 at N = 5 (the heptacross), 255 at N = 10,
  1023 at N = 12.
- Sky struts: a subgraph of that skeleton. Sparsest example: N = 5, S = 9 has
  degrees {4 x 12, 12 x 2}, 36 edges, 24 triangles = 3 octahedra sharing one
  strut axis (the two degree-12 nodes are a strut pair); N = 6, S = 17 is 7
  octahedra; N = 7, S = 33 is 15; N = 8, S = 65 is 31.
- Box-kites at every level. Points of PG(N-3,2) are the m strut pairs, and a
  line is a triple of pairs whose lo labels XOR to 0 or S. For every strut tested
  (N = 5..8, 13 struts), (a) each line is either all 12 octahedron edges present
  or none, (b) the present lines number DMZ/24, (c) every edge lies in exactly
  one present line, and (d) each present octahedron has 6 positive and
  6 negative edges. So each table is an edge-disjoint union of DMZ/24 octahedra
  indexed by projective lines. This is the generalization that find_box_kites
  (dim 16 only) lacks.
- Sails: an octahedron has 8 triangular faces; the emanation code identifies
  2 zigzag (all opposite-sign edges) and 6 trefoil faces, and 4 faces whose L-indices form
  an O-trip ("sails"). Hazard H6 lists the conflicting definitions.

Counts per full-fill strut are in 1.2 (vertices K, edges E, octahedra
Trip_{N-2}). Total ZD graph over all struts is the last column of 1.2. Fan
size in the sky regime is DMZ/24 with DMZ from Section 1.2 (N = 10: from 127
octahedra at the sparsest regime up to 10,795).

Local versus non-local edges (the falsifier for any embedding). An edge
(a, b) carries the emanation label a ^ b. Observed fraction of edges whose
label is a single bit:

| N, S | edges | single-bit-label edges | fraction |
| --- | --- | --- | --- |
| 6, 1 | 420 | 56 | 13.3% |
| 6, 9 | 228 | 54 | 23.7% |
| 6, 17 | 84 | 34 | 40.5% |
| 7, 1 | 1,860 | 150 | 8.1% |
| 7, 33 | 180 | 68 | 37.8% |
| 7, 57 | 756 | 104 | 13.8% |

For S = 1 the count is (N-2)(K-2)/2 (56 at N = 6, 150 at N = 7; bit 0 is
blocked because lo ^ 1 is the strut opposite), so the fraction is (N-2)/(K-2):
about 0.5% at N = 12 (about 10,200 of 2.09M edges). Other full-fill struts
were not counted. In a sky strut the fraction is far higher. The single-bit edges are the only ones
that stay short under a Morton embedding; the remaining edges are chords
across the lattice.

### 4.3 Nesting across levels: Theorem 11, skybox, meta-fractal

Observed (C++ port). The level-n table of strut S is the primary copy in the
level-(n+1) table, in tone-row order the four corner blocks with the central
cross removed (primaryCopyPosition): zero mismatches (DMZ pattern and signed
values) for 12 cases over n = 8..11 with sky and full-fill struts.
New finding, previously unverified in the port: the shifted copy (labels
lo + G_old) is also an exact copy: zero mismatches at n = 6..10 for 7 cases.
Each level therefore contains two copies of the previous one, related by
flipping bit (n-1) of every label, plus two extra labels (G_old and
G_old ^ S), which are the skybox label lines (skybox.rs: G x G grid with
S-assessor lines on all four sides). The remaining cross-block cells (the
central cross) carry the growth from 2x to 4x per level.

DMZ growth is 4x per level (259,080 to 1,042,440 to 4,182,024 for full fill).
Regimes double per level (2^(N-4)); Blackhole regimeAddress classifies them
exactly through N = 12 (observed). The repo's verify_four_corners compares
Option presence, which is true for every off-diagonal cell, and compares
unmapped positions; it does not test Theorem 11 (hazard H9).

Balloon ride (fixed S, rising N): mandala and generator struts stay full
fill; sky struts gain one address bit per level.

### 4.4 Fano planes, Steiner triple systems, trip counts

Imaginary units 1..2^N-1 with lines {a, b, a^b} form PG(N-1,2), a Steiner
triple system; each line is a quaternion subalgebra. Trip_N = (2^N-1)(2^N-2)/6:
N = 3: 7 (the Fano plane, the O-trips of de_marrais_2000/trips.rs), 4: 35,
5: 155, 6: 651, 7: 2,667, 8: 10,795, 9: 43,435, 10: 174,251, 11: 698,027,
12: 2,794,155. The box-kite lines of 4.2 are the PG(N-3,2) quotient by the strut.

### 4.5 Other objects

- Sign-function pattern (psi): a dim x dim self-similar bit image, 16.7M bits at
  N = 12; as geometry it is the rejected flat wall, as a handedness texture on
  strands it costs one sign call.
- 4D polytopes from unit sets: {+-e_0, +-e_a, +-e_b, +-e_(a^b)} is a 16-cell in
  the span of any quaternion line, and the Hurwitz set makes a 24-cell. The
  repo has the sets (hurwitz_1898, octonion_geometry.rs) but no projection to
  R^4; that map is a design choice (5.2).
- Twisted Sisters (PSL(2,7) graph on the 7 sedenion struts, twist_transitions.rs)
  and the Hjelmslev net (tested at 64 and 128) are level-specific.

## 5. Proposals for the raymarched SO(4)-sliced field

Common setup. The scene marches a 4D field over a period lattice (cell size,
strands along beams) and slices it with a rotating hyperplane. Each proposal
places CD structure as strands and cells inside that field so a slice rotation
moves it and the camera flies through it. No proposal uses a table texture at
march time.

### 5.1 Candidate 1: assessor-strand lattice (rank 1)

Geometry. Level-N structure of a strut S is a graph on K assessor vertices.
Draw (a) each assessor strand: capsule from p(lo) to p(lo ^ X), radius r0;
(b) each DMZ edge with single-bit label 2^b: a helical strand from
p(lo) to p(lo ^ 2^b), color hue by b, handedness by the edge sign (edge sign
is sgn(UL) sgn(LR), one of the four sign calls already computed).

Embedding p (design). Morton interleave, low bit first: bit b of the index
goes to axis (b mod 4) at binary weight 2^(b div 4). Then
- indices < 2^n fill a box, level n-1 is a half box, and level 12 is 8x8x8x8;
- XOR by 2^b flips one lattice digit: a hop of 2^(b div 4) cells along axis
  (b mod 4), so single-bit edges are short (1, 2, 4 cells for b in 0..3, 4..7,
  8..11), and bit groups map to scales, which is the "nesting as scale";
- edge lengths beyond single-bit labels are long chords and are not drawn.

Vertex and edge counts drawn per strut. Vertices K (up to 2,046). Single-bit
edges about (N-2)(K-2)/2 = 10,220 at N = 12 for S = 1 (Section 4.2). Not
the 2.09M full edges.

GPU cost. Per lattice cell: Morton decode of the cell to index i (bit
operations); membership test i != S, i < G, lo(i) from the inverse of the
closed form in 1.3; the N-2 single-bit neighbors each need one DMZ predicate
(4 sign loops of N iterations; about 600 integer ops at N = 12). Neighborhood
of 2x2x2x2 cells makes the march step about 10^4 ops: too slow inline. Bake
instead one 16-bit mask per index (bit b set when the edge to lo ^ 2^b is
DMZ): 4,096 x 2 B = 8 KB, a single texelFetch per cell, built on the CPU in
about 0.5 s (one strut) and rebuilt when the strut changes. This replaces
the 8.4 MB table texture by 8 KB.

Which edges are non-local: all with label popcount >= 2 (99.5% of a
full-fill strut at N = 12); these are the price of the embedding and are
omitted. Falsifier for the embedding: if the drawn strands read as isolated
segments with no visible octahedral clusters, use candidate 2 to add the
cluster faces.

Reading while flying. Strand length spans 3 octaves (1, 2, 4 cells); the
camera drifts through the hierarchy, hue by bit group keeps the octaves
distinct, and the lattice slice rotation shears which strands lie in the
hyperplane (an edge along a hidden axis appears as a moving dot).

### 5.2 Candidate 2: box-kite octahedra on projective lines (rank 2)

Geometry. A present projective line {a, b, a^b (or ^S)} is one octahedron:
6 vertices (assessors) at p(lo) or at the chord midpoint (p(lo) + p(hi))/2,
12 edges, 8 faces. Emissive faces on the 4 sails, dark or fog on the 4 others;
the 6 positive / 6 negative edge signs give the zigzag / trefoil coloring.
The strut axis (3 pairs) is drawn as the three long diagonals.

Local octahedra. Lines through vertex a with second point 2^k: N-2 octahedra
per vertex (N = 12: 10). Each is present or absent as a unit (observed
all-or-nothing, 4.2), so presence needs one DMZ predicate, cached in the same
16-bit mask as candidate 1: octahedron (a, k) is present exactly when the
single-bit edge a to a ^ 2^k is DMZ. Its 6 vertices are a, a^S, 2^k, 2^k^S,
a^2^k, a^2^k^S, all closed-form index arithmetic.

Sky regime. The sparse fan (3, 7, 15, 31 octahedra sharing one strut at
N = 5..8; 127 at N = 10) is a bundle of octahedra around a single axis; it
gives the scene a visible difference between mandala (dense) and sky (fan)
struts, with the regime address driving fan size.

Sizes. Full-fill octahedra per strut: 10,795 (N = 10), 43,435 (N = 11), 174,251
(N = 12); all levels summed 22.4M at N = 11. The scene cannot draw these, and
does not need to: the local subset is N-2 per drawn vertex.

Alternative projection to try if Morton clusters look clumped: a linear map
GF(2)^N to GF(2)^4 by four Walsh rows (fwht crate), which sends each label to a
tesseract vertex and folds the lattice 2^(N-4) to 1; this is a design
alternative, not run.

### 5.3 Candidate 3: Theorem 11 translation tiling and regime density (rank 3)

Geometry. Under the Morton embedding, flipping bit (n-1) is a translation by
2^((n-1) div 4) along axis (n-1) mod 4. Theorem 11 (primary + shifted copies,
Section 4.3) then says the level-(n+1) structure is the level-n structure
tiled twice by a lattice translation, plus two label-line strands and the
central-cross edges. Levels 5..12 are a sequence of doublings of one box along
axes 0, 1, 2, 3, 0, 1, 2, ...: a self-similar 4D tiling.

Rendering. Density field D(cell) = fill fraction of the regime at the
camera's current level (regimeAddress gives the class in O(N); the fill
fraction per class is a 2^(N-4)-entry table, 256 floats at N = 12). Multiply
strand emission by sqrt(D) so a sparse sky regime reads as a thin web and a
mandala strut as a dense one. Zoom moves through levels by clipping the
active box to 2^n cells; the port's emanationExpand becomes a pure bit
operation.

Cost. One address computation per march step (about 12 shifts), 256-entry
table. No new geometry, so it composes with candidates 1 and 2.

Falsifier. If the two copies are not visibly the same pattern at translation
2^((n-1) div 4), the DMZ pattern of a Morton box is not translation
invariant; Section 4.3's zero-mismatch check is in tone-row order, not in
lattice position, so this must be verified in the shader-side lattice
coordinates before commit (not run).

Not proposed: the sign table folded to 4D (a cross-hatch again); 16-cell or
24-cell glyphs per quaternion line (2.79M lines at N = 12, and the R^(2^N) to R^4
map is undefined in the source); the 16D density fields of sign_imbalance and
lattice_filtration (not tied to levels 5..12).

## 6. Correctness hazards and known differences

H1. Doubling formula. cd_kernel and the port use (a,b)(c,d) = (ac - d*b,
da + bc*), conj(a,b) = (a*, -b). Observed: the sign loop equals the explicit
doubling product for every pair at dim 16, 32 and for 600 and 300 random
pairs at 64 and 128; the recursive cd_basis_mul_sign and the iterative form
agree in the Rust tests. Variants (ac - db*, a*d + cb) are isomorphic with
relabeled units; a test must state its convention.

H2. cdp_signed_product (de Marrais's M, "LotusScript") vs the kernel sign.
Observed: identical for every pair up to N = 8 (dim 256, 65,536 pairs) and
4,000,000 random pairs each at N = 9, 10, 11, 12. The Rust tests check only
dims 16, 32, 64. The port uses the kernel form, so it carries no
transliteration.

H3. Indexing. Tone-row positions are 0-based in code, 1-based in de Marrais's
prose; the blank anti-diagonal is r + c == K - 1. The port matches the code.

H4. Table size documentation. algebra_experimental/src/emanation/mod.rs says the
table is (2^n - 2) square; table_builder.rs and types.rs build and document
(dim - 1) square. The strutted table (strutted_et.rs) is K = G - 2 = 2^(n-1) - 2.
Three sizes coexist: 2^n - 1, 2^n - 2 (documentation only), 2^(n-1) - 2.

H5. "Co-assessor" has two meanings. de_marrais_2000 defines co-assessors as
pairs sharing the XOR key (lo ^ hi) with hi in 9..15 and hi != lo ^ 8;
algebra_analysis defines them as pairs with a diagonal zero product (graph
adjacency). Same key is necessary, not sufficient (strut opposites share a key and
are non-adjacent). The strutted ET uses the second meaning.

H6. "Sail" has three definitions: BoxKite::sails() doc: faces whose edges all
carry "-"; lanyard.rs: 3-cycles of co-assessors with all Same-sign edges;
sail_classification.rs: faces whose L-indices form an O-trip (4 per box-kite,
containing 1 zigzag + 3 trefoil). The strutted-ET sign counts (6 + and 6 -
per octahedron) are independent of the naming.

H7. "Sky" is two things. de Marrais's Sky is a strut S > 8 that is not a power of
two (the code notes that the 2006 abstract says "< 8" while every other source
says "> 8"); sky_mapping.rs "sky" is a celestial 3D vector projected onto
lattice vectors (Claim C-458). The port already uses the first.

H8. O-trip orientation. Observed: de Marrais's oriented triples
(1,2,3), (1,4,5), (1,7,6), (2,4,6), (2,5,7), (3,4,7), (3,6,5) all satisfy
s(a,b) = s(b,c) = s(c,a) = +1 under the kernel convention. sky_mapping.rs uses
sorted triples [1,6,7] and [3,5,6], for which s(a,b) = -1 (reversed
orientation). Do not take chirality from sorted triples.

H9. verify_four_corners (meta_fractal.rs) compares cells with is_some(), which
is true for every off-diagonal cell (DMZ or not), and compares equal
positions in tables of different size; it does not test Theorem 11. Use
theorem11.rs or the port's primaryCopyPosition (observed exact).

H10. Brocade relabeling (brocade.rs): any node can serve as the strut, permuting
U-indices; comparing the port's labels with a literature diagram needs one of
4 relabelings per box-kite.

H11. find_box_kites(dim != 16) returns empty (comment: pathion extension needs a
different assessor definition). The strutted ET removes the need (Section 4.2).

H12. Evidence limits. The repo asserts regime doubling only for N = 4, 5
(tests to 7); observed here through N = 12. No check compares
de Marrais's published tables cell for cell with these tables.

Licensing. open_gororoba is GPL-2.0-or-later, Blackhole GPL-3.0, same owner:
translation allowed. Crate manifests: every listed crate is
GPL-2.0-or-later or workspace-inherited, except fwht (MIT OR Apache-2.0,
compatible with GPL-3.0). No SPDX or copyright headers in the listed crates'
sources. Third-party origins: cdp.rs transliterates de Marrais's published
LotusScript function M (Presto! Digitization I appendix, arXiv:math/0603281);
the port does not use it. cd_kernel simd.rs, soa_cache.rs and lloyd_max.rs
carry "translated from" notes (steinmarder, TurboQuant) with no license text;
they are outside the port set.

## 7. Port order

1. Add the tone-row closed form (1.3) and a per-index 16-bit DMZ-mask baker;
   test against createStruttedEt at N = 8..11 (falsifier: any mismatch); then
   raise EMANATION_RENDER_LEVEL, since the mask replaces the 8.4 MB texture.
2. Add a Morton embedding header and the 4D strand SDF (candidate 1).
3. Add octahedra (candidate 2) from the same mask; extend the all-or-nothing
   test to N = 9..11 with the baker.
4. Verify Theorem 11 translation in lattice coordinates before candidate 3.

Not run: any Rust code; the Walsh projection;
translation invariance in lattice coordinates; all-or-nothing octahedra at
N >= 9; visual quality of any embedding.
