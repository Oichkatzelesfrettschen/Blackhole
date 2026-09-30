# open_gororoba port inventory

Read-only surveys of open_gororoba (commit 2b90fe66, GPL-2.0-or-later, same
owner as Blackhole, so translation into Blackhole's GPL-3.0 tree is
permitted) and of the local Cayley-Dickson paper collection, against
Blackhole main at 29fe8ec.

| Report | Scope | Leading result |
| --- | --- | --- |
| [01-rocq-proofs.md](01-rocq-proofs.md) | proofs/theories and proofs/verified, 298 .v files | zero real Admitted; sign-table, box-kite and Wilmot counts become C++ test oracles; no emanation-table theory exists in Rocq |
| [02-cd-algebra-crates.md](02-cd-algebra-crates.md) | Rust Cayley-Dickson crates | closed-form DMZ predicate and tone row extend to N = 11, 12; every strutted table is an edge-disjoint union of box-kite octahedra; strand-lattice embedding |
| [03-physics-crates.md](03-physics-crates.md) | GR, GRMHD, optics, GPU crates | constant-l Kerr torus and MKS azimuth resampler are the top ports; the earlier audit plan has landed |
| [04-papers.md](04-papers.md) | local paper collection | Boyle-Mygdalas spacetime quasicrystals is the one new paper with a strong hook; Koebisu's zero-divisor characterization fails |
| [05-control-usability.md](05-control-usability.md) | every ImGui control | 245 controls: 37 dead on the default path, 95 gated; cut, merge and re-range list |

Cross-report agreement. Reports 01 and 04 enumerated the 32-dimensional
zero-divisor graph independently and both find 22 connected components (7 of
size 12 and 15 of size 14, 294 planes) when every 2-blade plane
span{e_p, e_q} is a vertex and two planes are adjacent when some signed
diagonals multiply to zero (one product order or both gives the same graph).
The 15 of open_gororoba's PathionZDGraph.v is the same relation restricted
to the cross pairs p < 16 <= q (motif_components_for_cross_assessors): it
keeps the 15 strut emanation tables of 14 assessors each and drops the 7
components formed by a sedenion box-kite and its copy shifted by 16.
open_gororoba now states both conventions (motif_components_for_all_planes
for the complete graph) and reads its dim/2 - 1 as the strut-table count.
At dimension 64 the complete graph has 53 components and the cross-pair
graph 31.

The design these surveys feed is
[docs/plans/tesseract-quasicrystal-algebra.md](../../plans/tesseract-quasicrystal-algebra.md).
