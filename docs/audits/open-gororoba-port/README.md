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
size 12 and 15 of size 14) under mutual zero-divisor adjacency of 2-blade
zero divisors, against the 15 that open_gororoba's PathionZDGraph.v states as
an Axiom. The 15 matches only the components new at dimension 32; the count
depends on the adjacency convention, so the discrepancy stays open until the
convention of de Marrais's papers is fixed, and Blackhole ports neither
number as an invariant yet.

The design these surveys feed is
[docs/plans/tesseract-quasicrystal-algebra.md](../../plans/tesseract-quasicrystal-algebra.md).
