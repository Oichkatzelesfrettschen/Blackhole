# open_gororoba Rocq proof corpus: port survey for Blackhole

Scope: open_gororoba/proofs/theories (137 .v files), open_gororoba/proofs/verified (161 .v files), _RocqProject, extraction/. Compared with Blackhole rocq/, src/physics/, src/render/tesseract/ (emanation_table.h and tests/emanation_table_test.cpp live on the PR branch feat/tesseract-emanation-lattice, not yet on main) and docs/plans/hyperdimensional-projection-research.md.

Method: every .v file listed; Admitted/admit/Axiom/Parameter/Conjecture counted by grep and then classified by reading; the Cayley-Dickson numbers below marked "survey" were recomputed by an independent script (recursive sign function of C1467, exhaustive over basis products) and are not quoted from the corpus. Nothing was built or run against Rocq: no proof was compiled in this survey (`not run`, reason: read-only task, no Rocq toolchain invoked). Compilation status of each theorem is therefore taken from the files' own claims plus the .vo artifacts existing next to them.

## Summary (highest-value items)

1. Whole-corpus Admitted count is 0: every `Admitted` grep hit is comment text ("Zero Admitted"). Unproved content is carried only by `Axiom`/`Parameter` (about 190 lines, most inside `Module Type` interfaces, i.e. hypotheses, not claims) plus 15 postulated gaps in SStructuralGaps.v and 3 postulated ZD-graph facts (PathionZDGraph, C958, CDFidelity).
2. PORT-TEST first: the sign-function stack (C1467 table of 256 signs for dim 16, C1474 fuel adequacy, M3IsAssociator*.v at dim 8/32, C1468 slot-shift) gives an exhaustive oracle for `cdBasisMulSign` in Blackhole emanation_table.h; the existing test only spot-checks 4 products at dim 4 and one prefix property.
3. PORT-TEST: box-kite partition numbers (BoxKite.v, ZDGraph.v, BrownAssessorEquivalence.v, C003/C013/C015/C016/C026): 42 assessors, 7 box-kites of 6, XOR signatures {15,10,11,12,13,14,9} = 8 xor S for strut constant S=1..7, 84 signed / 168 directed ZD pairs, 24 DMZ cells per box-kite (= BOX_KITE_CELLS), 7*24 = 168.
4. PORT-TEST: closed forms C1141/C958: ZD basis-participation graph has dim-2 vertices and (dim^2-6dim+8)/2 edges: 84, 420, 1860 at dim 16, 32, 64. The survey reproduced all three by brute force (see section 3.4); the Rocq statement itself is an Axiom (C958) checked only in Rust.
5. DISCREPANCY: PathionZDGraph.v (Axiom, "15 components at dim 32", reused by C999) is not reproduced by the survey: mutual-ZD adjacency of the 294 unordered assessor pairs at dim 32 has 22 components (7 of size 12, 15 of size 14). The 15 matches only the components new at dim 32. Do not port that axiom as a test oracle without fixing the definition.
6. PORT-TEST: Wilmot counting formulas (WilmotCDStructure.v, C1463): blade count 2^(m+3)-1, H_m = N(N-1)/6 (35, 155), triads C(N,3) (455, 4495), triad partitions 35+60+360, 155+620+3720; cheap `constexpr` asserts at any dimension.
7. PORT-TEST: quantized associator gap (C1134/C1137/C1140, SedenionGapWitnesses.v): |[e_i, e_k, e_(i^dim/2)]|^2 = 4 for all 7 (dim 16) and 15 (dim 32) involution pairs; extends to a dimension-parametric assertion up to dim 1024 by direct sign-function evaluation.
8. PORT-VISUAL: box-kite octahedron K_{2,2,2} (6 assessors, 12 edges, 3 struts, 4 ZD-pair "sails" of 24 directed cells) and the Fano-point to box-kite-signature bijection k -> 8 xor k (G2OctonionAutomorphisms.v, 168 = |PSL(2,7)| = 42*4 = 7*24): a per-strut overlay for the tesseract walls.
9. PORT-PROOF (small): HigherCD.v/C1471 give a uniform CD tower to dim 65536 with associator trilinearity by strict tower lift; the only tower-parametric proof idea worth copying is the CDDoubleFunctor/CDTowerInstantiation pattern. None of it proves anything about strut tables or emanation tables: emanation/strut/sail/DMZ constructions do not appear in any .v file (only the word "strut" in BoxKite.v prose).
10. GR/physics: open_gororoba has no Kerr, Kerr-Newman, geodesic, or horizon proofs (Blackhole rocq/ has 18 files, about 4000 lines, on exactly those). open_gororoba adds ADM Hamiltonian constraint, Painleve-Gullstrand lapse/shift, Brans-Dicke PPN bounds (omega > 43477 Cassini, > 1998 Nordtvedt, > 177 GPB), Bekenstein entropy, energy-condition chain, Ford-Roman QI, Casimir: small, mostly one-line real analysis; PORT-PROOF for PG and energy conditions, SKIP most of the rest.

## 1. Conventions, counts, licensing

- Axiom column: `Ax` = number of `Axiom`/`Parameter` lines; `MT` = the axioms sit inside a `Module Type` (an interface a caller instantiates, so they are hypotheses, not postulated truths). `Adm` is 0 for every file (grep hits were comments) and is omitted below except where a comment mentions it.
- Kernel-check method: most CD facts use `vm_compute` on integer sign tables or `cbv` + `ring`/`lra` on the real-valued records; the C1467/C1468/C1474/M3IsAssociator*.v files use boolean reflection over the recursive sign function `cd_sign_fuel`.
- Licensing: no .v file, and no file in proofs/extraction, carries a Copyright, SPDX or License line (grep over all .v and extraction files, case-insensitive: no hit). The paper-scoped files (Brown1972*.v, Schafer1954.v, Dickson1921.v, WedderburnPrimitive.v, Moreno1997.v, WalkerFermatAlgebras.v, HurwitzTheorem.v, BrownGeneralizedCD.v, SchaferDivAlg16.v, DicksonCDProcess.v) formalize published theorems of third-party authors and cite them; they copy no third-party code, so GPL-2.0-or-later -> GPL-3.0 translation needs no third-party header handling, only citation preservation. Blackhole rules: new files carry no copyright line.
- Blackhole hosting shorthand: `EMT` = src/render/tesseract/emanation_table.h; `EMT-test` = tests/emanation_table_test.cpp (both on the PR branch); `NEW-cd-test` = a new tests/cayley_dickson_oracle_test.cpp (must be registered in the ctest completeness gate); `rocq/CD` = a new rocq/theories/CayleyDickson/ directory (Blackhole rocq/ currently has Prelim, Cosmology, Kerr, Metrics, Geodesics, Compact, Wormholes).

## 2. Per-file index: theories/

Format: file | topic | key content | Ax | verdict. Line counts omitted. Verdict codes: PT = PORT-TEST, PV = PORT-VISUAL, PP = PORT-PROOF, SK = SKIP.

### 2.1 Core Cayley-Dickson (CD) algebra tower

- CayleyDicksonAlgebra.v | CDComplex, CDQuat records via doubling | complex/quaternion norm and commutation identities | 0 | PP (base of any rocq/CD)
- Prelude.v | shared imports and constants (imbalance attractor 3/8) | 0 | SK (project glue)
- Quaternion.v, QuatRotationLaws.v, QuatNormalize.v, QuatTranscendental.v, CDQuatRotationMatrix.v | quaternion rotation = 3x3 matrix, normalize, exp/log/slerp | unit-quaternion sandwich preserves norm | 0 | PP for rotation-matrix equivalence (Blackhole src/render/tesseract/so4.h uses quaternion products; a proof backs its Hamilton product); SK for slerp
- Sedenion.v | CDOct, CDSed by doubling | sed_mul, sed_zd_a/b witnesses | 0 | PP
- OctonionNorm.v | norm, add, neg, associator at dim 8 and 16 | 0 | PP
- OctonionInverse.v, OctonionSandwichNorm.v, CDInverse.v | inverse at dim 4/8, |x v conj(x)| = |x|^2 |v| | 0 | SK (renderer uses no octonion inverse)
- Pathion.v | CDPathion = (CDSed, CDSed), dim 32 | 0 | PP
- HigherCD.v | Chingon 64, Routon 128, Voudon 256, Eriston 512, DekaVoudon 1024, then 2048, 4096, 8192, 16384, 32768, 65536 records with mul/conj/assoc | 0 | PP (record tower; too slow to compute with, see section 3.6)
- CDDoubleFunctor.v | Module Type CD_ALG + functor CDDouble | 15 (MT) | PP (dimension-parametric construction pattern)
- CDDoubleTower.v, CDTowerInstantiation.v | RealBase -> tower instances via the functor | 0 | PP
- CDLinearLemmas.v, CDNegLemmas.v, CDScalarExtension.v, CDFusedBilinear.v | bilinearity of CD product at quat/oct/sed; scalar extension since all structure constants are in {-1,0,+1}; flattened bilinear forms | 0 | SK (proof plumbing; the {-1,0,1} fact is captured by section 3.2)
- CDConjAntimorph.v | conj(xy) = conj(y) conj(x) at all levels | 0 | PP (general statement useful in rocq/CD)
- CDInnerProduct.v | Euclidean inner product, Moreno Lemma 1.3 adjoint identity | 0 | SK
- CDTraceZero.v | ZDs are purely imaginary (Moreno Cor 1.6) | 45 (MT: 33 Axiom + 12 Parameter interface) | SK (interface-heavy)
- CDAssociator.v, SedenionAssociator.v, PathionAssociator.v | associator at dim 4 (zero), 16, 32 | 0 | PT (witnesses feed the gap oracle, section 3.5)
- CDPowerAssociative.v | power-associativity and sed_flexible ((xy)x = x(yx) at dim 16 by cbv+ring, ~22 s, ~2.4 GB) | 0 | PP low value; see 3.7
- CDPropertyTower.v | commutativity lost at 4, associativity at 8, division at 16 | 0 | PT (three one-line asserts)
- CDSignBridge.v, CDSignHalfStep.v, CDSignSection.v | Z-valued cd_sign_fuel <-> R-valued CDOct product; one-step peel lemmas; fixed-dim sections at 8/16/32 | 0 | PT (the recursion is what EMT `cdBasisMulSign` implements; PP the recursion equations)
- SedenionSignBridge.v | ordered basis products needed by the dim-16 gap lane | 0 | PT
- SedenionXorGroup.v | (Z_2)^4 index group; box-kite signatures = 8 xor {1..7}; generators 1,2,4,8 | 0 | PT
- SedenionAlternativityFails.v | integer-arithmetic witness that sedenions are not alternative | 0 | PT (see 3.7)
- SedenionGapWitnesses.v | norm-4 associator witnesses; sed_missing_gap_{1..7}_{9..15} | 0 | PT
- FanoPlane.v | PG(2,2): 7 points, 7 lines, 3 lines per point | 0 | PT + PV
- SymmetricGroup3.v, FiniteBijection.v | S_3 as 6 permutations; CD dimension <-> nacelle bijection | 0 | SK (game-lore of open_gororoba)
- G2OctonionAutomorphisms.v | Fano lines = O-trips; k -> 8 xor k maps Fano points to box-kite signatures; three realizations of 168 (7*6*4 = 42*4 = 7*24) | 0 | PT + PV
- G2StabilizerDimension.v | stabilizer of e_k in Der(O) has dim 8 (14 - 6) | 0 | PP low value
- BoxKite.v | the 42 assessors, 7 box-kites of 6, sizes/total | 0 | PT
- ZDGraph.v | XOR signature uniform per box-kite, 7 distinct | 0 | PT
- PathionZDGraph.v | "15 components at dim 32" | 1 Axiom (pathion_zd_components) | SK until definition reconciled (summary item 5)
- ParityClique.v | edge counts: 2*K_4 = 12 edges (dim 16), 2*K_8 = 56 (dim 32) | 0 | PT only after the parity-clique decomposition is defined precisely (the theorem is arithmetic on K_n; the graph claim is in Rust)
- DeMarraisAssessors.v | 7 O-trips + 28 S-trips = 35 trips, co-assessor relation (A xor B = C xor D), Production Rules 1-3 | 0 | PT + PP (best de Marrais content in the corpus, section 3.3)
- BrownAssessorEquivalence.v | assessors covered by box-kites, box-kites pairwise disjoint, signatures distinct; Brown-de Marrais bridge 168 = 42*4 | 0 | PT
- ZD_Criterion.v | Brown Theorem 7.15 detection of ZD pairs | 0 | PP
- ArchimedeanStratification.v | ZD cross-ratio condition for 2-blade pairs (zd_cross_ratio) | 0 | SK
- HomotopyTransferAssociator.v, M3IsAssociator.v, M3IsAssociatorPathion.v | m3 classification: 210 ordered triples of {1..7} = 42 Fano + 168 non-Fano; associator coefficient nonzero (value +-2) on all 168; pathion signs agree with octonion on {1..7}; 2730 ordered triples of {1..15} | 0 | PT
- WilmotCDStructure.v | counting formulas (blades, H_m, triads, ZD count 1260 / 39060) | 0 | PT
- WilmotRetractionTheorem.v | m3 = Wilmot decomposition; pathion statement only arithmetic 35+252+168 = 455 (comment says "Admitted" but the lemma is `reflexivity`) | 0 | PT for counts; the real theorem is not proved at dim 32
- WilmotPathionRetraction.v | m3 classification over 455 unordered triples of {1..15} at dim 32 | 0 | PT
- MorenoKerLaNonAlternative.v, MorenoSedenionInstance.v | Ker(L_a) for a non-alternative doubly-pure sedenion; concrete sedenion model of Moreno's inner-product interface | 0 | SK
- Moreno1997.v (index), C1538 (Cor 1.6), C1539 (Prop 1.7 L_x skew-symmetric, Ax 18 MT), C1540, C1541, C1542_* (5 files), C1543, C1544, C1546_* (4 files), C1547, C1548, C1549, C1627 | Moreno (1997) ZD theory: Cor 1.6 ZD symmetry, Thm 1.13 H_a quaternion subalgebra, Thm 1.15 decomposition, Thm 1.16 V_lambda dim = 0 mod 4, Cor 1.17 dim Ker L_a = 0 mod 4, Thm 2.9 (ZD iff eigenvalue -2), Thm 2.13 special triples | Ax: C1538 4 (MT), C1539 18 (MT), C1542_VlambdaOrbit 2 (MT) | SK for Blackhole (algebraic structure theory with no drawable or countable invariant beyond the mod-4 dimension); PP only if rocq/CD wants Moreno
- HModuleDim.v, FinDimHModule.v, WedderburnPrimitive.v | dim of finitely generated H-module divisible by 4; Wedderburn primitive algebras | HModuleDim Ax 16 (MT) | SK
- Brown1972.v (index), Brown1972ChapterIII.v (Ax 9, MT), Brown1972ChapterIV.v, Brown1972ChapterV.v, Brown1972ChapterVI.v, Brown1972ChapterVII.v | Brown (1972) zero-divisor structure: norm/trace lemmas, Theorem 4.2/4.3 (quaternion, octonion, sedenion), exponent lane, Lemma 6.10 / Thm 6.11, Thm 7.3 witness, Thm 7.15 fundamental ZD criterion, Appendix C summary | 0 (III: 9 MT) | PP optional; PT via Thm 7.15 witnesses
- BrownGeneralizedCD.v | Brown (1967) generalized CD with gamma parameters (cd_sign_gen, brown_condition_c_fails) | 0 | PP (only place a sign function with a gamma list appears; not needed by EMT)
- Schafer1954.v, SchaferDivAlg16.v | Schafer (1954) CD-process properties (quaternion/octonion flexibility, octonion power associativity, sedenion norm quadratic anchor); Schafer (1945) division algebras of order 16 | 0 | SK
- Dickson1921.v, DicksonCDProcess.v | Dickson (1919, 1921) CD process, eq. numbering | 0 | SK
- WalkerFermatAlgebras.v | reference stub | 0 | SK
- BaezNormedDivAlgebra.v | Bott periodicity Radon-Hurwitz rho(2^k), R/C/H/O only | 0 | PT (Hurwitz table 1, 2, 4, 8 as a 4-line assert)
- HurwitzTheorem.v | composition of quadratic forms only at n = 1, 2, 4, 8; Clifford structure derivation; hurwitz_fails_dim16 via ZD | Ax 6 (MT: gen_count, products_independent, n_is_even, ...) | PT for dim1/2/4/8 identity and dim-16 failure; PP for the odd-n exclusion
- SedenionAlternativityFails.v: see above.
- CDFidelity.v | associator norm Lipschitz continuity (TurboQuant bit allocation) | 2 (wht_preserves_associator postulated) | SK (quantization, unrelated)
- CDFusedBilinear.v: above.
- TightBindingTopology.v | FHS Berry curvature definitions | 9 (postulated chern_integral_linear etc.) | SK
- SStructuralGaps.v | seven structural gaps S1-S7 recorded as axioms (G2 stabilizer = SU(3), Brown 7.14/7.15 abstract, ...) | 15 postulated | SK (a lacunae ledger, not a proof; the honest place to see what is unproved)
- SpatialAlgebra.v | 3x3 symmetric tensor trace/trace-free | 0 | PP (for ADM)
- SU3StructureConstants.v, SU3JacobiFull.v, OctonionStandardModel.v | Gell-Mann structure constants, Jacobi in Z[sqrt 3]; U(1)xSU(2)xSU(3) dimension arithmetic | 0 | SK
- E6CartanDerivation.v, E7CartanDerivation.v, E8CartanDerivation.v, F4CartanDerivation.v | Cartan matrix = Gram of simple roots | 0 | SK (Lie theory; no tesseract link demonstrated)

### 2.2 Exact-arithmetic hardware lane (r300 / g3dvl, unrelated to Blackhole)

- IDCT8EvenOdd.v, IDCT8DP4ExactBound.v, FP24Representable.v, R2VBTransformDP4.v, FloatAxioms.v (Ax 16 MT), FloatQuaternion.v, FloatRealBridge.v, Tanh.v | 8-point IDCT butterfly, DP4 accumulator inside 2^17 exact FP24 window, quaternion rotation over an abstract FLOAT_OPS, tanh/sech lemmas | 0 (FloatAxioms 16 MT) | SK (Mesa r300 driver work; the FLOAT_OPS functor is the extraction pattern Blackhole rocq/extraction/ already has in its own form)
- extraction/ (ExtractQuaternion.v, ExtractFP24Admit.v, extracted_quat.ml/.mli) | OCaml extraction of quaternion multiply | SK

### 2.3 GR / physics / information

- ADM.v | Hamiltonian constraint H = R3 + K^2 - KijKij - 16 pi rho; PG lapse^2 = 1, shift = sqrt(2M/r), gamma_rr = 1 | 0 | PP (section 4)
- ADMAlgebraBridge.v | algebraic York-time correction, sedenion stress-energy | 0 | SK (open_gororoba-specific model)
- Foliation.v | list-of-slices imbalance model | 0 | SK
- WarpShapeFunction.v, WorldlineBound.v | Alcubierre-like tanh shape function, worldline T^(-5/2) integral finiteness | 0 | SK
- Casimir.v, CasimirF4.v | E/A = -pi^2/(720 a^3); F4 Casimir 1/4 | 0 | SK
- EnergyConditions.v | WEC/NEC/SEC/DEC on (rho, p); DEC => WEC => NEC | 0 | PP
- QuantumInequalities.v | Ford-Roman bound negative, tau^-4 scaling | 0 | SK
- BransDicke.v | PPN gamma = (1+w)/(2+w), Nordtvedt 1/(2+w) | 0 | PP
- BekensteinEntropy.v | S = A/(4 l_P^2) positivity/monotonicity, Schwarzschild S | 0 | PP
- ComplexTimeEIH.v | complex-time EIH potential well-posed, Wick contractivity | 0 | SK
- DarkEnergyEOS.v, SpectralDimension.v, HeatKernel.v | thawing w(z), Calcagni d_S = 4 - 2/(1+s), K_{2,...,2} heat kernel | 0 | SK
- FractalMetricPositivity.v | g_uv positive for D_f in (2,3) | 0 | SK
- BinaryEntropy.v, BellCHSH.v, ThreeBodyAngMom.v, CarlsonIntegrals.v (Ax 10 postulated RF/RD/RJ), CardanoEigensolver.v, GF2Algebra.v | Shannon entropy, CHSH 2 vs Tsirelson 2 sqrt 2, cross-product distributivity, Carlson integrals, trigonometric cubic root, GF(2) separation | 0 (Carlson 10) | SK (CardanoEigensolver PP if Blackhole ever needs a proven cubic solver)
- TightBindingTopology.v: see 2.1.

## 3. Per-file index: verified/

Naming: Cnnn is a claim id in open_gororoba's registry. Files are small (9 to 240 lines) except C1471 (592).

### 3.0 Trivial identities (SK for tests: identical statements are covered by Blackhole so4.h unit tests or are textbook)

- Complex: C893, C894, C895, C896, C918 (commutative, associative, norm multiplicative, conj anti-automorphism)
- Quaternion: C897-C907, C919, C920 (associative, norm multiplicative, conj anti-automorphism, re-comm, quadratic identity, imaginary square, Jordan, inverse, non-commutative); C876, C911, C912 (rotation = matrix, norm preserved, composition); C_ConjugateInvolution, C_NormConjugate, C_OctConjInvolution, C_SedConjInvolution
- Octonion: C909, C921 (non-associative), C910_OctonionAlternative + C910_Right_e0..e7 (left alternative; right alternative per basis element)
- Verdict PT for C919/C921/C1007 style asserts as a single "property tower" test (comm lost at 4, assoc at 8, division at 16); SK for the rest. Ax: 0 all.

### 3.1 CD structure facts (dimension 16 and up)

- C001 first non-associativity at dim 8; C002 sedenion ZD + norm failure (|ab|^2 = 0 vs |a|^2|b|^2 = 4); C008/C011/C023/C030/C032/C034 associator nonzero/obstruction/tower-doubling consistency; C908 sedenion ZD; C1007 property loss | 0 | PT (one property-tower test)
- C003 42 assessors / 7 box-kites of 6; C010_ZDGraphDisconnected, C010_ConnectivityObstruction (>= 6 bridge edges), C026 (7 K_6 blocks; note: the theorem proves distinct signatures, not clique-ness) | 0 | PT
- C013 each assessor in 2 of 7 "automorphemes" (3 Fano lines per point); C015 4 annihilating partners per ZD; C014 annihilator dim 4; C005 annihilator geometry; C017 XOR bucket necessary for box-kite membership | 0 | PT
- C016_M3TrilinearSplit 42 scalar + 168 vector = 210; C016_ParityFlips m3 scalar-sector permutation parity | 0 | PT
- C004 |GL(3,2)| = 168; C028 lo-half embedding closed (Aut group prerequisite); C036 K_4 clustering / K_{2,2,2} triangle count (8, and edges 12) | 0 | PT (168, 12, 8) + PV
- C1134 / C1137 / C1140(a,b,c) quantized gap: |[e_i, e_k, e_(i xor dim/2)]|^2 = 4 (dim 16 all 7 pairs, dim 32 all 15 pairs, probes as in file) | 0 | PT
- C1135 box-kite fusion rules: each box-kite has two distinct product signs (7 lemmas, one per kite) | 0 | PV (Ising sigma x sigma = 1 + psi analogy is open_gororoba's interpretation; the sign split itself is checkable)
- C1141 parametric ZD graph counts | 0 | PT
- C958 basis-participation graph: 3 components [dim-2, 1, 1] | Ax 1 | PT with caveat (3.4)
- C958b analytical ZD adjacency generator | 0 | PT
- C957 ZD persists at all dim >= 16 (embedding (x,0) preserves products); C956 non-associativity persists at all dim >= 8; C954 / C955 block-diagonal AVT decomposition and cross-block coupling non-vanishing | 0 | PT for embedding closure; SK for AVT (game-lore)
- C881 GF(2) cubic minimum separating degree in PG(3,2) | 0 | SK
- C882 parity-clique edge counts 12 and 56 | 0 | PT after definition fixed
- C879 dim <-> nacelle bijection; C037/C033/C035/C029/C022/C021/C018/C019/C020/C012/C009/C040/C038/C039/C883/C884/C885/C888 | assorted refuted-claim reformulations, wheels axioms, S_3 democratic form, spectral dimension | 0 | SK
- C1142 XOR involution / scatter-gather duality: j -> i xor j is a bijection (no write collisions in a gather formulation of CD product) | 0 | PT (permutation property of the xor map is what EMT indexing relies on) + PP (10-line proof)
- C1262 flat-band fraction = 1/2 for the CD 16 ZD partner graph (cd16, cd32) | 0 | SK
- C1313 "Thesis 42" arithmetic scaffold; C1363/C1364 halo and homotopy-bridge laws; C959 CHSH classical bound for CD associator correlations; C1133 braid parity preservation (associativity => parity commutes) | 0 | SK
- C1463 arithmetic inventory: 35+60+360 = 455; C(15,3) = 455; H_15 = 35; H_31 = 155; 155+620+3720 = 4495; 42*2 = 84; 84*2 = 168; 105 = 21+36+48; 35+84+84+252 = 455 | 0 | PT (pure integer asserts)
- C1464 imaginary sedenion basis anti-commute: 105 pairs (file checks a representative sample, not all 105) | 0 | PT (exhaustive loop in C++ is cheaper than the proof)
- C1465 Koebisu equal-norm for e_low +- e_high (low 1..7, high 9..15) | 0 | PT
- C1466 contiguous-block subalgebra closure (3 Tang + 3 interleaved octonionic subalgebras closed under sedenion product: 192 products) and a random set is not closed | 0 | PT
- C1467 XOR+sign cocycle: 256-entry table = cd_sign_fuel 5 16 | 0 | PT (primary oracle)
- C1468 slot-shift: 84 ZD pairs at dim 16 stay zero when embedded in slot 0 and slot 1 of dim 32 | 0 | PT
- C1469 / C1470 / C1471 / C1455 associator trilinearity via tower lift, dims 16, 32, 64, 128, 256, then through 65536 | 0 | SK (trilinearity is immediate from bilinearity of the product)
- C1474 fuel adequacy: fuel = log2(dim)+1 equals fuel 100 for all index pairs at each dim (dim <= 32 exhaustive by vm_compute) | 0 | PT
- C1630 / C1635 / C1636 / C1637 / C1638 sedenion-octonion downcast boundary; driver semantics; Cariow 2013 sedenion schedule; r300 witness (e1+e10)(e5+e14) = 0; downcast has no ZD | 0 | PT for the witness (a concrete ZD product as one C++ assert); SK for driver lane
- C1628 / C1629 IDCT lane | 0 | SK
- C999 pathion ZD graph information capacity 15 ln 2 (depends on the disputed 15) | 0 | SK

### 3.2 GR / physics claims

- C868 PG lapse = 1, shift >= 0, gamma_rr = 1; C875 Hamiltonian vacuum (Minkowski H = 0, pure-trace K: K^2 - KijKij = (2/3) K^2); C880 single-slice foliation | 0 | PP
- C869 / C870 / C874 nacelle warp bubble interior flat, modulation distinct, York time vanishes | 0 | SK
- C871 / C872 / C873 Casimir exact cubic scaling, pillar and sphere-in-cylinder finite; C_QIBoundNegative / C_QITauScaling | 0 | SK
- C886-C891 Brans-Dicke gamma deviation = -Nordtvedt, gamma in (1/2,1), monotone; Cassini omega > 43477, Nordtvedt omega > 1998, GPB omega > 177 | 0 | PP (three cross-multiplication lemmas)
- C_WECImpliesNEC, C_WarpEnergyNonpositive | 0 | PP for the chain; SK for the warp part
- C006 / C007 / C025 algebraic anchors named for GW, BH mass, sky data (they prove only octonion distributivity / non-negative norm; the names overstate) | 0 | SK
- C027 D_eff horizon toy; C877 / C878 / C_OverImbalancedSign zero coupling; C892 dichroism 4:7; C914 / C913 TCMT / Fano antiresonance; C915-C917 binary entropy; C931 / C932 orthoplex heat kernel and thawing w(z); C993 Carlson branch-free; C1138 Wick damping; C1233 / C1234 / C1236 Chern sum, valley Chern, flat-band group velocity | 0 | SK

## 4. Cayley-Dickson dimensions 16 through 4096: deep decomposition

Dimension = 2^N, level N = 4 (sedenion, 16), 5 (pathion, 32), 6 (chingon, 64), 7 (routon, 128), 8 (voudon, 256), 9 (eriston, 512), 10 (dekavoudon, 1024), 11 (2048), 12 (4096). Blackhole EMT uses G = 2^(N-1), strut constant S in [1, G), X = G + S, tone row K = G - 2.

### 4.1 What the corpus does and does not contain

- Present: box-kites at dim 16 (BoxKite.v, 7 kites), assessor/co-assessor XOR calculus and Production Rules 1-3 (DeMarraisAssessors.v), Fano/G2/PSL(2,7) cross-links, counting formulas (Wilmot), closed-form ZD graph counts, quantized gap witnesses at 16 and 32, ZD persistence at all dimensions, a record tower to 65536.
- Absent from every .v file: emanation tables (ET), strut constants as a general-dimension notion (only prose "3 struts" and "strut signature = missing low index" in BoxKite.v), "sails", tone rows, DMZ cells, regime addresses, automorphism-group orders beyond the 168 count, box-kites as a theorem beyond dim 16 (dim 32+ ZD content is Axiom or a counting formula). Blackhole EMT and EMT-test already exceed the corpus there: EMT-test asserts K = 510 and 259080 possible cells at dim 1024, DMZ counts divisible by BOX_KITE_CELLS, regime sets {72 x7, 168 x8} at dim 32 and {168 x8, 456 x7, 552 x7, 840 x9} at dim 64, and 2^(N-4) regime addresses. The port direction is therefore corpus -> Blackhole oracles for the lower layer (signs, XOR, counts), not the emanation layer.

### 4.2 Sign function and XOR/Fano closure

- Statement: for basis elements e_p e_q = s(p,q) e_(p xor q), s in {-1,+1}, with s defined by the recursion in C1467 (`cd_sign_fuel`): halves (p,q < h): s_h(p,q); p < h <= q: s_h(q-h, p); p >= h > q: (q = 0 ? 1 : -1) * s_h(p-h, q); both >= h: (q = h ? -1 : s_h(q-h, p-h)).
- Proved: dim 16 table of 256 signs equals the recursion (C1467, vm_compute); fuel adequacy per dim (C1474); dim 32 anti-commutation/unit/xor-range checks (M3IsAssociatorPathion.v, C1468); sign at dim 8 and the pathion-agrees-with-octonion prefix property on {1..7} (M3IsAssociatorPathion.v). Not proved: the sign recursion is the CD product's structure constants for all N (the bridges CDSignBridge/CDSignSection cover dims 8, 16, 32 only); no proof is dimension-parametric.
- Computable oracle: yes. Blackhole EMT `cdBasisMulSign(dim, p, q)` can be asserted against (a) the 16x16 literal table of C1467 (256 values), (b) prefix consistency s_dim(p,q) = s_(dim/2)(p,q) for p,q < dim/2 (EMT-test asserts this only once, dim 16 vs 8), (c) anti-commutation s(p,q) = -s(q,p) for p != q >= 1, s(p,p) = -1 for p >= 1, s(0,q) = s(q,0) = 1, for all dims to 1024 (1024^2 = 1,048,576 pairs, sub-second in C++). Host: EMT-test (extend) or NEW-cd-test.
- Fano closure at dim 8: 7 lines = triples with a xor b = c; 42 ordered Fano triples, 168 non-Fano; associator coefficient in {+2,-2} on all 168 (M3IsAssociator.v: fano_assoc_zero, nonfano_assoc_is_pm2). Survey (dim 8, all distinct nonzero ordered triples): 168 of 210 non-associating; at dim 16 1848 of 2730; dim 32 15960 of 26970; dim 64 130200 of 238266 (survey, not in corpus; basis-level flexibility and alternativity failures are 0 at every dim, see 4.7). Host: NEW-cd-test.

### 4.3 Assessors, box-kites, co-assessor calculus (dim 16)

- Statements (all vm_compute, fully proved, Ax 0): (i) 42 assessors (lo, hi), lo in 1..7, hi in 9..15, hi != lo+8; (ii) they partition into 7 box-kites of 6, pairwise disjoint (BrownAssessorEquivalence.v); (iii) lo xor hi is constant on each box-kite, the 7 signatures are {15,10,11,12,13,14,9} (order of BoxKite.v), all distinct, cover {9..15}; equivalently signature = 8 xor S with S the missing low index; (iv) co-assessors: lo1 xor hi1 = lo2 xor hi2 is an equivalence relation; Production Rule 1: from A^B = C^D, (A^D)^(A^C) = C^D; Rules 2 and 3 in DeMarraisAssessors.v; (v) 35 trips = 7 O-trips + 28 S-trips, all with a xor b = c; (vi) 4 annihilating partners per ZD (C015), 6*4 = 24 ZD products per box-kite, 7*24 = 168 directed ZD pairs (= 42*2 signed * 2 directions = 84*2), equals |GL(3,2)|.
- Invariant a renderer can draw or a test assert: yes, concrete numbers 42, 7, 6, 24, 168, signatures. EMT's DMZ cell count per strut at dim 16 is 24 = one box-kite, and BOX_KITE_CELLS = 24; the test `dmzCount % BOX_KITE_CELLS == 0` is the generalization. New assertion: at N = 4 for each S = 1..7, createStruttedEt(4, S).dmzCount == 24 and the tone-row label set {lo} = {1..7} \ {S} (6 labels), with 8 ^ S in {9..15} the sig. Host: EMT-test.
- Picture (PV): octahedron K_{2,2,2}: 6 vertices (assessors), 12 edges, 3 diagonal struts joining strut-opposite pairs (lo ^ S), 8 triangular "sails" (2^3, from C036). Draw the strut-opposite anti-diagonal of the emanation table wall as the three struts and colour the 24 DMZ cells by edge sign (C1135: two channels). The Fano point k -> box-kite 8^k correspondence lets the seven kites be coloured by the seven Fano points.
- Note the sail count 8 comes from C036 (K_{2,2,2} has 8 triangles, 2*2*2); the file's own comment self-corrects an earlier claim of 0 triangles.

### 4.4 Zero-divisor graph counts per dimension

- C958 (Axiom, checked in Rust at 16/32/64): basis-participation graph (vertices e_0..e_(d-1); edge when both appear in a common primitive ZD 2-blade product): components [d-2, 1, 1] with singletons e_0 and e_(d/2)... note the file's vertex set includes e_0 and e_(d/2) as the two singletons; missing edges within the giant are (i, i xor d/2), count d/2 - 1; edges (d^2 - 6d + 8)/2. C1141 proves only trivial parametric statements (dim/2-1 = 7, 15, 31, 63, 127 and arithmetic at 16/32/64: 84, 420, 1860; the "for all dim" edge formula is not proved).
- Survey, brute force over all (e_i +- e_j)(e_k +- e_l) = 0 products with i,j,k,l >= 1 using the C1467 recursion: vertices 14/30/62; edges 84/420/1860 = (d^2-6d+8)/2 (confirms C958 at 16, 32, 64); signed assessors (i,j,s) 84 / 588 / 3036; unordered assessor pairs {i,j} 42 / 294 / 1518; unordered ZD pairs 168 / 2520 / 26040 (= 168 * 1, 15, 155; 155 also equals Wilmot's H_2; survey observation only).
- Assessor adjacency components (two assessors adjacent when they multiply to zero): dim 16: 7 components of size 6; dim 32: 22 components (7 of size 12, 15 of size 14); dim 64: 53 (7 of size 24, 15 of size 28, 31 of size 30). Pattern 7, 7+15, 7+15+31 = sum of (2^k - 1), k = 3..N-1, sizes 6*2^(N-4), 14*2^(N-5), 30*2^(N-6) (survey; observed at N = 4, 5, 6, not proved). This is not the "15 components at dim 32" of PathionZDGraph.v/C999.
- Verdict: PT for the closed forms 84/420/1860 and 42/294/1518 (recompute in C++ from cdBasisMulSign, dims 16, 32, 64; dim 128 needs a much larger loop; give it a longer TIMEOUT or skip it); do not encode the 15-component claim. Host: NEW-cd-test. PP: none until C958 is proved; the CD-sign recursion plus a general argument that ZD 2-blades pair (i, j) with (i xor k, j xor k') is the missing step.
- Wilmot ZD count Z_m = N(N-1)(N-3)(N-7)/16 with N = 2^(m+3)-1: 0, 1260, 39060 at dim 8, 16, 32 (WilmotCDStructure.v; multiples of 84 for m >= 1). It counts ordered (b, c, d) with a = bcd, a different object from the 2-blade counts above; no relation to 168/2520/26040 is proved. PT for the arithmetic only.

### 4.5 Quantized associator gap ("friction")

- Statement: for each involution pair (i, i xor d/2), i in 1..d/2-1, with a fixed probe e_k, |[e_i, e_k, e_(i xor d/2)]|^2 = 4 where [a,b,c] = (ab)c - a(bc). Proved at d = 16 for 7 pairs (C1134, C1137, SedenionGapWitnesses.v) and d = 32 for 15 pairs (C1140a/b/c; probe e_1 for pairs (1..15, 17..31)). Not proved for d >= 64 and not proved for all probes; the file titles say "universal quantized gap conjecture".
- Basis-level: the associator of basis triples is +-2 e_(i^j^k) or 0, so the norm squared is 4 or 0, which explains the 4 (the corpus does not state this explanation; it follows from the two-term coefficient a - b in {0, +-2} used by `path_assoc_coeff` in M3IsAssociatorPathion.v). This makes the assertion decidable at every dim up to 1024 in C++ by two sign lookups.
- Renderer use (PV): draw the missing-edge involution pairs (i, i ^ G) as the "gap" chords of a wall (the pairs that are never assessor partners), all with the same weight because the gap is uniformly 2 in norm. Host: EMT-test gains `EXPECT_EQ(assocNormSq(dim, i, k, i ^ G), 4)`; EMT already exposes signs.

### 4.6 Tower-parametric and recursive theorems

- Proved, generic in the level: XOR involution and bijection (C1142); doubling embedding (x, 0) preserves products, hence non-associativity persists for all d >= 8 (C956) and zero divisors persist for all d >= 16 (C957; both only through the concrete witness lifted, the general lift is described in prose and encoded for the levels defined in HigherCD.v); associator trilinearity by strict tower lift for 16 through 65536 (C1469/C1470/C1471, generated code, 592 lines); CDDoubleFunctor (generic doubling with 15 interface axioms) and CDTowerInstantiation (instance to a fixed height); slot shift of ZD pairs into dim 32 slots 0 and 1 (C1468), not into 64+.
- Stated but not proved: dimension-parametric ZD graph shape (C958 Axiom); pathion 15 components (Axiom); WilmotRetractionTheorem pathion m3 classification (statement reduces to 35+252+168 = 455); Brown Thm 7.14/7.15 abstract versions (SStructuralGaps Ax).
- Norm composition failure: proved only at dim 16 (C002: |ab|^2 = 0 while |a|^2|b|^2 = 4 for the Moreno-Froloff witness (e3+e10)(e6-e15) = 0 and the r300 witness (e1+e10)(e5+e14) = 0 of C1637). Higher-dimensional failure follows from ZD persistence (C957); not stated as a norm theorem. Hurwitz (only n in {1,2,4,8}) is fully proved for the positive cases and dim 16 negative, the general odd/other-n exclusion carries 4 interface axioms in HurwitzTheorem.v.
- Checkable at all dims: for a ZD witness w1 w2 = 0 with nonzero w1, w2, evaluate via the sign function at dims 16, 32, ..., 1024 and check that the product is zero and the operands are nonzero. Concrete pair to reuse: (e1 + e10)(e5 + e14) = 0 at dim 16, embedded unchanged at every higher dim (C957, C1637). Host: NEW-cd-test.

### 4.7 Alternativity, flexibility, power-associativity, subalgebras, automorphisms

- Alternativity: octonions satisfy left and right alternativity (C910 and C910_Right_e0..e7, fixed basis element, general a); sedenions do not (SedenionAlternativityFails.v, integer arithmetic). Survey: at the basis-element level alternativity and flexibility hold at every dim 8..64, so any C++ test of failure must use non-basis elements (sums such as ZD witnesses); a basis-only test would pass vacuously.
- Flexibility: holds at all CD levels (Schafer 1954). Corpus proves it for quaternions, octonions (Schafer1954.v) and sedenions (CDPowerAssociative.v sed_flexible, ~22 s, ~2.4 GB by cbv+ring). Not proved for dim >= 32. Verdict SK for a proof port (cost), PT for a numeric flexibility check on random dim-32 elements (float tolerance from the test).
- Power-associativity and the quadratic identity x^2 - t(x) x + n(x) = 0 : CDPowerAssociative.v, dim 16 (1 lemma commented as heavy). PT optional.
- Subalgebras: 7 quaternionic subalgebras of O (H_0 = 7), 35 of S (H_1 = N(N-1)/6 with N = 15), 155 at dim 32; contiguous-block octonionic subalgebras closed (C1466, 6 sets, 192 products). Assertion: the set of 7 triples {a,b,a^b} (Fano lines) in {1..7} and 35 triples at N = 15 (all triples with a xor b = c, since XOR closure gives 35 = 15*14/6 for a^b^c = 0). PT.
- Automorphism/triality: |GL(3,2)| = |PSL(2,7)| = 168 (C004); three realizations of 168 (G2OctonionAutomorphisms.v: 7*6*4, 42*4, 7*24); dim Der(O) stabilizer of e_k = 8 (G2StabilizerDimension.v); Aut(S) preserves 3 octonion sub-algebra embeddings (C028: only the lo-half closure is proved, not the Aut group); 4-level G2 tower statement (g2_four_level_tower) and dihedral D_4 action on box-kite 7 (bk7_rot, bk7_ref; 4 rotations, 2 reflections, orders checked). Triality as such is not formalized (the only "triality" is C036's clustering arithmetic and CasimirF4's epsilon). No automorphism group orders at 32 and above.

### 4.8 Emanation tables, sails, strut constants at 32 through 4096 (comparison)

- Corpus coverage: none (section 4.1). Nearest support for EMT: the co-assessor relation and Production Rules in DeMarraisAssessors.v are the dim-16 special case of EMT's `regimeAddress`/`generateToneRow` (assessor (lo, hi = lo ^ X), mirror pairing lo ^ S). PP candidate: prove in rocq/CD that for every S in [1, G) the pairs (lo, lo ^ X), lo != S, K = G - 2 labels, are closed under the Production Rule 1 transform. That is a short xor argument in the style of DeMarraisAssessors.v and gives EMT a machine-checked closure lemma for all N. Strut counts G - 1 for N = 5..12 are 15, 31, 63, 127, 255, 511, 1023, 2047; tone-row sizes K = G - 2 for N = 4..12 are 6, 14, 30, 62, 126, 254, 510, 1022, 2046.
- EMT-test asserts 259080 possible cells at N = 10. That equals K*(K-2) = 510 * 508, the cells off the diagonal and the strut-opposite anti-diagonal. Assert `totalPossible == K*(K-2)` for N = 4..12 (K=6: 24 = 6*4 matches the one-box-kite count at N = 4 and shows the sedenion table is completely filled, all 24 cells are DMZ).
- Dim 2048 / 4096: corpus mentions them only in C1471 (2048 through 65536 trilinearity lemmas). Computing full tables at N = 11, 12 is 2046^2 / 4094^2 cells (4.2 M / 16.8 M), feasible in C++ (integer sign recursion), infeasible in Rocq. No corpus theorem supports EMT at N = 11 or 12.

## 5. Cayley-Dickson invariant table (for tests)

Source column: R = kernel-checked in Rocq, S = survey recomputation (not in corpus), A = Axiom or Rust-only in the corpus.

| Quantity | dim 8 | dim 16 | dim 32 | dim 64 | Source | Host |
|---|---|---|---|---|---|---|
| imaginary units | 7 | 15 | 31 | 63 | R (Wilmot N_m) | NEW-cd-test |
| quaternionic subalgebras H | 7 | 35 | 155 | 651 (formula) | R (8 to 32) | NEW-cd-test |
| triads C(N,3) | 35 | 455 | 4495 | 39711 (formula) | R (to 32) | NEW-cd-test |
| triad partition (assoc / non-cycle / cycle) | 7+4+24 | 35+60+360 | 155+620+3720 | | R | NEW-cd-test |
| ordered non-Fano triples | 168 | | | | R | NEW-cd-test |
| non-associating basis triples (ordered distinct nonzero) | 168 | 1848 | 15960 | 130200 | S | NEW-cd-test |
| assessors (unordered i<j, ZD-forming) | 0 | 42 | 294 | 1518 | R (16), S (32, 64) | NEW-cd-test |
| signed assessors | 0 | 84 | 588 | 3036 | R (16), S | NEW-cd-test |
| unordered ZD pairs | 0 | 168 | 2520 | 26040 | R (16), S | NEW-cd-test |
| ZD-graph edges (dim^2-6dim+8)/2 | 0 | 84 | 420 | 1860 | A (C958), S | NEW-cd-test |
| ZD-graph vertices dim-2 | | 14 | 30 | 62 | A, S | NEW-cd-test |
| missing edges dim/2-1 | | 7 | 15 | 31 | R (C1141) | EMT-test |
| assessor-graph components | | 7 | 22 | 53 | S (corpus claims 15 at 32: A) | do not port 15 |
| box-kites of 6 (dim 16 only) | | 7 | | | R | EMT-test |
| DMZ cells per strut at level 4 | | 24 | | | R + EMT | EMT-test |
| quantized gap norm squared | | 4 (7 pairs) | 4 (15 pairs) | | R | EMT-test |
| Wilmot ZD count | 0 | 1260 | 39060 | | R | NEW-cd-test |

Formulas checked from Wilmot: blades N = dim - 1, H = N(N-1)/6, triads N(N-1)(N-2)/6; these give 651 and 39711 at dim 64 (N = 63; survey arithmetic, not in the corpus).

## 6. GR / physics comparison with Blackhole

Blackhole rocq/ (main): Prelim.v; Metrics: Schwarzschild.v, Kerr.v, KerrNewman.v, KerrDeSitter.v; Kerr: Metric.v, Horizons.v, BPT_ISCO.v; Geodesics: Equations.v, NullConstraint.v, RK4.v; Cosmology: FLRW.v, Distances.v, Axiodilaton.v; Compact/EOS.v; Wormholes: MorrisThorne.v, Islands.v, EREPR.v. Roughly 4000 lines, about 60 axiom/parameter lines in total (Horizons 11, Distances 7, Metric 7, Kerr 6, others fewer; counted by grep, not classified). src/physics/ carries kerr.h, kerr_newman.h, kerr_extended.h, lqg_kerr.h, johannsen_psaltis.h, tov.h, penrose.h, hawking.h, novikov_thorne.h, and a verified/ directory (kerr.hpp, kerr_newman.hpp, kerr_de_sitter.hpp, geodesic.hpp, rk4.hpp, null_constraint.hpp, cosmology.hpp, eos.hpp, energy_conserving_geodesic.hpp, axiodilaton.h, kerr_extended.h).

| open_gororoba item | Blackhole state | Verdict and reason |
|---|---|---|
| ADM Hamiltonian constraint (ADM.v, C875) | no ADM in rocq/; src/physics has no 3+1 module | PORT-PROOF: 5-line real-analysis lemma set; needs a host in rocq/theories/ADM.v; no runtime consumer yet (renderer does not evolve data) |
| Painleve-Gullstrand lapse = 1, shift sqrt(2M/r), flat gamma_rr (ADM.v, C868) | Blackhole Schwarzschild.v is in Schwarzschild coordinates; no PG | PORT-PROOF and PORT-TEST: a rain-frame observer for a game camera would use PG; assert alpha = 1, beta^r = sqrt(r_s/r) with r_s = 2M against the C++ energy-conserving infall in src/physics/verified/energy_conserving_geodesic.hpp |
| Brans-Dicke gamma = (1+w)/(2+w), Nordtvedt, Cassini/GPB bounds | none | SKIP for the renderer (no scalar-tensor theory in src/physics); PORT-PROOF only if a PPN data panel is added |
| Bekenstein-Hawking entropy S = A/(4 l_P^2) (BekensteinEntropy.v) | hawking.h computes temperature, not entropy | PORT-PROOF (monotone in area; Schwarzschild S ~ M^2) plus PORT-TEST if hawking.h exposes entropy |
| Energy-condition chain DEC => WEC => NEC (EnergyConditions.v, C_WECImpliesNEC) | Blackhole has EOS/TOV (Compact/EOS.v) and no chain lemma | PORT-PROOF, cheap; use for TOV and Morris-Thorne (Wormholes/MorrisThorne.v) throat conditions |
| Casimir, Ford-Roman QI, warp shape functions | Blackhole has wormholes, no warp/QI | SKIP |
| Foliation, Complex-time EIH, spectral dimension | none | SKIP |
| Kerr metric, horizons, ISCO, geodesics, RK4, null constraint, KerrNewman, KerrDeSitter | present in Blackhole; open_gororoba has none of these | Blackhole has what open_gororoba lacks |

Disagreements and cross-checks:
- No direct numeric or symbolic disagreement was found, because the two corpora prove disjoint physics. Blackhole rocq/README claims Phases 0-3 complete (extraction to C++/GLSL); open_gororoba extraction is a quaternion demo (ExtractQuaternion.v) and an FP24 exactness lane, so open_gororoba has no theorem-to-runtime pipeline for physics.
- The docstring problems the two projects report share a pattern: open_gororoba's C006/C007/C025 "anchors" prove only octonion distributivity or norm positivity and carry physics names; a Blackhole port must not import those names as physics evidence.
- Blackhole memory notes that `physics::kerrTimeDilation` returns a static-observer lapse despite a ZAMO docstring (src/physics/kerr.h); open_gororoba has no Kerr theory to arbitrate, so nothing to port for that defect.
- Blackhole axiom counts in rocq/ are unclassified here; open_gororoba's counts are mostly interface (Module Type) axioms, so raw axiom counts are not comparable between the two corpora.

## 7. Recommended port order

1. EMT-test: add (a) exhaustive sign-function checks (anti-commutation, self-square, unit, prefix consistency) for N = 4..10; (b) the C1467 256-entry table; (c) dim-16 box-kite numbers (7 struts, 24 DMZ cells each, signatures 8 ^ S); (d) totalPossible = K*(K-2) for N = 4..12; (e) quantized gap 4 at N = 4, 5 (and up to 10 by direct evaluation).
2. NEW-cd-test: property tower (comm/assoc/division), Hurwitz-table asserts, Wilmot counts, ZD-graph closed forms at 16/32/64 recomputed from the sign function, the ZD witness (e1+e10)(e5+e14) = 0 at dims 16..1024, embedding closure (C957/C956), C1466 subalgebra closure.
3. rocq/CD (only if a machine-checked story is wanted for the emanation layer): CayleyDicksonAlgebra, the sign recursion (`cd_sign_fuel`) with C1474 adequacy stated for all N as a `Fixpoint` lemma rather than per-dim vm_compute, BoxKite/ZDGraph/DeMarraisAssessors/BrownAssessorEquivalence, then a new lemma: closure of the strutted tone row under Production Rule 1 at every level N. Skip Moreno and Brown chapters until a consumer exists.
4. Visuals (tesseract scene): strut/sail octahedron overlay on the wall table at level 4 view; involution-chord "gap" overlay with uniform weight 2; Fano-point colouring of the seven kites; regime-address colouring at levels 5..10 already exists on the PR branch.
5. Physics: PG and energy-condition lemmas only when a Blackhole consumer appears; otherwise leave in open_gororoba.

## 8. Caveats

- No proof was compiled in this survey; every "proved" statement is the corpus's claim, corroborated by a companion .vo in the source tree where present.
- "Survey" numbers use the sign recursion of C1467 (the same structure as Blackhole `cdBasisMulSign`) and a 2-blade ZD definition (e_i +- e_j)(e_k +- e_l) = 0 with i, j, k, l >= 1, i < j. At dim 16 this reproduces the corpus's 42 assessors and 168 directed ZD pairs. de Marrais restricts assessors to one index in the lower half and one in the upper half; the count under that restriction was not computed at dim 32 and above, so the 294 / 1518 rows may differ from a de Marrais-convention count. Treat rows marked S as checks to reproduce in the test, not as literature values.
- Axiom counts are grep counts of `Axiom` and `Parameter` lines at line start. The MT classification used the presence of a `Module Type` in the file and the first axiom lines, not a full parse.
