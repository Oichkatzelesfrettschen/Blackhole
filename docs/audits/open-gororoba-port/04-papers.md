# Audit 04: Paper survey of the local CayleyDickson collection

Scope: the local CayleyDickson collection (tier1_core_cd_algebra, tier2_architectural_precedent,
speculatory_*, metadata, four loose top-level PDFs), the DAS MERGUS and STAR Lambda monographs, the
two AI notes on TurboQuant and VLIW5, the solar-analysis note, and one loose arXiv PDF in the
documents root. Compared against the union of the Blackhole plan files (hyperdimensional-projection-research,
tesseract-interstellar-visuals, tesseract-mechanic, references/bibliography) and the open_gororoba
registry, curated, docs, crates/cd_papers and crates/lit_search trees. No network use; PDFs read by
first pages and abstracts; two long PDFs (Boyle-Mygdalas, Koebisu) read in the relevant sections.

## 1. Result in six lines

1. The collection is almost fully inside the baseline: of about 110 on-topic papers, 19 have zero hits in
   the union (NEW, table in section 3) and seven of those carry a usable hook. open_gororoba's docs/physics/sedenion_standard_model.md
   is a catalog of this very collection.
2. The strongest new item is Boyle-Mygdalas, Spacetime Quasicrystals (arXiv:2601.07769). It is not a
   Cayley-Dickson paper; it supplies the aperiodic-order structure the tesseract note calls unimplemented.
3. No new paper reaches past 32D. The 64D to 4096D hooks come from baseline papers (de Marrais, Wilmot,
   Biss et al., Bales) that Blackhole has not used; section 6 lists them.
4. Two flags contradict what the baseline assumes: Koebisu's zero-divisor characterization is false as stated
   (section 7.1), and the "complementary" reading of Koebisu versus Reggiani in open_gororoba fails with it.
5. The collection's own matrix reports "Mislabeled local file: 0". More than a dozen files hold a different paper
   than their name (section 2.2).
6. Cross-checks computed here (throwaway scripts) reproduce the baseline's 336 zero-divisor pairs at 16D and extend
   them to 32D and 64D (section 8).

## 2. Method, baseline rule, and collection triage

### 2.1 Baseline rule

New = zero hits in the union above, matched by arXiv id taken from the PDF's first-page stamp, DOI,
surname plus a distinctive title word. Depth tag for a baseline hit:

- BH: named in a Blackhole union file.
- F: formalized in crates (cd_papers re-exports hurwitz_1898, dickson_1919, schafer_1945, brown_1967,
  brown_1972, moreno_1997, de_marrais_2000, wilmot_2025).
- C: cited or discussed in open_gororoba docs, bibliography, or claims.
- K: catalog-only (source-list mirrors such as registry/artifact_source_of_truth.toml); no analysis.
- NEW: zero hits.

Pathions1.pdf is listed in the file inventory of registry/artifact_source_of_truth.toml (corpus source_files line) with no
citation or analysis, so it stays NEW by the id, DOI and title rule. Hits outside the union do not count (for example Freitas 2023 appears only in crates/data_core mirrors, so it is NEW).
Matching is text search; a paper cited under a wrong title or year is counted as cited (section 7.3).

### 2.2 Off-topic folders and mislabeled files

Confirmed off-topic and skipped: Joint MPEG-2 files and MPEG-TS notes, x87_bcd_precision_refs (four Agner Fog
manuals), references_style_guides, unrelated_physics_engineering (193 PDFs: dark sector, warp drives, holography,
tensor networks, metamaterials; the only Cayley-Dickson items are 2512.13002v1 and tower_2025_251222134, both
duplicates of tier1 files; hep-th/0212256 Cosmological Billiards is E10 physics already present in Blackhole docs).
Loose top-level PDFs: 2601.07769v2 is on topic; 2603.25709v1 (Calcagni-Briscese, fractional field theory, C),
s41598-025-02856-5 (fractional predator-prey, K) and 1-s2.0-S0167715225001737-main (space-time fractional diffusion with
resetting, NEW) are off topic; the loose PDF 2601.03210v2 (magnons in 2D materials, Kaman et al., C) is off topic.

Files whose content differs from the name (first-page text is the authority):

| File | Actual content |
| --- | --- |
| guterman_zhilina_2019_relationship_graphs_cd | Panin, short proof of a theorem of Gabber |
| guterman_zhilina_2021_sedenion_relation_graphs | Shcheglova, positive solutions of a Henon equation |
| zhilina_2020_split_sedenion_relation_graphs | Taranin, +-1 matrices with zero permanent |
| zhilina_2021_orthogonality_graphs_cd_part2 | SocAoG, social relation inference in dialogues |
| zhilina_2021_orthogonality_graphs_cd | zero bytes |
| zhilina_2023_doubly_alternative_zd_cd | French text on medical imaging for archaeology |
| gentili_struppa_2006 / 2007 | Kremnizer (DCKP conjecture) / Heinloth (zeta functions of Chow motives) |
| colombo_sabadini_struppa_2009 | Mieck, sine-Gordon-like equations for pair condensates |
| pfister_1995_composition_of_quadratic_forms | Peternell, Mori theory on Kaehler threefolds |
| huang_2010_location_left_eigenvalues | Xiangyun Chen (not Huang), left-eigenvalue location for quaternionic matrices |
| calvaruso_2024_..._paraquaternionic_contact | Tchomakova-Ivanov-Zamkovoy, arXiv:2404.16713 |
| reggiani_2025_251207210 / 251213002 | Wilmot arXiv:2512.07210 / Koebisu arXiv:2512.13002 |
| de_marrais_2007_math0703745_..._III (and the FETCHED, dup copies) | Placeholder Substructures I (stamp math/0703745) |
| Pathions2, Pathions3 | de Marrais Flying Higher, de Marrais Voyage by Catamaran (Pathions1 is Halayka) |
| freudenthal_1954_de_juiste_maat, homer_jacobson_1958 | book review on measurement; Homer Jacobson on reproduction models |

Placeholders or no text layer: schafer_1954_cbpf, cullen_1965_euclid (placeholders), the reconstructed Cullen file,
moreno_1998_journal_issue_boletin (journal front matter only). Consequence: the Guterman-Zhilina graph papers and
Zhilina 2020/2021/2023 are absent from disk although open_gororoba lists them; no hook is offered for them.
The de Marrais file math0207003 carries the Flying Higher text with no arXiv stamp; open_gororoba's bibliography
labels math/0207003 "Placeholder Substructures I" while the local Placeholder I stamp is math/0703745.

## 3. Table of on-topic papers

Duplicates share one row. Year is the first public version. Baseline column codes are defined in 2.1.

| Local file(s) | Title | Authors | Year | Id | Base |
| --- | --- | --- | --- | --- | --- |
| de_marrais_2000_math0011260, de_marrais_math0011260 | The 42 Assessors and the Box-Kites they fly | R. P. C. de Marrais | 2000 | math/0011260 | BH F |
| de_marrais_2006_math0603281 | Presto! Digitization I | de Marrais | 2006 | math/0603281 | BH C |
| de_marrais_2002_math0207003, Pathions2 | Flying Higher Than A Box-Kite | de Marrais | 2002 | math/0207003 (per OG) | C |
| de_marrais_2004_math0403113 | Box-Kites III | de Marrais | 2004 | math/0403113 | C |
| 0703745v3 (+4 copies) | Placeholder Substructures I | de Marrais | 2007 | math/0703745 | C |
| de_marrais_2007_07040026 (+FETCHED) | Placeholder Substructures II | de Marrais | 2007 | 0704.0026 | C |
| 0704.0112v3 (+2 copies) | Placeholder Substructures III | de Marrais | 2007 | 0704.0112 | C |
| 0804.3416v2, Pathions3 | Voyage by Catamaran | de Marrais | 2008 | 0804.3416 | C |
| de_marrais_2004_wolfram_science_slides | Something From Nothing Insertion Point | de Marrais | 2004 | Wolfram conf. | C |
| 2505.11747 (v1, v2, v3, 4 files) | Structure of the Cayley-Dickson algebras | G. P. Wilmot | 2025 | 2505.11747 | BH C |
| 2512.07210v1 (3 files) | Automorphisms of Sedenions | Wilmot | 2025 | 2512.07210 | C |
| s00006-025-01423-5 | Construction of G2 and non-associative algebras using Clifford algebra | Wilmot | 2026 | AACA 36:24 (OG cites 2505.06011) | C |
| reggiani_2024_2411.18881 (2 files) | The geometry of sedenion zero divisors | S. Reggiani | 2024 | 2411.18881 | C |
| reggiani_2025_251213002, unrelated/2512.13002v1 | Singular Structures and Geometric Holonomy in the Zero-Divisor Set of the Sedenions | S. Koebisu | 2025 | 2512.13002 | C |
| moreno_1997_q-alg9710013 | The zero divisors of the Cayley-Dickson algebras over the reals | G. Moreno | 1997 | q-alg/9710013 | F C |
| moreno_2004_math0404395, moreno_2004_math0405424, moreno_2005_math0512516, moreno_2005_math0512517 (2 files) | Alternative elements in CD algebras; exponential map on CD algebras; monomorphisms between CD algebras; constructing zero divisors in higher CD algebras | G. Moreno | 2004 to 2005 | math/0404395, 0405424, 0512516, 0512517 | C |
| biss_2005_math0511691, 0702075v2, biss_2009_0905.2987 | Large annihilators in CD algebras I and II; Eigentheory of CD algebras | Biss, Dugger, Isaksen (+ Christensen) | 2005, 2007, 2009 | math/0511691, math/0702075, 0905.2987 | C |
| chan_dokovic_conjugacy_sedenion_subalgebras | Conjugacy classes of subalgebras of the real sedenions | Chan, Dokovic | 2006 | Canad. Math. Bull. 49(4) | C |
| chapman_2022_2205.05605 | Roots and critical points of polynomials over CD algebras | Chapman, Guterman, Vishkautsan, Zhilina | 2022 | 2205.05605 | C |
| chapman_vishkautsan_2025 | Roots and right factors ... left eigenvalues over CD algebras | Chapman, Vishkautsan | 2025 | Comm. Math. 33(3) | C |
| bales_2011_1107.1375, bales_2011_1107.1301, bales_2016_1707.07318 | CD and Clifford algebras as twisted group algebras; a catalog of CD-like products; the CD doubling products | J. W. Bales | 2011, 2011, 2017 | 1107.1375, 1107.1301, 1707.07318 | C |
| flaut_2021_2103.12805 | Twisted group algebra structure for CD process | Flaut, Boboescu | 2021 | 2103.12805 | C |
| arxiv_2403.03763v3 (2 files) | Flipped non-associative polynomial rings and the CD construction | Aryapoor, Baeck | 2024 | 2403.03763 | C |
| arxiv_2401.01166 | Sixteen-dimensional sedenion-like associative algebra | Jitender, Kumar | 2024 | 2401.01166 | C |
| CawagasMatimyas, arxiv_0907.2047v3 (2 files) | Subloop structure of the CD sedenion loop; basic subalgebra structure of the 32D CD algebra | R. E. Cawagas et al. | 2005, 2009 | Matimyas Mat. 28; 0907.2047 | C |
| culbert_2007, kirshtein_2011_1102.5151, kirshtein_2012, kivunge_2004 | CD algebras and loops; automorphism groups of CD loops and dissertation; sedenion extension loops | Culbert; Kirshtein; Kivunge | 2007 to 2012 | JGLTA 1(1); 1102.5151; Iowa State thesis | C |
| imaeda_2000 (2 files) | Sedenions: algebra and analysis | K. Imaeda, M. Imaeda | 2000 | Appl. Math. Comput. 115 | C |
| cariow_2013 | An algorithm for fast multiplication of sedenions | Cariow, Cariowa | 2013 | IPL 113 | BH C |
| lockyer_2020 | Algebraic proof sedenions are not a division algebra | R. D. Lockyer | 2020 | ResearchGate/viXra | K |
| bilgici_2017 | Fibonacci and Lucas sedenions | Bilgici, Tokeser, Unal | 2017 | JIS 20, 17.1.8 | NEW |
| gursoy_2024 | Sedenionic matrices and their properties | Gursoy, Bektas | 2024 | GUJS 14(3) | C |
| krausshar_2021 | Function theories in CD algebras and number theory | R. S. Krausshar | 2021 | Milan J. Math. 89 | NEW |
| liebmann_2019 | Non-associative algebras and quantum physics, a historical perspective | Liebmann, Ruehaak, Henschenmacher | 2019 | 1909.04027 | NEW |
| shah_2019 | Literature survey on non-associative rings | Shah et al. | 2019 | EJPAM 12(2) | NEW |
| becvar_dlab_2024 | Hyperkomplexni cisla a maticove algebry | Becvar, Dlab | 2024 | PMFA 69(2) | NEW |
| freitas_2023 | Techniques for CD algebras and graded Lie (super)algebras for physics | I. P. de Freitas | 2023 | CBPF thesis | NEW |
| ludkovsky_2004, darpo_2020, dentoni_sce_1973 | Differentiable functions of CD numbers; von Neumann finiteness; funzioni regolari | Ludkovsky; Darpo, Nystedt; Dentoni, Sce | 2004; 2016; 1973 | math/0405471; 1608.04898 | C |
| saniga_2015 | From CD algebras to combinatorial Grassmannians | Saniga, Planat, Pracna | 2015 | Mathematics 3 | C |
| brown_1967 (2 files), brown_1972 | Generalized CD algebras; zero divisor structure (thesis) | R. B. Brown; H. C. Brown | 1967, 1972 | PJM 20 | F |
| baez_2002 (2 files) | The Octonions | J. C. Baez | 2002 | math/0105155 | BH C |
| elduque_2018, elduque_2009 | Composition algebras; gradings minicourse | A. Elduque | 2018, 2009 | 1810.09979 | C |
| eschenburg_2018, eschenburg_2010 | Geometry of octonions; Quaternionen und Oktaven (2) | J.-H. Eschenburg | 2018, 2010 | notes | NEW |
| pinto_2021, brada_1986, veldkamp_1968, pumplun_2005 | Octonionic planes; geometrie des octaves; unitary groups in octave planes; sums of squares in octonion algebras | Pinto; Brada; Veldkamp; Pumpluen | various | thesis; PDML; Compositio | C |
| petersson_1993 | Composition algebras over algebraic curves of genus zero | H. P. Petersson | 1993 | TAMS 337 | K |
| voight_2021 | Quaternion algebras | J. Voight | 2021 | book | K |
| allison_faulkner_1984, bremner_hentzel_2001, eakin_sathaye_1990, urbanik_wright_1960 | CD process for structurable algebras; identities from the CD process; automorphisms and derivations; absolute-valued algebras | as named | 1984 to 1960 | TAMS 283; CommAlg 29; JAlg 129; PAMS 11 | C |
| schafer_1945, 1954 (AJM), 1955, 1961, hurwitz_1898, dickson 1906 to 1921, albert_1942, zorn_1935, jacobson_1939 and 1958, freudenthal 1951 to 1985, wedderburn_1914 | classical primary sources and reconstructions (Freudenthal 1951 and Jacobson 1958 are spliced or preview copies) | as named | 1898 to 1985 | various | F C |
| walker_1954, seligman_1960 | Fermat's theorem for algebras; automorphisms of Lie algebras of classical type | Walker; Seligman | 1954, 1960 | PJM 4; Ann. Math. | NEW (peripheral) |
| hamilton 1835 to 1866, cayley_1845, cockle_1848 and 1849, niven_1941, eilenberg_niven_1944, coxeter_1946 | quaternion and split-quaternion primary sources | as named | 1835 to 1946 | various | C |
| bachet, bombelli, cardano, degen, girard, legendre, viete, euler E445, mmoires | sums-of-squares archival precursors | as named | 1545 to 1818 | archival | C |
| conrad_hurwitz_sums_of_squares, conrad_sums_of_squares_composition | expository notes on Hurwitz composition | K. Conrad | n.d. | notes | NEW (no hook) |
| brown_rice_2008/2021, rice_brown_2016 parts 1 and 2 | Dickson-Hurwitz; CD for beginners; why Hamilton could not multiply triples; commutativity and collinearity | Brown, Rice | 2008 to 2021 | various | K |
| sudbery_1979, huang_so_2001, zhang_1997, libine_2010, janovska_opfer_2014 (2 files), alayon_solarz_2008, bradford_2023, chen_2010 (file huang_2010) | quaternion and split-quaternion analysis and matrices | as named | 1979 to 2023 | various | C (Sudbery), K (Huang-So), else NEW |
| chanyal_2015; kuwata_2003; carlstrom_2001 | Octonionic gravi-electromagnetism; Born-Infeld with CD algebras; Wheels | Chanyal et al.; Kuwata; Carlstroem | 2014; 2003; 2001 | 1502.05293; hep-th/0306271 | C |
| gillard_gresnigt_2019; gourlay_gresnigt_2024; gresnigt_2026 | fermion generations from sedenions and Cl(8) | Gillard, Gourlay, Gresnigt | 2019 to 2026 | 1904.03186; 2407.01580; 2601.07857 | C |
| tang_tang_2023 (3 files), mironov_2014 | sedenion SU(5) and lepton-mass models; sedeonic gravitoelectromagnetism | Q. Tang, J. Tang; Mironov | 2023; 2014 | 2308.14768; 2307.02505 | C |
| g2_extension_sm_2021; dou_2025 | G2 extension of the Standard Model from CD automorphisms; convergence domains of sedenionic star-power series | Nature Sci. Rep.; Dou, Jin, Ren, Sabadini | 2021; 2025 | 2512.00600 | C |
| gazeau_2512.22134 (+tower_2025 copy); gazeau_2601.18433 | Mnemonic matrix rule for octonions; split-octonion conformal space | J.-P. Gazeau et al. | 2025; 2026 | 2512.22134; 2601.18433 | C |
| soton_2025_psl2_7 | Embedding of some finite geometries into Riemann surfaces (year 2001) | P. Martin Garcia | 2001 | Southampton PhD | C (dated 2025 in OG) |
| ruan_fan_2009 (2 files) | Temporal coupled-mode theory for Fano resonance (optics) | Ruan, Fan | 2009 | 0909.3323 | C (mis-cited, 7.3) |
| aastrup x3, connes 0810.2088 and hep-th/9603053, chamseddine_connes 9606001, vdDungen 1505.01939, devastato 1710.04965, alvarez 2601.19734, west hep-th/0104081 | spectral triples, spectral action, Clifford-invariant unification, E11 | as named | 1996 to 2026 | as named | C |
| muon g-2 (2), DUNE, Hyper-K, JUNO, T2K-NOvA | data references for the physics claims | collaborations | 2015 to 2025 | as named | C |
| Pathions1 | Calculating fractal sets in n >= 1 embedding dimensions without truncation | S. Halayka | 2022 | TechRxiv 10.36227/techrxiv.19425989 | NEW |
| 2601.07769v2 (loose) | Spacetime Quasicrystals | L. Boyle, S. Mygdalas | 2026 | 2601.07769 | NEW |
| leroux_2003, tchomakova_2024 (mislabeled calvaruso), priti_kumar_2025 | Baxter operads; paraquaternionic contact; space-time fractional diffusion | Leroux; Tchomakova et al.; Priti, Kumar | 2003; 2024; 2025 | math/0311214; 2404.16713 | NEW (off topic) |

Cited in the notes or monographs, no local PDF, zero hits in the union: Chapman-Levin arXiv:2306.15889 (roots and right
factors over CD algebras), Lopatin-Zubkov arXiv:2411.08500 (linear equations over split octonions), and the
Fano-plane incidence paper cited as arXiv:2203.03261 (title unverified). Buchholtz-Rijke arXiv:1610.01134 has one hit
(C). The AI notes, monographs and solar note carry no other on-topic external papers; their remaining arXiv ids are
holography, error correction and time-crystal papers.

## 4. New papers: result, novelty, hook

Convention used in every check below: (a,b)(c,d) = (ac - d*b, da + bc*), index XOR signs by the sgn loop of the
hyperdimensional note. A test must state its convention (section 7.2).

### 4.1 Boyle and Mygdalas, Spacetime Quasicrystals (2601.07769v2, 34 pp)

Result: a symmetric cut-and-project (sC&P) scheme extends Penrose and Ammann-Beenker order to Minkowski space.
Examples: a (1+1)D self-dual or globally scale-invariant quasicrystal from the odd lattice I(3,1), and four (3+1)D ones
from the even lattice II(9,1) = the E10 root lattice. The Coxeter element of II(9,1) acts as a discrete Lorentz boost
with eigenvalue 1.17628 (Lehmer's number, a Salem number) in one plane and as irrational rotations in four others;
the paper prints the 10x10 matrix and its eigenvalues. Euclidean warm-up: Ammann-Beenker from Z^4, whose unit
hypercube projects to a regular octagon window, scale factor the silver ratio 1+sqrt2; Elser-Sloane from E8.
Novelty: no Cayley-Dickson content. De Marrais, Moreno, Baez and Culbert describe finite XOR and zero-divisor
structure; this paper adds aperiodic long-range order and number-field units (Appendix B) as scale factors. The
Blackhole adaptation survey states that cut-and-project has no implementation and no source; this is the source.
Hooks:
- (a) Wall pattern for the tesseract [design]: Ammann-Beenker vertices from the Z^4 lattice already present (rank 4),
  window octagon with 8 boundary vertices, self-similar under a factor of 2.41421. A 4D Minkowski slice of the rank-10
  lattice would reuse the same 4D march with a boost-invariant weighting (Gaussian in the internal 6D).
- (b) C++ test, verified here in floating point: the E10 Cartan matrix (chain of 9 nodes with a tenth node on the
  third; T(2,3,7); det -1) gives, as the product of ten simple reflections, a Coxeter element whose characteristic
  polynomial rounds to the integer coefficients [1, 1, 0, -1, -1, -1, -1, -1, 0, 1, 1] (Lehmer's polynomial,
  deviation 1.2e-14), largest real root 1.17628081826, inverse root 0.850137, and the other eight roots on the
  unit circle. The test asserts the integer coefficients via Faddeev-LeVerrier (integer form not run) and the root to
  1e-9. The paper prints the numeric eigenvalues and states the polynomial by citation only.
- (c) Black-hole hook: a point set invariant under a boost by lambda maps to a point set invariant under
  Schwarzschild time translation of the static observers, because the Kruskal boost is the Killing flow.
  With surface gravity kappa = 1/(4M) (G = c = 1), lambda = 1+sqrt2 gives Delta t = 4M ln(2.41421) = 3.5255 M and
  Lehmer's number gives 0.6494 M. A Kruskal-diagram overlay of the (1+1)D quasicrystal with these periods is a
  design idea [design], not a published claim.
Contradiction: none. Confidence 0.7 that (c) is visually useful; it would drop if the boost-invariant weighting
gives no visible order on a 1080p Kruskal plot.

### 4.2 Halayka, fractal sets in n >= 1 dimensions without truncation (Pathions1, TechRxiv 2022)

Result: replaces the CD product with an O(n) "new multiplication operator" for Julia sets in n dimensions and reports
it is faster than the O(n^2) traditional product from n >= 32, visualized with OpenGL. The paper's C++ and Python are
"on request".
Flag: the O(n) operator is not a Cayley-Dickson product; the paper's comparison of the two operators shows differences,
not agreement. Only its use of the traditional 32D pathion product counts as real Cayley-Dickson mathematics.
Derived here [math, checkable]: in every CD algebra x + x* = 2Re(x) and x x* = |x|^2 hold, so x^2 = 2Re(x) x - |x|^2 e0.
The quadratic map z -> z^2 + c therefore costs O(n) in any 2^k dimension, and the orbit stays in span{e0, Im z0, Im c}
plus a radial component; at n = 16 the numerical orbit rank is 3 for z^2+c against 12 for z -> 0.9 (z a) z + c
(30 bounded iterates each; n = 32 and 64 overflowed and are not run to convergence). The hyperdimensional note
already gives z^2 = (w^2 - |v|^2, 2wv) and calls the octonion Julia set a 4D slice of an 8D set; the identity is the
reason and it extends to 4096D.
Hooks:
- (b) C++ test: for random x at n = 32, 64, 256, 1024, 4096 assert |x*x - (2 x0 x - |x|^2 e0)| < 1e-12 relative
  (the sgn-loop product is O(n^2) at 4096, so use n <= 1024 for the direct product and 4096 with the mask form).
- (a) A Julia pass whose non-triviality is real must use a map outside R[z], for example z -> (z a) z + c with fixed
  a: dimension per level 32, 64, ... with an SDF marched in a 4D slice chosen inside span{e0, a, c, z0}.
- (c) GLSL: the O(n) squaring cuts a 32D Julia iteration from 1024 multiply-adds to 64.
Confidence 0.8 on the identity (algebra), 0.5 that a (z a) z map gives a scene worth shipping.

### 4.3 Eschenburg, Geometry of octonions (2018)

Result: exposition from Hurwitz to G2 = Aut(O), the octonionic projective plane OP^2 = F4/Spin(9) (16-dimensional),
Spin(9) isotropy, Rosenfeld lines, Clifford-module periodicity.
Novelty: Baez surveys the octonions and touches OP^2; this adds the symmetric-space and Clifford-periodicity
account with proofs.
Hooks: (a) the Hopf fibration S^15 -> S^8 with S^7 fibers, h(x,y) = (|x|^2 - |y|^2, 2 x conj(y)); (b) test: h lands
on the sphere exactly when the norm is multiplicative. Measured on 200 unit pairs: max |h|^2 - 1 is 1.1e-15 at n = 4,
8.9e-16 at n = 8, 0.69 at n = 16, 0.46 at n = 32. The negative control at 16D and 32D shows why the construction
stops at the octonions. Size: total space 2n - 1 dimensional, base n. The plan's isoclinic S^3 flow is the n = 2
member; the n = 8 member is a 16D pair rendered as an S^7-fiber over a chosen base point via stereographic projection
to a 3D tesseract slice.

### 4.4 Janovska and Opfer, zeros and singular points of coquaternionic polynomials (ETNA 41, 2014)

Result: polynomials over the split quaternions (coquaternions, Cockle 1849) via a real companion polynomial of degree
2n; singular points (p(z) times its conjugate is zero) versus zeros; Newton's method with an exact Jacobian; no
Fundamental Theorem of Algebra for coquaternions; extension to the tessarine-type R^4 algebras.
Novelty: split quaternions are the 4D generalized Cayley-Dickson algebra with gamma = +1, and they already contain zero
divisors at n = 4, where the standard doubling stays a division algebra. Baseline holds Cockle 1849 and Libine-type
analysis nowhere; the collection files are the only coverage.
Hooks: (a) the norm-zero set a1^2 + a2^2 = a3^2 + a4^2 is a 3D cone in R^4 (signature 2+2), the zero-divisor locus at
4D; a 3D tesseract slice shows a cone or hyperboloid and needs no sedenions. (b) Test: with the 2x2 real matrix
model, det of left multiplication equals N(a)^2, so L_a is singular exactly on the cone (norm-zero cone; not run
here). Reach: 4D. Confidence 0.6 as a scene element.

### 4.5 Libine, an invitation to split quaternionic analysis (2010)

Result: split quaternions H_R = 2x2 real matrices; conformal group SL(2, H) and its split analogue; Cauchy formulas.
Hooks: (a) a Moebius (SL(2,H)) camera on S^4, adding inversions to the so4.h rotations; (b) test: cross ratio of four
points on S^4 invariant under the action to 1e-12. Reaches 4D only. Confidence 0.4 that a conformal camera reads better
than a rotation camera.

### 4.6 Krausshar, function theories in CD algebras and number theory (2021)

Result: octonionic generalized elliptic functions on lattices closed under octonion multiplication (CM lattices from
Q[sqrt m1, ..., sqrt mk]); trace formulas for CM division values.
Hooks: (a) a multiplicatively closed period lattice for the scene field: in 4D the Hurwitz order gives the D4 lattice
with 24 unit quaternions (a 24-cell vertex set); in 8D the Cayley integers give 240 units; [design, not in the paper];
(b) test: unit counts 24 and 240, closure of the lattice under the sgn product. 4D and 8D only.

### 4.7 Bilgici, Tokeser, Unal, Fibonacci and Lucas sedenions (2017)

Result: generating functions and Binet formulas for sedenion-valued Fibonacci and Lucas sequences.
Novelty: coefficients are real, so the identities hold in any power-associative CD algebra; the paper uses the
Imaeda-Imaeda parameter rho = -1 and the Cawagas basis table (conjugation bars were lost in text extraction, so
whether its sign table equals the standard doubling is not checked). It states that sedenions are power-associative,
which supports the identity of 4.2.
Hooks: (b) the sum of squares of the 2^k consecutive Fibonacci numbers f_n..f_(n+2^k-1) equals
f_(n+2^k-1) f_(n+2^k) - f_(n-1) f_n, which gives the exact squared norm of the level-k Fibonacci element at 16, 32, ...,
4096D in integers. Weak visual value; rank 7.

### 4.8 Freitas, Techniques for CD algebras and graded Lie superalgebras (CBPF thesis, 2023)

Result: matrix representation of octonions and sedenions by Pauli and Dirac matrices; octonionic Lagrangian of
dyon electromagnetism; doubling of Z2^n-graded Lie algebras from n-1 to n. Advisor: Toppan.
Hooks: (b) the XOR index group of CD_k is Z2^k; grading closure e_i e_j in span(e_(i xor j)) at all k. Already used
by the sgn mask in the hyperdimensional note; only the graded-superalgebra doubling is new and lacks a rendering.

Surveys and peripheral NEW items (Liebmann, Shah, Becvar-Dlab, Zhang, Alayon-Solarz, Bradford, Chen, Walker,
Seligman, Conrad) have no hook and serve as citation material only.

## 5. Ranking of new papers by hook value

Constraint used: a hook that scales from 32D to 4096D outranks one that stops at H, O or S.

| Rank | Paper | Best hook | Reach |
| --- | --- | --- | --- |
| 1 | Boyle-Mygdalas 2601.07769 | E10 Coxeter element test (Lehmer polynomial, verified); Ammann-Beenker walls; Kruskal overlay | lattice rank 4 to 10 |
| 2 | Halayka Pathions1 | z^2 identity test to 4096D; (z a) z Julia pass at 32D | 32D to 4096D |
| 3 | Eschenburg 2018 | Hopf S^15 -> S^8, negative control at 16D and 32D | 4D to 32D |
| 4 | Janovska-Opfer 2014 | zero-divisor cone in 4D (split quaternions) | 4D |
| 5 | Libine 2010 | SL(2,H) Moebius camera, cross-ratio test | 4D |
| 6 | Krausshar 2021 | multiplicatively closed lattices, 24 and 240 units | 4D and 8D |
| 7 | Bilgici et al. 2017 | exact Fibonacci norm identity at all 2^k | all k, no visuals |
| 8 | Freitas 2023 | Z2^k grading closure test | all k, already in note |

All eight are NEW by the strict rule. Lockyer 2020, the strongest single hook among catalog-only papers, is listed in
section 6. The survey found no further NEW paper with a usable hook.

## 6. Baseline papers Blackhole has not used (hooks)

The Blackhole plans cite only Baez, Wilmot 2505.11747, de Marrais math/0011260 and math/0603281, and Lemley. These
baseline items carry the 64D to 4096D reach:

0. Lockyer 2020 (K, catalog-only in open_gororoba; title and URL in its source lists, no analysis). The 7 quaternion
   subalgebras of an octonion algebra carry orientations; requiring a normed composition algebra leaves 16 proper
   orientations; the standard doubled sedenions contain 168 primitive zero divisors and 2048 maximal sets of proper
   octonion-subalgebra orientations; a "Law of Octonion Algebraic Invariance" is proposed as a physics constraint.
   Verified here: with a fixed Fano line set, exactly 16 of the 128 sign assignments give |xy|^2 = |x|^2 |y|^2
   (six random pairs each); 480 = 30 Fano labelings x 16 matches the "480 representations" in Wilmot's Clifford paper.
   The paper's 168 counts signed unit zero divisors (84 signed two-term elements e_a +- e_b times an overall sign);
   the 168 in open_gororoba's TOTAL_ZD_PAIRS = 42 assessors x 4 counts pairs, and my 336 ordered pairs are 168 unordered
   (section 8). The 2048 is not run. Hooks: (b) tests "16 of 128 orientations are composition algebras", "480 = 30 x 16",
   and the 84 signed elements; (a) one octahedral box-kite per orientation class drawn as 16 recolorings of the Fano
   diagram. Reach 8D and 16D.
1. Wilmot 2512.07210, Fano volume: the 15 imaginary sedenion units are the nonzero vertices of the 4-cube under
   XOR, the 35 quaternion subalgebras are the 35 lines {a, b, a xor b} of PG(3,2). The tesseract's 16 corners are the
   sedenion index set. Triple counts (2^k - 1)(2^k - 2)/6: 35, 155, 651, 2667, 10795 (k = 8, dim 256), 174251
   (k = 10), 2794155 (k = 12, dim 4096); 10795 is also the PG(7,2) line count behind the plan's dim-1024 DMZ figure 259080 = 24 x 10795 (one octahedron per line
   of PG(N-3,2), N = 10). This matches the Morton
   embedding proposed in audit 02, section 5.1. Test: the triple counts and PG line incidence for each k.
2. Biss et al.: maximum annihilator dimension 2^n - 4n + 4, so 4 at 16D (the S^3 annihilator), 16 at 32D, 44 at 64D,
   988 at 1024D, 4052 at 4096D. Test: exact bound at n = 4, 5, 6 by nullspace rank.
3. Bales 2017: 32 candidate doubling products, 8 pass the quaternion property, 4 give octonions; partly verified in
   section 7.2.
4. Reggiani: Z(S) is isometric to G2 (dim 14), ZD(S) to V2(R^7) (dim 11), fiber S^3; a 42-node zero-divisor graph in 7
   octahedra at 16D.
5. Cariow-Cariowa, 122 multiplies for a sedenion product: a 16D shader cost figure.
6. Kirshtein, Culbert, Cawagas: CD loop automorphism groups and the 32D subloop structure, for an independent check of
   the assessor count at 32D.

## 7. Contradictions and flags

### 7.1 Koebisu's zero-divisor characterization is false as stated (contradicts open_gororoba)

Koebisu arXiv:2512.13002, Cor. 3.7 and Thm. 4.4: a nonzero v = (v1, v2) is a zero divisor iff |v1| = |v2| and
<v1, v2> = 0 (for full octonion components), and the normalized set is V2(R^8) (dim 13, "codimension 2"). Direct
computation with the sgn-loop product: v = e0 + e9 has v1 = 1, v2 = e1, satisfying both conditions, and its left
multiplication matrix has minimum singular value 1.41421, so v is invertible as a left multiplier. Over 200 random
orthonormal frames with non-imaginary components, the smallest singular value is between 0.043 and 1.13; over 200 frames
with purely imaginary components, all are singular (below 1e-15). The real-part half needs no numerics: L_(u*) equals
the transpose of L_u in every CD algebra (checked at n = 16), so for imaginary u the matrix L_(r+u) = rI + L_u is a
scalar plus a skew matrix and is invertible for r != 0, under any doubling convention. The e8-component half is
computed: v = e1 + e8 (v1 = e1, v2 = 1; equal norms, orthogonal) has minimum singular value 1.41421, and 200 frames
with Re v1 = 0 and Re v2 != 0 have minimum singular values between 0.011 and 1.05. The set therefore needs
Re v1 = Re v2 = 0, which gives V2(R^7) as in Reggiani (dim 11); this conclusion is computed here and matches Reggiani. open_gororoba's docs/physics/sedenion_standard_model.md calls the two results
"complementary" (V2(R^8) with V2(R^7)); they disagree on dimension, 13 against 11. Confidence 0.9; a test that would
falsify it is any left zero divisor with a nonzero real part in v1 or v2.

### 7.2 The isomorphism claim in the hyperdimensional note needs a scope

The note says sign-flipped doubling variants "give isomorphic algebras with relabeled units". Bales 2017 lists 32
candidate products, of which only P0, P0-transpose, P3, P3-transpose give the octonions. Reimplementing his
f0..f7, g0..g3: 16 of 32 pass a partial quaternion filter (associative and normed at n = 4 on random vectors; Bales's
intermediate "half at the initial interior points"; his 8 needs the basis-cycle property (2.7) at all levels, which is
not implemented here), 4 give a normed alternative algebra at
n = 8 ((f0,g0), (f3,g1), (f4,g2), (f7,g3)), and none is normed at n = 16. Both conventions the note quotes,
(ac - db*, a*d + cb) and (ac - d*b, da + bc*), are in the octonion-producing four. The claim holds for those four at 8D;
whether the four are mutually isomorphic at 16D or higher is not run. Consequence: each C++ test states its product.

### 7.3 Catalog errors in open_gororoba's docs/physics/sedenion_standard_model.md

- Ruan and Fan arXiv:0909.3323 is cited as "Fano plane from quadratic residues"; the PDF is a temporal coupled-mode
  theory for Fano resonance in light scattering (optics), unrelated to the Fano plane.
- Koebisu arXiv:2512.13002 appears under "Reggiani (2025)" and again as Koebisu (2025).
- The Southampton PhD thesis is dated 2025; the file is a 2001 thesis by Martin Garcia (Fano plane and 3-biplane
  embedded in Riemann surfaces with PSL(2,7) automorphisms).
- Chan-Dokovic is dated 2018 in the doc and 2006 in bibliography.toml; the PDF is Canad. Math. Bull. 49(4), 2006.
- arXiv:1904.03186 is titled "Intersecting octonion subalgebras" in one line and correctly as the Gillard-Gresnigt
  three-generation paper in another.
- Wilmot's Clifford paper (same local file s00006-025-01423-5) is listed twice in the doc, as "G_2 from Clifford
  calibrations" (2026) and as "AACA (2025): G2 via CD doubling, 35:14"; the registry gives "35, 23 (2025)"; the PDF
  and DOI give 36:24 (2026).
- The 42 assessors paper is math/0011260 at bibliography line 1181 and math/0604092 at line 3962.
- Dou et al. is dated 2024 in the doc; the arXiv id 2512.00600 is November 2025.

### 7.4 Assumptions that hold

The 336 ordered zero-divisor pairs in the plan and open_gororoba's TOTAL_ZD_PAIRS = 168 (42 assessors x 4, unordered
pairs) agree with the count here (section 8: 336 ordered pairs, 168 unordered). Wilmot's zero_divisor_pair_count(1) = 1260 counts a different object and is not a disagreement. The
plan's claim that CD arithmetic adds no visual value for the lattice look stands for every new paper above.

## 8. Cross-checks computed here (throwaway scripts, not checked in)

Convention of section 4. Objects: signed two-term elements e_a +- e_b (1 <= a < b < n) with a right annihilator of the
same form; "assessor" means the unordered index pair {a, b}. This is a lower bound on all zero divisors beyond 16D
(Biss et al.: annihilators reach 2^n - 4n + 4 dimensions).

| Dim | Signed elements | Assessors | Ordered annihilating pairs | Components (size x count) |
| --- | --- | --- | --- | --- |
| 16 | 84 | 42 | 336 | 6 x 7 |
| 32 | 588 | 294 | 5040 | 14 x 15, 12 x 7 |
| 64 | 3036 | 1518 | 52080 | 30 x 31, 28 x 15, 24 x 7 |
| 128 | 13884 | 6942 | not run | not run |

Component pattern fitting n = 4 to 6 (dimension 2^n): sizes 2^(n-1) - 2^j with count 2^(n-j) - 1 for j = 1 to n - 3
[conjecture; proof not run]. Node degrees are 4 at 16D, {4, 8, 12} at 32D and {4, 8, ..., 28} at 64D. Consequences
for a test: 42 assessors and 7 components of 6 at 16D reproduce the box-kites; 294 assessors and 22 components at 32D.
Other checks run: sgn loop equals the recursive product at n = 16; 16 of 128 Fano orientations are composition
algebras (section 6, item 0); Bales counts (7.2); Hopf norm test (4.3); Koebisu counterexamples and the transpose
identity (7.1); z^2 identity orbit rank at n = 16 (4.2); E10 Coxeter characteristic polynomial (4.1).

Not run: any Blackhole build or C++ test; integer Faddeev-LeVerrier on the E10 matrix (a floating characteristic
polynomial was rounded); the eigenvalues of the paper's printed matrix; the norm-zero cone determinant identity;
the 2048 orientation count; isomorphism of
the four Bales products at 16D; Julia orbits at n = 32 and 64 to convergence; full reads of the long PDFs beyond
Boyle-Mygdalas and Koebisu; DOI resolution (no network).
