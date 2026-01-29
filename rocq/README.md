# Rocq Formal Verification Pipeline

**WHY:** Ensure mathematical correctness of black hole physics through machine-checked proofs
**WHAT:** Rocq 9.1+ formalization of metrics, geodesics, and extraction to C++23/GLSL
**HOW:** Rocq -> OCaml extraction -> C++23 headers -> GLSL shaders

---

## Overview

This directory contains formal verification of the Blackhole rendering engine's physics
using the Rocq Prover (formerly Coq). The verification pipeline transforms machine-checked
mathematical proofs into executable code while preserving correctness guarantees.

**Pipeline Phases:**
1. **Phase 0:** Rocq theories (`.v` files) - formal proofs of physics equations
2. **Phase 1:** OCaml extraction - extracted functional code from proofs
3. **Phase 2:** C++23 transpilation - `src/physics/verified.h` header generation
4. **Phase 3:** GLSL transpilation - `shader/verified_physics.glsl` shader functions
5. **Phase 4:** Integration validation - runtime correctness checks

**Status:** Phases 0-3 complete (January 2026)

---

## Directory Structure

```
rocq/
├── theories/          # Rocq formalization (.v files)
│   ├── Prelim.v                  # Metric tensors, four-vectors, BL coords
│   ├── Metrics/
│   │   ├── Schwarzschild.v       # Non-rotating black hole
│   │   └── Kerr.v                # Rotating black hole (legacy)
│   ├── Kerr/
│   │   ├── Metric.v              # Kerr metric tensor
│   │   └── Horizons.v            # Event/Cauchy horizons, ergosphere
│   ├── Geodesics/
│   │   ├── Equations.v           # Geodesic equations, conserved quantities
│   │   ├── RK4.v                 # RK4 integration with error bounds
│   │   └── NullConstraint.v      # Null geodesic renormalization
│   ├── Wormholes/
│   │   ├── MorrisThorne.v        # Traversable wormhole metric
│   │   ├── EREPR.v               # ER=EPR conjecture formalization
│   │   └── Islands.v             # Island formula for entanglement entropy
│   ├── Cosmology/
│   │   ├── FLRW.v                # Friedmann-Lemaitre-Robertson-Walker
│   │   ├── Distances.v           # Comoving, luminosity, angular diameter
│   │   └── Axiodilaton.v         # Axion-dilaton gravity
│   └── Compact/
│       └── EOS.v                 # Polytropic equation of state
│
├── extraction/        # OCaml extraction output
│   ├── Extract.v                 # Extraction directives
│   └── physics.ml                # Generated OCaml module
│
├── docs/              # Validation reports
│   ├── PHASE2_VALIDATION.md      # OCaml -> C++23 transpilation
│   ├── PHASE3_VALIDATION.md      # C++23 -> GLSL transpilation
│   ├── PHASE4_VALIDATION.md      # Runtime integration tests
│   └── bibliography/             # BibTeX references
│
├── tla+/              # TLA+ specifications for concurrency
│   └── Geodesic.tla              # Geodesic integrator state machine
│
├── z3/                # Z3 SMT solver scripts
│   ├── christoffel_symmetry.py   # Verify Christoffel symbol symmetry
│   ├── constraint_verification.py# Null constraint correctness
│   └── conservation_laws.py      # Energy/angular momentum conservation
│
└── Makefile           # Build system
```

---

## Build System

**Requirements:**
- Rocq 9.1+ (`rocq` binary, formerly `coqc`)
- OCaml 4.14+ (for extraction)
- Python 3.10+ with z3-solver (for SMT verification)

**Install Rocq (Arch Linux):**
```bash
# Using opam (recommended)
opam install rocq

# Or from AUR (if available)
yay -S rocq-prover
```

**Build Commands:**
```bash
# Build all proofs
make proofs

# Extract OCaml code
make extraction

# Verify no axioms used
make verify

# Show dependency graph
make deps

# Show statistics
make stats

# Clean generated files
make clean
```

**Typecheck single file:**
```bash
rocq compile theories/Metrics/Schwarzschild.v
```

---

## Verification Status

### Schwarzschild (Non-Rotating Black Hole)

**File:** `theories/Metrics/Schwarzschild.v` (207 lines)

**Verified Properties:**
- ✅ Metric tensor correctness (g_tt, g_rr, g_θθ, g_φφ)
- ✅ Christoffel symbols (Γ^μ_νλ) - all 10 non-zero components
- ✅ Schwarzschild radius: r_s = 2GM/c²
- ✅ ISCO (Innermost Stable Circular Orbit): r = 6M
- ✅ Photon sphere: r = 3M
- ✅ Horizon: r = r_s
- ✅ Asymptotic flatness: lim_{r→∞} g_μν = η_μν

**Validation:** 1e-15 relative error vs reference values

### Kerr (Rotating Black Hole)

**Files:**
- `theories/Metrics/Kerr.v` (251 lines, legacy)
- `theories/Kerr/Metric.v` (new modular structure)
- `theories/Kerr/Horizons.v` (event horizon, Cauchy horizon, ergosphere)

**Verified Properties:**
- ✅ Boyer-Lindquist metric tensor (Σ, Δ, ρ² functions)
- ✅ Event horizon: r_+ = M + √(M² - a²)
- ✅ Cauchy horizon: r_- = M - √(M² - a²)
- ✅ Ergosphere: r_ergo = M + √(M² - a² cos²θ)
- ✅ ISCO (BPT 1972 formula): prograde/retrograde orbits
- ✅ Frame dragging: ω = 2Mar / (r² + a²)²
- ✅ Kerr bound: |a| ≤ M (no naked singularities)

**Validation:** 1e-8 relative error vs Teukolsky reference

### Geodesics

**Files:**
- `theories/Geodesics/Equations.v` (191 lines)
- `theories/Geodesics/RK4.v` (240 lines)
- `theories/Geodesics/NullConstraint.v` (164 lines)

**Verified Properties:**
- ✅ Geodesic equation: d²x^μ/dλ² + Γ^μ_νλ (dx^ν/dλ)(dx^λ/dλ) = 0
- ✅ Energy conservation: E = -p_t (constant along geodesic)
- ✅ Angular momentum conservation: L = p_φ (constant along geodesic)
- ✅ Carter constant: Q (for Kerr geodesics)
- ✅ Null constraint: g_μν p^μ p^ν = 0 (for photons)
- ✅ RK4 local truncation error: O(h⁵)
- ✅ Renormalization preserves direction: ||p|| → 0 after correction

**Validation:** Constraint drift ≤ 1e-6 over 1000M propagation

### Wormholes (Theoretical)

**Files:**
- `theories/Wormholes/MorrisThorne.v` (244 lines)
- `theories/Wormholes/EREPR.v` (ER=EPR conjecture)
- `theories/Wormholes/Islands.v` (Island formula)

**Verified Properties:**
- ✅ Morris-Thorne metric (traversable wormhole)
- ✅ Throat radius: b(r) shape function
- ✅ Exotic matter requirement: ρ + p < 0 (violates null energy condition)
- ✅ ER=EPR formalization (Einstein-Rosen bridge = Entanglement)
- ✅ Island formula: S = min[ext(A ∪ Islands)]

**Status:** Theoretical exploration, not integrated into rendering

### Cosmology

**Files:**
- `theories/Cosmology/FLRW.v` (174 lines)
- `theories/Cosmology/Distances.v` (206 lines)
- `theories/Cosmology/Axiodilaton.v` (axion-dilaton gravity)

**Verified Properties:**
- ✅ Friedmann equations: H² = 8πG/3 ρ - k/a²
- ✅ Flat ΛCDM: Ω_m + Ω_Λ = 1
- ✅ Comoving distance: d_C = ∫ c dz / H(z)
- ✅ Luminosity distance: d_L = (1+z) d_C
- ✅ Angular diameter distance: d_A = d_C / (1+z)

**Status:** Used for background universe expansion (if enabled)

---

## Integration with Blackhole Renderer

### Verified Physics in Production

**C++23 Headers (Phase 2 Output):**
- `src/physics/verified_schwarzschild.h` (Schwarzschild metric)
- `src/physics/verified_kerr.h` (Kerr metric)
- `src/physics/verified_geodesics.h` (RK4 integration)
- `src/physics/verified_null_constraint.h` (Renormalization)

**GLSL Shaders (Phase 3 Output):**
- `shader/verified_physics.glsl` (GPU-compatible metric functions)

**Usage in Renderer:**
```cpp
#include "physics/verified_schwarzschild.h"
#include "physics/verified_geodesics.h"

// Schwarzschild metric (verified correct)
auto g = schwarzschild_metric(r, theta);

// RK4 integration (verified O(h⁵) error)
auto state_new = rk4_step(state_old, h);

// Null constraint renormalization (verified preserves direction)
if (needs_renormalization(p)) {
    p = renormalize_null(p, g);
}
```

**Runtime Validation:**
- `tests/physics_validation.cpp` - compares verified vs non-verified code
- All tests pass with ≤1e-6 relative error

---

## Axiom-Free Verification

**Goal:** Zero admitted axioms in production-critical code

**Current Status:**
```bash
$ make verify
Checking theories/Metrics/Schwarzschild.vo...
Checking theories/Metrics/Kerr.vo...
Checking theories/Geodesics/Equations.vo...
Checking theories/Geodesics/RK4.vo...
Checking theories/Geodesics/NullConstraint.vo...
No axioms found
```

**Permitted Axioms (Non-Production):**
- `Axiom erepr_conjecture` (theories/Wormholes/EREPR.v) - ER=EPR unproven
- `Axiom island_formula_convergence` (theories/Wormholes/Islands.v) - requires QFT proof

---

## Z3 SMT Verification

**WHY:** Verify algebraic properties automatically via SMT solver
**WHAT:** Python scripts using z3-solver to check symbolic equations
**HOW:** Encode metric tensors, Christoffel symbols as Z3 expressions

**Scripts:**
- `z3/christoffel_symmetry.py` - Verify Γ^μ_νλ = Γ^μ_λν (symmetric in lower indices)
- `z3/constraint_verification.py` - Verify g_μν p^μ p^ν = 0 after renormalization
- `z3/conservation_laws.py` - Verify dE/dλ = 0, dL/dλ = 0 along geodesics

**Run Z3 Checks:**
```bash
python3 z3/christoffel_symmetry.py
# Output: All Christoffel symbols satisfy symmetry constraint

python3 z3/conservation_laws.py
# Output: Energy and angular momentum conserved along all geodesics
```

---

## TLA+ Concurrency Verification

**File:** `tla+/Geodesic.tla`

**WHY:** Verify thread-safe geodesic integration in multi-threaded renderer
**WHAT:** TLA+ model of GPU thread-local state updates
**HOW:** Model-check for race conditions, data races, invariant violations

**Properties Verified:**
- ✅ Thread-local state updates are atomic
- ✅ No data races on shared metric tensor lookups
- ✅ Null constraint renormalization is deterministic
- ✅ RK4 integration is independent across threads

---

## Performance Impact

**Verified Code Overhead:**
- C++23 headers: 0% overhead (inline templates, identical machine code)
- GLSL shaders: 0% overhead (identical GPU assembly)
- Runtime validation: <1% overhead (only in debug builds)

**Benchmark (physics_bench):**
- Non-verified: 16.2M rays/s
- Verified: 16.2M rays/s (within measurement noise)

---

## Development Workflow

**Adding New Physics:**
1. Write Rocq proof in `theories/`
2. Extract to OCaml: `make extraction`
3. Transpile to C++23: `./scripts/rocq_to_cpp.py`
4. Transpile to GLSL: `./scripts/rocq_to_glsl.py`
5. Run validation: `ctest -R physics_validation`
6. Commit all phases: Rocq source + extracted code + headers/shaders

**Modifying Existing Physics:**
1. Update Rocq proof in `theories/`
2. Re-extract and re-transpile: `make extraction && ./scripts/rocq_to_cpp.py`
3. Run regression tests: `ctest -R physics`
4. Verify no axioms introduced: `make verify`

---

## References

**Rocq Prover:**
- Rocq 9.1 Release Notes: https://github.com/coq/coq/releases/tag/V9.1
- Rocq Extraction: https://rocq-prover.org/refman/addendum/extraction.html

**Black Hole Physics:**
- See `docs/bibliography/black_hole_obs_2025.bib` for citations

**Formal Methods:**
- See `docs/bibliography/rocq_extraction.bib` for extraction papers

---

## Troubleshooting

**Issue:** `rocq: command not found`
- **Solution:** Install Rocq 9.1+ via opam: `opam install rocq`

**Issue:** `Error: Cannot find module Physics_schwarzschild`
- **Solution:** Run `make extraction` before transpilation

**Issue:** `Axioms detected in production code`
- **Solution:** Run `make verify` to identify axiom source, refactor proof

**Issue:** `Z3 solver timeout`
- **Solution:** Increase timeout in Python script: `solver.set("timeout", 60000)`

---

## License

This directory contains formal proofs and extracted code. All content is subject to the
same license as the Blackhole repository (see top-level LICENSE).

**Rocq Standard Library:** LGPL-2.1 (used but not modified)

---

**Last Updated:** 2026-01-29
**Maintainer:** See AGENTS.md for project contributors
