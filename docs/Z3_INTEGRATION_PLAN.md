# Z3 Integration Plan

This plan scopes adding the Z3 SMT solver as an optional dependency for
constraint checks and invariant validation in the Blackhole pipeline.

## Why Z3
- Verify invariants (energy, Carter constant) for geodesic integrators.
- Solve constrained initial conditions (e.g., orbit parameters that match a target radius).
- Validate LUT monotonicity and guard against invalid ranges.
- Provide an offline sanity tool to check symbolic relationships.

## Conan + CMake
- Conan: `z3/4.14.1` from conancenter (center2).
- CMake: `-DENABLE_Z3=ON` to enable optional tooling.

## Proposed Targets
1. `z3_sanity` tool (CLI): solves a small constraint system to verify linkage.
2. `physics_z3_checks` (future): validates invariants using numeric samples.

## Integration Notes
- Keep Z3 optional to avoid increasing baseline build times.
- Bind to Z3 via the C++ API (`z3++.h`).
- Use solver results only for validation/diagnostics, not runtime rendering.

## Next Steps
1. Add Conan requirement and `ENABLE_Z3` CMake option.
2. Add a minimal `tools/z3_sanity.cpp` example.
3. Expand validation scripts to run Z3 checks when enabled.
