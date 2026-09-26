# Audit harness

These scripts and drivers produced the numbers in reports 00-05. They measure the sources
at base commit `34e1bf1`. Later commits fix several of the measured defects, so a
reproduction runs against a worktree at that commit. `*.expected.txt` and `referee.json` hold
the expected output. Nothing here is part of the CMake build or CTest.

## Environment

Run the blocks below in `sh` or `bash` from the checkout root; zsh does not word-split the
unquoted file lists.

    PYTHON=${PYTHON:-python3}      # needs numpy, scipy, mpmath
    HARNESS=$PWD/docs/audits/physics-and-game-engine/harness
    BH=<absolute path of a Blackhole worktree at 34e1bf1>
    BOOST=<Boost include directory, e.g. the Conan boost package's p/include>
    OUT=<absolute scratch directory outside the tree>
    OG=<absolute path of the open_gororoba checkout>
    export PYTHONDONTWRITEBYTECODE=1

The compiler in the audit was clang 22.1.8. Every block runs in a subshell under `$OUT`, so
the tree stays clean. The Rust crates (`grx/`, `pe_bench/`) take path dependencies on an
open_gororoba checkout beside the Blackhole checkout (`../open_gororoba` from the checkout
root); edit the `path` in their `Cargo.toml` for another layout. Each Rust block copies
open_gororoba's own `Cargo.lock` beside the manifest, because a fresh resolution selects
yanked `chacha20` versions, runs `--offline` (`--locked` refuses the added root entry), and
deletes the lock afterward. Timings were pinned with `taskset -c 3`;
the accuracy columns do not depend on the host.

## Files and the findings they reproduce

| File | Reproduces |
|---|---|
| `checks.py` | 01 F3 (impact-parameter sign), F6/F7 (face-on g, Page-Thorne vs Newtonian peak), Doppler speed (02 F11), F10 (static-observer NaN) |
| `rcheck.py` | 01 F1 (`R_code` vs `R_true`, Theta/Q convention) |
| `shadow.py` | 01 F1-F3 capture edges at a = 0.9 (shipped, Q-fixed, fine-step, exact) |
| `shadow2.py` | 01 F1 width table (0.674-0.687x) and F3 mirrored edges |
| `pt_check.py` | 02 F1 and recommendation 1 (Page-Thorne closed form vs quadrature; continuous peaks 1.592, 1.563, 1.483, 1.278 r_isco) |
| `referee.py` | 02 referee column (ISCO, photon orbits, KN, KdS, Page-Thorne, eta) |
| `kerr_clocks.py` | 03 F3, F4, canon options (ZAMO vs orbit clocks, Miller spin, tidal numbers) |
| `check_orbits.py` | 00 item 15 (61,403x at `1 - a = 1.33e-14`), 03 F4 (10.8x cap) |
| `bh/driver.cpp` | 02 Blackhole column (F1-F5, F12, F13) |
| `bh/mino2.cpp` | 02 F6 (turning-point stall, 1.58524) |
| `bh/gfac.cpp` | 02 F11, 01 F7 (`kerrDiskGFactor` face-on) |
| `bh/ecg.cpp` | 02 F7 (null correction zeroes v_r) |
| `grx/` | 02 gr_core column (F7-F11, KN, KdS) |
| `game/probe.cpp` | 03 F5 (probe 1), F2 (probe 2), F9 (probe 3) |
| `game/probe_multihop.cpp` | 03 F1 (unlinked three-system chain) |
| `game/cadence_main.cpp`, `game/campaign_session_nowin.patch` | 03 F6 (cadence and wins-off columns) |
| `carlson/gen_ref.py`, `carlson/bench.cpp` | 05 M1 (Carlson R_F/R_D/R_J) |
| `carlson/boostpol.cpp` | 05 M2 (`promote_double`) |
| `stokes/gen.py`, `stokes/bench.cpp` | 05 M3 generic segments |
| `stokes/gen_thin.py`, `stokes/bench_thin.cpp` | 05 M3 thin segments (split-form cancellation) |
| `stokes/gen_mid.py`, `stokes/bench_mid.cpp` | 05 M3 intermediate segments |
| `stokes/exact2.h` | 05 M3 direct-integral propagator used by the three benches |
| `stokes/thin32.cpp` | 05 M3 FP32 emission factor near the guard |
| `kahan/k.cpp` | 05 M4 (plain vs Kahan FP32 RK4 roundoff, cost) |
| `kahan/k2.cpp` | 05 M4 (h/64 truncation bound and total error) |
| `roots/r.cpp`, `roots/r2.cpp` | 05 M5 (`findRadialRoots` as shipped: critical curve, simple quartics) |
| `roots/r4.cpp`, `roots/r3.cpp`, `roots/akg_fixed.patch` | 05 M5 (both resolvent lines corrected: critical curve, simple quartics) |
| `pe_bench/` | 05 N6/M1 (`pathion_ellip` Carlson, binary `pe_bench`), M5 (`solve_quartic`, binary `quartic`) |
| `quant/q.py` | 05 M6 (block quantization) |

## Replay

Python (compare with `*.expected.txt` and `referee.json`):

    for s in checks rcheck shadow shadow2 pt_check referee kerr_clocks check_orbits; do
      $PYTHON "$HARNESS/$s.py"
    done
    $PYTHON "$HARNESS/quant/q.py"

Report 02 drivers:

    (mkdir -p "$OUT/bh" && cd "$OUT/bh" &&
     clang++ -std=c++23 -O2 -I"$BH/src" -I"$BOOST" "$HARNESS/bh/driver.cpp" "$BH/src/physics/kerr.cpp" "$BH/src/physics/schwarzschild.cpp" -o driver && ./driver &&
     clang++ -std=c++23 -O2 -DDL=1e-5 -I"$BH/src" "$HARNESS/bh/mino2.cpp" "$BH/src/physics/kerr.cpp" -o mino2 && ./mino2 &&
     clang++ -std=c++23 -O2 -I"$BH/src" "$HARNESS/bh/gfac.cpp" -o gfac && ./gfac &&
     clang++ -std=c++23 -O2 -I"$BH/src" "$HARNESS/bh/ecg.cpp" -o ecg && ./ecg)
    (cp "$OG/Cargo.lock" "$HARNESS/grx/Cargo.lock" && cd "$OUT" &&
     CARGO_TARGET_DIR="$OUT/target" cargo run --offline --release --manifest-path "$HARNESS/grx/Cargo.toml";
     rc=$?; rm -f "$HARNESS/grx/Cargo.lock"; exit $rc)

Report 03 drivers (the five physics sources plus the non-`main` game sources):

    PHYS="$BH/src/physics/schwarzschild.cpp $BH/src/physics/geodesics.cpp $BH/src/physics/cosmology.cpp $BH/src/physics/kerr.cpp $BH/src/physics/noise.cpp"
    GAME=$(ls "$BH"/src/game/*.cpp | grep -v _main.cpp)
    (mkdir -p "$OUT/game/shadow/game" && cd "$OUT/game" &&
     clang++ -std=c++23 -O2 -I"$BH/src" -I"$BH/src/physics" $PHYS $GAME "$HARNESS/game/probe.cpp" -o probe && ./probe &&
     clang++ -std=c++23 -O2 -I"$BH/src" -I"$BH/src/physics" $PHYS $GAME "$HARNESS/game/probe_multihop.cpp" -o probe_multihop && ./probe_multihop &&
     patch -o campaign_session_nowin.cpp "$BH/src/game/campaign_session.cpp" < "$HARNESS/game/campaign_session_nowin.patch" &&
     NOWIN=$(echo $GAME | sed "s#$BH/src/game/campaign_session.cpp#$OUT/game/campaign_session_nowin.cpp#") &&
     clang++ -std=c++23 -O2 -I"$BH/src" -I"$BH/src/physics" $PHYS $GAME "$HARNESS/game/cadence_main.cpp" -o cadence30 && ./cadence30 &&
     clang++ -std=c++23 -O2 -I"$BH/src" -I"$BH/src/physics" $PHYS $NOWIN "$HARNESS/game/cadence_main.cpp" -o cadence30_nowin && ./cadence30_nowin &&
     sed 's/K_REISSUE_EVERY = 30;/K_REISSUE_EVERY = 1;/' "$BH/src/game/campaign_sim_lines.h" > shadow/game/campaign_sim_lines.h &&
     clang++ -std=c++23 -O2 -I"$OUT/game/shadow" -I"$BH/src" -I"$BH/src/physics" $PHYS $GAME "$HARNESS/game/cadence_main.cpp" -o cadence1 && ./cadence1 &&
     clang++ -std=c++23 -O2 -I"$OUT/game/shadow" -I"$BH/src" -I"$BH/src/physics" $PHYS $NOWIN "$HARNESS/game/cadence_main.cpp" -o cadence1_nowin && ./cadence1_nowin)

Report 05 drivers:

    (mkdir -p "$OUT/carlson" && cd "$OUT/carlson" &&
     $PYTHON "$HARNESS/carlson/gen_ref.py" &&
     clang++ -std=c++23 -O2 -I"$BH/src" -I"$BOOST" "$HARNESS/carlson/bench.cpp" -o bench && taskset -c 3 ./bench &&
     clang++ -std=c++23 -O2 -I"$BOOST" "$HARNESS/carlson/boostpol.cpp" -o boostpol && taskset -c 3 ./boostpol)
    (mkdir -p "$OUT/stokes" && cd "$OUT/stokes" &&
     $PYTHON "$HARNESS/stokes/gen.py" && $PYTHON "$HARNESS/stokes/gen_thin.py" && $PYTHON "$HARNESS/stokes/gen_mid.py" &&
     for b in bench bench_thin bench_mid; do
       clang++ -std=c++23 -O2 -I"$BH/src" "$HARNESS/stokes/$b.cpp" -o $b && taskset -c 3 ./$b || exit 1
     done &&
     clang++ -std=c++23 -O2 -ffp-contract=off "$HARNESS/stokes/thin32.cpp" -o thin32 && ./thin32)
    (mkdir -p "$OUT/kahan" && cd "$OUT/kahan" &&
     clang++ -std=c++23 -O2 -ffp-contract=off "$HARNESS/kahan/k.cpp" -o k && taskset -c 3 ./k &&
     clang++ -std=c++23 -O2 -ffp-contract=off "$HARNESS/kahan/k2.cpp" -o k2 && taskset -c 3 ./k2)
    (mkdir -p "$OUT/roots" && cd "$OUT/roots" &&
     patch -o akg_fixed.h "$BH/src/physics/analytic_kerr_geodesic.h" < "$HARNESS/roots/akg_fixed.patch" &&
     for r in r r2; do
       clang++ -std=c++23 -O2 -I"$BH/src" -I"$BOOST" "$HARNESS/roots/$r.cpp" -o $r && ./$r || exit 1
     done &&
     for r in r3 r4; do
       clang++ -std=c++23 -O2 -I"$OUT/roots" -I"$BH/src" -I"$BOOST" "$HARNESS/roots/$r.cpp" -o $r && ./$r || exit 1
     done)
    (cp "$OG/Cargo.lock" "$HARNESS/pe_bench/Cargo.lock" && mkdir -p "$OUT/pe_bench" && cd "$OUT/pe_bench" &&
     CARGO_TARGET_DIR="$OUT/target" cargo run --offline --release --manifest-path "$HARNESS/pe_bench/Cargo.toml" --bin pe_bench &&
     CARGO_TARGET_DIR="$OUT/target" cargo run --offline --release --manifest-path "$HARNESS/pe_bench/Cargo.toml" --bin quartic;
     rc=$?; rm -f "$HARNESS/pe_bench/Cargo.lock"; exit $rc)

`pe_bench` reads `../carlson/ref.csv`, so the Carlson block runs first.
