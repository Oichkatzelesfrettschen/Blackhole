# Audit harness

These scripts and drivers produced the numbers in reports 00-05. They measure the sources
at base commit `34e1bf1`. Later commits fix several of the measured defects, so a
reproduction runs against a worktree at that commit. `*.expected.txt` and `referee.json` hold the
expected output. Nothing here is part of the CMake build or CTest.

## Environment

    PYTHON=${PYTHON:-python3}      # needs numpy, scipy, mpmath
    HARNESS=$PWD/docs/audits/physics-and-game-engine/harness   # set from the checkout root
    BH=<Blackhole worktree at 34e1bf1>
    BOOST=<Boost include directory, e.g. the Conan boost package's p/include>
    OUT=<scratch directory outside the tree>

The Rust crates (`grx/`, `pe_bench/`) take path dependencies on an open_gororoba checkout
beside the Blackhole checkout (`../open_gororoba` from the checkout root); edit the
`path` in their `Cargo.toml` for another layout.
    CXX="clang++ -std=c++23 -O2"   # clang 22.1.8 in the audit

Every C++ and CSV-writing step runs in `$OUT`, so the tree stays clean. Python writes no
bytecode with `PYTHONDONTWRITEBYTECODE=1`.

## Scripts and the findings they reproduce

| File | Reproduces | Run |
|---|---|---|
| `checks.py` | 01 F3 (impact-parameter sign), F6/F7 (face-on g, Page-Thorne vs Newtonian peak), Doppler speed (02 F11), F10 (static-observer NaN) | `$PYTHON $HARNESS/checks.py` |
| `rcheck.py` | 01 F1 (`R_code` vs `R_true`, Theta/Q convention) | `$PYTHON $HARNESS/rcheck.py` |
| `shadow.py` | 01 F1-F3 capture edges at a = 0.9 (shipped, Q-fixed, fine-step, exact) | `$PYTHON $HARNESS/shadow.py` |
| `shadow2.py` | 01 F1 width table (0.674-0.687x) and F3 mirrored edges | `$PYTHON $HARNESS/shadow2.py` |
| `pt_check.py` | 02 F1 and recommendation 1 (Page-Thorne closed form vs quadrature; continuous peaks 1.592, 1.563, 1.483, 1.278 r_isco) | `$PYTHON $HARNESS/pt_check.py` |
| `referee.py` | 02 referee column (ISCO, photon orbits, KN, KdS, Page-Thorne, eta) | `$PYTHON $HARNESS/referee.py` |
| `kerr_clocks.py` | 03 F3, F4, canon options (ZAMO vs orbit clocks, Miller spin, tidal numbers) | `$PYTHON $HARNESS/kerr_clocks.py` |
| `check_orbits.py` | 00 item 15 (61,403x at `1 - a = 1.33e-14`), 03 F4 (10.8x cap) | `$PYTHON $HARNESS/check_orbits.py` |
| `bh/driver.cpp` | 02 Blackhole column (F1-F5, F12, F13) | `$CXX -I$BH/src -I$BOOST $HARNESS/bh/driver.cpp $BH/src/physics/kerr.cpp $BH/src/physics/schwarzschild.cpp -o $OUT/driver` |
| `bh/mino2.cpp` | 02 F6 (turning-point stall, 1.58524) | `$CXX -DDL=1e-5 -I$BH/src $HARNESS/bh/mino2.cpp $BH/src/physics/kerr.cpp -o $OUT/mino2` |
| `bh/gfac.cpp` | 02 F11, 01 F7 (`kerrDiskGFactor` face-on) | `$CXX -I$BH/src $HARNESS/bh/gfac.cpp -o $OUT/gfac` |
| `bh/ecg.cpp` | 02 F7 (null correction zeroes v_r) | `$CXX -I$BH/src $HARNESS/bh/ecg.cpp -o $OUT/ecg` |
| `grx/` | 02 gr_core column (F7-F11, KN, KdS) | `(cd $OUT && CARGO_TARGET_DIR=$OUT/target cargo run --release --manifest-path $HARNESS/grx/Cargo.toml)` |
| `game/probe.cpp` | 03 F5 (probe 1), F2 (probe 2), F9 (probe 3) | game build below |
| `game/probe_multihop.cpp` | 03 F1 (unlinked three-system chain) | game build below |
| `game/cadence_main.cpp` | 03 F6 (cadence and wins-off columns) | game build below |
| `carlson/gen_ref.py`, `carlson/bench.cpp` | 05 M1 (Carlson R_F/R_D/R_J) | `mkdir -p $OUT/carlson && cd $OUT/carlson && $PYTHON $HARNESS/carlson/gen_ref.py && $CXX -I$BH/src -I$BOOST $HARNESS/carlson/bench.cpp -o bench && taskset -c 3 ./bench` |
| `carlson/boostpol.cpp` | 05 M2 (`promote_double`) | `$CXX -I$BOOST $HARNESS/carlson/boostpol.cpp -o $OUT/boostpol` |
| `stokes/gen*.py`, `stokes/bench*.cpp`, `stokes/exact2.h` | 05 M3 (exact propagator vs RK4; `gen.py`/`bench.cpp`, `gen_thin.py`/`bench_thin.cpp`, `gen_mid.py`/`bench_mid.cpp`) | `cd $OUT && $PYTHON $HARNESS/stokes/gen.py && $CXX -I$HARNESS/stokes -I$BH/src $HARNESS/stokes/bench.cpp -o bench && ./bench` |
| `stokes/thin32.cpp` | 05 M3 FP32 emission factor near the guard | `$CXX -ffp-contract=off $HARNESS/stokes/thin32.cpp -o $OUT/thin32` |
| `kahan/k.cpp`, `kahan/k2.cpp` | 05 M4 (Kahan FP32 RK4; `k2` is the h/64 truncation bound) | `$CXX -ffp-contract=off $HARNESS/kahan/k.cpp -o $OUT/k` |
| `roots/r.cpp`, `roots/r2.cpp` | 05 M5 (`findRadialRoots` as shipped) | `$CXX -I$BH/src -I$BOOST $HARNESS/roots/r2.cpp -o $OUT/r2` |
| `roots/r3.cpp`, `roots/r4.cpp`, `roots/akg_fixed.patch` | 05 M5 (both resolvent lines corrected) | `patch -o $OUT/akg_fixed.h $BH/src/physics/analytic_kerr_geodesic.h < $HARNESS/roots/akg_fixed.patch && $CXX -I$OUT -I$BH/src -I$BOOST $HARNESS/roots/r3.cpp -o $OUT/r3` |
| `pe_bench/` | 05 N6/M1 (`pathion_ellip` Carlson), M5 (`solve_quartic`, `src/bin/quartic.rs`) | `mkdir -p $OUT/pe_bench && cd $OUT/pe_bench && CARGO_TARGET_DIR=$OUT/target cargo run --release --manifest-path $HARNESS/pe_bench/Cargo.toml` (after the M1 step, which leaves `$OUT/carlson/ref.csv`) |
| `quant/q.py` | 05 M6 (block quantization) | `$PYTHON $HARNESS/quant/q.py` |

## Game build

Report 03 section 12 describes it. The five physics sources plus the non-`main` game
sources link each driver:

    PHYS="$BH/src/physics/schwarzschild.cpp $BH/src/physics/geodesics.cpp $BH/src/physics/cosmology.cpp $BH/src/physics/kerr.cpp $BH/src/physics/noise.cpp"
    GAME=$(ls $BH/src/game/*.cpp | grep -v _main.cpp)
    $CXX -I$BH/src -I$BH/src/physics $PHYS $GAME $HARNESS/game/probe.cpp -o $OUT/probe

For the 03 F6 wins-off columns, patch `campaign_session.cpp` to victory thresholds of 1e6
and link the patched copy in its place:

    patch -o $OUT/campaign_session_nowin.cpp $BH/src/game/campaign_session.cpp < $HARNESS/game/campaign_session_nowin.patch

For the cadence-1 columns, copy `src/game/campaign_sim_lines.h` to
`$OUT/shadow/game/campaign_sim_lines.h`, set `K_REISSUE_EVERY = 1`, and put
`-I$OUT/shadow` ahead of `-I$BH/src`.

## Notes

- Cargo writes `Cargo.lock` beside each manifest; delete it after the run. The audit copied
  open_gororoba's own `Cargo.lock` there and ran with `--offline --locked`.
- The benchmark timings were pinned with `taskset -c 3`; the accuracy columns do not
  depend on the host.
