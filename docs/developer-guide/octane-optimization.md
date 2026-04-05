# Octane Optimization

This document defines the repo's practical Octane optimization policy for the
Blackhole Blender lane.

## Goals

- keep CUDA bridge preview responsive enough for scene iteration
- keep Octane final render visually authoritative
- make the quality/performance tradeoff reproducible in code and reports
- avoid hidden manual tuning in the OctaneBlender UI

## Official references

The policy below is grounded in the installed OctaneBlender property surface and
the official OTOY documentation:

- Octane Blender manual PDF:
  `https://docs.otoy.com/BlenderP/BlenderPluginManual.pdf`
- Installation process:
  `https://docs.otoy.com/blender/InstallationProcess.html`
- Octane server workflow:
  `https://docs.otoy.com/blender/OctaneServer.html`

The main principles reflected in our tiering are:

- Path Tracing is the default photoreal final kernel for complex lighting.
- Adaptive Sampling should use a real noise threshold and a minimum sample floor.
- AI Light is useful for complex lighting and interior-like light transport.
- Coherent Ratio and Max Tile Samples are speed-vs-artifact knobs and should be
  treated as optimization controls, not static "max quality" switches.

## Repo quality tiers

The addon now exposes three named Octane tiers through
`blackhole_physics.quality.apply_studio_quality()`:

- `interactive`
  - intended for lookdev and camera iteration
  - moderate samples, higher adaptive threshold, higher coherent ratio
  - keeps AI light on
- `balanced`
  - intended for the default repo benchmark and day-to-day final checks
  - more samples, tighter adaptive threshold, lower coherent ratio
  - this is the default Octane benchmark tier
- `cinematic`
  - intended for slower final frames and higher confidence comparison against
    the CUDA bridge preview
  - highest samples, tightest adaptive threshold, lowest coherent ratio

## How to optimize Octane for this project

Start with these priorities, in this order:

1. Keep the kernel on Path Tracing.
2. Use Adaptive Sampling with a meaningful threshold.
3. Use AI Light for complex scene lighting.
4. Raise `max_samples` only after the threshold and minimum samples are sane.
5. Use Coherent Ratio carefully:
   - increase it for interactive preview speed
   - decrease it for cleaner final convergence
6. Increase `parallel_samples` and `max_tile_samples` only as far as local VRAM
   and stability allow.
7. Keep bounce depth increases deliberate. More bounces are not free.
8. Compare preview vs final with the repo's diff artifacts instead of trusting
   subjective impressions alone.

## Repo-native commands

Default Octane benchmark:

```bash
cmake --build --preset release --target verify-octane-interactive-benchmark
```

Tier sweep:

```bash
cmake --build --preset release --target verify-octane-quality-sweep
```

The tier sweep writes:

- `build/<preset>/reports/octane_quality_sweep.json`
- `build/<preset>/reports/octane_quality_sweep_verified.json`
- `build/<preset>/reports/octane_quality_sweep_verified.md`

## Interpreting the sweep

The sweep is expected to show:

- `interactive` uses the fewest samples and the loosest threshold
- `balanced` sits in the middle
- `cinematic` uses the most samples and the tightest threshold

The verifier checks the policy itself:

- `max_samples` must be non-decreasing across the tiers
- `adaptive_noise_threshold` must be non-increasing across the tiers
- all tiers must keep the kernel on path tracing
- all tiers must keep AI Light enabled

That keeps the optimization lane honest even when Octane package versions
change.

## Scene stress lanes

The repo also carries a second Octane benchmark scene profile:

- `baseline`
  - the normal studio scene used by the default interactive benchmark and tier sweep
- `harsh_lighting`
  - adds stronger multi-light stress so preview/final agreement is tested under
    more demanding lighting

Run it with:

```bash
cmake --build --preset release --target verify-octane-harsh-scene
```
