# Blackhole Simulator - Quick Reference Card
**Version 2026.1** | **EHT-Constrained Physics**

---

## One-Click Presets

```
┌─────────────────────────────────────────────────────┐
│ "Sgr A* (MAD, a*=0.94)" Button                     │
├─────────────────────────────────────────────────────┤
│ Mass:  4.3 × 10⁶ M☉  (EHT measured)                │
│ Spin:  0.94          (EHT-GRMHD constrained)       │
│ State: MAD           (magnetic equipartition)       │
│ Beta:  1.0           (P_gas ~ P_mag)                │
│ Flux:  50            (strong magnetic flux)         │
└─────────────────────────────────────────────────────┘
```

---

## Critical Parameters

### Black Hole Mass (M)
```
Range: 0.1 to 250 M☉
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Stellar:        3-100 M☉
Sgr A*:         4.3 × 10⁶ M☉
M87:            6.5 × 10⁹ M☉
GW231123 max:   225 M☉ (LIGO record)
```

### Kerr Spin (a*)
```
Range: -0.998 to +0.998
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Schwarzschild:  0.0   (non-rotating)
Sgr A*:         0.94  (EHT-constrained)
Near-extremal:  0.998 (maximum rotation)
Retrograde:     <0    (counter-rotating)

ISCO Scaling:
  a* = +0.998 → ISCO = 1.237 M  (near-extremal prograde)
  a* = +0.94  → ISCO = 2.024 M  (Sgr A*)
  a* = 0.0    → ISCO = 6.0 M    (Schwarzschild)
  a* = -0.998 → ISCO = 8.994 M  (near-extremal retrograde)
```

---

## Accretion States

```
┌──────────────┬──────────┬─────────┬──────────┐
│ State        │ Beta (β) │ Jet η   │ Variable │
├──────────────┼──────────┼─────────┼──────────┤
│ SANE         │ ~100     │ ~1%     │ No       │
│ MAD          │ ~1       │ 10-40%  │ Yes      │
│ Intermediate │ ~10      │ 5-15%   │ Moderate │
└──────────────┴──────────┴─────────┴──────────┘

β = P_gas / P_mag (magnetic pressure ratio)
η = P_jet / (Ṁc²)  (jet efficiency)
```

---

## Observing Frequencies

```
┌─────────────┬────────┬──────────────┬────────────┐
│ Frequency   │ λ (mm) │ Resolution   │ Status     │
├─────────────┼────────┼──────────────┼────────────┤
│ 230 GHz     │ 1.3    │ ~20 μas      │ Standard   │
│ 345 GHz     │ 0.87   │ ~13 μas      │ Next-gen!  │
│ Dual        │ Both   │ Multi-color  │ Combined   │
└─────────────┴────────┴──────────────┴────────────┘

Resolution improvement: 345/230 = 1.5× (50% better)
```

---

## Jet Physics

### Lorentz Factors (Γ)
```
Γ = 2      Mildly relativistic  (β = 0.87)
Γ = 5-15   Sgr A* typical
Γ = 10-20  M87 typical
Γ = 30-50  Blazars (extreme)

Velocity: β = √(1 - 1/Γ²)
```

### Opening Angles
```
5-10°   Narrow (MAD collimation)
15-30°  Moderate
45-60°  Wide (SANE, weak field)
```

### Jet Base Distance
```
Sgr A*: ~0.01 ly  (compact)
M87:    ~0.09 ly  (EHT measured, Jan 2026)
```

---

## Quick Validation Tests

### Test 1: Schwarzschild ISCO
```
Set: a* = 0.0
Expected: ISCO = 6.0 M
Visual: Disk inner edge at 3× Schwarzschild radius
```

### Test 2: Near-Extremal Kerr
```
Set: a* = 0.998
Expected: ISCO = 1.237 M
Visual: Disk very close to horizon
```

### Test 3: Retrograde
```
Set: a* = -0.9
Expected: ISCO > 6 M
Visual: Orange "Retrograde" label, larger disk
```

---

## Physics Constants

```
Schwarzschild radius:
  r_s = 2.95 km × (M/M☉)

Gravitational radius:
  r_g = GM/c² = 1.48 km × (M/M☉)

Hawking temperature:
  T_H = 6.17×10⁻⁸ K × (M☉/M)

Speed of light:
  c = 299,792 km/s

Solar mass:
  M☉ = 1.989 × 10³⁰ kg
```

---

## EHT Observational Constraints (2025-2026)

```
Sgr A*:
├─ Spin: a* = 0.94 ± 0.05  (arXiv:2510.03602)
├─ State: MAD favored
├─ Magnetic field: ~10% accuracy
└─ Variability: Hours timescale

M87:
├─ Jet base: 0.09 ly  (Jan 2026 detection)
├─ Frequency: 230 GHz, 345 GHz
├─ Opening angle: ~10°
└─ Lorentz factor: Γ ~ 10-20
```

---

## LIGO-Virgo-KAGRA O4 (2023-2025)

```
Total events: 250 merger detections

Record masses:
├─ GW231123: 225 M☉ final  (Nov 2023)
└─ Components: 140 M☉ + 100 M☉

Extreme spins:
├─ GW241011: Fastest rotating BH observed
└─ GW241110: First retrograde binary  (Oct 2024)

Validated range:
├─ Mass: 3 M☉ to 225 M☉
└─ Spin: -0.998 to +0.998
```

---

## Troubleshooting Quick Fixes

```
Low FPS:
  □ Disable magnetic field lines
  □ Disable jet visualization
  □ Reduce resolution

Wrong ISCO:
  □ Check spin sign (+ vs -)
  □ Prograde: small ISCO
  □ Retrograde: large ISCO

No magnetic effect:
  □ State must be MAD or Intermediate
  □ SANE ignores β and Φ parameters

Jet not visible:
  □ Check "Enable Jet Visualization"
  □ Increase Lorentz factor
  □ Adjust opening angle
```

---

## Keyboard Shortcuts

```
Camera:
  Click+Drag    Rotate view
  Scroll        Zoom in/out
  Middle-click  Pan

Window:
  F11           Fullscreen toggle
  ESC           Exit
```

---

## Citation

```bibtex
@software{blackhole2026,
  title = {Blackhole: EHT-Constrained Real-time Black Hole Renderer},
  year = {2026},
  version = {2026.1},
  url = {https://github.com/Oichkatzelesfrettschen/Blackhole},
  note = {Validated against EHT 2025-2026 and LIGO O4 observations}
}
```

---

## Key References

```
[1] EHT Collaboration (2025). arXiv:2510.03602
    "GRMHD modelling of Sgr A* constrained by EHT"

[2] LIGO-Virgo-KAGRA (2025). GW231123
    "Most massive black hole merger (225 M☉)"

[3] Blandford & Znajek (1977). MNRAS 179, 433
    "Electromagnetic extraction from Kerr black holes"

[4] Bardeen, Press, Teukolsky (1972). ApJ
    "Rotating black holes: ISCO formula"
```

---

## Version Info

```
Current: 2026.1 (EHT-Constrained)
Updated: 2026-01-31
Build:   Release, AVX2 optimized
Tests:   14/15 passing (93%)
GPU:     OpenGL 4.6+ required
```

---

**For detailed information, see USER_GUIDE.md**

**For physics background, see PHYSICS_UPDATE_2026.md**

**For implementation details, see PHYSICS_IMPLEMENTATION_PLAN.md**
