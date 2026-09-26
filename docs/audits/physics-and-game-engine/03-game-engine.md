# Game Engine Audit: Clocks, Canon, Gaps, Architecture

Scope: the game layer (`src/game/`, `src/ui/campaign_panels.cpp`,
`src/ui/strategic_map.cpp`, `tests/campaign_*_test.cpp`,
`tests/constellation_test.cpp`, `tests/kerr_time_field_test.cpp`) judged
against the stated vision: an Interstellar-canon black-hole setting with a
Cities: Skylines-style local builder running on local proper time and a
Stellaris-style interstellar layer where civilizations interact through
time dilation and light delay. Source baseline: `main` at `34e1bf1`
(2026-09-22).

Evidence provenance. The `build/Release` binaries date from 2026-07-19 and
predate `f1e0d16`, which touched `campaign.cpp`, `constellation.cpp`,
`serialize_bytes.h`, and `task_graph.cpp`. Every run below therefore uses a
fresh scratch compile of the HEAD sources (clang 22.1.8, the five
`PHYSICS_SRC_FILES` plus `src/game/*.cpp`, system GoogleTest 1.18); the
stale `ctest -R "campaign|constellation|kerr_time"` run (8/8 pass) is
reported only as corroboration. Fresh HEAD gtest results: balance-invariant
4/4, constellation 6/6, kerr_time_field 5/5, economy 10/10, clock 7/7,
task_graph 9/9, capabilities 6/6, instability 8/8. Canon numbers come from
an mpmath (60-digit) script and from arXiv PDFs fetched and grepped in this
session.

Tags: NEW (no repo doc names it), TRACKED (pointer given), TRACKED-BUT-WRONG
(a repo doc or comment asserts something the source contradicts).

## Summary

The game layer is a clean, deterministic, well-tested single-machine 4X
core, and it is not yet the vision. Its clocks model every entity as a
zero-angular-momentum hovering observer, so orbiting "lanes" carry the
wrong clock and Interstellar's Miller's planet cannot be represented at
all: the 0.998 spin clamp caps geodesic dilation at 10.8x where canon needs
61,362x at `1 - a = 1.33e-14`. The yield formula divides by `dtau/dt`,
which cancels time dilation out of the task-yield rate per coordinate turn,
so the central premise -- deep time is scarce -- does not reach the base
yield. Dilation reaches the game only through latency and through wear,
hazard, and containment, which accrue per proper day and so run slower per
turn in deep bands. The constellation layer leaks causality three ways: unlinked
systems exchange intel with zero delay, same-system intel skips the radial
light leg (2 turns instead of 154), and every authority knows its own remote
fleets' state instantly. The shipped balance invariant pins an artifact of
the scripted task cadence and the thresholds tuned to it: re-tasking every
turn instead of every 30 flips solo and pod from Lost to Won. There is no local layer, no diplomacy, no
tech, no pops, no versioned save, and no data-driven content; the digest
changes with `-march=native` through FMA contraction.

## 1. Ranked findings

### F1. Unlinked systems exchange intel, orders, and reports with zero delay -- NEW

- Location: `src/game/constellation.cpp:127-135` (`interAuthorityDelaySec`
  returns `0.0` for an unlinked pair), used unguarded by
  `scoreControlAndObserve` at `:420-432`, by `orderDelaySec` at `:137-144`,
  and by `reportDelaySec` at `:146-152`. The comment at `:132-133` ("a zero
  delay never applies because observations and orders across them are gated
  by the link check first") is false for observations and reports.
- OBSERVED for intel; orders and reports read from the code path. Probe
  on a chain of three systems, links 0-1 and 1-2 at 30
  light-days each, alpha holding system 0 band 0: after 2 turns the
  observer homed in system 1 (30 light-days away) still sees nothing, and
  the observer homed in system 2 (60 light-days away, unlinked) already
  sees alpha.
- Consequence: any constellation whose link graph is not complete gives
  distant factions omniscience about each other. The default two-system
  scenario is complete, so the bug is latent there and fires on the first
  third system.
- Falsifier: an observer two hops away learning of a band flip no earlier
  than the sum of the hop delays.
- Fix: replace the per-pair lookup with an all-pairs light-path matrix
  (Floyd-Warshall over the link graph at construction, `S^2` entries), and
  treat "no path" as "never delivered", never as zero.

### F2. Same-system and cross-system control intel skips the radial light leg -- NEW

- Location: `src/game/constellation.cpp:423-425` computes observation delay
  as `interAuthorityDelaySec(system, observerHome)` only; the band-to-
  authority leg that `reportDelaySec` includes is missing.
- OBSERVED. Two factions homed in the default M87 system (`a = 0.9`,
  authority at 200 r_s), alpha placed on band 0: the rival perceives alpha
  after 2 turns, while the Kerr radial light delay from band 0 to the
  authority is 153.8 turns.
- Consequence: the ledger's "DELAYED INTEL" thesis (`debt-ledger.md:1084`)
  holds only for the interstellar leg (TRACKED-BUT-WRONG in scope).
- Falsifier: a same-system observer seeing the flip no earlier than
  `ceil(signalDelaySec(band, authority) / secondsPerTurn)` turns.
- Fix: observation delay = intra(band -> local authority) + path(local
  authority -> observer authority), the same composition `reportDelaySec`
  already uses.

### F3. Every entity carries the ZAMO clock; lanes imply orbits the clock ignores -- ZAMO choice TRACKED, lane mismatch NEW

- Location: `src/game/kerr_time_field.h:5-9` ("Every fleet is modelled as a
  zero-angular-momentum observer"), `src/game/kerr_time_field.cpp:37-47`;
  lanes in `src/game/fleet.h` (`OrbitLane`) gate admissibility only. Ledger
  `debt-ledger.md:914` records the ZAMO choice and its reason (continuity
  into the ergoregion); no doc addresses what a lane's clock should be.
- OBSERVED (numbers from the source formula) plus INFERRED (which observer
  a "lane" means). A ZAMO has zero angular momentum and needs thrust to hold
  radius; a prograde or retrograde lane is an orbit. The two clocks differ
  by 0.5-64% on the shipped bands (section 3). Band 0 (0.85 r_s = 1.7 M at
  `a = 0.9`) sits below the prograde marginally bound radius 1.7325 M and
  inside the ISCO 2.3209 M: no bound orbit exists there, so only a powered
  hovering station can occupy it, and the "prograde lane" label with a
  Penrose-flavored yield bonus describes an orbit that does not exist.
- Falsifier: a prograde and a retrograde fleet at the same band reporting
  different `properTimeRate`.
- Fix: make the observer a property of the entity (`CircularGeodesic{pro|
  retro}`, `Hover{ZAMO}`, `Static`, `Transit{v}`) and route
  `properTimeRate` through it; refuse a geodesic lane below the photon
  orbit and flag it unstable below the ISCO; keep ZAMO for powered stations.

### F4. Canon Miller's planet is unrepresentable; the clamp caps geodesic dilation at 10.8x -- NEW

- Location: `src/game/kerr_time_field.cpp:20` (`K_MAX_SPIN_STAR = 0.998`),
  `:26` (clamp).
- OBSERVED (computed): at `a = 0.998` the prograde ISCO is 1.23697 M with
  `dtau/dt = 0.09267`, a 10.8x dilation. Canon needs 61,362x (1 hour = 7
  Julian years), which the BPT circular-orbit formula reaches at `1 - a =
  1.33e-14`, `r_ISCO = 1 + 3.76e-5 M` (section 4). The ZAMO model reaches
  61,362x at any spin only within `(r - r_+) ~ 1e-9 M` of the horizon,
  where no circular orbit exists.
- INFERRED: `a = 1 - 1.3e-14` stored as a `double` loses the physics,
  because `1 - a*a` cancels to about two significant digits (unit roundoff
  1.1e-16 against 2.7e-14). Option A below requires parameterizing the
  field by `delta = 1 - a` and computing `r_+ = M(1 + sqrt(delta(2 -
  delta)))` directly.
- Falsifier: a scenario whose Miller colony reports `dtau/dt` within 1% of
  1/61,362 while sitting on a stable prograde circular orbit.
- Fix: `KerrTimeField(massG, delta)` constructor, clamp removed, geodesic
  observer from F3; keep `a = 0.998` as a named preset.

### F5. `dtau/dt` cancels out of the task-yield rate; dilation reaches only latency and per-proper-day wear -- NEW

- Location: `src/game/economy.h:27-29` (`taskYieldUnits = properHours /
  properTimeRate * reliability`), consumed per report at
  `src/game/constellation.cpp:373-381` and per task at
  `src/game/campaign.cpp:309-312`.
- OBSERVED. A fleet working continuously produces `rate * T` proper seconds
  per turn, each paid `1/rate`, so every band yields `T/3600` units per
  coordinate turn. Probe (one fleet, M87 `a = 0.9`, 3000 turns, no bonus,
  wear, or instability): band 0 through 3 bank 68,242 / 68,393 / 68,532 /
  69,264 units; the spread equals 24 units times the report-delay
  difference (153.8 vs 112.2 turns) and nothing else.
- OBSERVED (source). The cancellation covers the yield rate only. Both
  shipped configs set `reliabilityWearPerProperDay = 0.002`
  (`campaign_session.cpp:47`, `constellation_session.cpp:82`), and wear,
  ergoregion hazard, and containment all accrue per proper day
  (`campaign.cpp:276-297`, `constellation.cpp:350-364`). Per coordinate
  turn a fleet therefore wears by `rate * (0.002 + 0.15 depth)` per day of
  turn length: base wear slows with depth, while the hazard term can make a
  prograde-ergoregion fleet wear faster. Yield multiplies by reliability,
  so a deep fleet outside the ergoregion keeps a higher yield multiplier
  per outside turn. In the campaign, wear accrues only while working, and
  the 0.9 corruption threshold (`campaign_session.cpp:66`) arrives after
  `50/rate` busy turns (at 86400 s per turn) instead of 50. The
  constellation wears every turn toward the 0.5 floor with no threshold.
  Containment per turn also scales with `rate * depth`.
- Consequence: the design premise "deep work is worth more because local
  hours are scarce" (`campaign.h` config comment, ledger `:911` "10x deep
  yield") is true per task and neutral per turn. The deep-versus-outer
  choice is carried by `frameDragYieldBonus`, `ergoContainmentPerProperDay`,
  and `containmentYieldRetention`, which are not clock effects, and by the
  slower per-turn wear above, which is. That wear effect rewards depth by
  aging it less, not by making its hours scarce. Interstellar's premise is the opposite
  direction: an hour at Miller's costs the outside seven years.
- Falsifier: two continuously busy fleets at different bands with no bonus
  knobs and wear disabled banking different energy per coordinate turn
  after reports settle.
- Fix is a design decision, not a bug fix: either value local output per
  proper hour (deep colonies produce less per outside year, which is the
  canon reading) and give depth its own payoff, or keep coordinate valuation
  and delete the "scarcity" framing. Section 10 states candidate payoffs as
  hypotheses.

### F6. The locked balance shape depends jointly on task cadence and thresholds -- NEW

- Location: `src/game/campaign_sim_lines.h:38-39` (`K_REISSUE_HOURS = 24`,
  `K_REISSUE_EVERY = 30`), asserted by
  `tests/campaign_balance_invariant_test.cpp:37-68`; thresholds in
  `src/game/campaign_session.cpp` (3150 energy, 8.0 stabilization).
- OBSERVED. One 24-proper-hour task per fleet per 30 turns leaves every
  fleet idle most of each window (about 2 turns of work outer, 4 deep).
  Scratch runs of the same four lines, 1200 turns:

  | Line | Cadence 30 (shipped) | Cadence 1, shipped thresholds | Wins off, cadence 30: energy / stab | Wins off, cadence 1: energy / stab |
  | --- | --- | --- | --- | --- |
  | outer | Won t1097 | Won t339 | 3,444 / 0.0 | 47,610 / 0.0 |
  | solo | Lost | Won t347 | 2,990 / 2.2 | 35,575 / 16.9 |
  | pod | Lost | Won t336 | 2,420 / 6.7 | 21,817 / 50.0 |
  | stab | Won t819 | Won t251 | 618 / 12.6 | 4,746 / 100.3 |

- INFERRED reading. Cadence 1 delivers about 14x the energy volume the
  thresholds were tuned for, so "every line wins" there says the thresholds
  are met trivially, not that the design changed. What the runs do show:
  the energy/stabilization ranking is identical at both cadences (a pure
  exchange along one front); the locked win/lose split is a joint property
  of cadence and thresholds, and a human player controls the cadence;
  under always-busy play all four lines clear within 96 turns of each
  other with pod edging past outer; and integrity falls to the 0.5 floor on
  every line, erasing outer's only off-axis advantage.
- Falsifier: the shipped Won/Lost split surviving cadences 1-30 with
  thresholds rescaled to the delivered volume.
- Fix: pin balance under the cadence a player would use (always busy) with
  thresholds scaled to it, or make task issuance a scarce resource so the
  cadence is a mechanic rather than a script constant.

### F7. The determinism digest depends on `-march=native` through FMA contraction -- TRACKED scope, NEW mechanism

- Location: `CMakeLists.txt:426` (`ENABLE_NATIVE_ARCH` default ON) with
  clang's default `-ffp-contract=on`; `blackhole_campaign` receives
  `-march=native ... -fno-fast-math` and no contraction override
  (`build/Release/compile_commands.json`).
- OBSERVED. Same HEAD sources, same host (Ryzen 5 5600X3D):

  | Build | campaign_sim (solo) | constellation outer / all-in / contest |
  | --- | --- | --- |
  | `-O3 -march=native` | `4501c3c8dfd4de66` | `2bb8c2e9...` / `c16d98d1...` / `76c20eb8...` |
  | `-O0 -march=native` | `4501c3c8dfd4de66` | same as above |
  | `-O3 -march=native -ffp-contract=off` | `ddec6029cb90c21d` | `648c1f2b...` / `bfe8f403...` / `12d302f4...` |
  | `-O2` generic x86-64 | `ddec6029cb90c21d` | same as contract-off |

  Printed energies, stabilization, and cleared turns are identical to three
  decimals across all builds; only low bits differ. The stale July binaries
  reproduce the native digests exactly, which corroborates `f1e0d16`'s
  "preserve replay serialization" claim. INFERRED, not verified: the
  ledger's "fast-math digest == IEEE" checks (`:937`, `:950`) held because
  both builds were native.
- Consequence: the scope "same binary and host" (`campaign.h:171-176`) is
  honest, but any save, replay, or lockstep peer built with different flags
  or run on a CPU without FMA diverges, and a low-bit difference can flip a
  `ceil` or a threshold compare later in a long game.
- Falsifier: native and generic digests matching.
- Fix: `-ffp-contract=off` and no `-march=native` on `blackhole_campaign`
  and on the `PHYSICS_SRC_FILES` objects the desktop executables compile
  themselves (the ledger's residual ODR note: those exes resolve physics
  symbols from their own objects, not from the archive);
  move `std::log` and `std::sqrt` out of the per-turn path by quantizing
  delays to integer turns and rates to fixed point at scenario load, and
  serialize the quantized tables into the save (section 8).

### F8. Authorities know their own remote fleets instantly -- NEW

- Location: `src/game/constellation.cpp:208-226` (issue-time gates read the
  fleet's true `inTransit`, band, and fuel), `:513-516` (`fleetAvailable`),
  `:499-507` (`factionOccupies`); `src/game/campaign.cpp:147` (fuel gate
  against the fleet's live fuel).
- OBSERVED by reading; INFERRED impact. A faction 40 light-days from its
  fleet validates orders against state light has not delivered; the
  Expansionist AI plans from the same live state. Rival state is causal
  (perceived table); own state is not.
- Referee leak, same class: when any faction wins, `decided_` makes
  `issueCommand` (`:202`) refuse every faction's orders from then on
  (`evaluateOutcomes`, `:458-490`), so a rival 40 light-days away is stopped
  by news that cannot have reached it. OBSERVED by reading.
- Falsifier: an order that the authority's last report says is affordable
  being refused because of a fuel spend the authority cannot yet know about.
- Fix: a per-faction "last-known own fleet" record updated by the same
  report deliveries; validate against belief, resolve at effect time (the
  effect-time fizzle already exists).

### F9. Interstellar transit ages crews at the coordinate rate -- NEW

- Location: `src/game/constellation.cpp:338-341`.
- OBSERVED. A 40 light-day hop at 0.5c occupies 80 turns; the fleet ages
  79.82 proper days. Special relativity gives `80 * sqrt(1 - 0.25) = 69.28`.
- Consequence: the twin paradox, the simplest time-dilation mechanic a
  Stellaris layer could use, is absent; fleets gain no proper-time saving
  from speed.
- Fix: accrue `sqrt(1 - beta^2) * T` in transit (plus the well-exit
  factors if departures start deep), and expose `beta` as a design axis
  against fuel.

### F10. Signal delay ignores azimuth and orbital motion -- NEW

- Location: `src/game/kerr_time_field.cpp:59` and
  `src/game/blackhole_time_field.cpp:34` return `0.0` for equal radii;
  `src/game/campaign.cpp:346-370` applies band-local effects instantly to
  the whole ring.
- OBSERVED (numbers) plus INFERRED (gameplay weight). At M87 scale
  (`GM/c^3 = 0.3706 d`) the half-circumference of the 50 r_s band is 116.4
  light-days, which the code treats as 0; authority-to-band at 100 M is
  112.2 d radially against at least 185.3 d for an antipodal station
  (section 5). Stations on different orbits also change separation every
  orbit, so real delay is time-dependent (conjunction and opposition).
- Fix: give each station an azimuth and an orbital phase; delay = radial
  closed form plus a flat-chord-plus-Shapiro correction, quantized per turn.

## 2. Further findings

| ID | Tag | Evidence | Location | Finding | Falsifier | Fix |
| --- | --- | --- | --- | --- | --- | --- |
| F11 | TRACKED-BUT-WRONG | OBSERVED (read + sim) | `tests/constellation_test.cpp:4`; `src/game/constellation_sim_lines.h:33` vs `:95-101` | Test brief says "non-dominance invariant", retracted by the ledger (`:1102`); the test proves one winning line (home fortress) against one scripted rival. `Contest` is documented as travelling onto rival bands; the code holds home bands. | A second rival policy under which a different line wins. | Rename to `Fortress`, fix both comments, pin a second rival. |
| F12 | TRACKED-BUT-WRONG | OBSERVED (computed) | `src/game/constellation_types.h:90-92`; `constellation_session.cpp:39,53` | The link is called "the dominant term" because it "dwarfs either hole's r_s"; the default 40 light-day link is shorter than M87's authority radius (148 light-days) and the 153.8-day band-0 leg. | Intra-system legs below 10% of the link delay. | Separate systems well beyond both authority radii, or model the link as a wormhole. |
| F13 | NEW | INFERRED (computed) | none | No tidal physics; at the canon orbit an Earth-density planet needs about 2.8e8 M_sun (section 4). `ergoHazardWearPerProperDay` is a free knob. | A tidal term derived from the metric in any game file. | Marck eigenvalue per station; Roche admissibility. |
| F14 | NEW, physics cross-ref | OBSERVED (read) | `src/physics/iron_kline.h:91-109` | `kerrDiskGFactor` uses `u^t = 1/sqrt(f)`, dropping `(1 + a r^{-3/2})` (about 1.73 at the `a = 0.998` ISCO); its comment calls `f = 0` the ISCO, which is the photon orbit. The game must not reuse it. | `g` matching the full Cunningham form at `a = 0.998`. | Route to report 01. |
| F15 | NEW | OBSERVED (grep) | `docs/developer-guide/status.md`, `roadmap.md` | Neither mentions the campaign or constellation; the ledger is the only tracker. | A game-layer entry in either file. | Add a status section pointing at the ledger tranches. |
| F16 | TRACKED (`debt-ledger.md:1114` (e); `campaign.h:171-176`) | OBSERVED (read) | `serializeState` | Determinism artifact only: no TimeField, no task-graph next id, no version tag. | A save that restores a mid-game state on a fresh process. | Versioned save (section 8). |
| F17 | TRACKED (`debt-ledger.md:1114` (c)) | OBSERVED (grep) | `src/ui/` | No constellation UI. | Any `Constellation` reference under `src/ui`. | Galaxy-map slice. |
| F18 | NEW | OBSERVED (read) | `src/game/campaign.cpp:423-424` | The authority's proper-time rate is displayed and never read; the turn is coordinate time at infinity, not the capital's clock. | A mechanic reading `authorityProperTimeRate`. | Decide whose calendar the player lives on (section 9). |

## 3. Clock fidelity: which observer each entity is

Default scenario: M87 (`6.5e9 M_sun`), `a = 0.9`, bands 1.7 / 6 / 20 / 100
M, authority 400 M. Characteristic radii at `a = 0.9`: `r_+ = 1.43589 M`,
static limit 2 M, prograde photon orbit 1.55785 M, prograde marginally bound
1.73246 M, prograde ISCO 2.32088 M, retrograde photon orbit 3.91027 M,
retrograde ISCO 8.71735 M. Rates are `dtau/dt` against coordinate time.

| Entity in code | Code clock | Physically correct observer | Correct `dtau/dt` | Gap |
| --- | --- | --- | --- | --- |
| Fleet, band 0 (1.7 M), prograde | ZAMO 0.25392 | No bound orbit (below r_mb, inside ISCO): powered hover only; the unbound, unstable prograde circular orbit would read 0.15480 | 0.25392 if hovering | lane label wrong; +64% if read as orbit |
| Fleet, band 1 (6 M), prograde | ZAMO 0.81798 | Stable prograde circular orbit | 0.74344 | +10.0% |
| Fleet, band 1 (6 M), retrograde | ZAMO 0.81798 | Retrograde circular orbit (exists, unstable inside 8.717 M) | 0.65451 | +25.0% |
| Fleet, band 2 (20 M) pro / retro | ZAMO 0.94869 | Stable circular orbits | 0.92351 / 0.92024 | +2.7% / +3.1% |
| Fleet, band 3 (100 M) pro / retro | ZAMO 0.98995 | Stable circular orbits | 0.98491 / 0.98486 | +0.5% |
| Authority station (400 M) | ZAMO 0.99750, displayed only | Orbiting station | 0.99624 | +0.13% |
| Relay, Fabrication, Verification | same as fleets | same as fleets | -- | -- |
| Fleet in interstellar transit | 1.0 (coordinate) | Inertial at 0.5c | 0.86603 | +15.5% |
| Colony / planet | does not exist | Circular geodesic | -- | -- |

The Schwarzschild field (`BlackholeTimeField`, used by tests and any `a = 0`
session) is the static observer `sqrt(1 - r_s/r)`: 0.81650 / 0.94868 /
0.98995 at 3 / 10 / 50 r_s, against circular-orbit 0.70711 / 0.92195 /
0.98489. The strategic map's ring colors and the ledger's CAMPAIGN-2
verification numbers (`debt-ledger.md`, "0.8165/0.9487/0.9899") are the
static values, correct for hovering stations and 15.5% fast at the 3 r_s
ISCO for anything that orbits.

The ZAMO lapse stays finite into the ergoregion, a merit of powered
stations; a colony on a planet is a geodesic, and canon dilation is a
geodesic number.

## 4. Interstellar canon

Sources fetched and grepped in this session:

- Quotations below are transliterated to ASCII per `scripts/ascii_sweep.py`; exponents read `x 10^-n`.
- arXiv:1502.03808 (James, von Tunzelmann, Franklin, Thorne 2015): "for
  visual purposes Nolan and Franklin slowed the spin to a/M = 0.6"; figure
  15 caption: "with the black hole's spin slowed from a/M = 0.999 to a/M =
  0.6"; the physics spin is "a/M ~= 1, required to explain the huge time
  losses".
- arXiv:1601.02897 (Opatrny, Richterek, Bakala, "Life under a black sun"):
  "For Gargantua, the rotation parameter a was extraordinarily large, a =
  1 - 1.3 x 10^-14"; orbit "r = 1.0000379GM/c2".
- arXiv:2606.01921 (Dhingra, Dhurandhar, Mitra): mass "~ 10^8 Msun"; "a
  factor of 60, 000 ... delta ~= 1.4 x 10^-14"; "epsilon ~= 3.8 x 10^-5" for `r_ISCO =
  (1 + epsilon)m`; "the planet remains marginally intact - the Roche limit is of
  the same order as the size of the horizon".
- Film transcript (scrapsfromtheloft.com): "Every hour we spend on that
  planet will be seven years back on Earth"; TARS: "23 years, four months,
  eight days"; "Data transmission back through the wormhole is
  rudimentary"; "We've been receiving, but nothing gets out"; "Messages span
  23 years."
- Luminet (inference-review.com, "Interstellar Science") gives "as close as
  1e-10 to the critical value Jmax", four orders of magnitude off the two
  independent derivations above for the same 60,000x; treat it as an
  inconsistent source.

Computed (mpmath, 60 digits, BPT prograde circular orbit `dtau/dt =
sqrt(1 - 3M/r + 2a M^{1/2} r^{-3/2}) / (1 + a M^{1/2} r^{-3/2})`, target
`7 * 365.25 * 24 = 61,362`): `1 - a = 1.3327e-14`, `r_ISCO = 1.0000376 M`,
`dtau/dt = 1.62967e-5`, `E = 0.57737`, `L = 1.15474 M`. This agrees with
both papers. The ZAMO lapse at the same point is 1.8818e-5, so the repo's
observer model at the canon orbit undercounts dilation by `2/sqrt(3)`
(53,140x instead of 61,362x): at the extremal ISCO the orbit moves at c/2
relative to the ZAMO.

Derived at `M = 1e8 M_sun` (`GM/c^3 = 492.56 s`), all INFERRED: coordinate
orbital period 1.719 h, proper period 0.101 s against distant stars;
frame dragging at that radius is `omega = 0.99999 Omega`, so the orbit
barely turns against local gyroscopes; Marck radial stretch
eigenvalue `(2 + 3K/r^2) M/r^3 = 3.00/M^2` with `K = (L - aE)^2`, a
gradient of 1.24e-5 s^-2 (8.0 g across an Earth radius) and a
self-gravity-equals-tide density of 44 g/cm^3, so an Earth-density planet
needs about 2.8e8 M_sun. That matches "marginally intact" in order of
magnitude. Endurance's parking radius and any numbers for Mann's and
Edmunds' planets are UNCONFIRMED: no fetched source states them. The film
attributes the message backlog to dilation, not to light travel.

### Canon options

| Option | Spin | Miller orbit | Miller `dtau/dt` | Dilation | Source | Game consequence |
| --- | --- | --- | --- | --- | --- | --- |
| A. Physics canon | `1 - a = 1.33e-14` | prograde ISCO `1 + 3.76e-5 M` | 1.630e-5 | 61,362x | computed; 1601.02897; 2606.01921 | Requires `delta` parameterization, clamp removal, geodesic observer. A 1-day turn gives the colony 1.41 s; a 1200-turn campaign gives it 28 proper minutes. |
| B. Rendered Gargantua | 0.6 | ISCO 3.8291 M | 0.5682 | 1.76x | 1502.03808 verbatim | No Miller's planet; the film itself decoupled render spin from physics spin. |
| C. Thorne 1974 limit (repo clamp) | 0.998 | ISCO 1.23697 M | 0.09267 | 10.8x | computed | Present engine ceiling for orbits. |
| D. Graded presets | `1 - a = 1e-4` / `1e-8` | ISCO 1.07853 / 1.00343 M | 0.03277 / 0.001483 | 30.5x / 674x | computed | Useful for secondary systems and difficulty tiers. |
| E. Hovering (repo ZAMO) | any | `r - r_+ = 6.6e-10 / 1.2e-9 / 8.4e-9 M` at a = 0.6 / 0.9 / 0.998 | 1.630e-5 | 61,362x | computed | Non-geodesic; hover thrust diverges at the horizon (INFERRED); contradicts a planet in orbit. |

Recommendation: A for the Gargantua system, with D as named presets
elsewhere and B as the renderer's spin, disclosed in the UI the way the
film's own team did it. A wormhole link to the home system is canon and
should be a distinct edge type: short path length, and the film's
asymmetric channel ("nothing gets out") is a mechanic the link graph can
express.

## 5. Signal delay beyond the radial case

The Kerr closed form in `kerr_time_field.cpp:54-76` is correct for the
principal null congruence: at `a = 0.9` from 1.7 M to 400 M it gives
414.82361 M, matching numerical quadrature of `(r^2 + a^2)/Delta` to 12
digits. The model is the problem, not the arithmetic.

| Pair (M87, `a` near 0 for the chord estimate) | Code | Geometry floor |
| --- | --- | --- |
| Authority 400 M -> band 100 M, same azimuth | 112.2 d | 112.2 d |
| Authority 400 M -> band 100 M, antipodal | 112.2 d | at least 185.3 d (flat chord) |
| Authority -> band 20 M, antipodal | 143.1 d | at least 155.6 d |
| Authority -> band 6 M, antipodal | 149.4 d | at least 150.5 d |
| Two stations on band 100 M, antipodal | 0 | 116.4 d |
| Two stations on band 6 M, antipodal | 0 | 7.0 d |

Deep-to-far links stay within 1%; same-band and outer-band pairs err by
weeks to months at M87 scale, while band-local effects and co-location
control act instantly across the whole ring. Orbiting stations make delay
periodic -- communication windows the radial model cannot produce.

## 6. Gap map against the vision

| Vision element | Exists? (evidence) | Minimal credible design | Effort |
| --- | --- | --- | --- |
| Local tile/zone grid | No (no grid, zone, or tile type in `src/game`) | Fixed-size grid per colony, zoning enum per cell, integer state | M |
| Road / network graph | No | Per-colony graph (roads, power, water) with integer capacities; flow solved per local tick | M |
| Population agents | No | Aggregate cohorts per cell (age buckets, needs) rather than per-agent; agents only for focused colony | L |
| Services and coverage | No | Service buildings with radius and capacity; coverage recomputed on change | M |
| Traffic | No | Aggregate trip assignment on the road graph at local tick; LOD off-focus | L |
| Per-district economy | No; one scalar `energyUnits` per faction | Fixed-point resource vectors per colony; trade via delayed shipments | M |
| Local clock in proper time | Partial: per-fleet `properTimeSec` accumulates (`fleet.h`), nothing runs on it | Fixed-point rate per colony, integer tick accumulator (section 9) | S |
| Regional (system) clock | Partial: one global `TemporalClock` | Per-system logical process with its own event queue | M |
| Correct orbital clocks | No (F3, F4) | Observer-typed entities, `delta`-parameterized Kerr | S |
| Tidal constraint | No (F13) | Marck eigenvalue per orbit, Roche admissibility | S |
| Factions | Yes: 4 policies, energy/stabilization/control (`constellation_types.h`) | Keep; add goals and memory | -- |
| Diplomacy | No | Messages (offer, treaty, threat) as light-delayed deliveries; treaties bind at the receiver's receipt | M |
| Intel delay | Yes with leaks (F1, F2, F8) | Path-matrix delay, per-faction belief for own and rival state | S |
| War / combat | Co-location denial only | Engagement resolution at co-located bands, damage in proper time | M |
| Species / pops | No | Species traits scaling needs and lifespan in proper time | M |
| Tech tree | No (Research is a yield multiplier) | Data-defined DAG, research paid in proper-time labor | M |
| Events | No | Data-defined event deck, triggers on state predicates, delayed notification | M |
| AI opponents | 3 greedy single-order policies | Utility AI over belief state; must read only perceived state | L |
| Ergosphere / near-horizon / far-field regimes | Yes (bands, ergo depth, lanes) | Keep; correct clocks | -- |
| Binary or multiple black holes in one system | No | Out of scope for exact metrics; superposed far-field clocks only | L |
| Relativistic travel / twin paradox | No (F9) | SR factor in transit; speed as a fuel trade | S |
| Wormhole links | No | Link type with short path and optional one-way channel | S |
| Versioned save/load | No (F16) | Section 8 | M |
| Data-driven content / modding | No: every scenario constant is C++ (`campaign_session.cpp`, `constellation_session.cpp`) | TOML/JSON scenario + content defs, schema-validated at load | M |
| ECS / data-oriented layout | No: vectors of structs with linear `find` | Struct-of-arrays per component once entity counts pass ~1e4 | M |
| Simulation LOD | No | Focus colony full-rate, others summarized per proper-time epoch | M |
| Time-dilation UX | Partial: rate-colored rings, `dtau/dt` column, delay labels | Per-colony local calendar, "age gap" readout, message-backlog inbox | M |
| Constellation UI | No (F17) | Galaxy map | M |
| Balance evidence | Partial: invariants pin one cadence (F6) and one rival (F11) | Invariants over cadence and rival sweeps | S |

## 7. What the balance tests prove

`campaign_balance_invariant_test` proves, for seed 42, 1200 turns, and a
24-hour task every 30 turns: outer wins by energy at t1097, all-in wins by
stabilization at t819, solo and pod lose, and replay digests match. It does
not prove that any line is a decision. All-in reaches Won 278 turns sooner
and nothing reads integrity, surplus, or cleared turn after Won, so all-in
weakly dominates (ledger `:1030` says so). F6 shows the solo/pod losses
depend on the scripted cadence together with thresholds tuned to it.

`constellation_test` proves determinism across two factions and two systems
with AI active, interstellar transit duration, the delayed interstellar
intel leg, co-location denial, and that against the Expansionist policy the
home fortress wins (t1325) while outer (t786) and all-in (t584) lose. That
is one solution to one opponent. The ledger's own framing ("FORCED CONTEST",
`:1102`) is the defensible claim; the test's brief ("non-dominance
invariant") is not.


## 8. Engine architecture

### Determinism

What holds: the integer turn is the only loop variable; coordinate time is
derived; arrival turns are quantized once with `ceil`; delivery order is
`(effectTurn, sequence)`; containers are id-ordered; serialization is
explicit-width little-endian with -0.0 canonicalized. That is the right
skeleton for lockstep and replay.

What breaks portability: gameplay state is IEEE `double` updated every turn
(`reliability`, `properTimeSec`, `energyUnits`, `instability`), computed
through `std::sqrt` (correctly rounded, portable) and `std::log`
(libm-dependent, not portable across glibc, macOS, and MSVC), and compiled
with FMA contraction on native builds (F7). The standard remedy is to keep
floating point at load time only: evaluate every metric quantity once per
scenario or per orbital epoch, quantize delays to integer turns and rates
to fixed point, store those tables in the save, and run the per-turn
simulation in integers. The save then carries its own physics, and a peer
never recomputes a transcendental function mid-game.

### Conservative parallel discrete-event structure

Regions on different proper clocks coupled by light delay are the textbook
case for Chandy-Misra-Bryant conservative simulation: each system is a
logical process, and the minimum light delay on its outgoing links is the
lookahead. In the default scenario the two systems could each advance 40
turns without synchronizing. The code is not structured to use it: one
global `deliveryQueue_` vector scanned and rebuilt every turn
(`constellation.cpp:275-307`), one global turn loop, and zero-delay
band-local effects inside a system (which pin a system to a single logical
process; that is acceptable). Per-system queues plus the F1 path matrix are
the prerequisite; parallel advance follows.

Scaling, INFERRED from the loop structure (no timing run): per turn,
`deliverDue` is O(Q); `scoreControlAndObserve` is O(S*B*F) plus O(N) per
control change; the Expansionist step is O(F*(F + S*B*(F + Q))) per
faction because `factionOccupies` scans fleets and `hasCommandInFlight`
scans the queue inside the band loop; `factionIndex` and `linkSeparationCm`
are linear scans called inside loops. The default scenario (S=2, B=4, F=8,
N=2) is trivial. At Stellaris scale (S=1000, B=5, F=5000, N=20, Q=1e4)
the Expansionist step alone is order 1e11 operations per faction per turn.
Fixes are indexes, not algorithms: a band-occupancy table, an in-flight
flag per fleet, id-indexed faction and fleet lookup, and a precomputed
`S x S` path matrix. Pairwise delay does not need an `n^2` table for n
colonies: delay(i, j) = intra(i -> authority) + path(S_i, S_j) +
intra(authority -> j) needs `S^2 + n` storage.

### Missing engine pieces

A versioned save needs a header (magic, format version, build id), the
scenario definition with field parameters and the quantized physics tables,
the full mutable state, the command log, and per-version migrations;
`serializeState` stays the digest input. Content (systems, factions,
capabilities, balance constants) moves to schema-checked TOML or JSON, with
C++ keeping mechanisms. Struct-of-arrays components follow once entity
counts pass thousands; stable ids already exist. LOD runs the focused
colony in full and advances the rest in proper-time epochs. `CampaignState`
becomes the 1-system, 1-faction case of `Constellation` (ledger `:1114`
(d)).

## 9. Proposed layered architecture

The layers are ordered by clock. The local layer runs in each colony's
proper time. The regional layer owns coordinate time for one black hole and
the light delays inside it. The interstellar layer is a message-passing
graph between regions whose edges are light paths or wormholes. The physics
oracle is consulted at load and at orbital epochs, never per tick.

```
            +-----------------------------------------------------+
 L3         | Interstellar: factions, diplomacy, war, tech        |
 (coord t)  | belief state per faction; messages on path matrix   |
            | edges: light path (S x S), wormhole (short, 1-way?) |
            +---------------+-----------------------+-------------+
                            | delayed deliveries    | lookahead = min edge delay
            +---------------v----------+  +---------v----------------+
 L2         | Region: Gargantua        |  | Region: other system     |
 (coord t,  | integer turn, event queue|  | integer turn, event queue|
  integer)  | intra delays (r, phi(t)) |  | ...                      |
            +----+-------------+-------+  +--------------------------+
                 | tau accum   | tau accum
            +----v----+   +----v----+
 L1         | Colony  |   | Colony  |   fixed local tick dtau (1 h)
 (proper    | Miller  |   | far orbit|  grid, networks, cohorts
  tau)      | rate Q32|   | rate Q32 |  focused = full; else LOD
            +---------+   +----------+
 L0  physics oracle (load time / epoch): observer-typed dtau/dt,
     delay tables, tidal limits  ->  quantized integers in the save
```

Local ticks map to regional turns through an integer accumulator per
colony: `rateQ = round(dtau/dt * 2^32)` fixed at load; each coordinate turn
adds `rateQ * T` to the accumulator, runs `acc / (dtau_tick * 2^32)` local
ticks, and keeps the remainder. For the canon Miller colony `rateQ =
69,994`; with 1-day turns and 1-hour local ticks it runs one local tick
every 2,557 turns (7.0 years), and a far colony runs 24 per turn. The
accumulator is exact, portable, and replayable; the rate quantization
error is 1.06e-6 relative at Miller, and a 64-bit fraction removes it.

Real-time versus turns: strategic time should stay in coordinate turns
(or pausable real time on a fixed coordinate tick) because diplomacy and
delivery need one ordering. The local layer runs at wall-clock pace only
for the focused colony, and the coordinate clock then advances at wall
rate divided by that colony's `dtau/dt`. Focusing Miller, one wall second
is 61,362 coordinate seconds, so 1-day turns elapse every 1.4 wall
seconds and the inbox fills with the outside world's years -- the film's
"Messages span 23 years" scene as a mechanic. Focusing a far colony, the
coordinate clock runs near wall rate and Miller advances 1.4 s per day,
effectively frozen, which LOD handles by skipping it until its accumulator
fires. The player's calendar is the focused colony's proper time; the
capital's clock (F18) is one more colony.

## 10. Proposed mechanics as hypotheses

None of these is claimed to create a decision. Each names the invariant
that would have to pass first, per the recorded lesson that a vector
outcome is a decision only when the axes compete and the off-axes carry
mechanical payoff.

- H1 time capsule: stocks and populations decay per proper time, so
  anything parked deep is preserved against outside-world decay while
  producing little per outside year (the F5 canon reading). Acceptance: a
  line that parks deep and a line that stays out each win on a scored axis
  the outcome reads, and neither wins every axis, across task cadences 1-30
  and two rival policies.
- H2 message burst on focus: playing a deep colony in real time delivers
  outside years of events at once. Acceptance: a UX test that the inbox
  groups by sender clock, plus a determinism test that focus changes only
  presentation, never simulation order.
- H3 wormhole edges: a short-path link with an optional one-way channel.
  Acceptance: a causality test that no reply crosses a one-way edge and an
  intel test that the path matrix routes around it.
- H4 relativistic transit: crew lifetime or cargo decay in proper time,
  speed bought with fuel. Acceptance: a mission-range invariant where the
  fast and slow lines each reach a target the other cannot within a stated
  crew lifetime.

## 11. Not run

- In-tree rebuild and in-tree `ctest` on HEAD: the caller forbade a rebuild
  in the primary checkout; HEAD was compiled in scratch instead.
- `ENABLE_FAST_MATH=ON` configuration: no scratch configure of the full
  CMake tree.
- Desktop GPU pass of `docs/validation/campaign-desktop-proof.md`: no
  interactive desktop session.
- Cross-libm and cross-platform digests (macOS, MSVC, aarch64): no such
  hosts.
- Scaling timings: section 8 complexity is inferred from loop structure.
- Endurance, Mann's, and Edmunds' orbital numbers: no fetched source
  states them.

## 12. Reproduction

From the repository root, compile outside the tree with `clang++ -std=c++23
-O2 -Isrc -Isrc/physics` over the five `PHYSICS_SRC_FILES`, the nine
non-`main` files in `src/game/`, and `src/game/constellation_sim_main.cpp`
or `campaign_sim_main.cpp`. F7 adds `-march=native` with and without
`-ffp-contract=off`. F6 shadows `src/game/campaign_sim_lines.h` (and, for
the wins-off columns, `campaign_session.cpp` with both thresholds at 1e6)
from a scratch directory. F1, F2, F5, and F9 are 20-line drivers over
`Constellation` printing `perceivedController`, faction `energyUnits`, and
fleet `properTimeSec` for the configurations each finding states. The
drivers (`harness/game/`), the threshold patch, and the canon scripts
(`harness/kerr_clocks.py`, `harness/check_orbits.py`) are in `harness/`;
`harness/README.md` gives the commands.
