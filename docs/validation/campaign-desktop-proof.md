# Campaign desktop proof checklist

The campaign's mechanics split into a deterministic core (verifiable headless,
in CTest) and a GPU/ImGui interaction layer (verifiable only on a real desktop
GL context). This checklist records which of the six vertical-slice interactions
each gate covers, so the manual desktop pass is scoped to exactly what automated
tests cannot reach.

A note on limits: any screenshot produced in CI or a sandbox here uses a virtual
display with software GL (Xvfb/llvmpipe). That proves the code path renders, not
that it renders on your GPU. The desktop pass below is run on the target machine
(the interaction and driver behaviour are what it checks); it is not something a
software-GL capture can stand in for.

## Automated (already gated in CTest)

| Interaction | Gate |
| --- | --- |
| Retrograde orders rejected in the ergosphere | `campaign_economy_test` (lane rule) |
| Delayed command arrival (orders take effect turns later) | `campaign_task_graph_test`, `campaign_economy_test` |
| Delayed completion intel (reports arrive late) | `campaign_task_graph_test`, `campaign_capabilities_test` |
| Both victory paths (energy at t1097, stabilization at t819) | `campaign_balance_invariant_test` |

Run them with:

```
ctest --test-dir build/Release -L campaign --output-on-failure
```

## Desktop pass (run on the target machine)

```
cd <repo root>
BLACKHOLE_CAMPAIGN=1 ./build/Release/Blackhole
```

The Campaign, Strategic Map, and Intel windows open. Then confirm:

1. **Fleet selection.** Click a fleet row in the roster, and a fleet marker on
   the strategic map. The selected fleet highlights in both; the order composer
   targets it. (Map selection is handled by an invisible full-canvas button in
   `strategic_map.cpp`, so it is a genuine ImGui hit test.)
2. **Map click does not move the camera.** With the Strategic Map focused, click
   and drag inside the map. The scene camera behind the panel must not rotate --
   the map's invisible button consumes the drag. This is the one interaction most
   worth eyeballing, because camera isolation depends on ImGui capturing the
   mouse before the scene input handler sees it.
3. **Redeploy and rejected retrograde.** Redeploy a fleet to the ergoregion band
   (index 0) prograde: accepted. Try the same band retrograde: rejected (the
   composer shows the command was refused). The core rule is tested; this
   confirms the UI surfaces the rejection.
4. **Delayed order, delayed intel.** Issue a task to a deep fleet, then advance
   turns. The order appears under "orders in flight" for several turns before it
   takes effect, and the completion appears under "reports in flight" before it
   reaches the intel log. Neither is instantaneous.
5. **A victory path.** Advance to a decision. The energy line clears near turn
   1097; an all-in stabilization line clears near turn 819. The victory banner
   names the turn the objective cleared (not the current turn).

## Capture

For the record, capture one gameplay screenshot (campaign windows over the
rendered scene) and one short recording of a turn resolution (advance several
turns, watching an order travel in and a report travel back). These are
review artifacts, not gates; the gates are the CTest suite above.
