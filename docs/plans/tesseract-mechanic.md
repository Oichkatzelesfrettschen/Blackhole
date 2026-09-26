# Tesseract Mechanic: Novikov Self-Consistent Message

Status: design note, not built. The tesseract scene (`src/render/tesseract/`)
stays render-only and speculative (Thorne, *The Science of Interstellar*
ch. 29-31); this note describes a later campaign mechanic that would reuse it
as a visualization. None of it is physics.

## Rule

A history occurs only if its time loop closes (Novikov self-consistency). The
campaign realizes that rule with a deterministic search outside the turn loop,
never with in-sim retrocausality.

1. **Pre-seeded slot.** At turn 0 the campaign seeds one bulk message with a
   fixed delivery turn `t_d` and a fixed sending turn `t_s > t_d`. Its content
   is undetermined: one element of a finite ordered set `M = {m_0, ..., m_k}`.
2. **Constraint.** A send rule `send(state)` maps the campaign state at `t_s`
   to an element of `M`. Content `m` is consistent when a replay that delivers
   `m` at `t_d` reaches a state at `t_s` with `send(state) == m`.
3. **Resolution by replay.** Before turn 0 runs for the player, a resolver
   replays turns `0..t_s` once per candidate in the fixed order of `M`, with
   the candidate injected as a seed-level input, and keeps the first consistent
   one. Cost is at most `|M| * t_s` turns per attempt. Player orders before
   `t_s` do not exist yet, so the replay needs a driver that depends only on
   the seed and the message. Open decision: a deterministic reference policy
   (the campaign_sim commitment lines), or resolution at `t_s` over the
   recorded order log with the message content sealed until then.
4. **Logging.** The chosen index, the attempt count, and the candidate order
   are written into the save and the seed record. Loading a save replays with
   the logged choice and skips the search; the state digest must match the
   resolving run.
5. **Re-roll.** If no candidate is consistent, the resolver derives the next
   seed deterministically, `seed' = hash(seed, "novikov", attempt)`, and
   retries up to a fixed budget. When the budget is spent, the bulk channel
   closes for that campaign: a history without the loop is consistent by
   construction, so resolution always terminates.

## Causality of the turn law

The in-sim turn law is unchanged. The integer turn count stays the only loop
variable, `advance(n)` stays `n` single steps, and ordinary orders and reports
keep their causal delivery queue and signal delay. The message reaches the
simulation as an input fixed before turn 0, delivered at `t_d` like any other
scheduled event; no turn reads a later turn's state. All acausal structure
lives in the resolver, which is an ordinary deterministic function of the seed.

## Presentation

The tesseract scene shows the resolved loop: the delivery turn maps to the lit
moment, the message runs as the gravity pulse from `t_s` back to `t_d` along
the strand of the object it moves, and the on-screen speculative label stays.

## Gates to write when built

- The resolved content satisfies the constraint on an independent replay.
- Loading a save with the logged choice reproduces the resolving digest.
- A fixture with no consistent candidate re-rolls to the same seed sequence on
  every run and closes the channel after the budget.
- The turn loop never reads state from a turn later than the current one.
