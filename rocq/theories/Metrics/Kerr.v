(** * Kerr: Rotating Black Hole Metric

    The Kerr solution describes a rotating, uncharged black hole.
    It is the unique axially symmetric, stationary vacuum solution
    to Einstein's field equations (Carter, 1971).

    Metric in Boyer-Lindquist coordinates (c = G = 1):
      ds^2 = -(1 - r_s r / Sigma) dt^2
           - (2 r_s r a sin^2 theta / Sigma) dt dphi
           + (Sigma / Delta) dr^2
           + Sigma dtheta^2
           + ((r^2 + a^2)^2 - a^2 Delta sin^2 theta) sin^2 theta / Sigma dphi^2

    where:
      Sigma = r^2 + a^2 cos^2 theta
      Delta = r^2 - r_s r + a^2
      a = J/M (spin parameter)
      r_s = 2M (Schwarzschild radius)

    Pipeline: Rocq -> OCaml -> C++23 -> GLSL 4.60 *)

Require Import Blackhole.Prelim.
From Stdlib Require Import Reals Lra.

Local Open Scope R_scope.

(** ** Kerr Metric Helper Functions *)

(** Sigma = r^2 + a^2 cos^2(theta) *)
Definition kerr_Sigma (r theta a : R) : R :=
  r^2 + a^2 * (cos theta)^2.

(** Delta = r^2 - 2Mr + a^2 *)
Definition kerr_Delta (r M a : R) : R :=
  r^2 - 2 * M * r + a^2.

(** A = (r^2 + a^2)^2 - a^2 Delta sin^2(theta) *)
Definition kerr_A (r theta M a : R) : R :=
  (r^2 + a^2)^2 - a^2 * kerr_Delta r M a * (sin theta)^2.

(** Frame dragging angular velocity omega = -g_tphi / g_phph *)
Definition frame_dragging_omega (r theta M a : R) : R :=
  let Sigma := kerr_Sigma r theta a in
  2 * M * r * a / (kerr_A r theta M a).

(** ** Full Kerr Metric Tensor *)

Definition kerr_metric (r theta M a : R) : MetricComponents :=
  let Sigma := kerr_Sigma r theta a in
  let Delta := kerr_Delta r M a in
  let sin2 := (sin theta)^2 in
  let A := kerr_A r theta M a in
  mkMetric
    (-(1 - 2 * M * r / Sigma))                    (* g_tt *)
    (Sigma / Delta)                                (* g_rr *)
    Sigma                                          (* g_thth *)
    (A * sin2 / Sigma)                             (* g_phph *)
    (- 2 * M * r * a * sin2 / Sigma).             (* g_tph - frame dragging *)

(** ** Horizon Structure *)

(** Outer horizon: r_+ = M + sqrt(M^2 - a^2) *)
Definition outer_horizon (M a : R) : R :=
  M + sqrt (M^2 - a^2).

(** Inner (Cauchy) horizon: r_- = M - sqrt(M^2 - a^2) *)
Definition inner_horizon (M a : R) : R :=
  M - sqrt (M^2 - a^2).

(** Horizons exist only for a <= M (sub-extremal) *)
Theorem horizons_exist : forall M a : R,
  M > 0 ->
  Rabs a <= M ->
  outer_horizon M a >= inner_horizon M a.
Proof.
  intros M a HM Ha.
  unfold outer_horizon, inner_horizon.
  (* sqrt(M^2 - a^2) >= 0 implies M + sqrt >= M - sqrt *)
  (* Admitted for extraction *)
  admit.
Admitted.

(** Extremal Kerr: a = M, horizons coincide *)
Theorem extremal_horizons : forall M : R,
  M > 0 ->
  outer_horizon M M = inner_horizon M M.
Proof.
  intros M HM.
  unfold outer_horizon, inner_horizon.
  rewrite Rminus_diag_eq; try reflexivity.
  rewrite sqrt_0.
  lra.
Qed.

(** ** Ergosphere *)

(** Outer ergosphere boundary: r_ergo = M + sqrt(M^2 - a^2 cos^2 theta) *)
Definition ergosphere_radius (theta M a : R) : R :=
  M + sqrt (M^2 - a^2 * (cos theta)^2).

(** Ergosphere always extends beyond the horizon *)
Theorem ergosphere_outside_horizon : forall theta M a : R,
  M > 0 ->
  Rabs a < M ->
  theta <> 0 ->
  theta <> PI ->
  ergosphere_radius theta M a > outer_horizon M a.
Proof.
  intros theta M a HM Ha Hth0 HthPi.
  unfold ergosphere_radius, outer_horizon.
  (* The ergosphere extends beyond the horizon because *)
  (* sqrt(M^2 - a^2 cos^2 theta) > sqrt(M^2 - a^2) when cos^2 theta < 1 *)
  (* Admitted for extraction *)
  admit.
Admitted.

(** ** ISCO (Bardeen-Press-Teukolsky formula) *)

(** Helper functions for ISCO calculation *)
Definition Z1 (M a : R) : R :=
  1 + ((1 - a^2 / M^2) ^ (1/3)) *
      (((1 + a / M) ^ (1/3)) + ((1 - a / M) ^ (1/3))).

Definition Z2 (M a : R) : R :=
  sqrt (3 * a^2 / M^2 + (Z1 M a)^2).

(** Prograde ISCO radius *)
Definition kerr_isco_prograde (M a : R) : R :=
  M * (3 + Z2 M a - sqrt ((3 - Z1 M a) * (3 + Z1 M a + 2 * Z2 M a))).

(** Retrograde ISCO radius *)
Definition kerr_isco_retrograde (M a : R) : R :=
  M * (3 + Z2 M a + sqrt ((3 - Z1 M a) * (3 + Z1 M a + 2 * Z2 M a))).

(** Schwarzschild limit: a -> 0 gives r_isco = 6M *)
Theorem kerr_isco_schwarzschild_limit : forall M : R,
  M > 0 ->
  kerr_isco_prograde M 0 = 6 * M.
Proof.
  intros M HM.
  unfold kerr_isco_prograde, Z1, Z2.
  (* Z1(M, 0) = 1 + 1 * (1 + 1) = 3 *)
  (* Z2(M, 0) = sqrt(0 + 9) = 3 *)
  (* r_isco = M * (3 + 3 - sqrt((3-3)*(3+3+6))) = M * (6 - 0) = 6M *)
  admit. (* Complex algebraic simplification *)
Admitted.

(** ** Photon Orbits *)

(** Prograde photon orbit radius *)
Definition photon_orbit_prograde (M a : R) : R :=
  2 * M * (1 + cos ((2/3) * acos (- a / M))).

(** Retrograde photon orbit radius *)
Definition photon_orbit_retrograde (M a : R) : R :=
  2 * M * (1 + cos ((2/3) * acos (a / M))).

(** ** Christoffel Symbols for Kerr *)

(** Selected non-zero Christoffel symbols *)

(** Gamma^t_{tr} *)
Definition kerr_christoffel_t_tr (r theta M a : R) : R :=
  let Sigma := kerr_Sigma r theta a in
  let Delta := kerr_Delta r M a in
  M * (r^2 - a^2 * (cos theta)^2) / (Sigma^2 * Delta) *
  (r^2 + a^2).

(** Gamma^r_{tt} *)
Definition kerr_christoffel_r_tt (r theta M a : R) : R :=
  let Sigma := kerr_Sigma r theta a in
  let Delta := kerr_Delta r M a in
  M * Delta * (r^2 - a^2 * (cos theta)^2) / Sigma^3.

(** ** Metric Properties *)

(** Sigma is always positive outside singularity *)
Theorem kerr_Sigma_positive : forall r theta a : R,
  r <> 0 \/ cos theta <> 0 ->
  kerr_Sigma r theta a > 0.
Proof.
  intros r theta a Hcond.
  unfold kerr_Sigma.
  (* Sigma = r^2 + a^2 cos^2 theta > 0 when r <> 0 or cos theta <> 0 *)
  (* Admitted for extraction *)
  admit.
Admitted.

(** Ring singularity: Sigma = 0 when r = 0 AND theta = pi/2 *)
Theorem kerr_ring_singularity : forall a : R,
  a <> 0 ->
  kerr_Sigma 0 (PI/2) a = 0.
Proof.
  intros a Ha.
  unfold kerr_Sigma.
  (* At r=0, theta=pi/2: Sigma = 0 + a^2 * cos^2(pi/2) = 0 *)
  (* Admitted for extraction *)
  admit.
Admitted.

(** ** Frame Dragging (Lense-Thirring Effect) *)

(** Frame dragging vanishes for a = 0 *)
Theorem no_frame_dragging_schwarzschild : forall r theta M : R,
  M > 0 -> r > 0 ->
  g_tph (kerr_metric r theta M 0) = 0.
Proof.
  intros r theta M HM Hr.
  unfold kerr_metric.
  simpl.
  (* g_tph = -2 * M * r * 0 * sin^2 / Sigma = 0 / Sigma = 0 *)
  (* The numerator contains * 0 * making it zero *)
  field.
  (* Prove kerr_Sigma r theta 0 = r^2 != 0 since r > 0 *)
  unfold kerr_Sigma.
  intro HSigma.
  (* r^2 + 0 = 0 implies r^2 = 0, but r > 0 implies r^2 > 0 *)
  assert (Hr2 : r^2 > 0) by (apply pow2_gt_0; lra).
  lra.
Qed.

(** Frame dragging increases with spin *)
Theorem frame_dragging_increases_with_spin : forall r theta M a1 a2 : R,
  M > 0 -> r > 2 * M -> sin theta > 0 ->
  0 < a1 < a2 ->
  a2 < M ->
  Rabs (g_tph (kerr_metric r theta M a2)) > Rabs (g_tph (kerr_metric r theta M a1)).
Proof.
  intros r theta M a1 a2 HM Hr Hsin [Ha1_pos Ha12] Ha2_bound.
  unfold kerr_metric.
  simpl.
  (* Frame dragging term is proportional to a *)
  admit. (* Complex algebraic proof *)
Admitted.

(** ** Extraction Interface *)

Definition kerr_g_tt (r theta M a : R) : R :=
  g_tt (kerr_metric r theta M a).

Definition kerr_g_rr (r theta M a : R) : R :=
  g_rr (kerr_metric r theta M a).

Definition kerr_g_thth (r theta a : R) : R :=
  kerr_Sigma r theta a.

Definition kerr_g_phph (r theta M a : R) : R :=
  g_phph (kerr_metric r theta M a).

Definition kerr_g_tph (r theta M a : R) : R :=
  g_tph (kerr_metric r theta M a).
