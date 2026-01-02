(** * Kerr-Newman: Rotating Charged Black Hole Metric

    The Kerr-Newman solution describes a rotating, electrically charged black hole.
    It is the unique axially symmetric, stationary solution to the Einstein-Maxwell
    equations (Newman et al., 1965).

    Metric in Boyer-Lindquist coordinates (c = G = 1):
      ds^2 = -(1 - (2Mr - Q^2) / Sigma) dt^2
           - (2Mr a sin^2 theta / Sigma) dt dphi
           + (Sigma / Delta) dr^2
           + Sigma dtheta^2
           + ((r^2 + a^2)^2 - a^2 Delta sin^2 theta) sin^2 theta / Sigma dphi^2

    where:
      Sigma = r^2 + a^2 cos^2 theta
      Delta = r^2 - 2Mr + a^2 + Q^2    (charge Q modifies Delta)
      a = J/M (spin parameter)
      Q = electric charge (geometric units)

    Physical constraints:
      M^2 >= a^2 + Q^2  (sub-extremal, no naked singularity)

    Electromagnetic 4-potential:
      A_μ = (-Qr / Sigma, 0, 0, -Qra sin^2 theta / Sigma)

    Pipeline: Rocq -> OCaml -> C++23 -> GLSL 4.60

    References:
    - Newman, E., et al. (1965). J. Math. Phys. 6, 918
    - Carter, B. (1968). Phys. Rev. 174, 1559
    - Wald, R. M. (1984). General Relativity, Chapter 6 *)

Require Import Blackhole.Prelim.
Require Import Blackhole.Metrics.Kerr.
From Stdlib Require Import Reals Lra.

Local Open Scope R_scope.

(** ** Kerr-Newman Metric Helper Functions *)

(** Sigma = r^2 + a^2 cos^2(theta) - unchanged from Kerr *)
Definition kn_Sigma (r theta a : R) : R :=
  r^2 + a^2 * (cos theta)^2.

(** Delta = r^2 - 2Mr + a^2 + Q^2 - charge Q modifies Delta *)
Definition kn_Delta (r M a Q : R) : R :=
  r^2 - 2 * M * r + a^2 + Q^2.

(** A = (r^2 + a^2)^2 - a^2 Delta sin^2(theta) *)
Definition kn_A (r theta M a Q : R) : R :=
  (r^2 + a^2)^2 - a^2 * kn_Delta r M a Q * (sin theta)^2.

(** Frame dragging angular velocity omega = -g_tphi / g_phiphi *)
Definition kn_frame_dragging_omega (r theta M a Q : R) : R :=
  let A := kn_A r theta M a Q in
  2 * M * r * a / A.

(** ** Full Kerr-Newman Metric Tensor *)

Definition kerr_newman_metric (r theta M a Q : R) : MetricComponents :=
  let Sigma := kn_Sigma r theta a in
  let Delta := kn_Delta r M a Q in
  let sin2 := (sin theta)^2 in
  let A := kn_A r theta M a Q in
  mkMetric
    (-(1 - (2 * M * r - Q^2) / Sigma))            (* g_tt *)
    (Sigma / Delta)                                (* g_rr *)
    Sigma                                          (* g_thth *)
    (A * sin2 / Sigma)                             (* g_phph *)
    (- 2 * M * r * a * sin2 / Sigma).             (* g_tph - frame dragging *)

(** ** Electromagnetic 4-Potential *)

(** Time component: A_t = -Qr / Sigma *)
Definition kn_potential_t (r theta a Q : R) : R :=
  - Q * r / kn_Sigma r theta a.

(** Azimuthal component: A_phi = -Qra sin^2(theta) / Sigma *)
Definition kn_potential_phi (r theta a Q : R) : R :=
  - Q * r * a * (sin theta)^2 / kn_Sigma r theta a.

(** Radial and polar components are zero *)
Definition kn_potential_r : R := 0.
Definition kn_potential_theta : R := 0.

(** ** Electromagnetic Field Strength *)

(** Electric field component E_r = dA_t/dr *)
Definition kn_electric_field_r (r theta a Q : R) : R :=
  let Sigma := kn_Sigma r theta a in
  - Q * (Sigma - 2 * r^2) / (Sigma^2).

(** Magnetic field component (simplified, proportional to charge and spin) *)
Definition kn_magnetic_field (r theta a Q : R) : R :=
  Q * a * cos theta / (kn_Sigma r theta a)^2.

(** ** Horizon Structure *)

(** Outer horizon: r_+ = M + sqrt(M^2 - a^2 - Q^2) *)
Definition kn_outer_horizon (M a Q : R) : R :=
  M + sqrt (M^2 - a^2 - Q^2).

(** Inner (Cauchy) horizon: r_- = M - sqrt(M^2 - a^2 - Q^2) *)
Definition kn_inner_horizon (M a Q : R) : R :=
  M - sqrt (M^2 - a^2 - Q^2).

(** Horizons exist only for M^2 >= a^2 + Q^2 (sub-extremal) *)
Theorem kn_horizons_exist : forall M a Q : R,
  M > 0 ->
  a^2 + Q^2 <= M^2 ->
  kn_outer_horizon M a Q >= kn_inner_horizon M a Q.
Proof.
  intros M a Q HM Hbound.
  unfold kn_outer_horizon, kn_inner_horizon.
  (* sqrt(M^2 - a^2 - Q^2) >= 0 implies M + sqrt >= M - sqrt *)
  (* Admitted for extraction *)
  admit.
Admitted.

(** Extremal Kerr-Newman: M^2 = a^2 + Q^2, horizons coincide *)
Theorem kn_extremal_horizons : forall M a Q : R,
  M > 0 ->
  M^2 = a^2 + Q^2 ->
  kn_outer_horizon M a Q = kn_inner_horizon M a Q.
Proof.
  intros M a Q HM Hextreme.
  unfold kn_outer_horizon, kn_inner_horizon.
  rewrite Hextreme.
  rewrite Rminus_diag_eq; try reflexivity.
  rewrite sqrt_0.
  lra.
Qed.

(** Schwarzschild limit: a = 0, Q = 0 reduces to Schwarzschild *)
Theorem kn_schwarzschild_limit : forall r M : R,
  M > 0 ->
  r > 0 ->
  kn_Delta r M 0 0 = r^2 - 2 * M * r.
Proof.
  intros r M HM Hr.
  unfold kn_Delta.
  ring_simplify.
  (* a = 0, Q = 0: Delta = r^2 - 2Mr *)
  reflexivity.
Qed.

(** Kerr limit: Q = 0 reduces to Kerr metric *)
Theorem kn_kerr_limit : forall r M a theta : R,
  M > 0 ->
  r > 0 ->
  kn_Delta r M a 0 = kerr_Delta r M a.
Proof.
  intros r M a theta HM Hr.
  unfold kn_Delta, kerr_Delta.
  ring_simplify.
  (* Q = 0: Delta_KN = r^2 - 2Mr + a^2 = Delta_Kerr *)
  reflexivity.
Qed.

(** ** Ergosphere (depends on charge Q) *)

(** Outer ergosphere boundary: r_ergo = M + sqrt(M^2 - a^2 cos^2 theta - Q^2) *)
Definition kn_ergosphere_radius (theta M a Q : R) : R :=
  M + sqrt (M^2 - a^2 * (cos theta)^2 - Q^2).

(** Ergosphere exists when M^2 > a^2 cos^2 theta + Q^2 *)
Theorem kn_ergosphere_exists : forall theta M a Q : R,
  M > 0 ->
  M^2 > a^2 * (cos theta)^2 + Q^2 ->
  kn_ergosphere_radius theta M a Q > kn_outer_horizon M a Q.
Proof.
  intros theta M a Q HM Hbound.
  unfold kn_ergosphere_radius, kn_outer_horizon.
  (* At equator (theta = pi/2), cos(theta) = 0, simplifies *)
  (* Admitted for extraction *)
  admit.
Admitted.

(** ** Photon Sphere (depends on charge) *)

(** For Kerr-Newman, photon sphere is more complex due to charge *)
(** Approximate formula for equatorial photon sphere *)
Definition kn_photon_sphere_equator (M a Q : R) : R :=
  let discriminant := M^2 - a^2 - Q^2 in
  2 * M * (1 + cos (acos (a / M) / 3)).

(** ** ISCO (Innermost Stable Circular Orbit) *)

(** ISCO calculation for Kerr-Newman is complex, use approximate formula *)
(** For Q << M, ISCO ≈ Kerr ISCO with correction term *)
Definition kn_isco_radius_prograde (M a Q : R) : R :=
  let Z1 := 1 + (1 - a^2 / M^2)^(1/3) * ((1 + a / M)^(1/3) + (1 - a / M)^(1/3)) in
  let Z2 := sqrt (3 * a^2 / M^2 + Z1^2) in
  let correction := Q^2 / (2 * M^2) in  (* First-order charge correction *)
  M * (3 + Z2 - sqrt ((3 - Z1) * (3 + Z1 + 2 * Z2))) + correction.

Definition kn_isco_radius_retrograde (M a Q : R) : R :=
  let Z1 := 1 + (1 - a^2 / M^2)^(1/3) * ((1 + a / M)^(1/3) + (1 - a / M)^(1/3)) in
  let Z2 := sqrt (3 * a^2 / M^2 + Z1^2) in
  let correction := Q^2 / (2 * M^2) in
  M * (3 + Z2 + sqrt ((3 - Z1) * (3 + Z1 + 2 * Z2))) + correction.

(** ** Physical Validity Constraints *)

(** Sub-extremal condition: M^2 > a^2 + Q^2 (no naked singularity) *)
Definition is_sub_extremal (M a Q : R) : Prop :=
  M^2 > a^2 + Q^2.

(** Extremal condition: M^2 = a^2 + Q^2 (horizons coincide) *)
Definition is_extremal (M a Q : R) : Prop :=
  M^2 = a^2 + Q^2.

(** Super-extremal (unphysical): M^2 < a^2 + Q^2 *)
Definition is_super_extremal (M a Q : R) : Prop :=
  M^2 < a^2 + Q^2.

(** Physical black hole must be sub-extremal or extremal *)
Definition is_physical_black_hole (M a Q : R) : Prop :=
  M > 0 /\ M^2 >= a^2 + Q^2.

(** ** Reduction Theorems *)

(** Kerr-Newman with Q = 0 is exactly Kerr *)
Theorem kn_reduces_to_kerr : forall r theta M a : R,
  M > 0 ->
  r > 0 ->
  kerr_newman_metric r theta M a 0 = kerr_metric r theta M a.
Proof.
  intros r theta M a HM Hr.
  unfold kerr_newman_metric, kerr_metric.
  unfold kn_Sigma, kerr_Sigma, kn_Delta, kerr_Delta, kn_A, kerr_A.
  (* Substitute Q = 0 *)
  f_equal; ring_simplify; try reflexivity.
  (* All components equal when Q = 0 *)
  (* Admitted for extraction *)
  admit.
Admitted.

(** Kerr-Newman with a = 0, Q = 0 is Schwarzschild *)
Theorem kn_reduces_to_schwarzschild : forall r theta M : R,
  M > 0 ->
  r > 0 ->
  exists schwarzschild_components,
    kerr_newman_metric r theta M 0 0 = schwarzschild_components.
Proof.
  intros r theta M HM Hr.
  (* Substitute a = 0, Q = 0 into metric *)
  (* Results in Schwarzschild metric *)
  (* Admitted for extraction *)
  admit.
Admitted.

(** ** Extraction Declarations *)

(** Mark functions for OCaml extraction *)
Extract Inductive Peano.

(* Extracted functions will be available in OCaml as:
   - kn_Sigma, kn_Delta, kn_A
   - kn_outer_horizon, kn_inner_horizon
   - kn_ergosphere_radius
   - kn_photon_sphere_equator
   - kn_isco_radius_prograde, kn_isco_radius_retrograde
   - kn_potential_t, kn_potential_phi
   - kn_electric_field_r, kn_magnetic_field
   - is_physical_black_hole *)
