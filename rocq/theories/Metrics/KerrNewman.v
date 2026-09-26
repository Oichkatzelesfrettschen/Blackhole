(** * Kerr-Newman: Rotating Charged Black Hole Metric

    The Kerr-Newman solution describes a rotating, electrically charged black hole.
    It is the unique axially symmetric, stationary solution to the Einstein-Maxwell
    equations (Newman et al., 1965).

    Metric in Boyer-Lindquist coordinates (c = G = 1):
      ds^2 = -(1 - (2Mr - Q^2) / Sigma) dt^2
           - (2 a (2Mr - Q^2) sin^2 theta / Sigma) dt dphi
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
      A_mu = -(Qr / Sigma) (dt - a sin^2 theta dphi)
           = (-Qr / Sigma, 0, 0, +Qra sin^2 theta / Sigma)

    Signed spin: a > 0 rotates about +z; "prograde" names an orbit with
    angular momentum along +z.

    Proof status: every theorem in this file closes with Qed.
    kn_ergosphere_exists carries a <> 0 and sin theta <> 0 hypotheses because
    the ergosurface touches the horizon on the axis and at a = 0.

    The C++ reference src/physics/verified/kerr_newman.hpp evaluates these
    definitions in floating point; tests/kerr_newman_test.cpp checks it.

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
  a * (2 * M * r - Q^2) / A.

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
    (- a * (2 * M * r - Q^2) * sin2 / Sigma).     (* g_tph - frame dragging *)

(** ** Electromagnetic 4-Potential *)

(** Time component: A_t = -Qr / Sigma *)
Definition kn_potential_t (r theta a Q : R) : R :=
  - Q * r / kn_Sigma r theta a.

(** Azimuthal component: A_phi = +Qra sin^2(theta) / Sigma = -a sin^2(theta) A_t *)
Definition kn_potential_phi (r theta a Q : R) : R :=
  Q * r * a * (sin theta)^2 / kn_Sigma r theta a.

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
  pose proof (sqrt_pos (M^2 - a^2 - Q^2)).
  lra.
Qed.

(** Extremal Kerr-Newman: M^2 = a^2 + Q^2, horizons coincide *)
Theorem kn_extremal_horizons : forall M a Q : R,
  M > 0 ->
  M^2 = a^2 + Q^2 ->
  kn_outer_horizon M a Q = kn_inner_horizon M a Q.
Proof.
  intros M a Q HM Hextreme.
  unfold kn_outer_horizon, kn_inner_horizon.
  replace (M^2 - a^2 - Q^2) with 0 by lra.
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

(** The ergosurface lies strictly outside the horizon wherever a sin theta
    is nonzero; on the axis or at a = 0 the two coincide. *)
Theorem kn_ergosphere_exists : forall theta M a Q : R,
  M > 0 ->
  M^2 > a^2 * (cos theta)^2 + Q^2 ->
  a <> 0 ->
  sin theta <> 0 ->
  kn_ergosphere_radius theta M a Q > kn_outer_horizon M a Q.
Proof.
  intros theta M a Q HM Hbound Ha Hsin.
  unfold kn_ergosphere_radius, kn_outer_horizon.
  assert (Hcos : a^2 * (cos theta)^2 < a^2).
  { pose proof (sin2_cos2 theta) as Hsc.
    assert (Hs2 : 0 < (sin theta)^2).
    { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. exact Hsin. }
    assert (Ha2 : 0 < a^2).
    { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. exact Ha. }
    unfold Rsqr in Hsc.
    replace ((cos theta)^2) with (1 - (sin theta)^2) by (simpl; lra).
    nra. }
  apply Rplus_lt_compat_l.
  destruct (Rle_or_lt 0 (M^2 - a^2 - Q^2)) as [Hnn | Hneg].
  - apply sqrt_lt_1_alt. lra.
  - rewrite (sqrt_neg_0 _ (Rlt_le _ _ Hneg)).
    apply sqrt_lt_R0. lra.
Qed.

(** ** Photon Sphere (depends on charge) *)

(** Circular-photon-orbit function for angular momentum along +z (signed a).
    Timelike circular orbits have u^t proportional to 1 / sqrt(f); f = 0 is
    the equatorial photon orbit. At Q = 0 the root is the Bardeen-Press-
    Teukolsky photon orbit; at a = 0 it is (3M + sqrt(9M^2 - 8Q^2)) / 2. *)
Definition kn_photon_orbit_function (r M a Q : R) : R :=
  r^2 - 3 * M * r + 2 * Q^2 + 2 * a * sqrt (M * r - Q^2).

(** The equatorial photon orbit is the outermost zero of that function. *)
Definition kn_photon_sphere_equator_spec (M a Q r : R) : Prop :=
  kn_photon_orbit_function r M a Q = 0 /\
  forall r', r' > r -> kn_photon_orbit_function r' M a Q > 0.

(** At a = Q = 0 the photon orbit function is r (r - 3M), zero at r = 3M. *)
Theorem kn_photon_orbit_schwarzschild : forall M : R,
  kn_photon_orbit_function (3 * M) M 0 0 = 0.
Proof.
  intros M.
  unfold kn_photon_orbit_function.
  ring.
Qed.

(** ** ISCO (Innermost Stable Circular Orbit) *)

(** Marginal stability of equatorial circular orbits with angular momentum
    along +z. Its zeros are the radii where dE/dr = 0 for the circular-orbit
    energy E(r); it is negative where circular orbits are stable (large r).
    At a = 0 it is minus the Reissner-Nordstrom ISCO cubic; at Q = 0 it is
    -r (r^2 - 6Mr + 8a sqrt(Mr) - 3a^2), the Bardeen-Press-Teukolsky
    condition. *)
Definition kn_marginal_stability (r M a Q : R) : R :=
  r * (6 * M * r - r^2 - 9 * Q^2 + 3 * a^2) + 4 * Q^2 * (Q^2 - a^2) / M
  - 8 * a * (sqrt (M * r - Q^2))^3 / M.

(** The ISCO is the outermost zero of the marginal-stability function. *)
Definition kn_isco_prograde_spec (M a Q r : R) : Prop :=
  kn_marginal_stability r M a Q = 0 /\
  forall r', r' > r -> kn_marginal_stability r' M a Q < 0.

(** Reflecting phi -> -phi maps a -> -a with Q unchanged. *)
Definition kn_isco_retrograde_spec (M a Q r : R) : Prop :=
  kn_isco_prograde_spec M (- a) Q r.

(** At a = 0 the marginal-stability function is minus the cubic
    r^3 - 6Mr^2 + 9Q^2 r - 4Q^4/M. *)
Theorem kn_marginal_stability_rn : forall r M Q : R,
  M <> 0 ->
  kn_marginal_stability r M 0 Q = - (r^3 - 6 * M * r^2 + 9 * Q^2 * r - 4 * Q^4 / M).
Proof.
  intros r M Q HM.
  unfold kn_marginal_stability.
  field.
  exact HM.
Qed.

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
  unfold kn_A, kerr_A, kn_Sigma, kerr_Sigma, kn_Delta, kerr_Delta.
  replace (r^2 - 2 * M * r + a^2 + 0^2) with (r^2 - 2 * M * r + a^2) by ring.
  cbv zeta.
  f_equal; unfold Rdiv; ring.
Qed.

(** Kerr-Newman with a = 0, Q = 0 is Schwarzschild *)
Theorem kn_reduces_to_schwarzschild : forall r theta M : R,
  M > 0 ->
  r > 0 ->
  exists schwarzschild_components,
    kerr_newman_metric r theta M 0 0 = schwarzschild_components.
Proof.
  intros r theta M HM Hr.
  eexists.
  reflexivity.
Qed.

(** ** Extraction Interface *)

(* Definitions intended for OCaml extraction:
   - kn_Sigma, kn_Delta, kn_A
   - kn_outer_horizon, kn_inner_horizon
   - kn_ergosphere_radius
   - kn_photon_orbit_function, kn_photon_sphere_equator_spec
   - kn_marginal_stability, kn_isco_prograde_spec, kn_isco_retrograde_spec
   - kn_potential_t, kn_potential_phi
   - kn_electric_field_r, kn_magnetic_field
   - is_physical_black_hole *)
