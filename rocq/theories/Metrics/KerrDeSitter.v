(******************************************************************************)
(** * Kerr-de Sitter Metric - Rotating Black Hole with Cosmological Constant *)
(******************************************************************************)

(**
  Carter (1968) form of the Kerr-de Sitter metric in Boyer-Lindquist
  coordinates (Griffiths and Podolsky 2009, sec. 11.1), c = G = 1:

    ds^2 = -(Delta_r / (Xi^2 Sigma)) (dt - a sin^2 theta dphi)^2
         + (Delta_theta sin^2 theta / (Xi^2 Sigma)) (a dt - (r^2 + a^2) dphi)^2
         + (Sigma / Delta_r) dr^2 + (Sigma / Delta_theta) dtheta^2

    Sigma       = r^2 + a^2 cos^2 theta
    Delta_r     = (r^2 + a^2)(1 - Lambda r^2 / 3) - 2 M r
    Delta_theta = 1 + Lambda a^2 cos^2 theta / 3
    Xi          = 1 + Lambda a^2 / 3

  Horizons are the positive roots of the quartic Delta_r: inner (Cauchy),
  event, and cosmological for M > 0 and Lambda > 0 below the Nariai limit.
  They are specified here as roots; src/physics/verified/kerr_de_sitter.hpp
  computes them by bracketed bisection and tests/kerr_de_sitter_test.cpp checks
  the metric against R_mu_nu = Lambda g_mu_nu.

  Proof status: every theorem in this file closes with Qed.

  References:
  - Carter, B. (1968). Commun. Math. Phys. 10, 280
  - Griffiths, J. B. and Podolsky, J. (2009). Exact Space-Times in Einstein's
    General Relativity, sec. 11.1
*)

Require Import Blackhole.Prelim.
Require Import Blackhole.Metrics.Kerr.
From Stdlib Require Import Reals Lra.

Local Open Scope R_scope.

(******************************************************************************)
(** ** Carter-form metric functions *)
(******************************************************************************)

Definition kds_Sigma (r theta a : R) : R :=
  r^2 + a^2 * (cos theta)^2.

(** Radial function, a quartic in r. *)
Definition kds_Delta (r M a Lambda : R) : R :=
  (r^2 + a^2) * (1 - Lambda * r^2 / 3) - 2 * M * r.

Definition kds_Delta_theta (theta a Lambda : R) : R :=
  1 + Lambda * a^2 * (cos theta)^2 / 3.

Definition kds_Xi (a Lambda : R) : R :=
  1 + Lambda * a^2 / 3.

Definition kds_A (r theta M a Lambda : R) : R :=
  kds_Delta_theta theta a Lambda * (r^2 + a^2)^2
  - kds_Delta r M a Lambda * a^2 * (sin theta)^2.

(******************************************************************************)
(** ** Metric Components in Boyer-Lindquist Coordinates *)
(******************************************************************************)

Definition kds_g_tt (r theta M a Lambda : R) : R :=
  (- kds_Delta r M a Lambda + kds_Delta_theta theta a Lambda * a^2 * (sin theta)^2)
  / ((kds_Xi a Lambda)^2 * kds_Sigma r theta a).

Definition kds_g_rr (r theta M a Lambda : R) : R :=
  kds_Sigma r theta a / kds_Delta r M a Lambda.

Definition kds_g_thth (r theta a Lambda : R) : R :=
  kds_Sigma r theta a / kds_Delta_theta theta a Lambda.

Definition kds_g_phph (r theta M a Lambda : R) : R :=
  (sin theta)^2 * kds_A r theta M a Lambda / ((kds_Xi a Lambda)^2 * kds_Sigma r theta a).

Definition kds_g_tph (r theta M a Lambda : R) : R :=
  a * (sin theta)^2 * (kds_Delta r M a Lambda - kds_Delta_theta theta a Lambda * (r^2 + a^2))
  / ((kds_Xi a Lambda)^2 * kds_Sigma r theta a).

Definition kds_metric (r theta M a Lambda : R) : MetricComponents :=
  mkMetric
    (kds_g_tt r theta M a Lambda)
    (kds_g_rr r theta M a Lambda)
    (kds_g_thth r theta a Lambda)
    (kds_g_phph r theta M a Lambda)
    (kds_g_tph r theta M a Lambda).

(******************************************************************************)
(** ** Horizons and ergosurface *)
(******************************************************************************)

(** A horizon is a positive root of Delta_r. *)
Definition kds_is_horizon (r M a Lambda : R) : Prop :=
  r > 0 /\ kds_Delta r M a Lambda = 0.

(** An ergosurface is a positive root of g_tt. *)
Definition kds_is_ergosurface (r theta M a Lambda : R) : Prop :=
  r > 0 /\ kds_g_tt r theta M a Lambda = 0.

(** Frame dragging angular velocity: omega = -g_tph / g_phph *)
Definition kds_frame_dragging_omega (r theta M a Lambda : R) : R :=
  - kds_g_tph r theta M a Lambda / kds_g_phph r theta M a Lambda.

(******************************************************************************)
(** ** Physical Validity Constraints *)
(******************************************************************************)

(** A Kerr-de Sitter black hole has three ordered horizons. At a = 0 the
    innermost root of Delta_r is r = 0, the curvature singularity. *)
Definition is_physical_kds_black_hole (M a Lambda : R) : Prop :=
  M > 0 /\ Lambda > 0 /\
  exists r_minus r_plus r_c : R,
    0 <= r_minus /\ r_minus <= r_plus /\ r_plus < r_c /\
    kds_Delta r_minus M a Lambda = 0 /\
    kds_is_horizon r_plus M a Lambda /\
    kds_is_horizon r_c M a Lambda.

(** Exterior region between an event horizon r_plus and a cosmological
    horizon r_c. *)
Definition is_exterior_region (r r_plus r_c : R) : Prop :=
  r > r_plus /\ r < r_c.

(** d/dt is spacelike: the black-hole ergoregion or beyond the cosmological
    ergosurface. *)
Definition is_in_ergosphere (r theta M a Lambda : R) : Prop :=
  kds_g_tt r theta M a Lambda > 0.

(******************************************************************************)
(** ** Reduction Theorems *)
(******************************************************************************)

(** Lambda = 0: Delta_r is the Kerr Delta. *)
Theorem kds_reduces_to_kerr : forall r M a : R,
  kds_Delta r M a 0 = kerr_Delta r M a.
Proof.
  intros r M a.
  unfold kds_Delta, kerr_Delta.
  unfold Rdiv; ring.
Qed.

(** M = 0, a = 0: pure de Sitter, Delta_r = r^2 (1 - Lambda r^2 / 3). *)
Theorem kds_reduces_to_de_sitter : forall r Lambda : R,
  kds_Delta r 0 0 Lambda = r^2 * (1 - Lambda * r^2 / 3).
Proof.
  intros r Lambda.
  unfold kds_Delta.
  unfold Rdiv; ring.
Qed.

(** a = 0: Schwarzschild-de Sitter, g_tt = -(1 - 2M/r - Lambda r^2 / 3). *)
Theorem kds_g_tt_schwarzschild_de_sitter : forall r theta M Lambda : R,
  r <> 0 ->
  kds_g_tt r theta M 0 Lambda = - (1 - 2 * M / r - Lambda * r^2 / 3).
Proof.
  intros r theta M Lambda Hr.
  unfold kds_g_tt, kds_Delta, kds_Delta_theta, kds_Xi, kds_Sigma.
  field.
  exact Hr.
Qed.

(** a = 0: g_rr g_tt = -1, the Schwarzschild-de Sitter pairing. *)
Theorem kds_g_rr_g_tt_schwarzschild_de_sitter : forall r theta M Lambda : R,
  r <> 0 ->
  kds_Delta r M 0 Lambda <> 0 ->
  kds_g_rr r theta M 0 Lambda * kds_g_tt r theta M 0 Lambda = -1.
Proof.
  intros r theta M Lambda Hr HDelta.
  unfold kds_g_rr, kds_g_tt, kds_Delta_theta, kds_Xi, kds_Sigma.
  unfold kds_Delta in *.
  field.
  split; [exact Hr |].
  intro Hzero.
  apply HDelta.
  replace ((r ^ 2 + 0 ^ 2) * (1 - Lambda * r ^ 2 / 3) - 2 * M * r)
    with ((r ^ 2 * (3 - Lambda * r ^ 2) - 2 * M * r * 3) / 3) by field.
  rewrite Hzero.
  field.
Qed.

(** Lambda = 0: the frame-dragging numerator is the Kerr 2 M r a. *)
Theorem kds_g_tph_kerr_limit : forall r theta M a : R,
  kds_Sigma r theta a <> 0 ->
  kds_g_tph r theta M a 0 = - 2 * M * r * a * (sin theta)^2 / kds_Sigma r theta a.
Proof.
  intros r theta M a HSigma.
  unfold kds_g_tph, kds_Delta, kds_Delta_theta, kds_Xi.
  field.
  exact HSigma.
Qed.

(******************************************************************************)
(** ** Invariant Properties *)
(******************************************************************************)

(** Sigma is positive off the ring singularity. *)
Theorem kds_Sigma_positive : forall r theta a : R,
  r > 0 ->
  kds_Sigma r theta a > 0.
Proof.
  intros r theta a Hr.
  unfold kds_Sigma.
  nra.
Qed.

(** Delta_r(0) = a^2: no horizon at r = 0 unless a = 0. *)
Theorem kds_Delta_at_origin : forall M a Lambda : R,
  kds_Delta 0 M a Lambda = a^2.
Proof.
  intros M a Lambda.
  unfold kds_Delta.
  unfold Rdiv; ring.
Qed.
