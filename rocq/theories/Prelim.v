(** * Prelim: Foundational Real Analysis for General Relativity

    This module establishes the mathematical foundations for formalizing
    general relativistic physics. We use Coq standard library reals
    for numerical computation, with ssreflect tactics for proofs.

    Key concepts:
    - Real numbers with standard analysis topology
    - Metric tensor type (Lorentzian signature)
    - Vector spaces and 4-vectors
    - Differentiation and integration

    Pipeline: Rocq -> OCaml -> C++23 -> GLSL 4.60 *)

From Stdlib Require Import Reals Lra Lia.
From Stdlib Require Import Rbase Rfunctions Rpower Rsqrt_def.

Local Open Scope R_scope.

(** ** Auxiliary Lemmas for Powers *)

Lemma pow2_gt_0 : forall x : R, x <> 0 -> x^2 > 0.
Proof.
  intros x Hx.
  rewrite <- Rsqr_pow2.
  apply Rsqr_pos_lt. assumption.
Qed.

Lemma pow2_ge_0 : forall x : R, x^2 >= 0.
Proof.
  intros x.
  rewrite <- Rsqr_pow2.
  apply Rle_ge, Rle_0_sqr.
Qed.

(** ** Physical Constants (Geometric Units: G = c = 1) *)

Definition G : R := 1.  (* Gravitational constant *)
Definition c : R := 1.  (* Speed of light *)
Definition pi : R := PI. (* Pi from Coq.Reals *)

(** ** Coordinate Systems *)

(** Boyer-Lindquist coordinates for Kerr-like metrics *)
Record BLCoords := mkBL {
  t_coord : R;     (* Coordinate time *)
  r_coord : R;     (* Radial coordinate *)
  theta_coord : R; (* Polar angle [0, pi] *)
  phi_coord : R;   (* Azimuthal angle [0, 2pi) *)
}.

(** 4-velocity / 4-momentum vector *)
Record FourVector := mkFV {
  v_t : R;
  v_r : R;
  v_theta : R;
  v_phi : R;
}.

(** ** Metric Tensor Structure *)

(** A metric tensor in Boyer-Lindquist coordinates.
    We store only the non-zero diagonal and off-diagonal (g_tphi) components
    for the metrics we care about (Schwarzschild, Kerr). *)
Record MetricComponents := mkMetric {
  g_tt : R;      (* Time-time component *)
  g_rr : R;      (* Radial-radial component *)
  g_thth : R;    (* Theta-theta component *)
  g_phph : R;    (* Phi-phi component *)
  g_tph : R;     (* Time-phi cross term (frame dragging) *)
}.

(** Metric determinant for volume element *)
Definition metric_det (g : MetricComponents) : R :=
  g.(g_tt) * g.(g_rr) * g.(g_thth) * g.(g_phph)
  - g.(g_tph) * g.(g_tph) * g.(g_rr) * g.(g_thth).

(** ** Lorentzian Signature Predicate *)

(** A metric has Lorentzian signature (-,+,+,+) if g_tt < 0
    and the spatial components are positive *)
Definition is_lorentzian (g : MetricComponents) : Prop :=
  g.(g_tt) < 0 /\
  g.(g_rr) > 0 /\
  g.(g_thth) > 0 /\
  g.(g_phph) > 0.

(** ** Norm of a 4-vector under the metric *)

Definition four_norm (g : MetricComponents) (v : FourVector) : R :=
  g.(g_tt) * v.(v_t) * v.(v_t) +
  g.(g_rr) * v.(v_r) * v.(v_r) +
  g.(g_thth) * v.(v_theta) * v.(v_theta) +
  g.(g_phph) * v.(v_phi) * v.(v_phi) +
  2 * g.(g_tph) * v.(v_t) * v.(v_phi).

(** Null geodesic condition: 4-velocity has zero norm *)
Definition is_null (g : MetricComponents) (v : FourVector) : Prop :=
  four_norm g v = 0.

(** Timelike geodesic condition: 4-velocity has negative norm *)
Definition is_timelike (g : MetricComponents) (v : FourVector) : Prop :=
  four_norm g v < 0.

(** Spacelike geodesic condition: 4-velocity has positive norm *)
Definition is_spacelike (g : MetricComponents) (v : FourVector) : Prop :=
  four_norm g v > 0.

(** ** Basic Trigonometric Identities *)

Lemma sin_sq_cos_sq : forall x : R, (sin x)^2 + (cos x)^2 = 1.
Proof.
  intros x.
  rewrite <- Rsqr_pow2, <- Rsqr_pow2.
  apply sin2_cos2.
Qed.

(** ** Positivity Lemmas for Radial Coordinates *)

Lemma r_positive_outside_singularity : forall r : R,
  r > 0 -> r^2 > 0.
Proof.
  intros r Hr.
  apply pow2_gt_0.
  lra.
Qed.

Lemma sin_sq_nonneg : forall x : R, (sin x)^2 >= 0.
Proof.
  intros x.
  apply pow2_ge_0.
Qed.

Lemma cos_sq_nonneg : forall x : R, (cos x)^2 >= 0.
Proof.
  intros x.
  apply pow2_ge_0.
Qed.

(** ** Schwarzschild Radius *)

Definition schwarzschild_radius (M : R) : R := 2 * M.

(** Outside the event horizon predicate *)
Definition outside_horizon (r M : R) : Prop :=
  r > schwarzschild_radius M.

(** Horizon is a coordinate singularity *)
Lemma horizon_singularity : forall M : R,
  M > 0 -> schwarzschild_radius M > 0.
Proof.
  intros M HM.
  unfold schwarzschild_radius.
  lra.
Qed.

(** ** ISCO (Innermost Stable Circular Orbit) *)

(** For Schwarzschild: r_isco = 6M *)
Definition schwarzschild_isco (M : R) : R := 6 * M.

(** ISCO is outside the horizon *)
Lemma isco_outside_horizon : forall M : R,
  M > 0 -> schwarzschild_isco M > schwarzschild_radius M.
Proof.
  intros M HM.
  unfold schwarzschild_isco, schwarzschild_radius.
  lra.
Qed.

(** ** Photon Sphere *)

(** For Schwarzschild: r_photon = 3M = 1.5 * r_s *)
Definition photon_sphere_radius (M : R) : R := 3 * M.

(** Photon sphere is between horizon and ISCO *)
Lemma photon_sphere_location : forall M : R,
  M > 0 ->
  schwarzschild_radius M < photon_sphere_radius M /\
  photon_sphere_radius M < schwarzschild_isco M.
Proof.
  intros M HM.
  unfold schwarzschild_radius, photon_sphere_radius, schwarzschild_isco.
  split; lra.
Qed.

(** ** Extraction Hints *)

(** These hints guide OCaml extraction to use efficient primitives *)

From Stdlib.extraction Require Import ExtrOcamlBasic.
From Stdlib.extraction Require Import ExtrOCamlFloats.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive nat => "int" [ "0" "(fun x -> x + 1)" ].

(** Map Coq Reals to OCaml floats *)
Extract Constant R => "float".
Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".
Extract Constant Rplus => "( +. )".
Extract Constant Rminus => "( -. )".
Extract Constant Rmult => "( *. )".
Extract Constant Rdiv => "( /. )".
Extract Constant Ropp => "Float.neg".
Extract Constant Rinv => "fun x -> 1.0 /. x".

Extract Constant sin => "Float.sin".
Extract Constant cos => "Float.cos".
Extract Constant sqrt => "Float.sqrt".
Extract Constant PI => "Float.pi".
Extract Constant pow => "Float.pow".
Extract Constant Rabs => "Float.abs".

(** Comparison extraction *)
Extract Constant Rlt_dec => "fun x y -> x < y".
Extract Constant Rgt_dec => "fun x y -> x > y".
Extract Constant Rle_dec => "fun x y -> x <= y".
Extract Constant Rge_dec => "fun x y -> x >= y".
Extract Constant Req_dec => "fun x y -> x = y".
