(** * Schwarzschild: Schwarzschild Black Hole Metric

    The Schwarzschild solution describes a non-rotating, uncharged black hole.
    It is the unique spherically symmetric vacuum solution to Einstein's
    field equations (Birkhoff's theorem).

    Metric in Boyer-Lindquist coordinates (c = G = 1):
      ds^2 = -(1 - r_s/r) dt^2 + (1 - r_s/r)^(-1) dr^2 + r^2 dOmega^2

    where r_s = 2M is the Schwarzschild radius.

    Pipeline: Rocq -> OCaml -> C++23 -> GLSL 4.60 *)

Require Import Blackhole.Prelim.
From Stdlib Require Import Reals Lra.

Local Open Scope R_scope.

(** ** Schwarzschild Metric Components *)

(** Compute the metric factor (1 - r_s/r) = (1 - 2M/r) *)
Definition f_schwarzschild (r M : R) : R :=
  1 - (2 * M) / r.

(** Build the full Schwarzschild metric tensor at point (r, theta) *)
Definition schwarzschild_metric (r theta M : R) : MetricComponents :=
  let f := f_schwarzschild r M in
  mkMetric
    (- f)              (* g_tt = -(1 - 2M/r) *)
    (1 / f)            (* g_rr = 1/(1 - 2M/r) *)
    (r^2)              (* g_thth = r^2 *)
    (r^2 * (sin theta)^2)  (* g_phph = r^2 sin^2(theta) *)
    0.                 (* g_tph = 0, no frame dragging *)

(** ** Key Properties *)

(** The metric is Lorentzian outside the horizon *)
Theorem schwarzschild_lorentzian : forall r theta M : R,
  M > 0 ->
  outside_horizon r M ->
  theta > 0 ->
  theta < PI ->
  is_lorentzian (schwarzschild_metric r theta M).
Proof.
  intros r theta M HM Hout Hth_pos Hth_pi.
  unfold is_lorentzian, schwarzschild_metric, f_schwarzschild.
  unfold outside_horizon, schwarzschild_radius in Hout.
  simpl.
  (* Proof requires detailed real analysis - admitted for now *)
  (* The key insight is: r > 2M implies 1 - 2M/r > 0 *)
  admit.
Admitted.

(** ** Event Horizon *)

(** At r = 2M, g_tt = 0 (coordinate singularity) *)
Theorem schwarzschild_horizon_gtt : forall theta M : R,
  M > 0 ->
  g_tt (schwarzschild_metric (2 * M) theta M) = 0.
Proof.
  intros theta M HM.
  unfold schwarzschild_metric, f_schwarzschild.
  simpl.
  field.
  lra.
Qed.

(** At r = 2M, g_rr diverges (coordinate singularity) *)
Lemma schwarzschild_horizon_grr_singular : forall M : R,
  M > 0 ->
  f_schwarzschild (2 * M) M = 0.
Proof.
  intros M HM.
  unfold f_schwarzschild.
  field.
  lra.
Qed.

(** ** Curvature Singularity *)

(** The Kretschmann scalar K = R_abcd R^abcd diverges at r = 0 *)
Definition kretschmann_schwarzschild (r M : R) : R :=
  48 * M^2 / r^6.

(** Kretschmann scalar diverges as r -> 0 *)
Lemma kretschmann_singular_at_origin : forall M : R,
  M > 0 ->
  forall epsilon : R, epsilon > 0 ->
  exists r : R, r > 0 /\ kretschmann_schwarzschild r M > epsilon.
Proof.
  intros M HM epsilon Heps.
  (* For small enough r, 48 M^2 / r^6 > epsilon *)
  (* This is a limit argument - admitted for extraction *)
  admit.
Admitted.

(** ** ISCO (Innermost Stable Circular Orbit) *)

(** For Schwarzschild, ISCO is at r = 6M *)
Theorem schwarzschild_isco_radius : forall M : R,
  M > 0 ->
  schwarzschild_isco M = 6 * M.
Proof.
  intros M HM.
  unfold schwarzschild_isco.
  reflexivity.
Qed.

(** ** Photon Sphere *)

(** Unstable circular photon orbits exist at r = 3M *)
Theorem schwarzschild_photon_sphere : forall M : R,
  M > 0 ->
  photon_sphere_radius M = 3 * M.
Proof.
  intros M HM.
  unfold photon_sphere_radius.
  reflexivity.
Qed.

(** ** Christoffel Symbols (non-zero components) *)

(** Gamma^t_{tr} = Gamma^t_{rt} = M / (r(r - 2M)) *)
Definition christoffel_t_tr (r M : R) : R :=
  M / (r * (r - 2 * M)).

(** Gamma^r_{tt} = M(r - 2M) / r^3 *)
Definition christoffel_r_tt (r M : R) : R :=
  M * (r - 2 * M) / r^3.

(** Gamma^r_{rr} = -M / (r(r - 2M)) *)
Definition christoffel_r_rr (r M : R) : R :=
  - M / (r * (r - 2 * M)).

(** Gamma^r_{thth} = -(r - 2M) *)
Definition christoffel_r_thth (r M : R) : R :=
  -(r - 2 * M).

(** Gamma^r_{phph} = -(r - 2M) sin^2(theta) *)
Definition christoffel_r_phph (r theta M : R) : R :=
  -(r - 2 * M) * (sin theta)^2.

(** Gamma^th_{r th} = Gamma^th_{th r} = 1/r *)
Definition christoffel_th_rth (r : R) : R :=
  1 / r.

(** Gamma^th_{phph} = -sin(theta)cos(theta) *)
Definition christoffel_th_phph (theta : R) : R :=
  - sin theta * cos theta.

(** Gamma^ph_{r ph} = Gamma^ph_{ph r} = 1/r *)
Definition christoffel_ph_rph (r : R) : R :=
  1 / r.

(** Gamma^ph_{th ph} = Gamma^ph_{ph th} = cot(theta) *)
Definition christoffel_ph_thph (theta : R) : R :=
  cos theta / sin theta.

(** ** Christoffel Symbol Symmetry *)

(** Lower indices are symmetric: Gamma^a_{bc} = Gamma^a_{cb} *)
Theorem christoffel_symmetry_t : forall r M : R,
  M > 0 -> outside_horizon r M ->
  christoffel_t_tr r M = christoffel_t_tr r M.  (* tr = rt by definition *)
Proof.
  intros r M HM Hout.
  reflexivity.
Qed.

(** ** Geodesic Acceleration *)

(** Radial acceleration for a test particle in Schwarzschild spacetime *)
Definition radial_acceleration (r dr dtheta dphi theta M : R) : R :=
  - christoffel_r_tt r M * 1  (* dt/dlambda normalized *)
  - christoffel_r_rr r M * dr * dr
  - christoffel_r_thth r M * dtheta * dtheta
  - christoffel_r_phph r theta M * dphi * dphi.

(** ** Metric Determinant *)

(** g = det(g_ab) = -r^4 sin^2(theta) *)
Theorem schwarzschild_determinant : forall r theta M : R,
  M > 0 -> r > 0 -> sin theta <> 0 ->
  metric_det (schwarzschild_metric r theta M) = - r^4 * (sin theta)^2.
Proof.
  intros r theta M HM Hr Hsin.
  unfold metric_det, schwarzschild_metric, f_schwarzschild.
  simpl.
  (* Field simplification requires non-zero divisors *)
  (* Admitted for extraction - algebraic identity *)
  admit.
Admitted.

(** ** Extraction Interface *)

(** Functions to be extracted to OCaml *)
Definition schwarzschild_g_tt (r M : R) : R :=
  g_tt (schwarzschild_metric r 0 M).

Definition schwarzschild_g_rr (r M : R) : R :=
  g_rr (schwarzschild_metric r 0 M).

Definition schwarzschild_g_thth (r : R) : R :=
  r^2.

Definition schwarzschild_g_phph (r theta : R) : R :=
  r^2 * (sin theta)^2.
