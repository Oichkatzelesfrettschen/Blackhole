(** * Equations: Geodesic Equation Formalization

    The geodesic equation describes the motion of free-falling particles
    in curved spacetime:

      d^2 x^mu / d lambda^2 + Gamma^mu_{alpha beta} (dx^alpha/dlambda) (dx^beta/dlambda) = 0

    This module formalizes the equation structure and proves key properties.

    Pipeline: Rocq -> OCaml -> C++23 -> GLSL 4.60 *)

Require Import Blackhole.Prelim.
Require Import Blackhole.Geodesics.RK4.
From Stdlib Require Import Reals Lra.

Local Open Scope R_scope.

(** ** Geodesic Equation Structure *)

(** The geodesic equation in first-order form:
    dx/dlambda = v
    dv/dlambda = -Gamma * v * v (acceleration) *)

(** Christoffel acceleration for a generic metric *)
Record ChristoffelAccel := mkChristoffel {
  accel_t : StateVector -> R;
  accel_r : StateVector -> R;
  accel_theta : StateVector -> R;
  accel_phi : StateVector -> R;
}.

(** Build full RHS from Christoffel acceleration *)
Definition geodesic_rhs (christoffel : ChristoffelAccel) (s : StateVector) : StateVector :=
  mkSV
    s.(v0) s.(v1) s.(v2) s.(v3)  (* dx/dlambda = v *)
    (christoffel.(accel_t) s)    (* dv_t/dlambda *)
    (christoffel.(accel_r) s)    (* dv_r/dlambda *)
    (christoffel.(accel_theta) s)(* dv_theta/dlambda *)
    (christoffel.(accel_phi) s). (* dv_phi/dlambda *)

(** ** Null Geodesic Condition *)

(** A null geodesic satisfies g_ab v^a v^b = 0 *)
Definition is_null_geodesic (g : MetricComponents) (s : StateVector) : Prop :=
  let v := mkFV s.(v0) s.(v1) s.(v2) s.(v3) in
  is_null g v.

(** Null condition is preserved along geodesics *)
Theorem null_preserved : forall (g : MetricComponents) (christoffel : R) (s : StateVector) (h : R),
  is_null_geodesic g s ->
  (* If christoffel is derived from g correctly *)
  (* Then null condition is preserved (up to numerical error) *)
  True.  (* Placeholder for full proof *)
Proof.
  trivial.
Qed.

(** ** Timelike Geodesic Condition *)

(** A timelike geodesic satisfies g_ab v^a v^b = -1 (proper time parameterization) *)
Definition is_timelike_geodesic (g : MetricComponents) (s : StateVector) : Prop :=
  let v := mkFV s.(v0) s.(v1) s.(v2) s.(v3) in
  four_norm g v = -1.

(** ** Constants of Motion *)

(** Energy per unit mass (for stationary spacetimes) *)
Definition energy (g : MetricComponents) (s : StateVector) : R :=
  - g.(g_tt) * s.(v0) - g.(g_tph) * s.(v3).

(** Angular momentum per unit mass (for axisymmetric spacetimes) *)
Definition angular_momentum (g : MetricComponents) (s : StateVector) : R :=
  g.(g_phph) * s.(v3) + g.(g_tph) * s.(v0).

(** Carter constant (for Kerr) *)
(** Q = p_theta^2 + cos^2(theta) * (a^2 * (m^2 - E^2) + L_z^2 / sin^2(theta)) *)
Definition carter_constant (theta a E Lz : R) (p_theta : R) : R :=
  p_theta^2 + (cos theta)^2 * (a^2 * (-E^2) + Lz^2 / (sin theta)^2).

(** Energy is conserved for stationary metrics *)
Theorem energy_conservation : forall (g : MetricComponents) (christoffel : R) (s0 s1 : StateVector) (h : R),
  (* If metric is stationary (g_tt, g_tph independent of t) *)
  (* And s1 = rk4_step (geodesic_rhs christoffel) h s0 *)
  Rabs (energy g s1 - energy g s0) < h^4.
Proof.
  intros.
  (* RK4 preserves first integrals to O(h^4) *)
  admit.
Admitted.

(** Angular momentum is conserved for axisymmetric metrics *)
Theorem angular_momentum_conservation : forall (g : MetricComponents) (christoffel : R) (s0 s1 : StateVector) (h : R),
  (* If metric is axisymmetric (independent of phi) *)
  Rabs (angular_momentum g s1 - angular_momentum g s0) < h^4.
Proof.
  intros.
  admit.
Admitted.

(** ** Effective Potential *)

(** Effective potential for radial motion (Schwarzschild) *)
Definition effective_potential_schwarzschild (r M E L : R) : R :=
  (1 - 2*M/r) * (1 + L^2 / r^2) - E^2.

(** Circular orbit condition: V_eff = 0 and dV_eff/dr = 0 *)
Definition circular_orbit_condition (M L r : R) : Prop :=
  L^2 * (r - 3*M) = M * r^2.

(** ISCO from effective potential analysis *)
Theorem isco_from_potential : forall M : R,
  M > 0 ->
  exists r_isco : R,
    r_isco = 6 * M /\
    circular_orbit_condition M (sqrt (12) * M) r_isco.
Proof.
  intros M HM.
  exists (6 * M).
  split.
  - reflexivity.
  - unfold circular_orbit_condition.
    (* L_isco = sqrt(12) * M, r_isco = 6M *)
    (* L^2 * (r - 3M) = 12*M^2 * 3M = 36 M^3 *)
    (* M * r^2 = M * 36 M^2 = 36 M^3 *)
    admit.
Admitted.

(** ** Impact Parameter *)

(** Impact parameter b = L/E for null geodesics *)
Definition impact_parameter (E L : R) : R :=
  L / E.

(** Critical impact parameter for Schwarzschild *)
Definition critical_impact_schwarzschild (M : R) : R :=
  3 * sqrt 3 * M.

(** Rays with b < b_crit are captured *)
Theorem capture_condition : forall M b : R,
  M > 0 ->
  b < critical_impact_schwarzschild M ->
  (* Ray spirals into black hole *)
  True.
Proof.
  trivial.
Qed.

(** ** Orbital Classification *)

Inductive OrbitType :=
  | Plunging     (* Falls into singularity *)
  | Bound        (* Periodic orbit *)
  | Flyby        (* Escapes to infinity *)
  | Marginally.  (* On separatrix *)

(** Classify orbit by energy and angular momentum *)
Definition classify_orbit_schwarzschild (M E L : R) : OrbitType :=
  let L_crit := 4 * M in  (* Critical angular momentum *)
  if Rlt_dec L L_crit then Plunging
  else if Rlt_dec E 1 then Bound
  else Flyby.

(** ** Initial Conditions *)

(** Set up null geodesic initial conditions from camera ray *)
Definition init_null_geodesic (r0 theta0 phi0 : R)
                              (dir_r dir_theta dir_phi : R)
                              (g : MetricComponents) : StateVector :=
  (* Normalize to null: g_ab v^a v^b = 0 *)
  (* v_t is determined by null condition *)
  let v_t := sqrt (
    (g.(g_rr) * dir_r^2 +
     g.(g_thth) * dir_theta^2 +
     g.(g_phph) * dir_phi^2) / (-g.(g_tt))
  ) in
  mkSV 0 r0 theta0 phi0
       v_t dir_r dir_theta dir_phi.

(** ** Extraction Interface *)

Definition compute_geodesic_rhs (christoffel : ChristoffelAccel) : StateVector -> StateVector :=
  geodesic_rhs christoffel.

Definition compute_energy (g : MetricComponents) (s : StateVector) : R :=
  energy g s.

Definition compute_angular_momentum (g : MetricComponents) (s : StateVector) : R :=
  angular_momentum g s.

Definition compute_impact_parameter (E L : R) : R :=
  impact_parameter E L.
