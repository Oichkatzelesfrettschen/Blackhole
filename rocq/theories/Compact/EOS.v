(** * EOS: Equation of State Formalization

    This module formalizes equations of state (EOS) for compact objects,
    including polytropic EOS for neutron star modeling.

    Key equations (cleanroom derived from physics):
    - Polytropic EOS: P = K * rho^gamma
    - Energy density: epsilon = rho * c^2 + P / (gamma - 1)
    - Sound speed: c_s^2 = gamma * P / (epsilon + P)

    References:
    - Shapiro & Teukolsky, "Black Holes, White Dwarfs, and Neutron Stars"
    - Oppenheimer & Volkoff (1939), Tolman (1939)

    Pipeline: Rocq -> OCaml -> C++23 -> GLSL 4.60 *)

Require Import Blackhole.Prelim.
From Stdlib Require Import Reals Lra Rpower.

Local Open Scope R_scope.

(** We use Rpower for real exponents: x^y = exp(y * ln(x)) *)

(** ** Polytropic Equation of State *)

(** A polytropic EOS is characterized by:
    - K: polytropic constant (units depend on gamma)
    - gamma: adiabatic index (must be > 1)

    The pressure-density relation is: P = K * rho^gamma *)

Record PolytropeParams := mkPolytrope {
  poly_K : R;      (** Polytropic constant *)
  poly_gamma : R;  (** Adiabatic index (> 1) *)
}.

(** Well-formed polytrope: K > 0 and gamma > 1 *)
Definition valid_polytrope (p : PolytropeParams) : Prop :=
  p.(poly_K) > 0 /\ p.(poly_gamma) > 1.

(** Pressure from density: P = K * rho^gamma *)
Definition polytrope_pressure (p : PolytropeParams) (rho : R) : R :=
  p.(poly_K) * Rpower rho p.(poly_gamma).

(** Energy density including rest mass: epsilon = rho * c^2 + P / (gamma - 1)
    In geometric units (c = 1): epsilon = rho + P / (gamma - 1) *)
Definition polytrope_energy_density (p : PolytropeParams) (rho : R) : R :=
  let P := polytrope_pressure p rho in
  rho + P / (p.(poly_gamma) - 1).

(** Sound speed squared: c_s^2 = gamma * P / (epsilon + P)
    Must satisfy c_s^2 <= 1 for causality (in c = 1 units) *)
Definition polytrope_sound_speed_sq (p : PolytropeParams) (rho : R) : R :=
  let P := polytrope_pressure p rho in
  let eps := polytrope_energy_density p rho in
  p.(poly_gamma) * P / (eps + P).

(** ** Physical Constraints *)

(** Pressure is positive for positive density *)
Theorem pressure_positive : forall (p : PolytropeParams) (rho : R),
  valid_polytrope p ->
  rho > 0 ->
  polytrope_pressure p rho > 0.
Proof.
  intros p rho [HK Hgamma] Hrho.
  unfold polytrope_pressure.
  apply Rmult_gt_0_compat.
  - exact HK.
  - (* rho^gamma > 0 for rho > 0 *)
    admit.
Admitted.

(** Energy density exceeds rest mass *)
Theorem energy_exceeds_rest_mass : forall (p : PolytropeParams) (rho : R),
  valid_polytrope p ->
  rho > 0 ->
  polytrope_energy_density p rho > rho.
Proof.
  intros p rho Hvalid Hrho.
  unfold polytrope_energy_density.
  (* epsilon = rho + P/(gamma-1) > rho since P > 0 and gamma > 1 *)
  admit.
Admitted.

(** Sound speed is subluminal for physically reasonable polytropes *)
Theorem sound_speed_subluminal : forall (p : PolytropeParams) (rho : R),
  valid_polytrope p ->
  p.(poly_gamma) <= 2 ->  (* Realistic constraint *)
  rho > 0 ->
  polytrope_sound_speed_sq p rho < 1.
Proof.
  intros p rho Hvalid Hgamma_bound Hrho.
  (* c_s^2 = gamma * P / (epsilon + P) < 1 requires analysis *)
  admit.
Admitted.

(** ** Common Polytropic Indices *)

(** Non-relativistic degenerate electrons: gamma = 5/3 *)
Definition gamma_nonrel_degenerate : R := 5 / 3.

(** Ultra-relativistic degenerate electrons: gamma = 4/3 *)
Definition gamma_ultrarel_degenerate : R := 4 / 3.

(** Stiff equation of state: gamma = 2 *)
Definition gamma_stiff : R := 2.

(** Radiation-dominated: gamma = 4/3 *)
Definition gamma_radiation : R := 4 / 3.

(** ** Polytropic Index n *)

(** Polytropic index: n = 1 / (gamma - 1)
    Commonly used in stellar structure literature *)
Definition polytropic_index (gamma : R) : R :=
  1 / (gamma - 1).

(** Inverse relation: gamma = 1 + 1/n *)
Theorem gamma_from_index : forall n : R,
  n > 0 ->
  1 + 1/n = (n + 1) / n.
Proof.
  intros n Hn.
  field.
  lra.
Qed.

(** Common indices:
    - n = 3/2 (gamma = 5/3): non-relativistic degenerate
    - n = 3 (gamma = 4/3): relativistic degenerate
    - n = 1 (gamma = 2): stiff EOS *)

(** ** Relativistic Polytrope *)

(** For relativistic stars, we need enthalpy: h = (epsilon + P) / rho *)
Definition polytrope_enthalpy (p : PolytropeParams) (rho : R) : R :=
  let P := polytrope_pressure p rho in
  let eps := polytrope_energy_density p rho in
  (eps + P) / rho.

(** Log-enthalpy for integration: H = ln(h) *)
Definition polytrope_log_enthalpy (p : PolytropeParams) (rho : R) : R :=
  ln (polytrope_enthalpy p rho).

(** ** Adiabatic Index *)

(** The adiabatic index Gamma_1 = d(ln P) / d(ln rho) at constant entropy
    For a polytrope, Gamma_1 = gamma by definition *)
Definition adiabatic_index (p : PolytropeParams) : R :=
  p.(poly_gamma).

(** ** Maximum Mass Scaling *)

(** For polytropes, maximum NS mass scales as:
    M_max ~ K^(n/2) * (central density)^((3-n)/(2n))

    The exact prefactor depends on solving the TOV equations. *)

(** Chandrasekhar mass for n = 3 (gamma = 4/3) white dwarfs:
    M_Ch ~ 1.44 * (2/mu_e)^2 solar masses *)

(** ** Extraction Interface *)

Definition compute_pressure (K gamma rho : R) : R :=
  K * Rpower rho gamma.

Definition compute_energy_density (K gamma rho : R) : R :=
  let P := K * Rpower rho gamma in
  rho + P / (gamma - 1).

Definition compute_sound_speed_sq (K gamma rho : R) : R :=
  let P := K * Rpower rho gamma in
  let eps := rho + P / (gamma - 1) in
  gamma * P / (eps + P).

Definition compute_enthalpy (K gamma rho : R) : R :=
  let P := K * Rpower rho gamma in
  let eps := rho + P / (gamma - 1) in
  (eps + P) / rho.
