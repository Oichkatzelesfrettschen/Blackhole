(** * Extract: Code Extraction to OCaml

    This module extracts verified physics code from Rocq proofs
    to OCaml, which is then transpiled to C++23 and GLSL 4.60.

    Extraction strategy:
    - Map Coq R (real numbers) to OCaml float
    - Map trigonometric functions to OCaml Float module
    - Preserve computational content of definitions
    - Skip proofs (erased during extraction)

    Pipeline: Rocq -> OCaml -> C++23 -> GLSL 4.60 *)

Require Import Blackhole.Prelim.
Require Import Blackhole.Metrics.Schwarzschild.
Require Import Blackhole.Metrics.Kerr.
Require Import Blackhole.Kerr.Metric.
Require Import Blackhole.Kerr.Horizons.
Require Import Blackhole.Kerr.BPT_ISCO.
Require Import Blackhole.Wormholes.MorrisThorne.
Require Import Blackhole.Wormholes.EREPR.
Require Import Blackhole.Wormholes.Islands.
Require Import Blackhole.Geodesics.RK4.
Require Import Blackhole.Geodesics.Equations.
Require Import Blackhole.Geodesics.NullConstraint.
Require Import Blackhole.Cosmology.Axiodilaton.

From Stdlib.extraction Require Import ExtrOcamlBasic.
From Stdlib.extraction Require Import ExtrOCamlFloats.
From Stdlib Require Import Extraction.
From Stdlib Require Import Reals.

(** ** Basic Type Extraction *)

(** Natural numbers to int *)
Extract Inductive nat => "int" ["0" "succ"]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(** Booleans *)
Extract Inductive bool => "bool" ["true" "false"].

(** Options *)
Extract Inductive option => "option" ["Some" "None"].

(** Lists *)
Extract Inductive list => "list" ["[]" "(::)"].

(** ** Real Number Extraction *)

(** Map Coq reals to OCaml floats *)
Extract Constant R => "float".
Extract Constant R0 => "0.0".
Extract Constant R1 => "1.0".

(** Arithmetic operations *)
Extract Constant Rplus => "( +. )".
Extract Constant Rminus => "( -. )".
Extract Constant Rmult => "( *. )".
Extract Constant Rdiv => "( /. )".
Extract Constant Ropp => "Float.neg".
Extract Constant Rinv => "(fun x -> 1.0 /. x)".

(** Comparison operations *)
Extract Constant Rlt_dec => "(fun x y -> x < y)".
Extract Constant Rgt_dec => "(fun x y -> x > y)".
Extract Constant Rle_dec => "(fun x y -> x <= y)".
Extract Constant Rge_dec => "(fun x y -> x >= y)".
Extract Constant Req_dec => "(fun x y -> x = y)".

(** Transcendental functions *)
Extract Constant sin => "Float.sin".
Extract Constant cos => "Float.cos".
Extract Constant sqrt => "Float.sqrt".
Extract Constant exp => "Float.exp".
Extract Constant ln => "Float.log".
Extract Constant atan => "Float.atan".
Extract Constant acos => "Float.acos".
Extract Constant asin => "Float.asin".

(** Constants *)
Extract Constant PI => "Float.pi".

(** Power function *)
Extract Constant pow => "Float.pow".
Extract Constant Rabs => "Float.abs".

(** ** Record Extraction *)

(** Boyer-Lindquist coordinates *)
Extract Inductive BLCoords => "bl_coords"
  ["{ t_coord = _; r_coord = _; theta_coord = _; phi_coord = _ }"].

(** Four-vectors *)
Extract Inductive FourVector => "four_vector"
  ["{ v_t = _; v_r = _; v_theta = _; v_phi = _ }"].

(** Metric components *)
Extract Inductive MetricComponents => "metric_components"
  ["{ g_tt = _; g_rr = _; g_thth = _; g_phph = _; g_tph = _ }"].

(** State vectors *)
Extract Inductive StateVector => "state_vector"
  ["{ x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ }"].

(** ** Schwarzschild Metric Extraction *)

Extraction "physics_schwarzschild.ml"
  f_schwarzschild
  schwarzschild_metric
  schwarzschild_g_tt
  schwarzschild_g_rr
  schwarzschild_g_thth
  schwarzschild_g_phph
  christoffel_t_tr
  christoffel_r_tt
  christoffel_r_rr
  christoffel_r_thth
  christoffel_r_phph
  christoffel_th_rth
  christoffel_th_phph
  christoffel_ph_rph
  christoffel_ph_thph
  schwarzschild_radius
  schwarzschild_isco
  photon_sphere_radius
  radial_acceleration.

(** ** Kerr Metric Extraction *)

Extraction "physics_kerr.ml"
  kerr_Sigma
  kerr_Delta
  kerr_A
  kerr_metric
  kerr_g_tt
  kerr_g_rr
  kerr_g_thth
  kerr_g_phph
  kerr_g_tph
  outer_horizon
  inner_horizon
  ergosphere_radius
  frame_dragging_omega
  kerr_isco_prograde
  kerr_isco_retrograde
  photon_orbit_prograde
  photon_orbit_retrograde
  kerr_christoffel_t_tr
  kerr_christoffel_r_tt.

(** ** Morris-Thorne Wormhole Extraction *)

Extraction "physics_wormhole.ml"
  shape_constant
  shape_ellis
  morris_thorne_metric
  throat_radius
  mt_g_tt
  mt_g_rr
  mt_g_thth
  mt_g_phph
  mt_christoffel_r_rr
  mt_christoffel_r_thth
  mt_christoffel_r_phph
  mt_christoffel_th_rth
  mt_christoffel_th_phph
  mt_christoffel_ph_rph
  mt_christoffel_ph_thph
  proper_distance
  embedding_height.

(** ** RK4 Integration Extraction *)

Extraction "physics_rk4.ml"
  sv_add
  sv_scale
  rk4_step
  rk4_k1
  rk4_k2
  rk4_k3
  rk4_k4
  rk4_combine
  local_error_bound
  integrate
  check_termination.

(** ** Geodesic Equations Extraction *)

Extraction "physics_geodesic.ml"
  geodesic_rhs
  energy
  angular_momentum
  carter_constant
  effective_potential_schwarzschild
  impact_parameter
  critical_impact_schwarzschild
  init_null_geodesic
  compute_geodesic_rhs
  compute_energy
  compute_angular_momentum
  compute_impact_parameter.

(** ** Null Constraint Extraction *)

Extraction "physics_null.ml"
  null_constraint_function
  constraint_after_step
  constraint_drift_step
  renormalize_null
  needs_renormalization
  check_null_constraint
  correct_null_constraint
  should_correct.

(** ** Phase 5 Extended Kerr Extraction *)

Extraction "physics_kerr_extended.ml"
  (* Kerr.Metric *)
  kerr_Sigma kerr_Delta kerr_A kerr_metric_tensor
  kerr_g_tt kerr_g_rr kerr_g_thth kerr_g_phph kerr_g_tph

  (* Kerr.Horizons *)
  outer_horizon inner_horizon ergosphere_outer_radius
  surface_gravity hawking_temperature

  (* Kerr.BPT_ISCO *)
  bpt_Z1 bpt_Z2
  isco_radius_prograde isco_radius_retrograde
  circular_orbit_radius binding_energy_isco.

(** ** Phase 5 Axiodilaton Cosmology Extraction *)

Extraction "physics_axiodilaton.ml"
  (* Axiodilaton *)
  omega_axiodilaton axiodilaton_function
  axiodilaton_hubble_normalized axiodilaton_hubble_parameter
  axiodilaton_H0_prediction
  axiodilaton_comoving_distance axiodilaton_luminosity_distance
  axiodilaton_angular_diameter_distance
  axiodilaton_equation_of_state axiodilaton_deceleration_parameter.

(** ** Phase 5 ER=EPR and Islands Extraction *)

Extraction "physics_quantum.ml"
  (* EREPR *)
  throat_radius throat_pinch_factor
  entanglement_entropy page_curve_entropy

  (* Islands *)
  page_time page_curve_early page_curve_late
  page_curve critical_island_transition_time
  generalized_entropy quantum_extremal_surface
  ryu_takayanagi_entropy entanglement_wedge_dimension
  hawking_radiation_entropy accessible_information.

(** ** Combined Physics Module *)

Extraction "physics.ml"
  (* Prelim *)
  G c pi
  four_norm is_null is_lorentzian
  schwarzschild_radius schwarzschild_isco photon_sphere_radius

  (* Schwarzschild *)
  f_schwarzschild schwarzschild_metric
  schwarzschild_g_tt schwarzschild_g_rr
  christoffel_t_tr christoffel_r_tt christoffel_r_rr

  (* Kerr *)
  kerr_Sigma kerr_Delta kerr_A kerr_metric
  kerr_g_tt kerr_g_rr kerr_g_tph
  outer_horizon inner_horizon ergosphere_outer_radius
  kerr_isco_prograde

  (* Morris-Thorne *)
  morris_thorne_metric throat_radius
  mt_g_tt mt_g_rr proper_distance

  (* RK4 *)
  sv_add sv_scale rk4_step integrate

  (* Geodesics *)
  geodesic_rhs energy angular_momentum
  init_null_geodesic

  (* Null constraint *)
  null_constraint_function renormalize_null

  (* Phase 5: Kerr Extended *)
  kerr_g_thth kerr_g_phph kerr_g_tph
  surface_gravity hawking_temperature
  bpt_Z1 bpt_Z2 isco_radius_prograde isco_radius_retrograde

  (* Phase 5: Axiodilaton *)
  axiodilaton_hubble_normalized axiodilaton_H0_prediction
  axiodilaton_luminosity_distance axiodilaton_deceleration_parameter

  (* Phase 5: ER=EPR and Islands *)
  page_curve critical_island_transition_time
  generalized_entropy ryu_takayanagi_entropy
  entanglement_wedge_dimension.
