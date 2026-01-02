(** * Distances: Cosmological Distance Measures

    This module formalizes cosmological distance measures in flat
    LambdaCDM cosmology.

    Key definitions (cleanroom derived from physics):
    - Comoving distance: D_C(z) = (c/H0) * integral_0^z dz'/E(z')
    - Luminosity distance: D_L(z) = (1+z) * D_C(z)
    - Angular diameter distance: D_A(z) = D_C(z) / (1+z)

    References:
    - Hogg, "Distance measures in cosmology" (arXiv:astro-ph/9905116)
    - Planck 2018 Cosmological Parameters

    Pipeline: Rocq -> OCaml -> C++23 -> GLSL 4.60 *)

Require Import Blackhole.Prelim.
Require Import Blackhole.Cosmology.FLRW.
From Stdlib Require Import Reals Lra.

Local Open Scope R_scope.

(** ** Comoving Distance *)

(** The comoving distance is the fundamental distance measure:
    D_C(z) = (c/H0) * integral_0^z dz'/E(z')

    For flat LambdaCDM, this integral must be computed numerically
    for general z. We provide the analytical form and numerical
    approximations. *)

(** Line-of-sight comoving distance (proper distance at present epoch) *)
(** D_C = c * integral_0^z dz' / H(z') *)

(** For small z (z << 1), linear approximation *)
Definition comoving_distance_linear (cosmo : FlatLCDM) (z : R) : R :=
  hubble_length cosmo.(H0) * z.

(** For larger z, we need integration. Here we provide a placeholder
    that will be replaced by proper numerical integration in OCaml. *)

(** Comoving distance requires numerical integration of 1/E(z) *)
(** We define it as a postulated function satisfying its differential
    equation: d(D_C)/dz = c / H(z) = (c/H0) / E(z) *)

Parameter comoving_distance : FlatLCDM -> R -> R.

(** Comoving distance satisfies D_C(0) = 0 *)
Axiom comoving_distance_at_z0 : forall cosmo : FlatLCDM,
  comoving_distance cosmo 0 = 0.

(** Comoving distance is monotonically increasing *)
Axiom comoving_distance_increasing : forall (cosmo : FlatLCDM) (z1 z2 : R),
  z2 > z1 -> z1 >= 0 ->
  comoving_distance cosmo z2 > comoving_distance cosmo z1.

(** ** Luminosity Distance *)

(** The luminosity distance relates flux to luminosity:
    D_L(z) = (1+z) * D_C(z)  [for flat universe]

    This is used for standard candle measurements (SNe Ia, etc.) *)

Definition luminosity_distance (cosmo : FlatLCDM) (z : R) : R :=
  (1 + z) * comoving_distance cosmo z.

(** Luminosity distance at z = 0 *)
Theorem luminosity_distance_at_z0 : forall cosmo : FlatLCDM,
  luminosity_distance cosmo 0 = 0.
Proof.
  intros cosmo.
  unfold luminosity_distance.
  rewrite comoving_distance_at_z0.
  ring.
Qed.

(** ** Angular Diameter Distance *)

(** The angular diameter distance relates angular size to physical size:
    D_A(z) = D_C(z) / (1+z)

    Note: D_A has a maximum at z ~ 1-2 for typical cosmologies *)

Definition angular_diameter_distance (cosmo : FlatLCDM) (z : R) : R :=
  comoving_distance cosmo z / (1 + z).

(** Relation between D_L and D_A (Etherington reciprocity theorem) *)
Theorem distance_duality : forall (cosmo : FlatLCDM) (z : R),
  z > 0 ->
  luminosity_distance cosmo z = (1 + z)^2 * angular_diameter_distance cosmo z.
Proof.
  intros cosmo z Hz.
  unfold luminosity_distance, angular_diameter_distance.
  field.
  lra.
Qed.

(** ** Distance Modulus *)

(** Distance modulus: mu = 5 * log10(D_L / 10 pc) = 5 * log10(D_L) + 25
    where D_L is in Mpc

    Used for comparing apparent and absolute magnitudes:
    m - M = mu *)

(** We parameterize by D_L in Mpc *)
Definition distance_modulus (D_L_Mpc : R) : R :=
  5 * ln D_L_Mpc / ln 10 + 25.

(** ** Lookback Time *)

(** Lookback time: time since light was emitted at redshift z
    t_L(z) = (1/H0) * integral_0^z dz' / ((1+z') * E(z'))

    For z = 0: t_L = 0
    For z -> infinity: t_L -> t_0 (age of universe) *)

Parameter lookback_time : FlatLCDM -> R -> R.

(** Lookback time at z = 0 is zero *)
Axiom lookback_time_at_z0 : forall cosmo : FlatLCDM,
  lookback_time cosmo 0 = 0.

(** ** Comoving Volume *)

(** Comoving volume element: dV_C = D_H * (1+z)^2 * D_A^2 * dOmega * dz / E(z)

    Total comoving volume within redshift z (for flat universe):
    V_C(z) = (4 pi / 3) * D_C(z)^3 *)

Definition comoving_volume (cosmo : FlatLCDM) (z : R) : R :=
  (4 * PI / 3) * (comoving_distance cosmo z)^3.

(** ** Transverse Comoving Distance *)

(** For flat universe, transverse comoving distance equals line-of-sight:
    D_M = D_C  [flat]
    D_M = D_H * sinh(sqrt(Omega_k) * D_C / D_H) / sqrt(Omega_k)  [open]
    D_M = D_H * sin(sqrt(-Omega_k) * D_C / D_H) / sqrt(-Omega_k)  [closed] *)

Definition transverse_comoving_distance (cosmo : FlatLCDM) (z : R) : R :=
  comoving_distance cosmo z.  (* Flat universe *)

(** ** Proper Motion Distance *)

(** Proper motion distance = transverse comoving distance
    Used for proper motion measurements *)

Definition proper_motion_distance (cosmo : FlatLCDM) (z : R) : R :=
  transverse_comoving_distance cosmo z.

(** ** Particle Horizon *)

(** Particle horizon: maximum comoving distance light could have traveled
    since the Big Bang. For flat LambdaCDM, this is finite. *)

Parameter particle_horizon : FlatLCDM -> R.

(** ** Event Horizon *)

(** Event horizon: maximum comoving distance light can travel in the future.
    For accelerating universe, this is finite and decreasing with time. *)

Parameter event_horizon : FlatLCDM -> R -> R.

(** ** Sound Horizon *)

(** Sound horizon at recombination: sets BAO scale
    r_s ~ 147 Mpc for Planck18 *)

Definition sound_horizon_Planck18 : R := 147.09.  (** Mpc *)

(** ** Numerical Approximations *)

(** For numerical evaluation, we provide Simpson's rule integration.
    The actual integration happens in extracted OCaml code. *)

(** Trapezoidal approximation for small z *)
Definition comoving_distance_trapz (cosmo : FlatLCDM) (z n : R) : R :=
  let dz := z / n in
  let D_H := hubble_length cosmo.(H0) in
  (* Placeholder: actual summation in OCaml *)
  D_H * z / E_z cosmo (z / 2).

(** ** Extraction Interface *)

Definition compute_luminosity_distance (cosmo : FlatLCDM) (z : R) : R :=
  luminosity_distance cosmo z.

Definition compute_angular_diameter_distance (cosmo : FlatLCDM) (z : R) : R :=
  angular_diameter_distance cosmo z.

Definition compute_distance_modulus (D_L_Mpc : R) : R :=
  distance_modulus D_L_Mpc.

Definition compute_comoving_volume (cosmo : FlatLCDM) (z : R) : R :=
  comoving_volume cosmo z.

(** Linear approximation for extraction testing *)
Definition compute_comoving_distance_linear (H0 z : R) : R :=
  c_km_s / H0 * z.

(** Distance duality check *)
Definition verify_distance_duality (D_L D_A z : R) : bool :=
  let ratio := D_L / ((1 + z)^2 * D_A) in
  if Rlt_dec (Rabs (ratio - 1)) 0.001 then true else false.
