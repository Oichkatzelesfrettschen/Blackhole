(** * FLRW: Friedmann-Lemaitre-Robertson-Walker Cosmology

    This module formalizes the FLRW metric and Friedmann equations
    for homogeneous, isotropic cosmology.

    Key equations (cleanroom derived from physics):
    - Friedmann equation: H^2 = (8 pi G / 3) * rho - k/a^2 + Lambda/3
    - Flat LambdaCDM: H(z) = H0 * sqrt(Omega_m * (1+z)^3 + Omega_Lambda)
    - Dimensionless Hubble: E(z) = H(z) / H0

    References:
    - Weinberg, "Cosmology" (2008)
    - Planck 2018 Cosmological Parameters

    Pipeline: Rocq -> OCaml -> C++23 -> GLSL 4.60 *)

Require Import Blackhole.Prelim.
From Stdlib Require Import Reals Lra.

Local Open Scope R_scope.

(** ** Cosmological Parameters *)

(** Planck 2018 TT,TE,EE+lowE+lensing best-fit values *)
Definition H0_Planck18 : R := 67.36.  (** km/s/Mpc *)
Definition Omega_m_Planck18 : R := 0.3153.  (** Total matter density parameter *)
Definition Omega_b_Planck18 : R := 0.0493.  (** Baryon density parameter *)
Definition T_CMB_Planck18 : R := 2.7255.    (** CMB temperature in Kelvin *)

(** Derived quantities for flat LambdaCDM *)
Definition Omega_Lambda_flat (Omega_m : R) : R := 1 - Omega_m.

(** ** Flat LambdaCDM Cosmology Parameters *)

Record FlatLCDM := mkFlatLCDM {
  H0 : R;       (** Hubble constant in km/s/Mpc *)
  Omega_m : R;  (** Matter density parameter (CDM + baryons) *)
  Omega_b : R;  (** Baryon density parameter *)
  T_CMB : R;    (** CMB temperature in Kelvin *)
}.

(** Planck 2018 default cosmology *)
Definition Planck18 : FlatLCDM :=
  mkFlatLCDM H0_Planck18 Omega_m_Planck18 Omega_b_Planck18 T_CMB_Planck18.

(** Dark energy density parameter (assuming flat universe) *)
Definition Omega_Lambda (cosmo : FlatLCDM) : R :=
  1 - cosmo.(Omega_m).

(** ** Friedmann Equation *)

(** Dimensionless Hubble parameter: E(z) = H(z) / H0
    For flat LambdaCDM: E(z) = sqrt(Omega_m * (1+z)^3 + Omega_Lambda) *)
Definition E_z (cosmo : FlatLCDM) (z : R) : R :=
  sqrt (cosmo.(Omega_m) * (1 + z)^3 + Omega_Lambda cosmo).

(** Hubble parameter at redshift z: H(z) = H0 * E(z) in km/s/Mpc *)
Definition hubble_parameter (cosmo : FlatLCDM) (z : R) : R :=
  cosmo.(H0) * E_z cosmo z.

(** ** Axiodilaton Extension (2025 Research) *)

(** The axiodilaton model modifies the Friedmann equation to resolve
    Hubble tension. From arXiv:2512.13544:
    - Raises H0 to ~69.2 km/s/Mpc
    - Reduces tension to < 3 sigma
    - Requires dilaton-matter coupling |g| ~ 10^-2 to 10^-1 *)

Record AxiodilatonParams := mkAxiodilaton {
  ad_Omega_m : R;     (** Matter density *)
  ad_Omega_ad : R;    (** Axiodilaton contribution *)
  ad_coupling : R;    (** Dilaton-matter coupling |g| *)
}.

(** Axiodilaton contribution function (placeholder for full model) *)
Definition f_axiodilaton (z : R) (ad : AxiodilatonParams) : R :=
  (* Simplified: axiodilaton acts like early dark energy *)
  (* Full model requires solving Klein-Gordon equation *)
  ad.(ad_Omega_ad) * (1 + z)^2.

(** Modified Hubble parameter with axiodilaton *)
Definition hubble_axiodilaton (H0 : R) (ad : AxiodilatonParams) (z : R) : R :=
  let Omega_Lambda := 1 - ad.(ad_Omega_m) - ad.(ad_Omega_ad) in
  H0 * sqrt (ad.(ad_Omega_m) * (1 + z)^3 +
             f_axiodilaton z ad +
             Omega_Lambda).

(** ** Physical Constraints *)

(** E(z) >= 1 at z = 0 for non-negative Omega *)
Theorem E_at_z0 : forall cosmo : FlatLCDM,
  cosmo.(Omega_m) >= 0 ->
  Omega_Lambda cosmo >= 0 ->
  E_z cosmo 0 = 1.
Proof.
  intros cosmo HOm HOL.
  unfold E_z, Omega_Lambda.
  simpl.
  (* (1+0)^3 = 1, so E(0) = sqrt(Omega_m + Omega_Lambda) = sqrt(1) = 1 *)
  admit.
Admitted.

(** E(z) is monotonically increasing for matter-dominated era *)
Theorem E_increasing_matter_dominated : forall (cosmo : FlatLCDM) (z1 z2 : R),
  cosmo.(Omega_m) > 0 ->
  z2 > z1 ->
  z1 >= 0 ->
  E_z cosmo z2 > E_z cosmo z1.
Proof.
  intros cosmo z1 z2 HOm Hz Hz1.
  (* At high z, E(z) ~ sqrt(Omega_m) * (1+z)^(3/2) which increases *)
  admit.
Admitted.

(** ** Hubble Time and Length *)

(** Hubble time: t_H = 1 / H0 *)
(** In standard units: t_H ~ 14.4 Gyr for H0 = 67.36 km/s/Mpc *)
Definition hubble_time (H0 : R) : R := 1 / H0.

(** Hubble length: c / H0 *)
(** In Mpc: D_H ~ 4450 Mpc for H0 = 67.36 km/s/Mpc *)
(** We use c_km_s = 299792.458 km/s *)
Definition c_km_s : R := 299792.458.

Definition hubble_length (H0 : R) : R := c_km_s / H0.

(** ** Critical Density *)

(** Critical density: rho_crit = 3 H^2 / (8 pi G)
    At z = 0: rho_crit,0 ~ 9.47e-27 kg/m^3 for H0 = 67.36 km/s/Mpc *)

(** Density parameter: Omega_X = rho_X / rho_crit *)

(** ** Age of the Universe *)

(** Age integral: t_0 = (1/H0) * integral_0^infinity dz / ((1+z) * E(z))
    For Planck18: t_0 ~ 13.8 Gyr *)

(** This integral requires numerical evaluation for general cosmologies *)

(** ** Matter-Radiation Equality *)

(** Redshift of matter-radiation equality:
    z_eq ~ 3400 for Planck18 parameters *)
Definition z_equality (Omega_m Omega_r : R) : R :=
  Omega_m / Omega_r - 1.

(** ** Deceleration Parameter *)

(** q(z) = -1 + (1+z) * (dE/dz) / E(z)
    q < 0 indicates accelerating expansion *)

Definition deceleration_q (cosmo : FlatLCDM) (z : R) : R :=
  let E := E_z cosmo z in
  let dEdz := (3/2) * cosmo.(Omega_m) * (1 + z)^2 / (2 * E) in
  -1 + (1 + z) * dEdz / E.

(** Universe transitions from deceleration to acceleration at z_acc *)
(** For Planck18: z_acc ~ 0.67 *)

(** ** Extraction Interface *)

Definition compute_E_z (Omega_m z : R) : R :=
  sqrt (Omega_m * (1 + z)^3 + (1 - Omega_m)).

Definition compute_hubble (H0 Omega_m z : R) : R :=
  H0 * compute_E_z Omega_m z.

Definition compute_hubble_length (H0 : R) : R :=
  c_km_s / H0.

Definition compute_Omega_Lambda (Omega_m : R) : R :=
  1 - Omega_m.
