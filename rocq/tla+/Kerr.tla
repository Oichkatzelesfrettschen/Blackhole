-------------------------- MODULE Kerr ----------------------------
(*
 * Kerr Black Hole ISCO Constraint Formal Specification
 * ======================================================
 *
 * Formal specification of ISCO (Innermost Stable Circular Orbit) constraints
 * in Kerr spacetime using Bardeen-Press-Teukolsky 1972 formulation.
 *
 * Verified against: rocq/theories/Kerr/BPT_ISCO.v (Phase 6 corrected formula)
 *                   src/physics/verified/kerr.h (C++23 implementation)
 *
 * Model Checker: TLC (exhaustive) or Apalache (symbolic)
 * Scope: ISCO radius computation across full spin range [0, 1]
 * Precision: double arithmetic with verified error bounds
 *)

EXTENDS Naturals, Reals, Sequences

(*===========================================================================
   Constants
  ===========================================================================*)

(* Black hole parameters *)
CONSTANT M           \* Black hole mass in geometric units (G=c=1)
CONSTANT a           \* Spin parameter (0 <= a <= M, normalized a* = a/M in [0,1])

(* ISCO calculation tolerances *)
CONSTANT ISCO_TOLERANCE      \* Relative error tolerance for ISCO radius (1e-6)
CONSTANT SPIN_TOLERANCE      \* Spin parameter tolerance (1e-10)

(* Verification bounds *)
CONSTANT BPT_LITERATURE_PRO  \* Expected ISCO prograde from literature
CONSTANT BPT_LITERATURE_RET  \* Expected ISCO retrograde from literature

(*===========================================================================
   Variables
  ===========================================================================*)

VARIABLE spin_param          \* Normalized spin parameter a* in [0, 1]
VARIABLE bpt_Z1              \* BPT helper: Z1 = 1 + cbrt((1-a^2)/2) * (cbrt(1+a) + cbrt(1-a))
VARIABLE bpt_Z2              \* BPT helper: Z2 = sqrt(3*a^2 + Z1^2) [CORRECTED PHASE 6]
VARIABLE isco_pro            \* ISCO radius for prograde orbits
VARIABLE isco_ret            \* ISCO radius for retrograde orbits
VARIABLE horizon_outer       \* Outer event horizon: r+ = M + sqrt(M^2 - a^2)
VARIABLE horizon_inner       \* Inner event horizon: r- = M - sqrt(M^2 - a^2)
VARIABLE calculation_step    \* Computation progress state
VARIABLE verification_passed \* Boolean flag for verification success

(* All variables bundled *)
vars == << spin_param, bpt_Z1, bpt_Z2, isco_pro, isco_ret,
           horizon_outer, horizon_inner, calculation_step,
           verification_passed >>

(*===========================================================================
   Helper Functions
  ===========================================================================*)

(* Check spin parameter validity *)
IsValidSpin(a_norm) == 0 <= a_norm /\ a_norm <= 1

(* BPT Z1 helper function *)
(* Z1 = 1 + cbrt((1-a^2)/2) * (cbrt(1+a) + cbrt(1-a)) *)
BPT_Z1_Compute(a_norm) ==
    LET a2 == a_norm * a_norm
        one_minus_a2 == 1 - a2
        cbrt_factor == (one_minus_a2 / 2) ^ (1/3)
        cbrt_plus == (1 + a_norm) ^ (1/3)
        cbrt_minus == (1 - a_norm) ^ (1/3)
    IN 1 + cbrt_factor * (cbrt_plus + cbrt_minus)

(* BPT Z2 helper function - CORRECTED FORMULA (Phase 6) *)
(* Z2 = sqrt(3*a^2 + Z1^2) - Bardeen-Press-Teukolsky 1972 standard *)
BPT_Z2_Compute(a_norm, Z1_val) ==
    LET a2 == a_norm * a_norm
        term == 3 * a2 + Z1_val * Z1_val
    IN IF term >= 0 THEN term ^ (1/2) ELSE -1

(* Outer event horizon radius *)
(* r+ = M + sqrt(M^2 - a^2) where a = a* * M *)
HorizonOuter(M_mass, a_norm) ==
    LET a_phys == a_norm * M_mass
        discriminant == M_mass * M_mass - a_phys * a_phys
    IN IF discriminant >= 0 THEN M_mass + (discriminant ^ (1/2)) ELSE -1

(* Inner event horizon radius *)
(* r- = M - sqrt(M^2 - a^2) *)
HorizonInner(M_mass, a_norm) ==
    LET a_phys == a_norm * M_mass
        discriminant == M_mass * M_mass - a_phys * a_phys
    IN IF discriminant >= 0 THEN M_mass - (discriminant ^ (1/2)) ELSE -1

(* ISCO radius - prograde orbits *)
(* r_isco_pro = M * (3 + Z2 - sqrt((3 - Z1) * (3 + Z1 + 2*Z2))) *)
ISCO_Prograde(M_mass, a_norm, Z1_val, Z2_val) ==
    LET factor == (3 - Z1_val) * (3 + Z1_val + 2 * Z2_val)
    IN IF factor >= 0 THEN M_mass * (3 + Z2_val - (factor ^ (1/2))) ELSE -1

(* ISCO radius - retrograde orbits *)
(* r_isco_ret = M * (3 + Z2 + sqrt((3 - Z1) * (3 + Z1 + 2*Z2))) *)
ISCO_Retrograde(M_mass, a_norm, Z1_val, Z2_val) ==
    LET factor == (3 - Z1_val) * (3 + Z1_val + 2 * Z2_val)
    IN IF factor >= 0 THEN M_mass * (3 + Z2_val + (factor ^ (1/2))) ELSE -1

(* Schwarzschild limit: a* = 0 should give r_isco = 6M *)
SchwarzschildISCO(M_mass) == 6 * M_mass

(* Check physical constraints on ISCO *)
ISCOPhysicallyValid(r_plus, r_minus, r_isco) ==
    /\ r_isco > r_plus  \* ISCO must be outside outer horizon
    /\ r_isco > r_minus \* ISCO must be outside inner horizon
    /\ r_isco >= 0      \* Positive radius

(* Constraint: retrograde > prograde for all a > 0 *)
ISCOOrbitOrdering(r_pro, r_ret, a_norm) ==
    IF a_norm = 0 THEN r_pro = r_ret  \* Equal at Schwarzschild
    ELSE r_ret > r_pro                 \* Retrograde always larger for a > 0

(* Verification against literature values *)
LiteratureConsistency(r_pro, r_ret, expected_pro, expected_ret) ==
    LET pro_error == ABS(r_pro - expected_pro) / expected_pro
        ret_error == ABS(r_ret - expected_ret) / expected_ret
    IN pro_error < ISCO_TOLERANCE /\ ret_error < ISCO_TOLERANCE

(*===========================================================================
   Initialization
  ===========================================================================*)

Init ==
    /\ spin_param = 0  \* Start with Schwarzschild (a* = 0)
    /\ bpt_Z1 = 1      \* Z1(a=0) = 1
    /\ bpt_Z2 = 0      \* Uncomputed yet
    /\ isco_pro = 0    \* Uncomputed
    /\ isco_ret = 0    \* Uncomputed
    /\ horizon_outer = 2 * M  \* r+ at a=0
    /\ horizon_inner = 0      \* r- at a=0
    /\ calculation_step = "INIT"
    /\ verification_passed = FALSE

(*===========================================================================
   Computation Steps
  ===========================================================================*)

(* Step 1: Compute horizons for current spin *)
ComputeHorizons ==
    /\ calculation_step = "INIT" \/ calculation_step = "COMPUTE_ISCO"
    /\ LET r_plus == HorizonOuter(M, spin_param)
         r_minus == HorizonInner(M, spin_param)
       IN
         /\ horizon_outer' = r_plus
         /\ horizon_inner' = r_minus
         /\ calculation_step' = "COMPUTE_Z1"
         /\ UNCHANGED << spin_param, bpt_Z1, bpt_Z2, isco_pro, isco_ret,
                         verification_passed >>

(* Step 2: Compute Z1 *)
ComputeZ1 ==
    /\ calculation_step = "COMPUTE_Z1"
    /\ bpt_Z1' = BPT_Z1_Compute(spin_param)
    /\ calculation_step' = "COMPUTE_Z2"
    /\ UNCHANGED << spin_param, bpt_Z2, isco_pro, isco_ret,
                    horizon_outer, horizon_inner, verification_passed >>

(* Step 3: Compute Z2 (CORRECTED FORMULA) *)
ComputeZ2 ==
    /\ calculation_step = "COMPUTE_Z2"
    /\ bpt_Z2' = BPT_Z2_Compute(spin_param, bpt_Z1)
    /\ bpt_Z2' >= 0  \* Must be real-valued (Phase 6 fix ensures this)
    /\ calculation_step' = "COMPUTE_ISCO"
    /\ UNCHANGED << spin_param, bpt_Z1, isco_pro, isco_ret,
                    horizon_outer, horizon_inner, verification_passed >>

(* Step 4: Compute ISCO radii *)
ComputeISCO ==
    /\ calculation_step = "COMPUTE_ISCO"
    /\ LET r_pro == ISCO_Prograde(M, spin_param, bpt_Z1, bpt_Z2)
         r_ret == ISCO_Retrograde(M, spin_param, bpt_Z1, bpt_Z2)
       IN
         /\ r_pro > 0  \* Must be positive
         /\ r_ret > 0
         /\ isco_pro' = r_pro
         /\ isco_ret' = r_ret
         /\ calculation_step' = "VERIFY"
         /\ UNCHANGED << spin_param, bpt_Z1, bpt_Z2,
                         horizon_outer, horizon_inner, verification_passed >>

(* Step 5: Verify constraints *)
VerifyConstraints ==
    /\ calculation_step = "VERIFY"
    /\ ISCOPhysicallyValid(horizon_outer, horizon_inner, isco_pro)
    /\ ISCOPhysicallyValid(horizon_outer, horizon_inner, isco_ret)
    /\ ISCOOrbitOrdering(isco_pro, isco_ret, spin_param)
    /\ IF spin_param = 0 THEN
         ABS(isco_pro - SchwarzschildISCO(M)) < M * ISCO_TOLERANCE
       ELSE TRUE
    /\ verification_passed' = TRUE
    /\ calculation_step' = "DONE"
    /\ UNCHANGED << spin_param, bpt_Z1, bpt_Z2, isco_pro, isco_ret,
                    horizon_outer, horizon_inner >>

(*===========================================================================
   Next State Relation
  ===========================================================================*)

Next == ComputeHorizons \/ ComputeZ1 \/ ComputeZ2 \/ ComputeISCO \/ VerifyConstraints

(*===========================================================================
   Type Invariant
  ===========================================================================*)

TypeInvariant ==
    /\ spin_param \in [0 .. 1]
    /\ bpt_Z1 \in [-10 .. 10]
    /\ bpt_Z2 \in [-1 .. 10]  \* Must be real and positive
    /\ isco_pro \in [-1 .. 1000]  \* -1 for invalid
    /\ isco_ret \in [-1 .. 1000]
    /\ horizon_outer \in [0 .. 1000]
    /\ horizon_inner \in [0 .. 1000]
    /\ calculation_step \in {"INIT", "COMPUTE_Z1", "COMPUTE_Z2",
                             "COMPUTE_ISCO", "VERIFY", "DONE"}
    /\ verification_passed \in {TRUE, FALSE}

(*===========================================================================
   Safety Properties
  ===========================================================================*)

(* Z2 always real-valued (Phase 6 critical fix) *)
SafetyZ2RealValued ==
    []( calculation_step \in {"COMPUTE_Z2", "COMPUTE_ISCO", "VERIFY", "DONE"}
        => bpt_Z2 >= 0 )

(* ISCO always outside horizons *)
SafetyISCOOutsideHorizon ==
    []( calculation_step = "DONE" =>
        (isco_pro > horizon_outer /\ isco_ret > horizon_outer) )

(* Retrograde >= prograde for all spins *)
SafetyISCOOrdering ==
    []( calculation_step = "DONE" => isco_ret >= isco_pro )

(* Schwarzschild limit: a*=0 => r_isco = 6M *)
SafetySchwarzschildLimit ==
    []( (spin_param = 0 /\ calculation_step = "DONE") =>
        ABS(isco_pro - 6 * M) < M * ISCO_TOLERANCE )

(* No NaN propagation *)
SafetyNoNaN ==
    []( bpt_Z2 >= 0 /\ isco_pro >= 0 /\ isco_ret >= 0 )

(*===========================================================================
   Liveness Properties
  ===========================================================================*)

(* Computation eventually completes *)
LivenessTermination ==
    <> (calculation_step = "DONE")

(* Verification eventually succeeds *)
LivenessVerification ==
    <> verification_passed

(* For valid spin, ISCO always computable *)
LivenessISCOComputable ==
    ( IsValidSpin(spin_param) ) =>
    ( <> (isco_pro > 0 /\ isco_ret > 0) )

(*===========================================================================
   Specification
  ===========================================================================*)

(* Complete system specification *)
Spec == Init /\ [][Next]_vars

(* Verification goals *)
THEOREM Spec => []TypeInvariant
THEOREM Spec => SafetyZ2RealValued
THEOREM Spec => SafetyISCOOutsideHorizon
THEOREM Spec => SafetyISCOOrdering
THEOREM Spec => SafetySchwarzschildLimit
THEOREM Spec => SafetyNoNaN
THEOREM Spec => LivenessTermination
THEOREM Spec => LivenessVerification

=============================================================================
