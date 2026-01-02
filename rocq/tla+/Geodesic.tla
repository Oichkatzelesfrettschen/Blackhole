---------------------------- MODULE Geodesic ----------------------------
(*
 * Geodesic Integration Formal Specification
 * ==========================================
 *
 * Formal specification of null geodesic ray tracing in Schwarzschild spacetime
 * using RK4 integration with constraint preservation.
 *
 * Verified against: rocq/theories/Geodesics/RK4.v, RK4 integration correctness
 *                   rocq/theories/Geodesics/NullConstraint.v, constraint drift bounds
 *
 * Model Checker: TLC (exhaustive) or Apalache (symbolic)
 * Scope: Single ray integration from r=100 to capture/escape
 * Precision: float32 arithmetic with bounded errors
 *)

EXTENDS Naturals, Reals, Sequences

(*===========================================================================
   Constants
  ===========================================================================*)

(* Black hole parameters *)
CONSTANT M           \* Black hole mass in geometric units (G=c=1)
CONSTANT r_s         \* Schwarzschild radius = 2*M

(* Integration parameters *)
CONSTANT h           \* Integration step size (adaptive in real implementation)
CONSTANT MAX_STEPS   \* Maximum RK4 steps before timeout
CONSTANT TOLERANCE   \* Null constraint tolerance (1e-10)

(* Physical limits *)
CONSTANT r_min       \* Minimum radius (just outside horizon for safety)
CONSTANT r_max       \* Maximum radius (observer distance)

(*===========================================================================
   Variables
  ===========================================================================*)

VARIABLE pos_r      \* Radial coordinate
VARIABLE pos_theta  \* Polar angle (fixed at theta=pi/2 for equatorial orbits)
VARIABLE pos_phi    \* Azimuthal angle
VARIABLE vel_t      \* d(t)/d(lambda), v^t (time component)
VARIABLE vel_r      \* d(r)/d(lambda), v^r (radial component)
VARIABLE vel_theta  \* d(theta)/d(lambda), v^theta (polar component)
VARIABLE vel_phi    \* d(phi)/d(lambda), v^phi (azimuthal component)

VARIABLE step_count     \* Number of RK4 steps taken
VARIABLE constraint_v   \* Null constraint: g_μν v^μ v^ν (should be 0)
VARIABLE constraint_max \* Maximum constraint violation seen
VARIABLE status         \* Propagation status

(* All variables bundled for easier manipulation *)
vars == << pos_r, pos_theta, pos_phi, 
           vel_t, vel_r, vel_theta, vel_phi,
           step_count, constraint_v, constraint_max, status >>

(*===========================================================================
   Helper Functions
  ===========================================================================*)

(* Schwarzschild metric components in geometric units *)
g_tt(r) == -(1 - r_s / r)
g_rr(r) == 1 / (1 - r_s / r)
g_thth(r) == r * r
g_phph(r, theta) == r * r * Sin(theta) * Sin(theta)

(* Christoffel symbols needed for RK4 acceleration *)
Gamma_t_tr(r) == M / (r * (r - r_s))
Gamma_r_tt(r) == (M * (r - r_s)) / (r * r * r)
Gamma_r_rr(r) == -M / (r * (r - r_s))
Gamma_r_thth(r) == -(r - r_s)
Gamma_r_phph(r, theta) == -(r - r_s) * Sin(theta) * Sin(theta)

(* Four-norm (should be 0 for null geodesic) *)
FourNorm(r, v_t, v_r, v_theta, v_phi) ==
    g_tt(r) * v_t * v_t +
    g_rr(r) * v_r * v_r +
    g_thth(r) * v_theta * v_theta +
    g_phph(r, 3.14159/2) * v_phi * v_phi

(* RK4 acceleration in r-direction (simplified for equatorial plane) *)
RK4_accel_r(r, v_t, v_r, v_phi) ==
    Gamma_r_tt(r) * v_t * v_t +
    Gamma_r_rr(r) * v_r * v_r +
    Gamma_r_phph(r, 3.14159/2) * v_phi * v_phi

(* Check if ray has captured (crossed horizon) *)
IsCaptured(r) == r <= r_s + 0.01  \* Small safety margin

(* Check if ray has escaped (reached far field) *)
IsEscaped(r) == r >= r_max

(* Check if integration should continue *)
ShouldContinue(r, steps) ==
    /\ r > r_min
    /\ r < r_max
    /\ steps < MAX_STEPS
    /\ ABS(constraint_v) < TOLERANCE * 10  \* Allow 10x tolerance for divergence detection

(*===========================================================================
   Initialization
  ===========================================================================*)

Init ==
    /\ pos_r = 100      \* Start far from black hole
    /\ pos_theta = 3.14159 / 2  \* Equatorial plane
    /\ pos_phi = 0
    /\ vel_t = 1        \* Outgoing ray at c=1
    /\ vel_r = 0.1      \* Radial velocity (outgoing)
    /\ vel_theta = 0    \* No polar motion (equatorial)
    /\ vel_phi = 0      \* No azimuthal motion (radial ray)
    /\ step_count = 0
    /\ constraint_v = FourNorm(100, 1, 0.1, 0, 0)
    /\ constraint_max = ABS(constraint_v)
    /\ status = "PROPAGATING"

(*===========================================================================
   RK4 Integration Step
  ===========================================================================*)

DoStep ==
    /\ status = "PROPAGATING"
    /\ ShouldContinue(pos_r, step_count)
    /\ LET
         \* RK4 stage 1
         k1_r == vel_r
         k1_t == vel_t
         k1_phi == vel_phi
         k1_accel_r == RK4_accel_r(pos_r, vel_t, vel_r, vel_phi)
         
         \* RK4 stage 2 (simplified, using k1 for half-step)
         r_half == pos_r + (h / 2) * k1_r
         k2_accel_r == RK4_accel_r(r_half, vel_t + (h/2)*k1_accel_r, 
                                     vel_r + (h/2)*k1_accel_r, vel_phi)
         
         \* RK4 stage 3
         k3_accel_r == RK4_accel_r(r_half, vel_t + (h/2)*k2_accel_r, 
                                     vel_r + (h/2)*k2_accel_r, vel_phi)
         
         \* RK4 stage 4 (full step)
         r_new == pos_r + h * k1_r
         k4_accel_r == RK4_accel_r(r_new, vel_t + h*k3_accel_r, 
                                     vel_r + h*k3_accel_r, vel_phi)
         
         \* RK4 combination (weighted average)
         vel_r_new == vel_r + (h/6) * (k1_accel_r + 2*k2_accel_r + 2*k3_accel_r + k4_accel_r)
         
         \* Update constraint
         constraint_new == FourNorm(r_new, vel_t, vel_r_new, 0, vel_phi)
         drift == constraint_new - constraint_v
       IN
         /\ pos_r' = r_new
         /\ pos_phi' = pos_phi + h * vel_phi  \* Phi updates trivially
         /\ vel_r' = vel_r_new
         /\ vel_t' = vel_t  \* Time component conserved (stationary spacetime)
         /\ vel_theta' = 0  \* Polar motion stays zero
         /\ vel_phi' = vel_phi  \* Azimuthal velocity conserved (axisymmetry)
         /\ constraint_v' = constraint_new
         /\ constraint_max' = MAX(constraint_max, ABS(constraint_new))
         /\ step_count' = step_count + 1
         /\ status' = status

(*===========================================================================
   Capture/Escape Detection
  ===========================================================================*)

CheckTermination ==
    /\ status = "PROPAGATING"
    /\ ((IsCaptured(pos_r) /\ status' = "CAPTURED") \/ 
        (IsEscaped(pos_r) /\ status' = "ESCAPED") \/
        (step_count >= MAX_STEPS /\ status' = "TIMEOUT") \/
        (ABS(constraint_v) >= TOLERANCE * 10 /\ status' = "CONSTRAINT_VIOLATION"))
    /\ UNCHANGED << pos_r, pos_theta, pos_phi, 
                    vel_t, vel_r, vel_theta, vel_phi,
                    step_count, constraint_v, constraint_max >>

(*===========================================================================
   Next State Relation
  ===========================================================================*)

Next == DoStep \/ CheckTermination

(*===========================================================================
   Type Invariant
  ===========================================================================*)

TypeInvariant ==
    /\ pos_r \in [0 .. 1000]
    /\ pos_theta \in [0 .. 3.14159]
    /\ pos_phi \in [0 .. 6.28318]
    /\ vel_t \in [-10 .. 10]
    /\ vel_r \in [-10 .. 10]
    /\ vel_theta \in [-10 .. 10]
    /\ vel_phi \in [-10 .. 10]
    /\ step_count \in 0 .. MAX_STEPS
    /\ constraint_v \in [-1 .. 1]
    /\ constraint_max \in [0 .. 1]
    /\ status \in {"PROPAGATING", "CAPTURED", "ESCAPED", "TIMEOUT", "CONSTRAINT_VIOLATION"}

(*===========================================================================
   Safety Properties
  ===========================================================================*)

(* Ray never crosses the horizon *)
SafetyHorizonViolation ==
    []( pos_r > r_s )

(* Constraint violation bounded by O(h^4) *)
SafetyConstraintBound ==
    []( ABS(constraint_v) <= TOLERANCE )

(* Ray doesn't escape the problem domain prematurely *)
SafetyBoundsViolation ==
    []( pos_r >= r_min /\ pos_r <= r_max )

(* Integration completes without divergence *)
SafetyNoNaNPropagation ==
    []( /\ constraint_max <= 1.0
        /\ vel_t >= -10 /\ vel_t <= 10
        /\ vel_r >= -10 /\ vel_r <= 10 )

(*===========================================================================
   Liveness Properties
  ===========================================================================*)

(* Ray eventually terminates (either escapes, captures, or times out) *)
LivenessTermination ==
    <> ( status \in {"CAPTURED", "ESCAPED", "TIMEOUT"} )

(* If ray reaches horizon, it gets captured *)
LivenessCaptureAtHorizon ==
    ( <> pos_r <= r_s ) => ( <> status = "CAPTURED" )

(* If ray maintains course, it eventually escapes *)
LivenessEscapeToInfinity ==
    ( <> (pos_r >= r_max - 10) ) => ( <> status = "ESCAPED" )

(*===========================================================================
   Specification
  ===========================================================================*)

(* Complete system specification *)
Spec == Init /\ [][Next]_vars

(* Verification goals *)
THEOREM Spec => []TypeInvariant
THEOREM Spec => SafetyHorizonViolation
THEOREM Spec => SafetyConstraintBound
THEOREM Spec => SafetyBoundsViolation
THEOREM Spec => SafetyNoNaNPropagation
THEOREM Spec => LivenessTermination

=============================================================================
