
type __ = Obj.t

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val pred : int -> int

val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val pow : int -> int -> int
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_succ_nat : int -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val pow : positive -> positive -> positive

  val size_nat : positive -> int

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val of_nat : int -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z

  val to_nat : z -> int

  val of_nat : int -> z

  val to_pos : z -> positive

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val div : z -> z -> z

  val sgn : z -> z

  val abs : z -> z

  val ggcd : z -> z -> z * (z * z)
 end

val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val z_lt_dec : z -> z -> bool

val z_lt_ge_dec : z -> z -> bool

val z_lt_le_dec : z -> z -> bool

type q = { qnum : z; qden : positive }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qlt_le_dec : q -> q -> bool

val qarchimedean : q -> positive

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

val qabs : q -> q

val pos_log2floor_plus1 : positive -> positive

val qbound_lt_ZExp2 : q -> z

type cReal = { seq : (z -> q); scale : z }

val sig_forall_dec : (int -> bool) -> int option

val lowerCutBelow : (q -> bool) -> q

val lowerCutAbove : (q -> bool) -> q

type dReal = (q -> bool)

val dRealQlim_rec : (q -> bool) -> int -> int -> q

val dRealAbstr : cReal -> dReal

val dRealQlim : dReal -> int -> q

val dRealQlimExp2 : dReal -> int -> q

val cReal_of_DReal_seq : dReal -> z -> q

val cReal_of_DReal_scale : dReal -> z

val dRealRepr : dReal -> cReal

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val rminus :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val rdiv :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val pow0 : RbaseSymbolsImpl.coq_R -> int -> RbaseSymbolsImpl.coq_R

val rlt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rabs : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val sqrt : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val v_t : four_vector -> RbaseSymbolsImpl.coq_R

val v_r : four_vector -> RbaseSymbolsImpl.coq_R

val v_theta : four_vector -> RbaseSymbolsImpl.coq_R

val v_phi : four_vector -> RbaseSymbolsImpl.coq_R

val g_tt : metric_components -> RbaseSymbolsImpl.coq_R

val g_rr : metric_components -> RbaseSymbolsImpl.coq_R

val g_thth : metric_components -> RbaseSymbolsImpl.coq_R

val g_phph : metric_components -> RbaseSymbolsImpl.coq_R

val g_tph : metric_components -> RbaseSymbolsImpl.coq_R

val four_norm : metric_components -> four_vector -> RbaseSymbolsImpl.coq_R

val x0 : state_vector -> RbaseSymbolsImpl.coq_R

val x1 : state_vector -> RbaseSymbolsImpl.coq_R

val x2 : state_vector -> RbaseSymbolsImpl.coq_R

val x3 : state_vector -> RbaseSymbolsImpl.coq_R

val v0 : state_vector -> RbaseSymbolsImpl.coq_R

val v1 : state_vector -> RbaseSymbolsImpl.coq_R

val v2 : state_vector -> RbaseSymbolsImpl.coq_R

val v3 : state_vector -> RbaseSymbolsImpl.coq_R

val sv_add : state_vector -> state_vector -> state_vector

val sv_scale : RbaseSymbolsImpl.coq_R -> state_vector -> state_vector

val rk4_step :
  (state_vector -> state_vector) -> RbaseSymbolsImpl.coq_R -> state_vector ->
  state_vector

type christoffelAccel = { accel_t : (state_vector -> RbaseSymbolsImpl.coq_R);
                          accel_r : (state_vector -> RbaseSymbolsImpl.coq_R);
                          accel_theta : (state_vector ->
                                        RbaseSymbolsImpl.coq_R);
                          accel_phi : (state_vector -> RbaseSymbolsImpl.coq_R) }

val geodesic_rhs : christoffelAccel -> state_vector -> state_vector

val null_constraint_function :
  metric_components -> state_vector -> RbaseSymbolsImpl.coq_R

val constraint_after_step :
  metric_components -> christoffelAccel -> RbaseSymbolsImpl.coq_R ->
  state_vector -> RbaseSymbolsImpl.coq_R

val constraint_drift_step :
  metric_components -> christoffelAccel -> RbaseSymbolsImpl.coq_R ->
  state_vector -> RbaseSymbolsImpl.coq_R

val renormalize_null : metric_components -> state_vector -> state_vector

val needs_renormalization :
  metric_components -> state_vector -> RbaseSymbolsImpl.coq_R -> bool

val check_null_constraint :
  metric_components -> state_vector -> RbaseSymbolsImpl.coq_R

val correct_null_constraint :
  metric_components -> state_vector -> state_vector

val should_correct :
  metric_components -> state_vector -> RbaseSymbolsImpl.coq_R -> bool
