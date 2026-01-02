
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



(** val pred : int -> int **)

let pred n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> n)
    (fun u -> u)
    n

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add n m =
   (fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> m)
     (fun p -> succ (add p m))
     n
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun p -> add m (mul p m))
    n

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (succ 0)

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x4 -> x4

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (succ 0)

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) XH

  (** val size_nat : positive -> int **)

  let rec size_nat = function
  | XI p0 -> succ (size_nat p0)
  | XO p0 -> succ (size_nat p0)
  | XH -> succ 0

  (** val ggcdn :
      int -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a, b)))
      (fun n0 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n0 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n0 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 ->
           let (g, p) = ggcdn n0 a b0 in
           let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ ->
           let (g, p) = ggcdn n0 a0 b in
           let (aa, bb) = p in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val of_nat : int -> positive **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> XH)
        (fun _ -> succ (of_nat x))
        x)
      n
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x4 -> Zneg x4
  | Zneg x4 -> Zpos x4

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val to_nat : z -> int **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Pos.of_succ_nat n0))
      n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q0, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q0, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q0, r) = pos_div_eucl a' (Zpos b') in (q0, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q0, _) = div_eucl a b in q0

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
 end

(** val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos rmul x = function
| XI i0 -> let p = pow_pos rmul x i0 in rmul x (rmul p p)
| XO i0 -> let p = pow_pos rmul x i0 in rmul p p
| XH -> x

(** val z_lt_dec : z -> z -> bool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val z_lt_ge_dec : z -> z -> bool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : z -> z -> bool **)

let z_lt_le_dec =
  z_lt_ge_dec

type q = { qnum : z; qden : positive }

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qlt_le_dec : q -> q -> bool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qarchimedean : q -> positive **)

let qarchimedean q0 =
  let { qnum = qnum0; qden = _ } = q0 in
  (match qnum0 with
   | Zpos p -> Coq_Pos.add p XH
   | _ -> XH)

(** val qpower_positive : q -> positive -> q **)

let qpower_positive =
  pow_pos qmult

(** val qpower : q -> z -> q **)

let qpower q0 = function
| Z0 -> { qnum = (Zpos XH); qden = XH }
| Zpos p -> qpower_positive q0 p
| Zneg p -> qinv (qpower_positive q0 p)

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

(** val pos_log2floor_plus1 : positive -> positive **)

let rec pos_log2floor_plus1 = function
| XI p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XO p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XH -> XH

(** val qbound_lt_ZExp2 : q -> z **)

let qbound_lt_ZExp2 q0 =
  match q0.qnum with
  | Z0 -> Zneg (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))
  | Zpos p ->
    Z.pos_sub (Coq_Pos.succ (pos_log2floor_plus1 p))
      (pos_log2floor_plus1 q0.qden)
  | Zneg _ -> Z0

type cReal = { seq : (z -> q); scale : z }

(** val sig_forall_dec : (int -> bool) -> int option **)

let sig_forall_dec =
  failwith "AXIOM TO BE REALIZED (Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec)"

(** val lowerCutBelow : (q -> bool) -> q **)

let lowerCutBelow f =
  let s =
    sig_forall_dec (fun n ->
      let b = f (qopp { qnum = (Z.of_nat n); qden = XH }) in
      if b then false else true)
  in
  (match s with
   | Some s0 -> qopp { qnum = (Z.of_nat s0); qden = XH }
   | None -> assert false (* absurd case *))

(** val lowerCutAbove : (q -> bool) -> q **)

let lowerCutAbove f =
  let s =
    sig_forall_dec (fun n ->
      let b = f { qnum = (Z.of_nat n); qden = XH } in
      if b then true else false)
  in
  (match s with
   | Some s0 -> { qnum = (Z.of_nat s0); qden = XH }
   | None -> assert false (* absurd case *))

type dReal = (q -> bool)

(** val dRealQlim_rec : (q -> bool) -> int -> int -> q **)

let rec dRealQlim_rec f n p =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> assert false (* absurd case *))
    (fun n0 ->
    let b =
      f
        (qplus (lowerCutBelow f) { qnum = (Z.of_nat n0); qden =
          (Coq_Pos.of_nat (succ n)) })
    in
    if b
    then qplus (lowerCutBelow f) { qnum = (Z.of_nat n0); qden =
           (Coq_Pos.of_nat (succ n)) }
    else dRealQlim_rec f n n0)
    p

(** val dRealAbstr : cReal -> dReal **)

let dRealAbstr x =
  let h = fun q0 n ->
    let s =
      qlt_le_dec
        (qplus q0
          (qpower { qnum = (Zpos (XO XH)); qden = XH } (Z.opp (Z.of_nat n))))
        (x.seq (Z.opp (Z.of_nat n)))
    in
    if s then false else true
  in
  (fun q0 -> match sig_forall_dec (h q0) with
             | Some _ -> true
             | None -> false)

(** val dRealQlim : dReal -> int -> q **)

let dRealQlim x n =
  let s = lowerCutAbove x in
  let s0 = qarchimedean (qminus s (lowerCutBelow x)) in
  dRealQlim_rec x n (mul (succ n) (Coq_Pos.to_nat s0))

(** val dRealQlimExp2 : dReal -> int -> q **)

let dRealQlimExp2 x n =
  dRealQlim x (pred (Nat.pow (succ (succ 0)) n))

(** val cReal_of_DReal_seq : dReal -> z -> q **)

let cReal_of_DReal_seq x n =
  dRealQlimExp2 x (Z.to_nat (Z.opp n))

(** val cReal_of_DReal_scale : dReal -> z **)

let cReal_of_DReal_scale x =
  qbound_lt_ZExp2
    (qplus (qabs (cReal_of_DReal_seq x (Zneg XH))) { qnum = (Zpos (XO XH));
      qden = XH })

(** val dRealRepr : dReal -> cReal **)

let dRealRepr x =
  { seq = (cReal_of_DReal_seq x); scale = (cReal_of_DReal_scale x) }

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

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst =
    dRealAbstr

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr =
    dRealRepr

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.0

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.0

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = ( +. )

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = ( *. )

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = Float.neg

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

(** val rminus :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rminus = ( -. )

(** val iPR_2 : positive -> RbaseSymbolsImpl.coq_R **)

let rec iPR_2 = function
| XI p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1
      RbaseSymbolsImpl.coq_R1)
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0))
| XO p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1
      RbaseSymbolsImpl.coq_R1)
    (iPR_2 p0)
| XH ->
  RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1

(** val iPR : positive -> RbaseSymbolsImpl.coq_R **)

let iPR = function
| XI p0 -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0)
| XO p0 -> iPR_2 p0
| XH -> RbaseSymbolsImpl.coq_R1

(** val iZR : z -> RbaseSymbolsImpl.coq_R **)

let iZR = function
| Z0 -> RbaseSymbolsImpl.coq_R0
| Zpos n -> iPR n
| Zneg n -> RbaseSymbolsImpl.coq_Ropp (iPR n)

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv = (fun x -> 1.0 /. x)

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val rdiv :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rdiv = ( /. )

(** val pow0 : RbaseSymbolsImpl.coq_R -> int -> RbaseSymbolsImpl.coq_R **)

let rec pow0 = Float.pow

(** val rlt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rlt_dec = (fun x y -> x < y)

(** val rabs : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rabs = Float.abs

(** val sqrt : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let sqrt = Float.sqrt

(** val v_t : four_vector -> RbaseSymbolsImpl.coq_R **)

let v_t = function
| { v_t = _; v_r = _; v_theta = _; v_phi = _ } (v_t0, _, _, _) -> v_t0

(** val v_r : four_vector -> RbaseSymbolsImpl.coq_R **)

let v_r = function
| { v_t = _; v_r = _; v_theta = _; v_phi = _ } (_, v_r0, _, _) -> v_r0

(** val v_theta : four_vector -> RbaseSymbolsImpl.coq_R **)

let v_theta = function
| { v_t = _; v_r = _; v_theta = _; v_phi = _ } (_, _, v_theta0, _) -> v_theta0

(** val v_phi : four_vector -> RbaseSymbolsImpl.coq_R **)

let v_phi = function
| { v_t = _; v_r = _; v_theta = _; v_phi = _ } (_, _, _, v_phi0) -> v_phi0

(** val g_tt : metric_components -> RbaseSymbolsImpl.coq_R **)

let g_tt = function
| { g_tt = _; g_rr = _; g_thth = _; g_phph = _; g_tph = _ } (g_tt0, _, _, _, _) ->
  g_tt0

(** val g_rr : metric_components -> RbaseSymbolsImpl.coq_R **)

let g_rr = function
| { g_tt = _; g_rr = _; g_thth = _; g_phph = _; g_tph = _ } (_, g_rr0, _, _, _) ->
  g_rr0

(** val g_thth : metric_components -> RbaseSymbolsImpl.coq_R **)

let g_thth = function
| { g_tt = _; g_rr = _; g_thth = _; g_phph = _; g_tph = _ } (_, _, g_thth0,
                                                             _, _) ->
  g_thth0

(** val g_phph : metric_components -> RbaseSymbolsImpl.coq_R **)

let g_phph = function
| { g_tt = _; g_rr = _; g_thth = _; g_phph = _; g_tph = _ } (_, _, _,
                                                             g_phph0, _) ->
  g_phph0

(** val g_tph : metric_components -> RbaseSymbolsImpl.coq_R **)

let g_tph = function
| { g_tt = _; g_rr = _; g_thth = _; g_phph = _; g_tph = _ } (_, _, _, _,
                                                             g_tph0) ->
  g_tph0

(** val four_norm :
    metric_components -> four_vector -> RbaseSymbolsImpl.coq_R **)

let four_norm g v =
  RbaseSymbolsImpl.coq_Rplus
    (RbaseSymbolsImpl.coq_Rplus
      (RbaseSymbolsImpl.coq_Rplus
        (RbaseSymbolsImpl.coq_Rplus
          (RbaseSymbolsImpl.coq_Rmult
            (RbaseSymbolsImpl.coq_Rmult (g_tt g) (v_t v)) (v_t v))
          (RbaseSymbolsImpl.coq_Rmult
            (RbaseSymbolsImpl.coq_Rmult (g_rr g) (v_r v)) (v_r v)))
        (RbaseSymbolsImpl.coq_Rmult
          (RbaseSymbolsImpl.coq_Rmult (g_thth g) (v_theta v)) (v_theta v)))
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (g_phph g) (v_phi v)) (v_phi v)))
    (RbaseSymbolsImpl.coq_Rmult
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH))) (g_tph g)) (v_t v))
      (v_phi v))

(** val x0 : state_vector -> RbaseSymbolsImpl.coq_R **)

let x0 = function
| { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
    x4, _, _, _, _, _, _, _) ->
  x4

(** val x1 : state_vector -> RbaseSymbolsImpl.coq_R **)

let x1 = function
| { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
    _, x4, _, _, _, _, _, _) ->
  x4

(** val x2 : state_vector -> RbaseSymbolsImpl.coq_R **)

let x2 = function
| { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
    _, _, x4, _, _, _, _, _) ->
  x4

(** val x3 : state_vector -> RbaseSymbolsImpl.coq_R **)

let x3 = function
| { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
    _, _, _, x4, _, _, _, _) ->
  x4

(** val v0 : state_vector -> RbaseSymbolsImpl.coq_R **)

let v0 = function
| { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
    _, _, _, _, v4, _, _, _) ->
  v4

(** val v1 : state_vector -> RbaseSymbolsImpl.coq_R **)

let v1 = function
| { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
    _, _, _, _, _, v4, _, _) ->
  v4

(** val v2 : state_vector -> RbaseSymbolsImpl.coq_R **)

let v2 = function
| { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
    _, _, _, _, _, _, v4, _) ->
  v4

(** val v3 : state_vector -> RbaseSymbolsImpl.coq_R **)

let v3 = function
| { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
    _, _, _, _, _, _, _, v4) ->
  v4

(** val sv_add : state_vector -> state_vector -> state_vector **)

let sv_add a b =
  { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ }
    ((RbaseSymbolsImpl.coq_Rplus (x0 a) (x0 b)),
    (RbaseSymbolsImpl.coq_Rplus (x1 a) (x1 b)),
    (RbaseSymbolsImpl.coq_Rplus (x2 a) (x2 b)),
    (RbaseSymbolsImpl.coq_Rplus (x3 a) (x3 b)),
    (RbaseSymbolsImpl.coq_Rplus (v0 a) (v0 b)),
    (RbaseSymbolsImpl.coq_Rplus (v1 a) (v1 b)),
    (RbaseSymbolsImpl.coq_Rplus (v2 a) (v2 b)),
    (RbaseSymbolsImpl.coq_Rplus (v3 a) (v3 b)))

(** val sv_scale : RbaseSymbolsImpl.coq_R -> state_vector -> state_vector **)

let sv_scale c a =
  { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ }
    ((RbaseSymbolsImpl.coq_Rmult c (x0 a)),
    (RbaseSymbolsImpl.coq_Rmult c (x1 a)),
    (RbaseSymbolsImpl.coq_Rmult c (x2 a)),
    (RbaseSymbolsImpl.coq_Rmult c (x3 a)),
    (RbaseSymbolsImpl.coq_Rmult c (v0 a)),
    (RbaseSymbolsImpl.coq_Rmult c (v1 a)),
    (RbaseSymbolsImpl.coq_Rmult c (v2 a)),
    (RbaseSymbolsImpl.coq_Rmult c (v3 a)))

(** val rk4_step :
    (state_vector -> state_vector) -> RbaseSymbolsImpl.coq_R -> state_vector
    -> state_vector **)

let rk4_step f h y =
  let k1 = f y in
  let k2 = f (sv_add y (sv_scale (rdiv h (iZR (Zpos (XO XH)))) k1)) in
  let k3 = f (sv_add y (sv_scale (rdiv h (iZR (Zpos (XO XH)))) k2)) in
  let k4 = f (sv_add y (sv_scale h k3)) in
  sv_add y
    (sv_scale (rdiv h (iZR (Zpos (XO (XI XH)))))
      (sv_add k1
        (sv_add (sv_scale (iZR (Zpos (XO XH))) k2)
          (sv_add (sv_scale (iZR (Zpos (XO XH))) k3) k4))))

type christoffelAccel = { accel_t : (state_vector -> RbaseSymbolsImpl.coq_R);
                          accel_r : (state_vector -> RbaseSymbolsImpl.coq_R);
                          accel_theta : (state_vector ->
                                        RbaseSymbolsImpl.coq_R);
                          accel_phi : (state_vector -> RbaseSymbolsImpl.coq_R) }

(** val geodesic_rhs : christoffelAccel -> state_vector -> state_vector **)

let geodesic_rhs christoffel s =
  { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
    (v0 s), (v1 s), (v2 s), (v3 s), (christoffel.accel_t s),
    (christoffel.accel_r s), (christoffel.accel_theta s),
    (christoffel.accel_phi s))

(** val null_constraint_function :
    metric_components -> state_vector -> RbaseSymbolsImpl.coq_R **)

let null_constraint_function g s =
  let v = { v_t = _; v_r = _; v_theta = _; v_phi = _ } ((v0 s), (v1 s),
    (v2 s), (v3 s))
  in
  four_norm g v

(** val constraint_after_step :
    metric_components -> christoffelAccel -> RbaseSymbolsImpl.coq_R ->
    state_vector -> RbaseSymbolsImpl.coq_R **)

let constraint_after_step g christoffel h s =
  let s' = rk4_step (geodesic_rhs christoffel) h s in
  null_constraint_function g s'

(** val constraint_drift_step :
    metric_components -> christoffelAccel -> RbaseSymbolsImpl.coq_R ->
    state_vector -> RbaseSymbolsImpl.coq_R **)

let constraint_drift_step g christoffel h s =
  rminus (constraint_after_step g christoffel h s)
    (null_constraint_function g s)

(** val renormalize_null :
    metric_components -> state_vector -> state_vector **)

let renormalize_null g s =
  let new_v0 =
    sqrt
      (rdiv
        (RbaseSymbolsImpl.coq_Rplus
          (RbaseSymbolsImpl.coq_Rplus
            (RbaseSymbolsImpl.coq_Rmult (g_rr g)
              (pow0 (v1 s) (succ (succ 0))))
            (RbaseSymbolsImpl.coq_Rmult (g_thth g)
              (pow0 (v2 s) (succ (succ 0)))))
          (RbaseSymbolsImpl.coq_Rmult (g_phph g)
            (pow0 (v3 s) (succ (succ 0)))))
        (RbaseSymbolsImpl.coq_Ropp (g_tt g)))
  in
  { x0 = _; x1 = _; x2 = _; x3 = _; v0 = _; v1 = _; v2 = _; v3 = _ } (
  (x0 s), (x1 s), (x2 s), (x3 s), new_v0, (v1 s), (v2 s), (v3 s))

(** val needs_renormalization :
    metric_components -> state_vector -> RbaseSymbolsImpl.coq_R -> bool **)

let needs_renormalization g s tol =
  if rlt_dec tol (rabs (null_constraint_function g s)) then true else false

(** val check_null_constraint :
    metric_components -> state_vector -> RbaseSymbolsImpl.coq_R **)

let check_null_constraint =
  null_constraint_function

(** val correct_null_constraint :
    metric_components -> state_vector -> state_vector **)

let correct_null_constraint =
  renormalize_null

(** val should_correct :
    metric_components -> state_vector -> RbaseSymbolsImpl.coq_R -> bool **)

let should_correct =
  needs_renormalization
