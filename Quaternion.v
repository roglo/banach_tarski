From Stdlib Require Import Utf8.

Require Import RingLike.Core.

Declare Scope vec_scope.
Declare Scope quat_scope.
Delimit Scope vec_scope with vec.
Delimit Scope quat_scope with quat.

Class vector3 T := mk_v { v_x : T; v_y : T; v_z : T }.
Class quaternion T := mk_q { q_re : T; q_im : vector3 T }.

Bind Scope vec_scope with vector3.
Bind Scope quat_scope with quaternion.

Arguments mk_v {T} (v_x v_y v_z)%_L.
Arguments mk_q {T} q_re%_L q_im%_vec.
Arguments v_x {T} v%_vec : rename.
Arguments v_y {T} v%_vec : rename.
Arguments v_z {T} v%_vec : rename.
Arguments q_re {T} q%_quat : rename.
Arguments q_im {T} q%_quat : rename.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

Definition vec3_add a b :=
  mk_v
    (v_x a + v_x b)
    (v_y a + v_y b)
    (v_z a + v_z b).

Definition quat_add a b :=
  mk_q
    (q_re a + q_re b)
    (vec3_add (q_im a) (q_im b)).

Definition quat_mul (u v : quaternion T) :=
  let '(mk_q a (mk_v b c d)) := u in
  let '(mk_q a' (mk_v b' c' d')) := v in
  mk_q
    (a * a' - b * b' - c * c' - d * d')
    (mk_v
      (a * b' + b * a' + c * d' - d * c')
      (a * c' - b * d' + c * a' + d * b')
      (a * d' + b * c' - c * b' + d * a')).

End a.

(*
Definition of_number (n : Number.int) : option Q :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos n =>
          Some (Q.of_num_den (Z.of_nat (Nat.of_uint n), 1%pos))
      | Decimal.Neg n =>
          Some (Q.of_num_den (- Z.of_nat (Nat.of_uint n), 1%pos))
      end
  | Number.IntHexadecimal n => None
  end.

Definition to_number (a : Q) : option Number.int :=
  match q_den a with
  | 1%pos => Some (Z.to_number (q_num a))
  | _ => None
  end.
*)

From Stdlib Require Import ZArith.
Require Import RingLike.Z_algebra.
Open Scope Z_scope.

Record quaternion_Z := mk_q_Z { q_re_Z : Z;  q_im_Z : vector3 Z }.

Definition z_quat_of_number (n : Number.int) : option quaternion_Z :=
  match n with
  | Number.IntDecimal n =>
      match n with
      | Decimal.Pos n =>
          Some (mk_q_Z (Z.of_nat (Nat.of_uint n)) (mk_v 0 0 0))
      | Decimal.Neg n =>
          Some (mk_q_Z (- Z.of_nat (Nat.of_uint n)) (mk_v 0 0 0))
      end
  | Number.IntHexadecimal n => None
  end.

Definition z_quat_to_number (a : quaternion_Z) : option Number.int :=
  match q_im_Z a with
  | mk_v 0 0 0 =>
      Some
        (Number.IntDecimal
           (match q_re_Z a with
            | 0%Z => Decimal.Pos (Nat.to_uint 0)
            | Zpos a => Decimal.Pos (Pos.to_uint a)
            | Zneg a => Decimal.Neg (Pos.to_uint a)
            end))
  | _ => None
  end.

Number Notation quaternion_Z z_quat_of_number z_quat_to_number : quat_scope.

Notation "a +ℹ b +𝐣 c +𝐤 d" :=
  (mk_q a (mk_v b c d)) (at level 50, b, c, d at level 0) : quat_scope.
Notation "a * b" := (quat_mul a b) : quat_scope.

Compute (
  let i := mk_q_Z 0 (mk_v 1 0 0) in
  let j := mk_q_Z 0 (mk_v 0 1 0) in
  let k := mk_q_Z 0 (mk_v 0 0 1) in
  (i * i)%quat).

