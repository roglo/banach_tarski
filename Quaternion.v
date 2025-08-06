(* c'est bien, les quaternions, mais avant, il faut
   que j'utilise ring-like sur les matrices *)

From Stdlib Require Import Utf8.

Require Import RingLike.Core.

Declare Scope vec_scope.
Declare Scope quat_scope.
Delimit Scope vec_scope with vec.
Delimit Scope quat_scope with quat.

Class vector3 T := mk_v { v_x : T; v_y : T; v_z : T }.
Class quaternion T := mk_quat { q_re : T; q_im : vector3 T }.

Bind Scope vec_scope with vector3.
Bind Scope quat_scope with quaternion.

Arguments mk_v {T} (v_x v_y v_z)%_L.
Arguments mk_quat {T} q_re%_L q_im%_vec.
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

Definition vec3_opp a := mk_v (- v_x a) (- v_y a) (- v_z a).
Definition vec3_sub a b :=
  mk_v
    (v_x a - v_x b)
    (v_y a - v_y b)
    (v_z a - v_z b).

Theorem vec3_eq_dec :
  ∀ (eq_dec : ∀ a b : T, {a = b} + {a ≠ b}) (v v' : vector3 T),
  {v = v'} + {v ≠ v'}.
Proof.
intros.
destruct v as (x, y, z).
destruct v' as (x', y', z').
destruct (eq_dec x x') as [Hx| Hx]. {
  destruct (eq_dec y y') as [Hy| Hy]. {
    destruct (eq_dec z z') as [Hz| Hz]. {
      now subst; left.
    }
    right; subst.
    now intros H; injection H; clear H; intros H.
  }
  right; subst.
  now intros H; injection H; clear H; intros H.
}
right; subst.
now intros H; injection H; clear H; intros H.
Qed.

Notation "- a" := (vec3_opp a) : vec_scope.
Notation "a - b" := (vec3_sub a b) : vec_scope.

Definition quat_zero := (mk_quat 0 (mk_v 0 0 0))%L.
Definition quat_one := (mk_quat 1 (mk_v 0 0 0))%L.

Definition quat_add a b :=
  mk_quat
    (q_re a + q_re b)
    (vec3_add (q_im a) (q_im b)).

Definition quat_mul (q q' : quaternion T) :=
  let '(mk_quat a (mk_v b c d)) := q in
  let '(mk_quat a' (mk_v b' c' d')) := q' in
  mk_quat
    (a * a' - b * b' - c * c' - d * d')
    (mk_v
      (a * b' + b * a' + c * d' - d * c')
      (a * c' - b * d' + c * a' + d * b')
      (a * d' + b * c' - c * b' + d * a')).

Definition quat_opp a := mk_quat (- q_re a) (- q_im a).
Definition quat_subt a b := mk_quat (q_re a - q_re b) (q_im a - q_im b).

Definition quat_conj a := mk_quat (q_re a) (- q_im a).
Definition quat_norm_squ q :=
  let '(mk_quat a (mk_v b c d)) := q in
  (a² + b² + c² + d²)%L.

Definition quat_ext_mul h q :=
  let '(mk_quat a (mk_v b c d)) := q in
  mk_quat (h * a) (mk_v (h * b) (h * c) (h * d)).
Definition quat_ext_div q h :=
  let '(mk_quat a (mk_v b c d)) := q in
  mk_quat (a / h) (mk_v (b / h) (c / h) (d / h)).

Definition quat_inv a := quat_ext_div (quat_conj a) (quat_norm_squ a).

Notation "a +ℹ b +𝐣 c +𝐤 d" :=
  (mk_quat a (mk_v b c d)) (at level 50, b, c, d at level 0) : quat_scope.

Notation "0" := (quat_zero) : quat_scope.
Notation "1" := (quat_one) : quat_scope.
Notation "a * b" := (quat_mul a b) : quat_scope.

Definition quat_opt_opp_or_subt :=
  match rngl_opt_opp_or_subt T with
  | Some (inl _) => Some (inl quat_opp)
  | Some (inr _) => Some (inr quat_subt)
  | None => None
  end.

Definition quat_opt_inv_or_quot :
  option
    ((quaternion T → quaternion T) +
     (quaternion T → quaternion T → quaternion T)) :=
  match rngl_opt_inv_or_quot T with
  | Some (inl _) => Some (inl quat_inv)
  | Some (inr _) => None
  | None => None
  end.

Theorem quat_eq_dec :
  ∀ (eq_dec : ∀ a b : T, {a = b} + {a ≠ b}) (q q' : quaternion T),
  {q = q'} + {q ≠ q'}.
Proof.
intros.
destruct q as (re, im).
destruct q' as (re', im').
destruct (eq_dec re re') as [Hre| Hre]. {
  destruct (vec3_eq_dec eq_dec im im') as [Him| Him]. {
    now subst; left.
  }
  now right; intros H; injection H; clear H; intros H1 H2.
}
now right; intros H; injection H; clear H; intros H1 H2.
Qed.

Definition quat_opt_eq_dec :
  option (∀ a b : quaternion T, {a = b} + {a ≠ b}) :=
  match rngl_opt_eq_dec T with
  | Some eq_dec => Some (quat_eq_dec eq_dec)
  | None => None
  end.

...

Instance quat_ring_like_op : ring_like_op (quaternion T) :=
  {| rngl_zero := 0%quat;
     rngl_add := quat_add;
     rngl_mul := quat_mul;
     rngl_opt_one := Some 1%quat;
     rngl_opt_opp_or_subt := quat_opt_opp_or_subt;
     rngl_opt_inv_or_quot := quat_opt_inv_or_quot;
     rngl_opt_is_zero_divisor := None;
     rngl_opt_eq_dec := quat_opt_eq_dec;
     rngl_opt_leb := Some Nat.leb |}.

End a.

Notation "a +ℹ b +𝐣 c +𝐤 d" :=
  (mk_q a (mk_v b c d)) (at level 50, b, c, d at level 0) : quat_scope.
Notation "a * b" := (quat_mul a b) : quat_scope.

(*
From Stdlib Require Import ZArith.
Require Import RingLike.Z_algebra.
Open Scope Z_scope.

Compute (
  let i := mk_q 0 (mk_v 1 0 0) in
  let j := mk_q 0 (mk_v 0 1 0) in
  let k := mk_q 0 (mk_v 0 0 1) in
  (j * k)%quat).
*)
