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

Definition vec2_scal_mul x y x' y' := (x * y' + y * x')%L.
Definition mat2_det y z y' z' := (y * z' - z * y')%L.

Definition quat_mul (q q' : quaternion T) :=
  let '(mk_quat a (mk_v x y z)) := q in
  let '(mk_quat a' (mk_v x' y' z')) := q' in
  mk_quat
    (a * a' - (x * x' + y * y' + z * z'))
    (mk_v
      (vec2_scal_mul a x a' x' + mat2_det y z y' z')
      (vec2_scal_mul a y a' y' + mat2_det z x z' x')
      (vec2_scal_mul a z a' z' + mat2_det x y x' y')).

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
Notation "a + b" := (quat_add a b) : quat_scope.
Notation "a * b" := (quat_mul a b) : quat_scope.

Definition quat_opt_one :=
  match rngl_opt_one T with
  | Some _ => Some 1%quat
  | None => None
  end.

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

Definition quat_opt_eq_dec : option (∀ a b, {a = b} + {a ≠ b}) :=
  match rngl_opt_eq_dec T with
  | Some eq_dec => Some (quat_eq_dec eq_dec)
  | None => None
  end.

Definition quat_opt_leb : option (quaternion T → quaternion T → bool) :=
  (* no order in quaternions, like for complex numbers *)
  None.

Instance quat_ring_like_op : ring_like_op (quaternion T) :=
  {| rngl_zero := 0%quat;
     rngl_add := quat_add;
     rngl_mul := quat_mul;
     rngl_opt_one := quat_opt_one;
     rngl_opt_opp_or_subt := quat_opt_opp_or_subt;
     rngl_opt_inv_or_quot := quat_opt_inv_or_quot;
     rngl_opt_is_zero_divisor := None;
     rngl_opt_eq_dec := quat_opt_eq_dec;
     rngl_opt_leb := quat_opt_leb |}.

Context {rp : ring_like_prop T}.

Theorem quat_add_comm : ∀ a b : quaternion T, (a + b)%L = (b + a)%L.
Proof.
intros.
destruct a as (a, (x, y, z)).
destruct b as (a', (x', y', z')); cbn.
progress unfold quat_add; cbn.
f_equal; [ apply rngl_add_comm | ].
progress unfold vec3_add; cbn.
f_equal; apply rngl_add_comm.
Qed.

Theorem quat_add_assoc :
  ∀ a b c : quaternion T, (a + (b + c))%L = (a + b + c)%L.
Proof.
intros.
destruct a as (a, (x, y, z)).
destruct b as (a', (x', y', z')).
destruct c as (a'', (x'', y'', z'')); cbn.
progress unfold quat_add; cbn.
f_equal; [ apply rngl_add_assoc | ].
progress unfold vec3_add; cbn.
f_equal; apply rngl_add_assoc.
Qed.

Theorem quat_add_0_l : ∀ a : quaternion T, (0 + a)%L = a.
Proof.
intros.
destruct a as (a, (x, y, z)); cbn.
progress unfold quat_add; cbn.
f_equal; [ apply rngl_add_0_l | ].
progress unfold vec3_add; cbn.
f_equal; apply rngl_add_0_l.
Qed.

Context {Hop : rngl_has_opp T = true}.

Definition Hos := rngl_has_opp_has_opp_or_subt Hop.

Ltac group_by_3_factors :=
  remember 42 as v eqn:Hv_; remember 42 as v0 eqn:Hv0;
  do 16 (
    let vn := fresh "v" in
    remember (_ * _ * _)%L as vn eqn:Hv in |-*; clear Hv);
  clear v v0 Hv_ Hv0.

Ltac ring_light_step :=
  match goal with
  | |- context[rngl_sub (rngl_add ?x ?y) ?z] =>
      rewrite (rngl_add_sub_swap Hop x y z)
  | |- context[rngl_sub ?x (rngl_add ?y ?z)] =>
      rewrite (rngl_sub_add_distr Hos x y z)
  | |- context[rngl_sub ?x (rngl_sub ?y ?z)] =>
      rewrite (rngl_sub_sub_distr Hop x y z)
  end.

Theorem quat_mul_assoc :
  ∀ a b c : quaternion T, (a * (b * c) = (a * b) * c)%L.
Proof.
intros.
destruct a as (a, (x, y, z)).
destruct b as (a', (x', y', z')).
destruct c as (a'', (x'', y'', z'')).
cbn - [ quat_mul ].
cbn.
progress unfold vec2_scal_mul.
progress unfold mat2_det.
do 24 rewrite rngl_mul_add_distr_l.
do 24 rewrite rngl_mul_add_distr_r.
do 24 rewrite rngl_mul_assoc.
do 16 rewrite (rngl_mul_sub_distr_l Hop).
do 16 rewrite (rngl_mul_sub_distr_r Hop).
do 8 rewrite rngl_mul_add_distr_l.
do 8 rewrite rngl_mul_add_distr_r.
do 40 rewrite rngl_mul_assoc.
f_equal. {
  group_by_3_factors.
  progress do 44 ring_light_step.
  symmetry.
  progress do 2 rewrite (rngl_add_add_swap _ v16).
  progress do 3 f_equal.
  progress do 3 rewrite (rngl_sub_sub_swap Hop _ v15).
  progress f_equal.
  progress do 8 rewrite (rngl_sub_sub_swap Hop _ v14).
  progress f_equal.
  progress do 1 rewrite (rngl_sub_sub_swap Hop _ v13).
  progress f_equal.
  progress do 4 rewrite (rngl_sub_sub_swap Hop _ v11).
  progress f_equal.
  progress do 6 rewrite (rngl_sub_sub_swap Hop _ v10).
  progress f_equal.
  progress do 2 rewrite (rngl_sub_sub_swap Hop _ v9).
  progress do 2 f_equal.
  progress do 4 rewrite (rngl_sub_sub_swap Hop _ v6).
  progress f_equal.
  progress do 2 rewrite (rngl_sub_sub_swap Hop _ v5).
  easy.
}
f_equal. {
  group_by_3_factors.
  do 12 rewrite (rngl_add_sub_assoc Hop).
  progress do 36 ring_light_step.
  do 6 rewrite rngl_add_assoc.
  progress do 6 rewrite (rngl_add_add_swap _ v16).
  progress f_equal.
  progress do 5 rewrite (rngl_add_add_swap _ v11).
  progress f_equal.
  progress do 2 rewrite (rngl_add_add_swap _ v10).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_add_add_swap _ v5).
  progress do 3 f_equal.
  progress do 5 rewrite (rngl_sub_sub_swap Hop _ v15).
  progress f_equal.
  progress do 4 rewrite (rngl_sub_sub_swap Hop _ v14).
  progress f_equal.
  progress do 1 rewrite (rngl_sub_sub_swap Hop _ v13).
  progress f_equal.
  progress do 3 rewrite (rngl_sub_sub_swap Hop _ v12).
  progress f_equal.
  progress do 2 rewrite (rngl_sub_sub_swap Hop _ v8).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_sub_sub_swap Hop _ v6).
  easy.
} {
  group_by_3_factors.
  do 12 rewrite (rngl_add_sub_assoc Hop).
  progress do 36 ring_light_step.
  do 6 rewrite rngl_add_assoc.
  progress do 6 rewrite (rngl_add_add_swap _ v16).
  progress f_equal.
  progress do 5 rewrite (rngl_add_add_swap _ v11).
  progress f_equal.
  progress do 2 rewrite (rngl_add_add_swap _ v10).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_add_add_swap _ v5).
  progress do 3 f_equal.
  progress do 7 rewrite (rngl_sub_sub_swap Hop _ v15).
  progress f_equal.
  progress do 4 rewrite (rngl_sub_sub_swap Hop _ v14).
  progress f_equal.
  progress do 1 rewrite (rngl_sub_sub_swap Hop _ v13).
  progress f_equal.
  progress do 3 rewrite (rngl_sub_sub_swap Hop _ v12).
  progress do 2 f_equal.
  progress do 2 rewrite (rngl_sub_sub_swap Hop _ v7).
  progress f_equal.
  progress do 1 rewrite (rngl_sub_sub_swap Hop _ v6).
  easy.
} {
  group_by_3_factors.
  do 12 rewrite (rngl_add_sub_assoc Hop).
  progress do 36 ring_light_step.
  do 6 rewrite rngl_add_assoc.
  progress do 6 rewrite (rngl_add_add_swap _ v16).
  progress f_equal.
  progress do 5 rewrite (rngl_add_add_swap _ v11).
  progress f_equal.
  progress do 2 rewrite (rngl_add_add_swap _ v10).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_add_add_swap _ v5).
  progress do 3 f_equal.
  progress do 6 rewrite (rngl_sub_sub_swap Hop _ v15).
  progress f_equal.
  progress do 4 rewrite (rngl_sub_sub_swap Hop _ v14).
  progress f_equal.
  progress do 1 rewrite (rngl_sub_sub_swap Hop _ v13).
  progress f_equal.
  progress do 4 rewrite (rngl_sub_sub_swap Hop _ v12).
  progress f_equal.
  progress do 3 rewrite (rngl_sub_sub_swap Hop _ v8).
  progress f_equal.
  progress do 2 rewrite (rngl_sub_sub_swap Hop _ v7).
  easy.
}
Qed.

Theorem quat_opt_mul_1_l :
  if rngl_has_1 (quaternion T) then ∀ a : quaternion T, (1 * a)%L = a
  else not_applicable.
Proof.
remember (rngl_has_1 (quaternion T)) as onq eqn:Honq.
symmetry in Honq.
destruct onq; [ | easy ].
intros.
progress unfold rngl_has_1 in Honq; cbn in Honq.
progress unfold quat_opt_one in Honq; cbn in Honq.
progress unfold rngl_one; cbn.
progress unfold quat_opt_one.
remember (rngl_has_1 T) as on eqn:Hon.
symmetry in Hon.
generalize Hon; intros H.
progress unfold rngl_has_1 in H.
remember (rngl_opt_one T) as oon eqn:Hoon.
symmetry in Hoon.
destruct oon; [ | easy ].
destruct on; [ | easy ].
clear Honq H.
destruct a as (a, (x, y, z)); cbn.
f_equal. {
  do 2 rewrite <- rngl_mul_add_distr_l.
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_sub_0_r Hos).
  apply (rngl_mul_1_l Hon).
}
progress unfold vec2_scal_mul, mat2_det.
do 3 rewrite (rngl_mul_1_l Hon).
do 4 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_diag Hos).
do 6 rewrite rngl_add_0_r.
easy.
Qed.

Theorem quat_mul_add_distr_l :
  ∀ a b c : quaternion T, (a * (b + c))%L = (a * b + a * c)%L.
Proof.
intros.
destruct a as (a, (x, y, z)).
destruct b as (a', (x', y', z')).
destruct c as (a'', (x'', y'', z'')); cbn.
progress unfold vec2_scal_mul; cbn.
progress unfold mat2_det; cbn.
progress unfold quat_add; cbn.
f_equal. {
  do 4 rewrite rngl_mul_add_distr_l.
  rewrite (rngl_add_sub_assoc Hop).
  do 11 ring_light_step.
  do 2 f_equal.
  progress do 2 rewrite (rngl_sub_sub_swap Hop _ (z * z')).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_sub_sub_swap Hop _ (y * y')).
  easy.
}
progress unfold vec3_add; cbn.
do 12 rewrite rngl_mul_add_distr_l.
f_equal. {
  do 2 ring_light_step.
  do 4 rewrite rngl_add_assoc.
  do 4 rewrite (rngl_add_sub_assoc Hop).
  do 15 ring_light_step.
  f_equal.
  progress do 2 rewrite (rngl_add_add_swap _ (y * z')).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_add_add_swap _ (a * x'')).
  easy.
} {
  do 2 ring_light_step.
  do 4 rewrite rngl_add_assoc.
  do 4 rewrite (rngl_add_sub_assoc Hop).
  do 15 ring_light_step.
  f_equal.
  progress do 2 rewrite (rngl_add_add_swap _ (z * x')).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_add_add_swap _ (a * y'')).
  easy.
} {
  do 2 ring_light_step.
  do 4 rewrite rngl_add_assoc.
  do 4 rewrite (rngl_add_sub_assoc Hop).
  do 15 ring_light_step.
  f_equal.
  progress do 2 rewrite (rngl_add_add_swap _ (x * y')).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_add_add_swap _ (a * z'')).
  easy.
}
Qed.

Theorem quat_opt_mul_1_r :
  if rngl_has_1 (quaternion T) then ∀ a : quaternion T, (a * 1)%L = a
  else not_applicable.
Proof.
remember (rngl_has_1 (quaternion T)) as onq eqn:Honq.
symmetry in Honq.
destruct onq; [ | easy ].
intros.
progress unfold rngl_has_1 in Honq; cbn in Honq.
progress unfold quat_opt_one in Honq; cbn in Honq.
progress unfold rngl_one; cbn.
progress unfold quat_opt_one.
remember (rngl_has_1 T) as on eqn:Hon.
symmetry in Hon.
generalize Hon; intros H.
progress unfold rngl_has_1 in H.
remember (rngl_opt_one T) as oon eqn:Hoon.
symmetry in Hoon.
destruct oon; [ | easy ].
destruct on; [ | easy ].
clear Honq H.
destruct a as (a, (x, y, z)); cbn.
f_equal. {
  do 2 rewrite <- rngl_mul_add_distr_r.
  rewrite (rngl_mul_0_r Hos).
  rewrite (rngl_sub_0_r Hos).
  apply (rngl_mul_1_r Hon).
}
progress unfold vec2_scal_mul, mat2_det.
do 3 rewrite (rngl_mul_1_r Hon).
do 4 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_diag Hos).
do 3 rewrite rngl_add_0_l.
do 3 rewrite rngl_add_0_r.
easy.
Qed.

Theorem quat_opt_mul_add_distr_r :
  ∀ a b c : quaternion T, ((a + b) * c)%L = (a * c + b * c)%L.
Proof.
intros.
destruct a as (a, (x, y, z)).
destruct b as (a', (x', y', z')).
destruct c as (a'', (x'', y'', z'')); cbn.
progress unfold vec2_scal_mul; cbn.
progress unfold mat2_det; cbn.
progress unfold quat_add; cbn.
f_equal. {
  do 4 rewrite rngl_mul_add_distr_r.
  rewrite (rngl_add_sub_assoc Hop).
  do 11 ring_light_step.
  do 2 f_equal.
  progress do 2 rewrite (rngl_sub_sub_swap Hop _ (z * z'')).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_sub_sub_swap Hop _ (y * y'')).
  easy.
}
progress unfold vec3_add; cbn.
do 12 rewrite rngl_mul_add_distr_r.
f_equal. {
  do 2 ring_light_step.
  do 4 rewrite rngl_add_assoc.
  do 4 rewrite (rngl_add_sub_assoc Hop).
  do 15 ring_light_step.
  f_equal.
  progress do 2 rewrite (rngl_add_add_swap _ (y * z'')).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_add_add_swap _ (x * a'')).
  easy.
} {
  do 2 ring_light_step.
  do 4 rewrite rngl_add_assoc.
  do 4 rewrite (rngl_add_sub_assoc Hop).
  do 15 ring_light_step.
  f_equal.
  progress do 2 rewrite (rngl_add_add_swap _ (z * x'')).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_add_add_swap _ (a' * y'')).
  easy.
} {
  do 2 ring_light_step.
  do 4 rewrite rngl_add_assoc.
  do 4 rewrite (rngl_add_sub_assoc Hop).
  do 15 ring_light_step.
  f_equal.
  progress do 2 rewrite (rngl_add_add_swap _ (x * y'')).
  progress do 2 f_equal.
  progress do 1 rewrite (rngl_add_add_swap _ (a' * z'')).
  easy.
}
Qed.

Theorem quat_opt_add_opp_diag_l :
  if rngl_has_opp (quaternion T) then ∀ a : quaternion T, (- a + a)%L = 0%L
  else not_applicable.
Proof.
generalize Hop; intros H.
progress unfold rngl_has_opp in H |-*; cbn in H |-*.
progress unfold rngl_opp; cbn.
progress unfold quat_opt_opp_or_subt.
remember (rngl_opt_opp_or_subt T) as osq eqn:Hosq.
symmetry in Hosq.
destruct osq as [opp| ]; [ | easy ].
destruct opp as [opp| subt]; [ | easy ].
clear H.
intros.
progress unfold quat_opp.
progress unfold quat_add; cbn.
progress unfold vec3_add; cbn.
progress unfold quat_zero.
f_equal; [ apply (rngl_add_opp_diag_l Hop) | ].
do 3 rewrite (rngl_add_opp_diag_l Hop).
easy.
Qed.

From Stdlib Require Import Arith.
Instance quat_ring_like_prop : ring_like_prop (quaternion T) :=
  {| rngl_mul_is_comm := false;
     rngl_is_archimedean := rngl_is_archimedean T;
     rngl_is_alg_closed := false;
     rngl_characteristic := rngl_characteristic T;
     rngl_add_comm := quat_add_comm;
     rngl_add_assoc := quat_add_assoc;
     rngl_add_0_l := quat_add_0_l;
     rngl_mul_assoc := quat_mul_assoc;
     rngl_opt_mul_1_l := quat_opt_mul_1_l;
     rngl_mul_add_distr_l := quat_mul_add_distr_l;
     rngl_opt_mul_comm := NA;
     rngl_opt_mul_1_r := quat_opt_mul_1_r;
     rngl_opt_mul_add_distr_r := quat_opt_mul_add_distr_r;
     rngl_opt_add_opp_diag_l := quat_opt_add_opp_diag_l;
     rngl_opt_add_sub := 32;
     rngl_opt_sub_add_distr := Nat.sub_add_distr;
     rngl_opt_sub_0_l := Nat.sub_0_l;
     rngl_opt_mul_inv_diag_l := NA;
     rngl_opt_mul_inv_diag_r := NA;
     rngl_opt_mul_div := 42;
     rngl_opt_mul_quot_r := NA;
     rngl_opt_integral := 42;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := 42;
     rngl_opt_ord := 42;
     rngl_opt_archimedean := 42 |}.
...

End a.

Notation "a +ℹ b +𝐣 c +𝐤 d" :=
  (mk_quat a (mk_v b c d)) (at level 50, b, c, d at level 0) : quat_scope.
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
