(* c'est bien, les quaternions, mais avant, il faut
   que j'utilise ring-like sur les matrices *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith.

Require Import RingLike.Core.

Declare Scope vec2_scope.
Declare Scope vec3_scope.
Declare Scope quat_scope.
Delimit Scope vec2_scope with v2.
Delimit Scope vec3_scope with v3.
Delimit Scope quat_scope with quat.

Class vector2 T := mk_v2 { v2_x : T; v2_y : T }.
Class vector3 T := mk_v3 { v3_x : T; v3_y : T; v3_z : T }.
Class quaternion T := mk_quat { q_re : T; q_im : vector3 T }.

Bind Scope vec2_scope with vector2.
Bind Scope vec3_scope with vector3.
Bind Scope quat_scope with quaternion.

Arguments mk_v2 {T} (v2_x v2_y)%_L.
Arguments mk_v3 {T} (v3_x v3_y v3_z)%_L.
Arguments mk_quat {T} q_re%_L q_im%_v3.
Arguments v2_x {T} v%_v2 : rename.
Arguments v2_y {T} v%_v2 : rename.
Arguments v3_x {T} v%_v3 : rename.
Arguments v3_y {T} v%_v3 : rename.
Arguments v3_z {T} v%_v3 : rename.
Arguments q_re {T} q%_quat : rename.
Arguments q_im {T} q%_quat : rename.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

Definition vec3_zero := mk_v3 0 0 0.

Definition vec3_add a b :=
  mk_v3
    (v3_x a + v3_x b)
    (v3_y a + v3_y b)
    (v3_z a + v3_z b).

Definition vec3_opp a := mk_v3 (- v3_x a) (- v3_y a) (- v3_z a).
Definition vec3_sub a b :=
  mk_v3
    (v3_x a - v3_x b)
    (v3_y a - v3_y b)
    (v3_z a - v3_z b).

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

Definition vec3_dot_mul u v :=
  (v3_x u * v3_x v + v3_y u * v3_y v + v3_z u * v3_z v)%L.

Definition vec3_scal_mul a u :=
  mk_v3 (a * v3_x u) (a * v3_y u) (a * v3_z u).

Definition cross_mul u v :=
  mk_v3
    (v3_y u * v3_z v - v3_z u * v3_y v)
    (v3_z u * v3_x v - v3_x u * v3_z v)
    (v3_x u * v3_y v - v3_y u * v3_x v).

Arguments vec3_scal_mul a%_L u%_v3.

Notation "0" := vec3_zero : vec3_scope.
Notation "- a" := (vec3_opp a) : vec3_scope.
Notation "a + b" := (vec3_add a b) : vec3_scope.
Notation "a - b" := (vec3_sub a b) : vec3_scope.
Notation "u ⋆ v" := (vec3_dot_mul u v) (at level 40).
Notation "a · v" := (vec3_scal_mul a v) (at level 40).
Notation "u × v" := (cross_mul u v) (at level 40).

Definition quat_zero := mk_quat 0 0.
Definition quat_one := mk_quat 1 0.

Definition quat_add a b :=
  mk_quat
    (q_re a + q_re b)
    (vec3_add (q_im a) (q_im b)).

Definition quat_re_im_mul a u b v :=
  mk_quat
    (a * b - u ⋆ v)
    (vec3_scal_mul a v + vec3_scal_mul b u + cross_mul u v).

Definition quat_mul (q q' : quaternion T) :=
  quat_re_im_mul (q_re q) (q_im q) (q_re q') (q_im q').

Definition quat_opp a := mk_quat (- q_re a) (- q_im a).
Definition quat_subt a b := mk_quat (q_re a - q_re b) (q_im a - q_im b).
Definition quat_sub a b := quat_add a (quat_opp b).

Definition quat_conj a := mk_quat (q_re a) (- q_im a).
Definition quat_norm_squ q :=
  ((q_re q)² + (v3_x (q_im q))² + (v3_y (q_im q))² + (v3_z (q_im q))²)%L.

Definition quat_ext_mul h q :=
  let '(mk_quat a (mk_v3 b c d)) := q in
  mk_quat (h * a) (mk_v3 (h * b) (h * c) (h * d)).
Definition quat_ext_div q h :=
  let '(mk_quat a (mk_v3 b c d)) := q in
  mk_quat (a / h) (mk_v3 (b / h) (c / h) (d / h)).

Definition quat_inv a := quat_ext_div (quat_conj a) (quat_norm_squ a).

Notation "a +ℹ b +𝐣 c +𝐤 d" :=
  (mk_quat a (mk_v3 b c d)) (at level 50, b, c, d at level 0) : quat_scope.

Notation "0" := (quat_zero) : quat_scope.
Notation "1" := (quat_one) : quat_scope.
Notation "a + b" := (quat_add a b) : quat_scope.
Notation "a - b" := (quat_sub a b) : quat_scope.
Notation "a * b" := (quat_mul a b) : quat_scope.
Notation "- a" := (quat_opp a) : quat_scope.
Notation "a ⁻¹" := (quat_inv a) : quat_scope.

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
  ∀ a b c : quaternion T, (a + (b + c) = a + b + c)%quat.
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

Theorem quat_add_0_l : ∀ a, (0 + a)%quat = a.
Proof.
intros.
destruct a as (a, (x, y, z)); cbn.
progress unfold quat_add; cbn.
f_equal; [ apply rngl_add_0_l | ].
progress unfold vec3_add; cbn.
f_equal; apply rngl_add_0_l.
Qed.

Theorem quat_add_0_r : ∀ a, (a + 0)%quat = a.
Proof.
intros.
rewrite quat_add_comm.
apply quat_add_0_l.
Qed.

Context {Hic : rngl_mul_is_comm T = true}.
Context {Hop : rngl_has_opp T = true}.
Context {Hiv : rngl_has_inv T = true}.
Definition Hos := rngl_has_opp_has_opp_or_subt Hop.
Definition Hiq := rngl_has_inv_has_inv_or_quot Hiv.

Theorem vec3_add_opp_diag_l : ∀ a, vec3_add (- a) a = vec3_zero.
Proof.
intros.
progress unfold vec3_add, vec3_zero; cbn.
now do 3 rewrite (rngl_add_opp_diag_l Hop).
Qed.

Theorem vec3_add_opp_diag_r : ∀ a, vec3_add a (- a) = vec3_zero.
Proof.
intros.
progress unfold vec3_add, vec3_zero; cbn.
now do 3 rewrite (rngl_add_opp_diag_r Hop).
Qed.

Theorem vec3_add_opp_opp : ∀ a b, vec3_add (- a) (- b) = (- vec3_add a b)%v3.
Proof.
intros.
progress unfold vec3_add.
progress unfold vec3_opp; cbn.
do 3 rewrite (rngl_opp_add_distr Hop).
do 3 rewrite (rngl_add_opp_r Hop).
now f_equal; rewrite (rngl_opp_sub_swap Hop).
Qed.

Theorem rngl_mul_vec3_dot_mul_l :
  ∀ a u v, (a * (u ⋆ v))%L = (a · u) ⋆ v.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 2 rewrite rngl_mul_add_distr_l.
do 3 rewrite rngl_mul_assoc.
easy.
Qed.

Theorem vec3_dot_mul_comm : ∀ u v, u ⋆ v = v ⋆ u.
Proof.
intros.
progress unfold vec3_dot_mul.
rewrite (rngl_mul_comm Hic (v3_x _)).
rewrite (rngl_mul_comm Hic (v3_y _)).
rewrite (rngl_mul_comm Hic (v3_z _)).
easy.
Qed.

Theorem vec3_dot_mul_add_distr_l : ∀ u v w, u ⋆ (v + w) = (u ⋆ v + u ⋆ w)%L.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 3 rewrite rngl_mul_add_distr_l.
do 4 rewrite rngl_add_assoc.
progress f_equal.
rewrite rngl_add_add_swap.
progress f_equal.
rewrite (rngl_add_add_swap _ (v3_z _ * _)).
progress f_equal.
apply rngl_add_add_swap.
Qed.

Theorem vec3_dot_mul_add_distr_r : ∀ u v w, (u + v) ⋆ w = (u ⋆ w + v ⋆ w)%L.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 3 rewrite rngl_mul_add_distr_r.
do 4 rewrite rngl_add_assoc.
progress f_equal.
rewrite rngl_add_add_swap.
progress f_equal.
rewrite (rngl_add_add_swap _ (v3_z _ * _)).
progress f_equal.
apply rngl_add_add_swap.
Qed.

Theorem vec3_dot_mul_scal_mul_l : ∀ a u v, (a · u) ⋆ v = (a * (u ⋆ v))%L.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 2 rewrite rngl_mul_add_distr_l.
do 3 rewrite rngl_mul_assoc.
easy.
Qed.

Theorem vec3_dot_mul_scal_mul_r : ∀ a u v, u ⋆ (a · v) = (a * (u ⋆ v))%L.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 2 rewrite rngl_mul_add_distr_l.
do 6 rewrite rngl_mul_assoc.
do 3 rewrite (rngl_mul_comm Hic a).
easy.
Qed.

Theorem vec3_dot_mul_cross_mul_l : ∀ u v w, u ⋆ (v × w) = (u × v) ⋆ w.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 3 rewrite (rngl_mul_sub_distr_l Hop).
do 3 rewrite (rngl_mul_sub_distr_r Hop).
do 4 rewrite (rngl_add_sub_assoc Hop).
do 6 rewrite rngl_mul_assoc.
do 6 rewrite <- (rngl_add_sub_swap Hop).
do 2 rewrite (rngl_sub_sub_swap Hop _ (v3_z u * _ * _)).
progress f_equal.
progress f_equal.
progress f_equal.
rewrite (rngl_add_add_swap _ (v3_z u * _ * _)).
progress f_equal.
apply rngl_add_comm.
Qed.

Theorem vec3_scal_mul_add_distr_l : ∀ a u v, a · (u + v) = (a · u + a · v)%v3.
Proof.
intros.
progress unfold vec3_scal_mul.
progress unfold vec3_add; cbn.
do 3 rewrite rngl_mul_add_distr_l.
easy.
Qed.

Theorem vec3_scal_mul_add_distr_r : ∀ a b u, (a + b) · u = (a · u + b · u)%v3.
Proof.
intros.
progress unfold vec3_scal_mul.
progress unfold vec3_add; cbn.
do 3 rewrite rngl_mul_add_distr_r.
easy.
Qed.

Theorem vec3_scal_mul_sub_distr_r : ∀ a b u, (a - b) · u = (a · u - b · u)%v3.
Proof.
intros.
progress unfold vec3_scal_mul.
progress unfold vec3_sub; cbn.
do 3 rewrite (rngl_mul_sub_distr_r Hop).
easy.
Qed.

Theorem vec3_scal_mul_assoc : ∀ a b u, a · (b · u) = (a * b) · u.
Proof.
intros.
progress unfold vec3_scal_mul; cbn.
do 3 rewrite rngl_mul_assoc.
easy.
Qed.

Theorem vec3_add_sub_assoc : ∀ u v w, (u + (v - w) = u + v - w)%v3.
Proof.
intros.
progress unfold vec3_add.
progress unfold vec3_sub; cbn.
do 3 rewrite (rngl_add_sub_assoc Hop).
easy.
Qed.

Theorem vec3_add_assoc : ∀ u v w, (u + (v + w) = u + v + w)%v3.
Proof.
intros.
progress unfold vec3_add; cbn.
do 3 rewrite rngl_add_assoc.
easy.
Qed.

Theorem vec3_add_comm : ∀ u v, (u + v = v + u)%v3.
Proof.
intros.
progress unfold vec3_add.
f_equal; apply rngl_add_comm.
Qed.

Theorem vec3_add_add_swap : ∀ u v w, (u + v + w = u + w + v)%v3.
Proof.
intros.
do 2 rewrite <- vec3_add_assoc.
progress f_equal.
apply vec3_add_comm.
Qed.

Theorem vec3_add_sub_swap : ∀ u v w, (u + v - w = u - w + v)%v3.
Proof.
intros.
rewrite vec3_add_comm.
rewrite <- vec3_add_sub_assoc.
apply vec3_add_comm.
Qed.

Theorem cross_mul_add_distr_l :
  ∀ u v w, (u × (v + w) = u × v + u × w)%v3.
Proof.
intros.
progress unfold cross_mul.
progress unfold vec3_add.
cbn.
do 6 rewrite rngl_mul_add_distr_l.
do 3 rewrite <- (rngl_add_sub_swap Hop).
do 3 rewrite (rngl_sub_add_distr Hos).
do 3 rewrite (rngl_add_sub_assoc Hop).
now f_equal; rewrite (rngl_sub_sub_swap Hop).
Qed.

Theorem cross_mul_add_distr_r :
  ∀ u v w, ((u + v) × w = u × w + v × w)%v3.
Proof.
intros.
progress unfold cross_mul.
progress unfold vec3_add.
cbn.
do 6 rewrite rngl_mul_add_distr_r.
do 3 rewrite <- (rngl_add_sub_swap Hop).
do 3 rewrite (rngl_sub_add_distr Hos).
do 3 rewrite (rngl_add_sub_assoc Hop).
now f_equal; rewrite (rngl_sub_sub_swap Hop).
Qed.

Theorem vec3_scal_mul_cross_mul_l : ∀ a u v, a · (u × v) = (a · u) × v.
Proof.
intros.
progress unfold vec3_scal_mul.
progress unfold cross_mul; cbn.
do 3 rewrite (rngl_mul_sub_distr_l Hop).
do 6 rewrite rngl_mul_assoc.
easy.
Qed.

Theorem vec3_scal_mul_cross_mul_r : ∀ a u v, a · (u × v) = u × (a · v).
Proof.
intros.
progress unfold vec3_scal_mul.
progress unfold cross_mul; cbn.
do 3 rewrite (rngl_mul_sub_distr_l Hop).
do 12 rewrite rngl_mul_assoc.
do 3 rewrite (rngl_mul_comm Hic a).
easy.
Qed.

Theorem cross_mul_anticomm : ∀ u v, u × v = (- (v × u))%v3.
Proof.
intros.
progress unfold vec3_opp.
progress unfold cross_mul; cbn.
do 3 rewrite (rngl_opp_sub_distr Hop).
do 2 rewrite (rngl_mul_comm Hic _ (v3_x u)).
do 2 rewrite (rngl_mul_comm Hic _ (v3_y u)).
do 2 rewrite (rngl_mul_comm Hic _ (v3_z u)).
easy.
Qed.

Theorem vec3_opp_sub_distr : ∀ u v, (- (u - v) = v - u)%v3.
Proof.
intros.
progress unfold vec3_opp.
progress unfold vec3_sub; cbn.
do 3 rewrite (rngl_opp_sub_distr Hop).
easy.
Qed.

Theorem vec3_triple_prod_l :
  ∀ u v w, u × (v × w) = ((u ⋆ w) · v - (u ⋆ v) · w)%v3.
Proof.
intros.
progress unfold cross_mul.
progress unfold vec3_sub.
progress unfold vec3_scal_mul.
progress unfold vec3_dot_mul; cbn.
do 6 rewrite (rngl_mul_sub_distr_l Hop).
do 12 rewrite rngl_mul_assoc.
do 12 rewrite rngl_mul_add_distr_r.
do 3 rewrite (rngl_sub_sub_distr Hop).
do 6 rewrite (rngl_sub_add_distr Hos).
do 3 rewrite (rngl_mul_mul_swap Hic _ _ (v3_x v)).
do 3 rewrite (rngl_mul_mul_swap Hic _ _ (v3_y v)).
do 3 rewrite (rngl_mul_mul_swap Hic _ _ (v3_z v)).
do 6 rewrite <- (rngl_add_sub_swap Hop).
f_equal. {
  progress f_equal.
  progress f_equal.
  do 2 rewrite (rngl_add_sub_swap Hop).
  rewrite (rngl_sub_diag Hos).
  now rewrite rngl_add_0_l.
} {
  rewrite rngl_add_comm.
  rewrite (rngl_sub_sub_swap Hop _ _ (v3_y u * v3_y v * v3_y w)).
  rewrite (rngl_add_sub_swap Hop _ _ (v3_y u * v3_y v * v3_y w)).
  rewrite (rngl_add_sub Hos).
  apply (rngl_sub_sub_swap Hop).
} {
  do 2 rewrite (rngl_sub_sub_swap Hop _ _ (v3_z u * v3_z v * v3_z w)).
  now rewrite (rngl_add_sub Hos).
}
Qed.

Theorem vec3_triple_prod_r :
  ∀ u v w, (u × v) × w = ((w ⋆ u) · v - (w ⋆ v) · u)%v3.
Proof.
intros.
rewrite cross_mul_anticomm.
rewrite vec3_triple_prod_l.
apply vec3_opp_sub_distr.
Qed.

Theorem vec3_sub_sub_swap : ∀ u v w, (u - v - w = u - w - v)%v3.
Proof.
intros.
progress unfold vec3_sub; cbn.
f_equal; apply (rngl_sub_sub_swap Hop).
Qed.

Theorem quat_mul_assoc :
  ∀ a b c : quaternion T, (a * (b * c) = (a * b) * c)%quat.
Proof.
intros.
progress unfold quat_mul.
progress unfold quat_re_im_mul at 1 4.
f_equal. {
  destruct a as (a, u).
  destruct b as (b, v).
  destruct c as (c, w).
  move b before a; move c before b.
  cbn - [ vec3_dot_mul ].
  rewrite (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite rngl_mul_assoc.
  do 2 rewrite vec3_dot_mul_add_distr_l.
  do 2 rewrite vec3_dot_mul_add_distr_r.
  do 4 rewrite (rngl_sub_add_distr Hos).
  do 2 rewrite (rngl_sub_sub_swap Hop _ (u ⋆ v * c)).
  rewrite rngl_mul_vec3_dot_mul_l.
  rewrite (vec3_dot_mul_scal_mul_r b).
  rewrite (vec3_dot_mul_scal_mul_l b).
  rewrite (vec3_dot_mul_scal_mul_r _ u).
  rewrite (rngl_mul_comm Hic c).
  progress f_equal.
  clear a b c.
  apply vec3_dot_mul_cross_mul_l.
}
cbn.
destruct a as (a, u).
destruct b as (b, v).
destruct c as (c, w); cbn.
move b before a; move c before b.
do 4 rewrite vec3_scal_mul_add_distr_l.
do 2 rewrite vec3_scal_mul_sub_distr_r.
rewrite vec3_add_sub_assoc.
do 2 rewrite vec3_add_assoc.
do 4 rewrite vec3_scal_mul_assoc.
do 2 rewrite (rngl_mul_comm Hic c).
rewrite (vec3_add_add_swap _ _ ((b * c) · u)).
do 5 rewrite <- vec3_add_sub_swap.
rewrite <- vec3_add_sub_assoc.
rewrite <- vec3_add_assoc; symmetry.
rewrite <- vec3_add_sub_assoc.
rewrite <- vec3_add_assoc; symmetry.
progress f_equal.
do 2 rewrite cross_mul_add_distr_l.
do 2 rewrite cross_mul_add_distr_r.
do 2 rewrite vec3_add_sub_assoc.
do 4 rewrite vec3_add_assoc.
do 2 rewrite <- vec3_scal_mul_cross_mul_l.
do 2 rewrite <- vec3_scal_mul_cross_mul_r.
rewrite (vec3_add_comm _ (a · (v × w))).
rewrite (vec3_add_add_swap _ _ (b · (u × w))).
do 2 rewrite <- vec3_add_sub_assoc.
progress f_equal.
rewrite vec3_triple_prod_l.
rewrite vec3_triple_prod_r.
rewrite (vec3_dot_mul_comm _ u).
rewrite (vec3_dot_mul_comm w v).
apply vec3_sub_sub_swap.
Qed.

Context {Hon : rngl_has_1 T = true}.

Theorem rngl_opt_one_T : rngl_opt_one T = Some 1%L.
Proof.
progress unfold rngl_has_1 in Hon.
progress unfold rngl_one; cbn.
now destruct (rngl_opt_one T).
Qed.

Theorem rngl_opt_one_quat : rngl_opt_one (quaternion T) = Some 1%quat.
Proof.
cbn.
progress unfold quat_opt_one.
now rewrite rngl_opt_one_T.
Qed.

Theorem rngl_one_quat_one : 1%L = 1%quat.
Proof.
progress unfold rngl_one.
now rewrite rngl_opt_one_quat.
Qed.

Theorem rngl_opp_quat_opp : ∀ a, (- a)%L = (- a)%quat.
Proof.
intros.
progress unfold rngl_has_opp in Hop.
progress unfold rngl_opp; cbn.
progress unfold quat_opt_opp_or_subt.
destruct (rngl_opt_opp_or_subt T) as [opp_subt| ]; [ | easy ].
now destruct opp_subt.
Qed.

Theorem vec3_dot_mul_0_l : ∀ v, vec3_dot_mul 0 v = 0%L.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 3 rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_l.
apply rngl_add_0_l.
Qed.

Theorem vec3_dot_mul_0_r : ∀ v, vec3_dot_mul v 0 = 0%L.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 3 rewrite (rngl_mul_0_r Hos).
rewrite rngl_add_0_l.
apply rngl_add_0_l.
Qed.

Theorem vec3_scal_mul_1_l : ∀ u, 1 · u = u.
Proof.
intros.
progress unfold vec3_scal_mul; cbn.
do 3 rewrite (rngl_mul_1_l Hon).
now destruct u.
Qed.

Theorem vec3_scal_mul_0_r : ∀ u, (u · 0) = 0%v3.
Proof.
intros.
progress unfold vec3_scal_mul; cbn.
now rewrite (rngl_mul_0_r Hos).
Qed.

Theorem vec3_add_0_l : ∀ u, (0 + u)%v3 = u.
Proof.
intros.
progress unfold vec3_add; cbn.
do 3 rewrite rngl_add_0_l.
now destruct u.
Qed.

Theorem vec3_add_0_r : ∀ u, (u + 0)%v3 = u.
Proof.
intros.
progress unfold vec3_add; cbn.
do 3 rewrite rngl_add_0_r.
now destruct u.
Qed.

Theorem cross_mul_0_l : ∀ u, 0 × u = 0%v3.
Proof.
intros.
progress unfold cross_mul; cbn.
do 3 rewrite (rngl_mul_0_l Hos).
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem cross_mul_0_r : ∀ u, u × 0 = 0%v3.
Proof.
intros.
progress unfold cross_mul; cbn.
do 3 rewrite (rngl_mul_0_r Hos).
now rewrite (rngl_sub_0_r Hos).
Qed.

Theorem quat_mul_1_l : ∀ a, (1 * a)%quat = a.
Proof.
intros.
progress unfold quat_mul.
progress unfold quat_re_im_mul; cbn.
rewrite (rngl_mul_1_l Hon).
rewrite vec3_dot_mul_0_l.
rewrite (rngl_sub_0_r Hos).
rewrite vec3_scal_mul_1_l.
rewrite vec3_scal_mul_0_r.
rewrite cross_mul_0_l.
do 2 rewrite vec3_add_0_r.
now destruct a.
Qed.

Theorem rngl_has_1_quaternion : rngl_has_1 (quaternion T) = true.
Proof.
progress unfold rngl_has_1 in Hon; cbn in Hon.
progress unfold rngl_has_1; cbn.
progress unfold quat_opt_one.
now destruct (rngl_opt_one T).
Qed.

Theorem rngl_has_opp_quaternion : rngl_has_opp (quaternion T) = true.
Proof.
progress unfold rngl_has_opp in Hop |-*; cbn in Hop |-*.
progress unfold quat_opt_opp_or_subt.
remember (rngl_opt_opp_or_subt T) as osq eqn:Hosq.
symmetry in Hosq.
destruct osq as [opp| ]; [ | easy ].
now destruct opp.
Qed.

Theorem rngl_has_subt_quaternion : rngl_has_subt (quaternion T) = false.
Proof.
progress unfold rngl_has_opp in Hop; cbn in Hop.
progress unfold rngl_has_subt; cbn.
progress unfold quat_opt_opp_or_subt.
remember (rngl_opt_opp_or_subt T) as osq eqn:Hosq.
symmetry in Hosq.
destruct osq as [opp| ]; [ | easy ].
now destruct opp.
Qed.

Theorem rngl_has_inv_quaternion : rngl_has_inv (quaternion T) = true.
Proof.
progress unfold rngl_has_inv in Hiv; cbn in Hiv.
progress unfold rngl_has_inv; cbn.
progress unfold quat_opt_inv_or_quot.
destruct (rngl_opt_inv_or_quot T) as [inv_quot| ]; [ | easy ].
now destruct inv_quot.
Qed.

Theorem rngl_has_quot_quaternion : rngl_has_quot (quaternion T) = false.
Proof.
progress unfold rngl_has_inv in Hiv; cbn in Hiv.
progress unfold rngl_has_quot; cbn.
progress unfold quat_opt_inv_or_quot.
destruct (rngl_opt_inv_or_quot T) as [inv_quot| ]; [ | easy ].
now destruct inv_quot.
Qed.

Theorem rngl_opt_inv_or_quot_quaternion :
  rngl_opt_inv_or_quot (quaternion T) = Some (inl quat_inv).
Proof.
progress unfold rngl_opt_inv_or_quot; cbn.
progress unfold quat_opt_inv_or_quot.
progress unfold rngl_has_inv in Hiv; cbn in Hiv.
destruct (rngl_opt_inv_or_quot T) as [inv_quot| ]; [ | easy ].
now destruct inv_quot.
Qed.

Theorem quat_opt_mul_1_l :
  if rngl_has_1 (quaternion T) then ∀ a : quaternion T, (1 * a)%L = a
  else not_applicable.
Proof.
rewrite rngl_has_1_quaternion.
intros; cbn.
rewrite rngl_one_quat_one.
apply quat_mul_1_l.
Qed.

Theorem quat_mul_1_r : ∀ a, (a * 1)%quat = a%quat.
Proof.
intros.
progress unfold quat_mul.
progress unfold quat_re_im_mul; cbn.
rewrite (rngl_mul_1_r Hon).
rewrite vec3_dot_mul_0_r.
rewrite (rngl_sub_0_r Hos).
rewrite vec3_scal_mul_0_r.
rewrite vec3_scal_mul_1_l.
rewrite cross_mul_0_r.
rewrite vec3_add_0_l.
rewrite vec3_add_0_r.
now destruct a.
Qed.

Theorem quat_opt_mul_1_r :
  if rngl_has_1 (quaternion T) then ∀ a : quaternion T, (a * 1)%L = a
  else not_applicable.
Proof.
rewrite rngl_has_1_quaternion.
intros.
rewrite rngl_one_quat_one; cbn.
apply quat_mul_1_r.
Qed.

Theorem quat_mul_add_distr_l :
  ∀ a b c, (a * (b + c))%quat = (a * b + a * c)%quat.
Proof.
intros.
progress unfold quat_mul.
progress unfold quat_re_im_mul.
progress unfold quat_add; cbn.
rewrite rngl_mul_add_distr_l.
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop _ (q_re a * q_re c)).
rewrite <- (rngl_sub_add_distr Hos).
rewrite vec3_dot_mul_add_distr_l.
progress f_equal.
rewrite vec3_scal_mul_add_distr_l.
rewrite vec3_scal_mul_add_distr_r.
rewrite cross_mul_add_distr_l.
do 4 rewrite vec3_add_assoc.
progress f_equal.
rewrite vec3_add_add_swap.
progress f_equal.
rewrite (vec3_add_add_swap _ _ (vec3_scal_mul _ _)).
rewrite vec3_add_add_swap.
easy.
Qed.

Theorem quat_mul_add_distr_r :
  ∀ a b c, ((a + b) * c)%quat = (a * c + b * c)%quat.
Proof.
intros.
progress unfold quat_mul.
progress unfold quat_re_im_mul.
progress unfold quat_add; cbn.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_add_sub_assoc Hop).
rewrite <- (rngl_add_sub_swap Hop _ (q_re b * q_re c)).
rewrite <- (rngl_sub_add_distr Hos).
rewrite vec3_dot_mul_add_distr_r.
progress f_equal.
rewrite vec3_scal_mul_add_distr_r.
rewrite vec3_scal_mul_add_distr_l.
rewrite cross_mul_add_distr_r.
do 4 rewrite vec3_add_assoc.
progress f_equal.
rewrite vec3_add_add_swap.
progress f_equal.
rewrite (vec3_add_add_swap _ _ (vec3_scal_mul _ _)).
rewrite vec3_add_add_swap.
easy.
Qed.

Theorem vec3_dot_mul_opp_l : ∀ u v, - u ⋆ v = (- (u ⋆ v))%L.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 3 rewrite (rngl_mul_opp_l Hop).
do 2 rewrite (rngl_add_opp_r Hop).
rewrite (rngl_opp_add_distr Hop).
progress f_equal.
symmetry.
apply (rngl_opp_add_distr Hop).
Qed.

Theorem vec3_dot_mul_opp_r : ∀ u v, u ⋆ - v = (- (u ⋆ v))%L.
Proof.
intros.
progress unfold vec3_dot_mul; cbn.
do 3 rewrite (rngl_mul_opp_r Hop).
do 2 rewrite (rngl_add_opp_r Hop).
rewrite (rngl_opp_add_distr Hop).
progress f_equal.
symmetry.
apply (rngl_opp_add_distr Hop).
Qed.

Theorem vec3_scal_mul_opp_l : ∀ a u, - a · u = (- (a · u))%v3.
Proof.
intros.
progress unfold vec3_scal_mul.
progress unfold vec3_opp; cbn.
do 3 rewrite (rngl_mul_opp_l Hop).
easy.
Qed.

Theorem vec3_scal_mul_opp_r : ∀ a u, a · - u = (- (a · u))%v3.
Proof.
intros.
progress unfold vec3_scal_mul.
progress unfold vec3_opp; cbn.
do 3 rewrite (rngl_mul_opp_r Hop).
easy.
Qed.

Theorem vec3_add_opp_r : ∀ u v, (u + - v = u - v)%v3.
Proof.
intros.
progress unfold vec3_add.
progress unfold vec3_opp.
progress unfold vec3_sub; cbn.
do 3 rewrite (rngl_add_opp_r Hop).
easy.
Qed.

Theorem cross_mul_opp_l : ∀ u v, - u × v = (- (u × v))%v3.
Proof.
intros.
progress unfold cross_mul.
progress unfold vec3_opp; cbn.
do 6 rewrite (rngl_mul_opp_l Hop).
do 3 rewrite (rngl_sub_opp_r Hop).
do 3 rewrite (rngl_add_opp_l Hop).
do 3 rewrite (rngl_opp_sub_distr Hop).
easy.
Qed.

Theorem vec3_opp_add_distr : ∀ u v, (- (u + v) = - u - v)%v3.
Proof.
intros.
progress unfold vec3_opp.
progress unfold vec3_sub.
progress unfold vec3_add; cbn.
do 3 rewrite (rngl_opp_add_distr Hop).
easy.
Qed.

Theorem quat_mul_opp_l : ∀ a b, (- a * b = - (a * b))%quat.
Proof.
intros.
progress unfold quat_mul.
progress unfold quat_re_im_mul.
progress unfold quat_opp; cbn.
rewrite (rngl_mul_opp_l Hop).
rewrite vec3_dot_mul_opp_l.
rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_add_opp_l Hop).
rewrite (rngl_opp_sub_distr Hop).
progress f_equal.
rewrite vec3_scal_mul_opp_r.
rewrite vec3_scal_mul_opp_l.
rewrite cross_mul_opp_l.
do 2 rewrite vec3_add_opp_r.
do 2 rewrite vec3_opp_add_distr.
easy.
Qed.

Theorem quat_mul_sub_distr_r :
  ∀ a b c, ((a - b) * c)%quat = (a * c - b * c)%quat.
Proof.
intros.
progress unfold quat_sub.
rewrite quat_mul_add_distr_r.
progress f_equal.
apply quat_mul_opp_l.
Qed.

Theorem quat_add_opp_diag_l : ∀ a, (- a + a = 0)%quat.
Proof.
intros.
progress unfold quat_opp; cbn.
progress unfold quat_add; cbn.
rewrite (rngl_add_opp_diag_l Hop).
now rewrite vec3_add_opp_diag_l.
Qed.

Theorem quat_opt_add_opp_diag_l :
  if rngl_has_opp (quaternion T) then ∀ a : quaternion T, (- a + a)%L = 0%L
  else not_applicable.
Proof.
rewrite rngl_has_opp_quaternion; cbn.
intros.
rewrite rngl_opp_quat_opp.
apply quat_add_opp_diag_l.
Qed.

Theorem quat_opt_add_sub :
  if rngl_has_subt (quaternion T) then ∀ a b : quaternion T, (a + b - b)%L = a
  else not_applicable.
Proof. now rewrite rngl_has_subt_quaternion. Qed.

Theorem quat_add_opp_r : ∀ a b, (a + - b = a - b)%quat.
Proof. easy. Qed.

Theorem quat_sub_add_distr :
  ∀ a b c : quaternion T, (a - (b + c) = a - b - c)%quat.
Proof.
intros.
progress unfold quat_sub.
progress unfold quat_opp.
rewrite <- quat_add_assoc.
progress f_equal.
progress unfold quat_add; cbn.
f_equal. {
  rewrite (rngl_add_opp_r Hop).
  apply (rngl_opp_add_distr Hop).
}
symmetry.
apply vec3_add_opp_opp.
Qed.

Theorem quat_opt_sub_add_distr :
  if rngl_has_subt (quaternion T) then
    ∀ a b c : quaternion T, (a - (b + c))%L = (a - b - c)%L
  else not_applicable.
Proof. now rewrite rngl_has_subt_quaternion. Qed.

Theorem quat_opt_sub_0_l :
  if rngl_has_subt (quaternion T) then ∀ a : quaternion T, (0 - a)%L = 0%L
  else not_applicable.
Proof. now rewrite rngl_has_subt_quaternion. Qed.

Context {Hor : rngl_is_ordered T = true}.
Definition Heo := rngl_has_eq_dec_or_is_ordered_r Hor.

Theorem eq_quat_norm_squ_0 : ∀ a, quat_norm_squ a = 0%L → a = 0%quat.
Proof.
assert (Hio :
  (rngl_is_integral_domain T ||
     rngl_has_inv_and_1_or_quot T &&
     rngl_has_eq_dec_or_order T)%bool = true). {
  specialize (rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv) as Hi1.
  apply Bool.orb_true_iff; right.
  rewrite Hi1; cbn.
  now apply rngl_has_eq_dec_or_is_ordered_r.
}
intros (a, (x, y, z)) HN; cbn.
progress unfold quat_norm_squ in HN.
cbn in HN.
apply (rngl_eq_add_0 Hor) in HN; cycle 1. {
  apply (rngl_add_nonneg_nonneg Hor). {
    apply (rngl_add_nonneg_nonneg Hor).
    apply (rngl_squ_nonneg Hos Hor).
    apply (rngl_squ_nonneg Hos Hor).
  }
  apply (rngl_squ_nonneg Hos Hor).
} {
  apply (rngl_squ_nonneg Hos Hor).
}
destruct HN as (HN, H).
apply (eq_rngl_squ_0 Hos Hio) in H; subst.
apply (rngl_eq_add_0 Hor) in HN; cycle 1. {
  apply (rngl_add_nonneg_nonneg Hor).
  apply (rngl_squ_nonneg Hos Hor).
  apply (rngl_squ_nonneg Hos Hor).
} {
  apply (rngl_squ_nonneg Hos Hor).
}
destruct HN as (HN, H).
apply (eq_rngl_squ_0 Hos Hio) in H; subst.
apply (rngl_eq_add_0 Hor) in HN; cycle 1.
apply (rngl_squ_nonneg Hos Hor).
apply (rngl_squ_nonneg Hos Hor).
destruct HN as (HN, H).
apply (eq_rngl_squ_0 Hos Hio) in H; subst.
apply (eq_rngl_squ_0 Hos Hio) in HN; subst.
easy.
Qed.

Theorem quat_mul_inv_diag_l : ∀ a, a ≠ 0%quat → (a⁻¹ * a = 1)%quat.
Proof.
intros * Haz.
progress unfold quat_mul.
progress unfold quat_re_im_mul.
progress unfold quat_inv.
progress unfold quat_one.
progress unfold vec3_dot_mul; cbn.
do 3 rewrite (rngl_div_opp_l Hop Hiv).
do 3 rewrite (rngl_mul_opp_l Hop).
do 2 rewrite (rngl_add_opp_r Hop).
do 2 rewrite (rngl_sub_sub_distr Hop).
rewrite (rngl_sub_opp_r Hop).
do 4 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 4 rewrite fold_rngl_squ.
do 3 rewrite <- (rngl_div_add_distr_r Hiv).
rewrite (rngl_div_diag Hon Hiq). 2: {
  intros H; apply Haz; clear Haz.
  now apply eq_quat_norm_squ_0.
}
progress f_equal.
progress unfold vec3_scal_mul; cbn.
progress unfold vec3_add; cbn.
do 3 rewrite (rngl_add_sub_assoc Hop).
do 6 rewrite (rngl_mul_opp_l Hop).
do 3 rewrite (rngl_add_opp_r Hop).
do 3 rewrite (rngl_sub_opp_r Hop).
do 3 rewrite (rngl_mul_opp_r Hop).
do 3 rewrite (rngl_add_opp_r Hop).
do 3 rewrite (rngl_mul_div_assoc Hiv).
do 9 rewrite (rngl_div_mul_mul_div Hic Hiv).
do 3 rewrite (rngl_sub_diag Hos).
do 3 rewrite (rngl_sub_0_l Hop).
rewrite (rngl_mul_comm Hic (v3_y _)).
rewrite (rngl_add_opp_diag_l Hop).
rewrite (rngl_mul_comm Hic (v3_z _)).
rewrite (rngl_add_opp_diag_l Hop).
rewrite (rngl_mul_comm Hic (v3_x _)).
rewrite (rngl_add_opp_diag_l Hop).
easy.
Qed.

Theorem quat_opt_mul_inv_diag_l :
  if (rngl_has_inv (quaternion T) && rngl_has_1 (quaternion T))%bool then
    ∀ a : quaternion T, a ≠ 0%L → (a⁻¹ * a)%L = 1%L
  else not_applicable.
Proof.
rewrite rngl_has_inv_quaternion.
rewrite rngl_has_1_quaternion.
rewrite rngl_one_quat_one; cbn.
progress unfold rngl_inv.
rewrite rngl_opt_inv_or_quot_quaternion.
apply quat_mul_inv_diag_l.
Qed.

Theorem vec3_sub_add_distr : ∀ u v w, (u - (v + w) = u - v - w)%v3.
Proof.
intros.
progress unfold vec3_sub.
progress unfold vec3_add; cbn.
do 3 rewrite (rngl_sub_add_distr Hos).
easy.
Qed.

Theorem vec3_opp_sub_swap : ∀ u v, (- u - v)%v3 = (- v - u)%v3.
Proof.
intros.
progress unfold vec3_opp.
progress unfold vec3_sub; cbn.
f_equal; apply (rngl_opp_sub_swap Hop).
Qed.

Theorem vec3_add_move_l : ∀ u v w, (u + v)%v3 = w ↔ v = (w - u)%v3.
Proof.
intros.
progress unfold vec3_add.
progress unfold vec3_sub; cbn.
split; intros; subst; cbn. {
  do 3 rewrite rngl_add_comm, (rngl_add_sub Hos).
  now destruct v.
} {
  do 3 rewrite rngl_add_comm, (rngl_sub_add Hop).
  now destruct w.
}
Qed.

Theorem vec3_sub_diag : ∀ u, (u - u = 0)%v3.
Proof.
intros.
progress unfold vec3_sub.
do 3 rewrite (rngl_sub_diag Hos).
easy.
Qed.

Theorem vec3_sub_opp_r : ∀ u v, (u - - v = u + v)%v3.
Proof.
intros.
progress unfold vec3_add.
progress unfold vec3_sub.
progress unfold vec3_opp; cbn.
do 3 rewrite (rngl_sub_opp_r Hop).
easy.
Qed.

Theorem vec3_mul_2_l : ∀ u, 2 · u = (u + u)%v3.
Proof.
intros.
progress unfold vec3_scal_mul.
progress unfold vec3_add; cbn.
do 3 rewrite (rngl_mul_2_l Hon).
easy.
Qed.

Theorem vec3_sub_sub_distr : ∀ u v w, (u - (v - w) = u - v + w)%v3.
Proof.
intros.
progress unfold vec3_sub.
progress unfold vec3_add; cbn.
do 3 rewrite (rngl_sub_sub_distr Hop).
easy.
Qed.

Theorem vec3_add_sub : ∀ u v, (u + v - v)%v3 = u.
Proof.
intros.
progress unfold vec3_sub; cbn.
do 3 rewrite (rngl_add_sub Hos).
now destruct u.
Qed.

Theorem vec3_sub_add : ∀ u v, (u - v + v)%v3 = u.
Proof.
intros.
rewrite <- vec3_add_sub_swap.
apply vec3_add_sub.
Qed.

Theorem quat_add_move_l : ∀ a b c, (a + b)%quat = c ↔ b = (c - a)%quat.
Proof.
intros.
progress unfold quat_sub.
progress unfold quat_add.
progress unfold quat_opp; cbn.
rewrite (rngl_add_opp_r Hop).
rewrite vec3_add_opp_r.
split; intros; subst; cbn. {
  rewrite rngl_add_comm, (rngl_add_sub Hos).
  rewrite vec3_add_comm, vec3_add_sub.
  now destruct b.
} {
  rewrite rngl_add_comm, (rngl_sub_add Hop).
  rewrite vec3_add_comm, vec3_sub_add.
  now destruct c.
}
Qed.

Theorem quat_comm :
  ∀ a b, (a * b - b * a = mk_quat 0 (2 · (q_im a × q_im b)))%quat.
Proof.
intros.
progress unfold quat_sub.
progress unfold quat_add.
progress unfold quat_opp.
progress unfold quat_mul.
progress unfold quat_re_im_mul; cbn - [ cross_mul ].
rewrite (rngl_mul_comm Hic _ (q_re a)).
rewrite (vec3_dot_mul_comm _ (q_im a)).
rewrite (rngl_add_opp_diag_r Hop).
progress f_equal.
rewrite (vec3_add_comm _ (q_re a · q_im b)).
rewrite (cross_mul_anticomm _ (q_im a)).
do 2 rewrite vec3_add_opp_r.
rewrite vec3_sub_sub_distr.
rewrite vec3_add_sub_swap.
rewrite vec3_sub_diag.
rewrite vec3_add_0_l.
symmetry.
apply vec3_mul_2_l.
Qed.

Theorem quat_mul_comm_eq :
  ∀ a b, (a * b = b * a + mk_quat 0 (2 · (q_im a × q_im b)))%quat.
Proof.
intros.
symmetry.
apply quat_add_move_l.
symmetry.
apply quat_comm.
Qed.

Theorem quat_mul_inv_diag_r :
  ∀ a,
  a ≠ 0%quat
  → (a * a⁻¹)%quat = 1%quat.
Proof.
intros * Haz.
rewrite quat_mul_comm_eq.
rewrite quat_mul_inv_diag_l; [ | easy ].
progress unfold vec3_scal_mul.
progress unfold cross_mul.
cbn.
do 3 rewrite (rngl_div_opp_l Hop Hiv).
do 6 rewrite (rngl_mul_opp_r Hop).
do 6 rewrite (rngl_mul_div_assoc Hiv).
do 3 rewrite (rngl_sub_opp_r Hop).
rewrite (rngl_mul_comm Hic _ (v3_y _)).
rewrite (rngl_add_opp_diag_l Hop).
rewrite (rngl_mul_comm Hic _ (v3_x _)).
rewrite (rngl_add_opp_diag_l Hop).
rewrite (rngl_mul_comm Hic _ (v3_x _)).
rewrite (rngl_add_opp_diag_l Hop).
rewrite (rngl_mul_0_r Hos).
apply quat_add_0_r.
Qed.

Theorem quat_opt_mul_inv_diag_r :
  if (rngl_has_inv (quaternion T) && rngl_has_1 (quaternion T) &&
        negb false)%bool then
    ∀ a : quaternion T, a ≠ 0%L → (a * a⁻¹)%L = 1%L
  else not_applicable.
Proof.
rewrite rngl_has_inv_quaternion.
rewrite rngl_has_1_quaternion; cbn.
progress unfold rngl_inv.
rewrite rngl_opt_inv_or_quot_quaternion.
rewrite rngl_one_quat_one.
apply quat_mul_inv_diag_r.
Qed.

Theorem quat_opt_mul_div :
  if rngl_has_quot (quaternion T) then
    ∀ a b : quaternion T, b ≠ 0%L → (a * b / b)%L = a
  else not_applicable.
Proof. now rewrite rngl_has_quot_quaternion. Qed.

Theorem quat_opt_mul_quot_r :
  if (rngl_has_quot (quaternion T) && negb false)%bool then
    ∀ a b : quaternion T, b ≠ 0%L → (b * a / b)%L = a
  else not_applicable.
Proof. now rewrite rngl_has_quot_quaternion. Qed.

Theorem quat_sub_diag : ∀ a, (a - a = 0)%quat.
Proof.
intros.
progress unfold quat_sub.
progress unfold quat_add.
progress unfold quat_opp; cbn.
rewrite (rngl_add_opp_diag_r Hop).
rewrite vec3_add_opp_diag_r.
easy.
Qed.

Theorem vec3_opp_0 : (- 0 = 0)%v3.
Proof.
progress unfold vec3_opp; cbn.
now rewrite (rngl_opp_0 Hop).
Qed.

Theorem fold_vec3_zero : mk_v3 0 0 0 = vec3_zero.
Proof. easy. Qed.

Theorem quat_opp_0 : (- 0 = 0)%quat.
Proof.
progress unfold quat_opp; cbn.
rewrite (rngl_opp_0 Hop).
rewrite vec3_opp_0.
easy.
Qed.

Theorem quat_mul_0_l : ∀ a, (0 * a)%quat = 0%quat.
Proof.
intros.
rewrite <- (quat_sub_diag 0) at 1.
rewrite quat_mul_sub_distr_r.
apply quat_sub_diag.
Qed.

Theorem quat_opt_integral :
   ∀ a b : quaternion T,
   (a * b)%L = 0%L
   → a = 0%L ∨ b = 0%L ∨ rngl_is_zero_divisor a ∨ rngl_is_zero_divisor b.
Proof.
intros * Hab.
cbn in Hab |-*.
apply (f_equal (λ x, quat_mul x (quat_inv b))) in Hab.
rewrite quat_mul_0_l in Hab.
rewrite <- quat_mul_assoc in Hab.
destruct (quat_eq_dec (rngl_eq_dec Heo) b 0) as [Hbz| Hbz].
now right; left.
rewrite (quat_mul_inv_diag_r) in Hab; [ | easy ].
rewrite quat_mul_1_r in Hab.
now left.
Qed.

Theorem q_re_rngl_of_nat :
  ∀ i, q_re (rngl_of_nat i) = rngl_of_nat i.
Proof.
intros.
induction i; [ easy | ].
do 2 rewrite rngl_of_nat_succ.
cbn.
f_equal; [ | easy ].
progress unfold rngl_one at 1; cbn.
progress unfold quat_opt_one.
progress unfold rngl_has_1 in Hon.
now destruct (rngl_opt_one T).
Qed.

Theorem q_im_rngl_of_nat :
  ∀ i, q_im (rngl_of_nat i) = 0%v3.
Proof.
intros.
induction i; [ easy | ].
rewrite rngl_of_nat_succ; cbn.
rewrite rngl_one_quat_one; cbn.
now rewrite vec3_add_0_l.
Qed.

Theorem quat_add_sub : ∀ a b, (a + b - b)%quat = a.
Proof.
intros.
progress unfold quat_sub.
progress unfold quat_add.
progress unfold quat_opp; cbn.
rewrite (rngl_add_opp_r Hop).
rewrite (rngl_add_sub Hos).
rewrite vec3_add_opp_r.
rewrite vec3_add_sub.
now destruct a.
Qed.

Theorem quat_add_move_0_l : ∀ a b, (a + b)%quat = 0%quat ↔ b = (- a)%quat.
Proof.
intros.
split; intros Hab; [ | subst; apply quat_sub_diag ].
apply (f_equal (λ x, quat_sub x a)) in Hab.
rewrite quat_add_comm in Hab; cbn in Hab.
rewrite quat_add_sub in Hab.
subst.
progress unfold quat_sub.
apply quat_add_0_l.
Qed.

Theorem quat_characteristic_0_prop :
  rngl_characteristic T = 0
  → ∀ i, rngl_of_nat (S i) ≠ 0%quat.
Proof.
intros Hch * H1.
rewrite rngl_of_nat_succ in H1; cbn in H1.
rewrite rngl_one_quat_one in H1.
injection H1; clear H1; intros H4 H3 H2 H1.
clear H2 H3 H4.
rewrite q_re_rngl_of_nat in H1.
specialize rngl_opt_characteristic_prop as H2.
rewrite Hon, Hch in H2.
cbn - [ rngl_of_nat ] in H2.
specialize (H2 i).
now rewrite rngl_of_nat_succ in H2.
Qed.

Theorem q_re_rngl_of_nat_inj :
  ∀ i j,
  q_re (rngl_of_nat i) = q_re (rngl_of_nat j)
  → rngl_of_nat i = rngl_of_nat j.
Proof.
intros * Hij.
do 2 rewrite q_re_rngl_of_nat in Hij.
revert i Hij.
induction j; intros. {
  cbn in Hij |-*.
  destruct i; [ easy | ].
  rewrite rngl_of_nat_succ in Hij.
  rewrite rngl_of_nat_succ; cbn.
  rewrite rngl_one_quat_one.
  progress unfold quat_add.
  rewrite q_re_rngl_of_nat; cbn.
  rewrite Hij.
  rewrite vec3_add_0_l.
  rewrite q_im_rngl_of_nat.
  easy.
}
destruct i. {
  rewrite rngl_of_nat_succ in Hij.
  rewrite rngl_of_nat_succ.
  cbn in Hij |-*.
  rewrite rngl_one_quat_one.
  progress unfold quat_add.
  rewrite q_re_rngl_of_nat; cbn.
  rewrite <- Hij.
  rewrite vec3_add_0_l.
  rewrite q_im_rngl_of_nat.
  easy.
}
do 2 rewrite rngl_of_nat_succ in Hij.
do 2 rewrite rngl_of_nat_succ.
apply (rngl_add_cancel_l Hos) in Hij.
f_equal.
now apply IHj.
Qed.

Theorem quat_characteristic_not_0_prop :
  rngl_characteristic T ≠ 0
  → (∀ i, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%quat) ∧
    rngl_of_nat (rngl_characteristic T) = 0%quat.
Proof.
intros Hch *.
specialize rngl_opt_characteristic_prop as H1.
rewrite Hon in H1.
generalize Hch; intros H; apply Nat.eqb_neq in H.
rewrite H in H1; clear H.
destruct H1 as (H1, H2).
split. {
  intros * (Hzi, Hi) H3.
  apply (f_equal q_re) in H3.
  rewrite q_re_rngl_of_nat in H3; cbn in H3.
  revert H3.
  now apply H1.
}
remember (rngl_characteristic T) as j eqn:Hj.
destruct j; [ easy | ].
rewrite rngl_of_nat_succ in H2.
replace 0%quat with (rngl_of_nat 0) by easy.
apply q_re_rngl_of_nat_inj.
rewrite q_re_rngl_of_nat.
now rewrite rngl_of_nat_succ.
Qed.

Theorem quat_opt_characteristic_prop :
  if rngl_has_1 (quaternion T) then
    if rngl_characteristic T =? 0 then ∀ i : nat, rngl_of_nat (S i) ≠ 0%L
    else
      (∀ i : nat, 0 < i < rngl_characteristic T → rngl_of_nat i ≠ 0%L) ∧
      rngl_of_nat (rngl_characteristic T) = 0%L
  else not_applicable.
Proof.
rewrite rngl_has_1_quaternion.
remember (rngl_characteristic T =? 0) as ch eqn:Hch.
symmetry in Hch.
destruct ch. {
  apply Nat.eqb_eq in Hch.
  cbn - [ rngl_of_nat ].
  apply (quat_characteristic_0_prop Hch).
}
apply Nat.eqb_neq in Hch; cbn.
now apply quat_characteristic_not_0_prop.
Qed.

Instance quat_ring_like_prop : ring_like_prop (quaternion T) :=
  {| rngl_mul_is_comm := false;
     rngl_is_archimedean := false;
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
     rngl_opt_mul_add_distr_r := quat_mul_add_distr_r;
     rngl_opt_add_opp_diag_l := quat_opt_add_opp_diag_l;
     rngl_opt_add_sub := quat_opt_add_sub;
     rngl_opt_sub_add_distr := quat_opt_sub_add_distr;
     rngl_opt_sub_0_l := quat_opt_sub_0_l;
     rngl_opt_mul_inv_diag_l := quat_opt_mul_inv_diag_l;
     rngl_opt_mul_inv_diag_r := quat_opt_mul_inv_diag_r;
     rngl_opt_mul_div := quat_opt_mul_div;
     rngl_opt_mul_quot_r := quat_opt_mul_quot_r;
     rngl_opt_integral := quat_opt_integral;
     rngl_opt_alg_closed := NA;
     rngl_opt_characteristic_prop := quat_opt_characteristic_prop;
     rngl_opt_ord := NA;
     rngl_opt_archimedean := NA |}.

End a.

Notation "a +ℹ b +𝐣 c +𝐤 d" :=
  (mk_quat a (mk_v3 b c d)) (at level 50, b, c, d at level 0) : quat_scope.
Notation "a * b" := (quat_mul a b) : quat_scope.

(*
From Stdlib Require Import ZArith.
Require Import RingLike.Z_algebra.
Open Scope Z_scope.

Compute (
  let i := mk_quat 0 (mk_v3 1 0 0) in
  let j := mk_quat 0 (mk_v3 0 1 0) in
  let k := mk_quat 0 (mk_v3 0 0 1) in
  (j * j)%quat).
*)
