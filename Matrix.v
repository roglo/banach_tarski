(* Banach-Tarski paradox. *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith List.
From Stdlib Require Import Ring Field.
Require Import Datatypes.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import RingLike.Utils.
Require Import RingLike.IterAdd.
Require Import TrigoWithoutPi.Core.
Require Import a.Words a.Normalize a.Reverse a.Misc.
Require Import a.MiscTrigo a.MiscReals.

Record matrix A := mkmat
  { a₁₁ : A; a₁₂ : A; a₁₃ : A;
    a₂₁ : A; a₂₂ : A; a₂₃ : A;
    a₃₁ : A; a₃₂ : A; a₃₃ : A }.
Arguments a₁₁ [A] _.
Arguments a₁₂ [A] _.
Arguments a₁₃ [A] _.
Arguments a₂₁ [A] _.
Arguments a₂₂ [A] _.
Arguments a₂₃ [A] _.
Arguments a₃₁ [A] _.
Arguments a₃₂ [A] _.
Arguments a₃₃ [A] _.
Arguments mkmat [A] _ _ _ _ _ _ _ _ _.

Inductive vector A := V : A → A → A → vector A.

Declare Scope vec_scope.
Delimit Scope vec_scope with vec.

Arguments mkmat {A} (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃)%_L.
Arguments V {A} (x y z)%_L.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T }.
Context {Hch : rngl_characteristic T = 0}.
Context {Hc1 : rngl_characteristic T ≠ 1}.

Ltac fold_rngl :=
  replace (let (_, _, _, rngl_mul, _, _, _, _, _) := ro in rngl_mul)
    with rngl_mul by easy;
  replace (let (_, _, rngl_add, _, _, _, _, _, _) := ro in rngl_add)
    with rngl_add by easy;
  replace (let (rngl_zero, _, _, _, _, _, _, _, _) := ro in rngl_zero)
    with rngl_zero by easy;
  replace (let (_, rngl_one, _, _, _, _, _, _, _) := ro in rngl_one)
    with rngl_one by easy.

Definition mkrmat := @mkmat T.
Arguments mkrmat (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃)%_L.

(*
Definition Rmult5_sqrt2_sqrt5 := @Rmult5_sqrt2_sqrt5 T ro rp rl Hic Hon Hop Hor.
Arguments Rmult5_sqrt2_sqrt5 (a b c d)%_L.
*)

Add Ring rngl_ring : (rngl_ring_theory ac_ic ac_op).
Add Field rngl_field : (rngl_field_theory ac_ic ac_op ac_iv Hc1).

Definition mat_add (M₁ M₂ : matrix T) :=
  mkmat
    (a₁₁ M₁ + a₁₁ M₂) (a₁₂ M₁ + a₁₂ M₂) (a₁₃ M₁ + a₁₃ M₂)
    (a₂₁ M₁ + a₂₁ M₂) (a₂₂ M₁ + a₂₂ M₂) (a₂₃ M₁ + a₂₃ M₂)
    (a₃₁ M₁ + a₃₁ M₂) (a₃₂ M₁ + a₃₂ M₂) (a₃₃ M₁ + a₃₃ M₂).

Definition mat_opp M :=
  mkmat
    (- a₁₁ M) (- a₁₂ M) (- a₁₃ M)
    (- a₂₁ M) (- a₂₂ M) (- a₂₃ M)
    (- a₃₁ M) (- a₃₂ M) (- a₃₃ M).

Definition mat_sub M₁ M₂ := mat_add M₁ (mat_opp M₂).

Definition mat_vec_mul M '(V x y z) :=
  V (a₁₁ M * x + a₁₂ M * y + a₁₃ M * z)
    (a₂₁ M * x + a₂₂ M * y + a₂₃ M * z)
    (a₃₁ M * x + a₃₂ M * y + a₃₃ M * z).

Definition vec_norm '(V x y z) := √ (x² + y² + z²).
Definition vec_opp '(V x y z) := V (-x) (-y) (-z).
Definition vec_add '(V u₁ u₂ u₃) '(V v₁ v₂ v₃) :=
  V (u₁ + v₁) (u₂ + v₂) (u₃ + v₃).
Definition vec_sub u v := vec_add u (vec_opp v).
Definition vec_dot_mul '(V x₁ y₁ z₁) '(V x₂ y₂ z₂) :=
  (x₁ * x₂ + y₁ * y₂ + z₁ * z₂)%L.
Definition vec_cross_mul '(V u₁ u₂ u₃) '(V v₁ v₂ v₃) :=
  V (u₂ * v₃ - u₃ * v₂) (u₃ * v₁ - u₁ * v₃) (u₁ * v₂ - u₂ * v₁).
Definition vec_const_mul k '(V x y z) := V (k * x) (k * y) (k * z).
Definition mat_const_mul k (M : matrix T) :=
  mkmat
    (k * a₁₁ M) (k * a₁₂ M) (k * a₁₃ M)
    (k * a₂₁ M) (k * a₂₂ M) (k * a₂₃ M)
    (k * a₃₁ M) (k * a₃₂ M) (k * a₃₃ M).

Arguments vec_norm _%_vec.
Arguments vec_add _%_vec _%_vec.
Arguments vec_dot_mul _%_vec _%_vec.
Arguments vec_cross_mul _%_vec _%_vec.
Arguments vec_const_mul _%_L _%_vec.

Notation "0" := (V 0 0 0) : vec_scope.
Notation "k ⁎ v" := (vec_const_mul k v) (at level 40).
Notation "v ⁄ k" := (vec_const_mul (k⁻¹) v) (at level 40).
Notation "M * v" := (mat_vec_mul M v) : vec_scope.
Notation "u + v" := (vec_add u v) : vec_scope.
Notation "u - v" := (vec_sub u v) : vec_scope.
Notation "- v" := (vec_opp v) : vec_scope.
Notation "u · v" := (vec_dot_mul u v) (at level 44, left associativity).
Notation "u × v" := (vec_cross_mul u v) (at level 40, no associativity).
Notation "v ²" := (vec_dot_mul v v) : vec_scope.
Notation "‖ v ‖" := (vec_norm v) (at level 0, v at level 0, format "‖ v ‖").

Definition rot_x := mkmat
  1         0         0
  0         (1/3)     (-2*√2/3)
  0         (2*√2/3)  (1/3).
Definition rot_inv_x := mkmat
  1         0         0
  0         (1/3)     (2*√2/3)
  0         (-2*√2/3) (1/3).
Definition rot_z := mkmat
  (1/3)     (-2*√2/3) 0
  (2*√2/3)  (1/3)     0
  0         0         1.
Definition rot_inv_z := mkmat
  (1/3)     (2*√2/3)  0
  (-2*√2/3) (1/3)     0
  0         0         1.

Definition is_neg_vec '(V x y z) :=
  if (x <? 0)%L then true
  else if (0 <? x)%L then false
  else if (y <? 0)%L then true
  else if (0 <? y)%L then false
  else if (z <? 0)%L then true
  else if (0 <? z)%L then false
  else true.

Arguments is_neg_vec _%_vec.

Definition mat_of_elem e :=
  match e with
  | ạ => rot_x
  | ạ⁻¹ => rot_inv_x
  | ḅ => rot_z
  | ḅ⁻¹ => rot_inv_z
  end.

Definition rotate e pt := mat_vec_mul (mat_of_elem e) pt.

Definition mat_mul M₁ M₂ :=
  mkmat
    (a₁₁ M₁ * a₁₁ M₂ + a₁₂ M₁ * a₂₁ M₂ + a₁₃ M₁ * a₃₁ M₂)
    (a₁₁ M₁ * a₁₂ M₂ + a₁₂ M₁ * a₂₂ M₂ + a₁₃ M₁ * a₃₂ M₂)
    (a₁₁ M₁ * a₁₃ M₂ + a₁₂ M₁ * a₂₃ M₂ + a₁₃ M₁ * a₃₃ M₂)
    (a₂₁ M₁ * a₁₁ M₂ + a₂₂ M₁ * a₂₁ M₂ + a₂₃ M₁ * a₃₁ M₂)
    (a₂₁ M₁ * a₁₂ M₂ + a₂₂ M₁ * a₂₂ M₂ + a₂₃ M₁ * a₃₂ M₂)
    (a₂₁ M₁ * a₁₃ M₂ + a₂₂ M₁ * a₂₃ M₂ + a₂₃ M₁ * a₃₃ M₂)
    (a₃₁ M₁ * a₁₁ M₂ + a₃₂ M₁ * a₂₁ M₂ + a₃₃ M₁ * a₃₁ M₂)
    (a₃₁ M₁ * a₁₂ M₂ + a₃₂ M₁ * a₂₂ M₂ + a₃₃ M₁ * a₃₂ M₂)
    (a₃₁ M₁ * a₁₃ M₂ + a₃₂ M₁ * a₂₃ M₂ + a₃₃ M₁ * a₃₃ M₂).

Definition mat_id :=
  mkmat
    1 0 0
    0 1 0
    0 0 1.

Fixpoint mat_pow M n :=
  match n with
  | O => mat_id
  | S n' => mat_mul M (mat_pow M n')
  end.

Declare Scope mat_scope.
Delimit Scope mat_scope with mat.
Notation "M₁ + M₂" := (mat_add M₁ M₂) : mat_scope.
Notation "M₁ - M₂" := (mat_sub M₁ M₂) : mat_scope.
Notation "M₁ * M₂" := (mat_mul M₁ M₂) : mat_scope.
Notation "k ⁎ M" := (mat_const_mul k M) : mat_scope.
Notation "M ⁄ k" := (mat_const_mul (k⁻¹) M) : mat_scope.
Notation "- M" := (mat_opp M) : mat_scope.
Notation "M ^ n" := (mat_pow M n) : mat_scope.

Arguments mat_pow M%_mat n%_nat.
Arguments mat_mul M₁%_mat M₂%_mat.
Arguments mat_vec_mul M%_mat _%_vec.

Theorem vec_eq_dec : ∀ u v : vector T, { u = v } + { u ≠ v }.
Proof.
destruct_ac.
intros (x₁, y₁, z₁) (x₂, y₂, z₂).
destruct (rngl_eqb_dec x₁ x₂) as [H₁| H₁]. {
  apply (rngl_eqb_eq Heo) in H₁; subst x₂.
  destruct (rngl_eqb_dec y₁ y₂) as [H₁| H₁]. {
    apply (rngl_eqb_eq Heo) in H₁; subst y₂.
    destruct (rngl_eqb_dec z₁ z₂) as [H₁| H₁]. {
      apply (rngl_eqb_eq Heo) in H₁; subst z₂.
      now left.
    }
    apply (rngl_eqb_neq Heo) in H₁.
    right.
    now intros H; injection H; intros.
  }
  apply (rngl_eqb_neq Heo) in H₁.
  right.
  now intros H; injection H; intros.
}
apply (rngl_eqb_neq Heo) in H₁.
right.
now intros H; injection H; intros.
Qed.

Arguments vec_eq_dec _%_vec _%_vec.

Theorem vec_zerop : ∀ v : vector T, { v = 0%vec } + { v ≠ 0%vec }.
Proof.
intros.
now specialize (vec_eq_dec v 0).
Qed.

Theorem mat_eq_dec : ∀ m₁ m₂ : matrix T, { m₁ = m₂ } + { m₁ ≠ m₂ }.
Proof.
destruct_ac.
intros.
destruct (rngl_eqb_dec (a₁₁ m₁) (a₁₁ m₂)) as [H₁₁| H₁₁].
apply (rngl_eqb_eq Heo) in H₁₁.
destruct (rngl_eqb_dec (a₁₂ m₁) (a₁₂ m₂)) as [H₁₂| H₁₂].
apply (rngl_eqb_eq Heo) in H₁₂.
destruct (rngl_eqb_dec (a₁₃ m₁) (a₁₃ m₂)) as [H₁₃| H₁₃].
apply (rngl_eqb_eq Heo) in H₁₃.
destruct (rngl_eqb_dec (a₂₁ m₁) (a₂₁ m₂)) as [H₂₁| H₂₁].
apply (rngl_eqb_eq Heo) in H₂₁.
destruct (rngl_eqb_dec (a₂₂ m₁) (a₂₂ m₂)) as [H₂₂| H₂₂].
apply (rngl_eqb_eq Heo) in H₂₂.
destruct (rngl_eqb_dec (a₂₃ m₁) (a₂₃ m₂)) as [H₂₃| H₂₃].
apply (rngl_eqb_eq Heo) in H₂₃.
destruct (rngl_eqb_dec (a₃₁ m₁) (a₃₁ m₂)) as [H₃₁| H₃₁].
apply (rngl_eqb_eq Heo) in H₃₁.
destruct (rngl_eqb_dec (a₃₂ m₁) (a₃₂ m₂)) as [H₃₂| H₃₂].
apply (rngl_eqb_eq Heo) in H₃₂.
destruct (rngl_eqb_dec (a₃₃ m₁) (a₃₃ m₂)) as [H₃₃| H₃₃].
apply (rngl_eqb_eq Heo) in H₃₃.
now left; destruct m₁, m₂; simpl in *; subst.
apply (rngl_eqb_neq Heo) in H₃₃.
now right; intros H; subst m₁; apply H₃₃.
apply (rngl_eqb_neq Heo) in H₃₂.
now right; intros H; subst m₁; apply H₃₂.
apply (rngl_eqb_neq Heo) in H₃₁.
now right; intros H; subst m₁; apply H₃₁.
apply (rngl_eqb_neq Heo) in H₂₃.
now right; intros H; subst m₁; apply H₂₃.
apply (rngl_eqb_neq Heo) in H₂₂.
now right; intros H; subst m₁; apply H₂₂.
apply (rngl_eqb_neq Heo) in H₂₁.
now right; intros H; subst m₁; apply H₂₁.
apply (rngl_eqb_neq Heo) in H₁₃.
now right; intros H; subst m₁; apply H₁₃.
apply (rngl_eqb_neq Heo) in H₁₂.
now right; intros H; subst m₁; apply H₁₂.
apply (rngl_eqb_neq Heo) in H₁₁.
now right; intros H; subst m₁; apply H₁₁.
Qed.

Theorem mat_mul_id_l : ∀ m, (mat_id * m)%mat = m.
Proof.
destruct_ac.
intros m.
unfold mat_mul, mat_id; simpl.
progress repeat rewrite rngl_mul_1_l.
progress repeat rewrite (rngl_mul_0_l Hos).
progress repeat rewrite rngl_add_0_l.
progress repeat rewrite rngl_add_0_r.
now destruct m.
Qed.

Theorem mat_mul_id_r : ∀ m, (m * mat_id)%mat = m.
Proof.
destruct_ac.
intros m.
unfold mat_mul, mat_id; simpl.
progress repeat rewrite rngl_mul_1_r.
progress repeat rewrite (rngl_mul_0_r Hos).
progress repeat rewrite rngl_add_0_l.
progress repeat rewrite rngl_add_0_r.
now destruct m.
Qed.

Theorem mat_vec_mul_id : ∀ p, (mat_id * p)%vec = p.
Proof.
destruct_ac.
intros (x, y, z).
unfold mat_vec_mul; simpl.
progress repeat rewrite (rngl_mul_0_l Hos).
progress repeat rewrite rngl_mul_1_l.
progress repeat rewrite rngl_add_0_l.
progress repeat rewrite rngl_add_0_r.
easy.
Qed.

Theorem mat_const_mul_distr_l : ∀ k M₁ M₂,
  (k ⁎ (M₁ * M₂) = (k ⁎ M₁) * M₂)%mat.
Proof.
intros.
unfold mat_const_mul, mat_mul.
destruct M₁, M₂; simpl.
f_equal; ring.
Qed.

Theorem mat_vec_mul_assoc : ∀ m₁ m₂ p,
  ((m₁ * m₂)%mat * p = m₁ * (m₂ * p))%vec.
Proof.
intros m₁ m₂ (x, y, z).
unfold mat_vec_mul.
simpl; f_equal; ring.
Qed.

Theorem  mat_vec_mul_add_distr_l : ∀ M u v, (M * (u + v) = M * u + M * v)%vec.
Proof.
intros.
destruct u as (u₁, u₂, u₃).
destruct v as (v₁, v₂, v₃); simpl; f_equal; ring.
Qed.

Theorem  mat_vec_mul_const_distr : ∀ M k v, (M * (k ⁎ v) = k ⁎ (M * v))%vec.
Proof.
intros.
destruct v as (v₁, v₂, v₃); simpl; f_equal; ring.
Qed.

Theorem rot_rot_inv_x : (rot_x * rot_inv_x)%mat = mat_id.
Proof.
destruct_ac.
specialize (rngl_0_le_2 Hos Hto) as H02.
unfold mat_mul, mat_id; simpl.
progress unfold rngl_div.
rewrite Hiv.
progress repeat rewrite rngl_mul_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
assert (H30 : (1 + 2 ≠ 0)%L). {
  rewrite rngl_add_comm.
  apply (rngl_3_neq_0 Hos Hc1 Hto).
}
now f_equal; field.
Qed.

Theorem rot_inv_rot_x : (rot_inv_x * rot_x)%mat = mat_id.
Proof.
destruct_ac.
specialize (rngl_0_le_2 Hos Hto) as H02.
unfold mat_mul, mat_id, mkrmat; simpl.
unfold rngl_div; rewrite Hiv.
progress repeat rewrite rngl_mul_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
assert (H30 : (1 + 2 ≠ 0)%L). {
  specialize (rngl_characteristic_0 Hch 2) as H1.
  now cbn in H1; rewrite rngl_add_0_r in H1.
}
now f_equal; field.
Qed.

Theorem rot_rot_inv_z : (rot_z * rot_inv_z)%mat = mat_id.
Proof.
destruct_ac.
specialize (rngl_0_le_2 Hos Hto) as H02.
unfold mat_mul, mat_id, mkrmat; simpl.
unfold rngl_div; rewrite Hiv.
progress repeat rewrite rngl_mul_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
assert (H30 : (1 + 2 ≠ 0)%L). {
  specialize (rngl_characteristic_0 Hch 2) as H1.
  now cbn in H1; rewrite rngl_add_0_r in H1.
}
now f_equal; field.
Qed.

Theorem rot_inv_rot_z : (rot_inv_z * rot_z)%mat = mat_id.
Proof.
destruct_ac.
specialize (rngl_0_le_2 Hos Hto) as H02.
unfold mat_mul, mat_id, mkrmat; simpl.
unfold rngl_div; rewrite Hiv.
progress repeat rewrite rngl_mul_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
assert (H30 : (1 + 2 ≠ 0)%L). {
  specialize (rngl_characteristic_0 Hch 2) as H1.
  now cbn in H1; rewrite rngl_add_0_r in H1.
}
now f_equal; field.
Qed.

Theorem mat_of_elem_mul_negf_l : ∀ e,
  (mat_of_elem (negf e) * mat_of_elem e = mat_id)%mat.
Proof.
intros (t, d); simpl.
destruct t, d; simpl.
apply rot_rot_inv_x.
apply rot_inv_rot_x.
apply rot_rot_inv_z.
apply rot_inv_rot_z.
Qed.

Theorem mat_of_elem_mul_negf_r : ∀ e,
  (mat_of_elem e * mat_of_elem (negf e) = mat_id)%mat.
Proof.
intros (t, d); simpl.
destruct t, d; simpl.
apply rot_inv_rot_x.
apply rot_rot_inv_x.
apply rot_inv_rot_z.
apply rot_rot_inv_z.
Qed.

Definition mat_of_path el :=
  fold_right mat_mul mat_id (map mat_of_elem el).

Theorem rotate_vec_mul : ∀ el p,
  fold_right rotate p el = (mat_of_path el * p)%vec.
Proof.
intros el p.
unfold mat_of_path.
induction el as [| e]; [ rewrite mat_vec_mul_id; reflexivity | simpl ].
rewrite IHel, mat_vec_mul_assoc; reflexivity.
Qed.

Theorem rotate_rotate_neg : ∀ e p, rotate e (rotate (negf e) p) = p.
Proof.
intros (t, d) p; simpl.
unfold rotate; simpl.
rewrite <- mat_vec_mul_assoc.
destruct t, d; simpl.
 now rewrite rot_inv_rot_x, mat_vec_mul_id.
 now rewrite rot_rot_inv_x, mat_vec_mul_id.
 now rewrite rot_inv_rot_z, mat_vec_mul_id.
 now rewrite rot_rot_inv_z, mat_vec_mul_id.
Qed.

Theorem rotate_neg_rotate : ∀ e p, rotate (negf e) (rotate e p) = p.
Proof.
intros (t, d) p; simpl.
unfold rotate; simpl.
rewrite <- mat_vec_mul_assoc.
destruct t, d; simpl.
 now rewrite rot_rot_inv_x, mat_vec_mul_id.
 now rewrite rot_inv_rot_x, mat_vec_mul_id.
 now rewrite rot_rot_inv_z, mat_vec_mul_id.
 now rewrite rot_inv_rot_z, mat_vec_mul_id.
Qed.

Theorem rotate_cancel_in : ∀ el₁ el₂ e p,
  (mat_of_path (el₁ ++ e :: negf e :: el₂) * p)%vec =
  (mat_of_path (el₁ ++ el₂) * p)%vec.
Proof.
intros.
do 2 rewrite <- rotate_vec_mul.
do 2 rewrite fold_right_app; simpl.
now rewrite rotate_rotate_neg.
Qed.

Theorem rotate_rotate_norm : ∀ el p,
  (mat_of_path el * p)%vec = (mat_of_path (norm_list el) * p)%vec.
Proof.
intros el p.
remember (length el) as len eqn:Hlen; symmetry in Hlen.
revert el p Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct (norm_list_dec el) as [H₁| H₁]; [ now rewrite H₁ | ].
destruct H₁ as (el₁ & t & d & el₂ & H₁).
subst el.
rewrite rotate_cancel_in, norm_list_cancel_in.
destruct len; [ now destruct el₁ | ].
destruct len.
 destruct el₁; [ easy | simpl in Hlen ].
 now destruct el₁.

 apply IHlen with len.
  transitivity (S len); apply Nat.lt_succ_diag_r.

  clear - Hlen.
  revert len el₂ Hlen.
  induction el₁ as [| e₁]; intros.
   simpl in Hlen; simpl.
   now do 2 apply Nat.succ_inj in Hlen.

   simpl in Hlen; simpl.
   apply Nat.succ_inj in Hlen.
   destruct len.
    destruct el₁; [ easy | simpl in Hlen ].
    now destruct el₁.

    f_equal.
    now apply IHel₁.
Qed.

Definition mat_transp m :=
  mkrmat
   (a₁₁ m) (a₂₁ m) (a₃₁ m)
   (a₁₂ m) (a₂₂ m) (a₃₂ m)
   (a₁₃ m) (a₂₃ m) (a₃₃ m).

Definition mat_det m :=
  (a₁₁ m * (a₂₂ m * a₃₃ m - a₃₂ m * a₂₃ m) +
   a₁₂ m * (a₂₃ m * a₃₁ m - a₃₃ m * a₂₁ m) +
   a₁₃ m * (a₂₁ m * a₃₂ m - a₃₁ m * a₂₂ m))%L.

Arguments mat_transp m%_mat.
Arguments mat_det m%_mat.

Theorem mat_transp_id : mat_transp mat_id = mat_id.
Proof. easy. Qed.

Theorem mat_transp_mul : ∀ m₁ m₂,
  mat_transp (mat_mul m₁ m₂) = mat_mul (mat_transp m₂) (mat_transp m₁).
Proof.
intros m₁ m₂.
unfold mat_transp, mat_mul; simpl.
progress unfold mkrmat.
f_equal; ring.
Qed.

Theorem mat_transp_involutive : ∀ M, mat_transp (mat_transp M) = M.
Proof.
now intros; unfold mat_transp; destruct M.
Qed.

Theorem mat_mul_assoc : ∀ m₁ m₂ m₃,
  (m₁ * (m₂ * m₃) = m₁ * m₂ * m₃)%mat.
Proof.
intros m₁ m₂ m₃.
unfold mat_mul; simpl; f_equal; ring.
Qed.

Theorem mat_det_mul : ∀ m₁ m₂,
  mat_det (m₁ * m₂) = (mat_det m₂ * mat_det m₁)%L.
Proof.
intros m₁ m₂.
unfold mat_det; simpl; ring.
Qed.

Definition is_ortho_matrix A := mat_mul (mat_transp A) A = mat_id.
Definition is_rotation_matrix A := is_ortho_matrix A ∧ mat_det A = 1%L.

Arguments is_rotation_matrix A%_mat.

Theorem mat_id_is_rotation_matrix : is_rotation_matrix mat_id.
Proof.
split. {
  progress unfold is_ortho_matrix.
  now rewrite mat_transp_id, mat_mul_id_l.
}
unfold mat_det; simpl; ring.
Qed.

Theorem rot_x_is_rotation_matrix : is_rotation_matrix rot_x.
Proof.
destruct_ac.
specialize (rngl_0_le_2 Hos Hto) as H02.
progress unfold is_rotation_matrix.
progress unfold is_ortho_matrix.
progress unfold mat_transp, mat_mul, mat_det; simpl.
unfold mat_id, rngl_div; rewrite Hiv.
do 18 rewrite rngl_mul_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
rewrite Rmult5_sqrt2_sqrt5; [ | easy ].
assert (H30 : (1 + 2 ≠ 0)%L). {
  specialize (rngl_characteristic_0 Hch 2) as H1.
  now cbn in H1; rewrite rngl_add_0_r in H1.
}
split; [ now f_equal; try field | now field ].
Qed.

Theorem rot_inv_x_is_rotation_matrix : is_rotation_matrix rot_inv_x.
Proof.
destruct_ac.
specialize (rngl_0_le_2 Hos Hto) as H02.
assert (H30 : (1 + 2 ≠ 0)%L). {
  rewrite rngl_add_comm.
  apply (rngl_3_neq_0 Hos Hc1 Hto).
}
progress unfold is_rotation_matrix.
progress unfold is_ortho_matrix.
progress unfold rot_inv_x, mat_transp, mat_mul, mat_det; simpl.
progress unfold mat_id.
progress unfold rngl_div; rewrite Hiv.
progress repeat rewrite (rngl_mul_0_l Hos).
progress repeat rewrite (rngl_mul_0_r Hos).
progress repeat rewrite rngl_mul_1_l.
progress repeat rewrite rngl_add_0_l.
progress repeat rewrite rngl_add_0_r.
progress repeat rewrite rngl_mul_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | easy ]).
split; [ now f_equal; field | now field ].
Qed.

Theorem rot_z_is_rotation_matrix : is_rotation_matrix rot_z.
Proof.
destruct_ac.
specialize (rngl_0_le_2 Hos Hto) as H02.
assert (H30 : (1 + 2 ≠ 0)%L). {
  rewrite rngl_add_comm.
  apply (rngl_3_neq_0 Hos Hc1 Hto).
}
progress unfold is_rotation_matrix.
progress unfold is_ortho_matrix.
progress unfold mat_transp, mat_mul, mat_det; simpl.
progress unfold mat_id.
progress unfold rngl_div; rewrite Hiv.
progress repeat rewrite (rngl_mul_0_l Hos).
progress repeat rewrite (rngl_mul_0_r Hos).
progress repeat rewrite rngl_mul_1_l.
progress repeat rewrite rngl_mul_1_r.
progress repeat rewrite rngl_add_0_l.
progress repeat rewrite rngl_add_0_r.
progress repeat rewrite (rngl_sub_0_l Hop).
progress repeat rewrite (rngl_sub_0_r Hos).
progress repeat rewrite <- (rngl_mul_opp_l Hop).
progress repeat rewrite rngl_mul_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | easy ]).
split; [ now f_equal; field | now field ].
Qed.

Theorem rot_inv_z_is_rotation_matrix : is_rotation_matrix rot_inv_z.
Proof.
destruct_ac.
specialize (rngl_0_le_2 Hos Hto) as H02.
assert (H30 : (1 + 2 ≠ 0)%L). {
  rewrite rngl_add_comm.
  apply (rngl_3_neq_0 Hos Hc1 Hto).
}
progress unfold is_rotation_matrix.
progress unfold is_ortho_matrix.
progress unfold mat_transp, mat_mul, mat_det; simpl.
progress unfold mat_id.
progress unfold rngl_div; rewrite Hiv.
progress repeat rewrite (rngl_mul_0_l Hos).
progress repeat rewrite (rngl_mul_0_r Hos).
progress repeat rewrite rngl_mul_1_l.
progress repeat rewrite rngl_mul_1_r.
progress repeat rewrite rngl_add_0_l.
progress repeat rewrite rngl_add_0_r.
progress repeat rewrite (rngl_sub_0_l Hop).
progress repeat rewrite (rngl_sub_0_r Hos).
progress repeat rewrite <- (rngl_mul_opp_l Hop).
progress repeat rewrite rngl_mul_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | easy ]).
split; [ now f_equal; field | now field ].
Qed.

Theorem rotate_is_rotation_matrix : ∀ e, is_rotation_matrix (mat_of_elem e).
Proof.
intros (t, d); destruct t, d.
apply rot_inv_x_is_rotation_matrix.
apply rot_x_is_rotation_matrix.
apply rot_inv_z_is_rotation_matrix.
apply rot_z_is_rotation_matrix.
Qed.

Theorem mat_mul_is_rotation_matrix : ∀ m1 m2,
  is_rotation_matrix m1
  → is_rotation_matrix m2
  → is_rotation_matrix (m1 * m2).
Proof.
destruct_ac.
intros * (Hm1, Hd1) (Hm2, Hd2).
progress unfold is_rotation_matrix.
progress unfold is_ortho_matrix.
rewrite mat_transp_mul.
rewrite mat_mul_assoc.
setoid_rewrite <- mat_mul_assoc at 2.
rewrite Hm1, mat_mul_id_r, Hm2.
split; [ easy | ].
rewrite mat_det_mul, Hd1, Hd2.
apply rngl_mul_1_l.
Qed.

Theorem mat_pow_is_rotation_matrix : ∀ M n,
  is_rotation_matrix M → is_rotation_matrix (M ^ n).
Proof.
intros * HM.
induction n; [ apply mat_id_is_rotation_matrix | simpl ].
now apply mat_mul_is_rotation_matrix.
Qed.

Theorem mat_of_path_is_rotation_matrix : ∀ el,
 is_rotation_matrix (mat_of_path el).
Proof.
intros.
induction el as [| e el].
 unfold mat_of_path; simpl.
 apply mat_id_is_rotation_matrix.

 unfold mat_of_path; simpl; fold (mat_of_path el).
 apply mat_mul_is_rotation_matrix; [ apply rotate_is_rotation_matrix | easy ].
Qed.

Theorem mat_of_path_app : ∀ el₁ el₂,
  mat_of_path (el₁ ++ el₂) = (mat_of_path el₁ * mat_of_path el₂)%mat.
Proof.
intros.
revert el₁.
induction el₂ as [| e₂ el₂]; intros. {
  unfold mat_of_path at 3; simpl.
  rewrite app_nil_r.
  now rewrite mat_mul_id_r.
}
rewrite cons_comm_app, app_assoc, IHel₂.
unfold mat_of_path; simpl.
rewrite map_app, fold_right_app; simpl.
rewrite mat_mul_assoc; f_equal.
rewrite mat_mul_id_r.
induction el₁ as [| e₁]; [ now rewrite mat_mul_id_l | ].
now simpl; rewrite IHel₁, mat_mul_assoc.
Qed.

Theorem vec_const_mul_assoc : ∀ a b v, a ⁎ (b ⁎ v) = (a * b) ⁎ v.
Proof.
intros a b (x, y, z); simpl.
f_equal; apply rngl_mul_assoc.
Qed.

Theorem vec_const_mul_div : ∀ a b u v,
  a ≠ 0%L
  → a ⁎ u = b ⁎ v
  → u = (b / a) ⁎ v.
Proof.
destruct_ac.
intros * Ha Hm.
destruct u as (u₁, u₂, u₃).
destruct v as (v₁, v₂, v₃).
simpl in Hm; simpl.
injection Hm; clear Hm; intros H₃ H₂ H₁.
(**)
do 3 rewrite (rngl_div_mul_mul_div Hic Hiv).
rewrite <- H₁, <- H₂, <- H₃.
do 3 rewrite (rngl_mul_comm Hic a).
do 3 (rewrite (rngl_mul_div Hi1); [ | easy ]).
easy.
Qed.

Theorem nonneg_sqr_vec_norm : ∀ x y z, (0 ≤ x² + y² + z²)%L.
Proof.
destruct_ac.
intros.
apply (rngl_le_0_add Hos Hor).
apply (rngl_le_0_add Hos Hor).
apply (rngl_squ_nonneg Hos Hto).
apply (rngl_squ_nonneg Hos Hto).
apply (rngl_squ_nonneg Hos Hto).
Qed.

Theorem vec_norm_nonneg : ∀ v, (0 ≤ ‖v‖)%L.
Proof.
intros (x, y, z); simpl.
apply rl_sqrt_nonneg.
apply nonneg_sqr_vec_norm.
Qed.

Theorem vec_norm_opp : ∀ v, ‖(- v)‖ = ‖v‖.
Proof.
destruct_ac.
intros (x, y, z); simpl.
now do 3 rewrite (rngl_squ_opp Hop).
Qed.

Theorem vec_norm_vec_const_mul : ∀ a v, ‖(a ⁎ v)‖ = (rngl_abs a * ‖v‖)%L.
Proof.
destruct_ac.
intros a (x, y, z); simpl.
do 3 rewrite (rngl_squ_mul Hic).
do 2 rewrite <- rngl_mul_add_distr_l.
rewrite rl_sqrt_mul.
progress f_equal.
apply (rl_sqrt_squ Hop Hto).
apply (rngl_squ_nonneg Hos Hto).
apply nonneg_sqr_vec_norm.
Qed.

Theorem sqr_vec_norm_eq_0 : ∀ x y z,
  (x² + y² + z² = 0)%L
  → (x = 0 ∧ y = 0 ∧ z = 0)%L.
Proof.
destruct_ac.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros * H.
apply (rngl_eq_add_0 Hos Hor) in H.
destruct H as (H, H3).
apply (rngl_eq_add_0 Hos Hor) in H.
destruct H as (H1, H2).
now apply (eq_rngl_squ_0 Hos Hio) in H1, H2, H3.
apply (rngl_squ_nonneg Hos Hto).
apply (rngl_squ_nonneg Hos Hto).
apply (rngl_le_0_add Hos Hor).
apply (rngl_squ_nonneg Hos Hto).
apply (rngl_squ_nonneg Hos Hto).
apply (rngl_squ_nonneg Hos Hto).
Qed.

Theorem vec_norm_0 : ‖0‖ = 0%L.
Proof.
destruct_ac.
simpl; rewrite (rngl_squ_0 Hos).
do 2 rewrite rngl_add_0_l.
apply (rl_sqrt_0 Hop Hto Hii).
Qed.

Theorem vec_norm_eq_0 : ∀ v, ‖v‖ = 0%L ↔ v = 0%vec.
Proof.
destruct_ac.
intros.
split; intros Hv. {
  destruct v as (v₁, v₂, v₃); simpl in Hv.
  apply (eq_rl_sqrt_0 Hos) in Hv.
  apply sqr_vec_norm_eq_0 in Hv.
  now destruct Hv as (H1 & H2 & H3); subst.
  apply nonneg_sqr_vec_norm.
}
destruct v as (v₁, v₂, v₃); simpl.
injection Hv; clear Hv; intros; subst.
rewrite (rngl_squ_0 Hos).
do 2 rewrite rngl_add_0_r.
apply (rl_sqrt_0 Hop Hto Hii).
Qed.

Theorem vec_norm_neq_0 : ∀ v, ‖v‖ ≠ 0%L ↔ v ≠ 0%vec.
Proof.
intros v.
now split; intros H1 H2; apply vec_norm_eq_0 in H2.
Qed.

Theorem vec_norm_pos : ∀ v, v ≠ 0%vec → (0 < ‖v‖)%L.
Proof.
destruct_ac.
intros * Hv.
specialize (vec_norm_nonneg v) as H.
apply vec_norm_neq_0 in Hv.
now apply rngl_le_neq.
Qed.

Theorem vec_add_0_r : ∀ v, (v + 0 = v)%vec.
Proof.
intros (x, y, z); simpl; f_equal; apply rngl_add_0_r.
Qed.

Theorem vec_sub_0_r : ∀ v, (v - 0 = v)%vec.
Proof.
destruct_ac.
intros (x, y, z); cbn; f_equal; rewrite (rngl_opp_0 Hop); apply rngl_add_0_r.
Qed.

Theorem vec_const_mul_0_l : ∀ v, (0 ⁎ v = 0)%vec.
Proof.
destruct_ac.
intros (x, y, z); simpl.
now do 3 rewrite (rngl_mul_0_l Hos).
Qed.

Theorem vec_const_mul_0_r : ∀ a, (a ⁎ 0 = 0)%vec.
Proof.
destruct_ac.
intros x; simpl.
now rewrite (rngl_mul_0_r Hos).
Qed.

Theorem vec_const_mul_1_l : ∀ v, 1 ⁎ v = v.
Proof.
destruct_ac.
intros (x, y, z).
unfold vec_const_mul.
now f_equal; rewrite rngl_mul_1_l.
Qed.

Theorem neg_vec_involutive : ∀ p, (- - p)%vec = p.
Proof.
destruct_ac.
intros (x, y, z); simpl.
now f_equal; rewrite (rngl_opp_involutive Hop).
Qed.

Theorem is_neg_vec_neg_vec : ∀ v,
  v ≠ 0%vec
  → is_neg_vec (- v) = negb (is_neg_vec v).
Proof.
destruct_ac.
intros (x, y, z) Hv; simpl.
destruct (rngl_ltb_dec x 0) as [Hx| Hx]; rewrite Hx. {
  destruct (rngl_ltb_dec (-x) 0) as [Hx'| Hx']; rewrite Hx'. {
    rewrite (rngl_ltb_opp_l Hop Hto) in Hx'.
    rewrite (rngl_opp_0 Hop) in Hx'.
    apply (rngl_ltb_lt Heo) in Hx, Hx'.
    now apply (rngl_lt_asymm Hor) in Hx.
  }
  clear Hx'.
  destruct (rngl_ltb_dec 0 (-x)) as [Hx'| Hx']; rewrite Hx'; [ easy | ].
  rewrite (rngl_ltb_opp_r Hop Hto) in Hx'.
  rewrite (rngl_opp_0 Hop) in Hx'.
  congruence.
}
destruct (rngl_ltb_dec (-x) 0) as [Hx'| Hx']; rewrite Hx'. {
  rewrite (rngl_ltb_opp_l Hop Hto) in Hx'.
  rewrite (rngl_opp_0 Hop) in Hx'.
  now rewrite Hx'.
}
rewrite (rngl_ltb_opp_l Hop Hto) in Hx'.
rewrite (rngl_opp_0 Hop) in Hx'.
apply (rngl_ltb_ge_iff Hto) in Hx, Hx'.
apply (rngl_le_antisymm Hor) in Hx; [ | easy ].
subst x.
rewrite (rngl_opp_0 Hop).
rewrite (rngl_ltb_ge Hor); [ clear Hx' | easy ].
destruct (rngl_ltb_dec y 0) as [Hy| Hy]; rewrite Hy. {
  destruct (rngl_ltb_dec (-y) 0) as [Hy'| Hy']; rewrite Hy'. {
    rewrite (rngl_ltb_opp_l Hop Hto) in Hy'.
    rewrite (rngl_opp_0 Hop) in Hy'.
    apply (rngl_ltb_lt Heo) in Hy, Hy'.
    now apply (rngl_lt_asymm Hor) in Hy.
  }
  clear Hy'.
  destruct (rngl_ltb_dec 0 (-y)) as [Hy'| Hy']; rewrite Hy'; [ easy | ].
  rewrite (rngl_ltb_opp_r Hop Hto) in Hy'.
  rewrite (rngl_opp_0 Hop) in Hy'.
  congruence.
}
destruct (rngl_ltb_dec (-y) 0) as [Hy'| Hy']; rewrite Hy'. {
  rewrite (rngl_ltb_opp_l Hop Hto) in Hy'.
  rewrite (rngl_opp_0 Hop) in Hy'.
  now rewrite Hy'.
}
rewrite (rngl_ltb_opp_l Hop Hto) in Hy'.
rewrite (rngl_opp_0 Hop) in Hy'.
apply (rngl_ltb_ge_iff Hto) in Hy, Hy'.
apply (rngl_le_antisymm Hor) in Hy; [ | easy ].
subst y.
rewrite (rngl_opp_0 Hop).
rewrite (rngl_ltb_ge Hor); [ clear Hy' | easy ].
destruct (rngl_ltb_dec z 0) as [Hz| Hz]; rewrite Hz. {
  destruct (rngl_ltb_dec (-z) 0) as [Hz'| Hz']; rewrite Hz'. {
    rewrite (rngl_ltb_opp_l Hop Hto) in Hz'.
    rewrite (rngl_opp_0 Hop) in Hz'.
    apply (rngl_ltb_lt Heo) in Hz, Hz'.
    now apply (rngl_lt_asymm Hor) in Hz.
  }
  clear Hz'.
  destruct (rngl_ltb_dec 0 (-z)) as [Hz'| Hz']; rewrite Hz'; [ easy | ].
  rewrite (rngl_ltb_opp_r Hop Hto) in Hz'.
  rewrite (rngl_opp_0 Hop) in Hz'.
  congruence.
}
destruct (rngl_ltb_dec (-z) 0) as [Hz'| Hz']; rewrite Hz'. {
  rewrite (rngl_ltb_opp_l Hop Hto) in Hz'.
  rewrite (rngl_opp_0 Hop) in Hz'.
  now rewrite Hz'.
}
rewrite (rngl_ltb_opp_l Hop Hto) in Hz'.
rewrite (rngl_opp_0 Hop) in Hz'.
apply (rngl_ltb_ge_iff Hto) in Hz, Hz'.
apply (rngl_le_antisymm Hor) in Hz; [ | easy ].
subst z.
rewrite (rngl_opp_0 Hop).
rewrite (rngl_ltb_ge Hor); [ clear Hz' | easy ].
easy.
Qed.

Theorem vec_add_assoc : ∀ u v w, (u + (v + w))%vec = (u + v + w)%vec.
Proof.
intros.
destruct u as (u₁, u₂, u₃).
destruct v as (v₁, v₂, v₃).
destruct w as (w₁, w₂, w₃).
simpl; f_equal; apply rngl_add_assoc.
Qed.

Theorem vec_add_opp_diag_l : ∀ v, (- v + v = 0)%vec.
Proof.
destruct_ac.
intros (v₁, v₂, v₃); simpl; f_equal; apply (rngl_add_opp_diag_l Hop).
Qed.

Theorem vec_add_opp_diag_r : ∀ v, (v + - v = 0)%vec.
Proof.
destruct_ac.
intros (v₁, v₂, v₃); simpl; f_equal; apply (rngl_add_opp_diag_r Hop).
Qed.

Theorem vec_sub_diag : ∀ v, (v - v = 0)%vec.
Proof.
destruct_ac.
intros (v₁, v₂, v₃); simpl; f_equal; apply (rngl_add_opp_diag_r Hop).
Qed.

Theorem vec_sub_diag_uniq : ∀ u v, (u - v = 0)%vec → u = v.
Proof.
destruct_ac.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) Huv.
injection Huv; clear Huv; intros H1 H2 H3.
rewrite (rngl_add_opp_r Hop) in H1, H2, H3.
apply -> (rngl_sub_move_0_r Hop) in H1.
apply -> (rngl_sub_move_0_r Hop) in H2.
apply -> (rngl_sub_move_0_r Hop) in H3.
now subst.
Qed.

Theorem vec_sub_opp_r : ∀ u v, (u - - v = u + v)%vec.
Proof.
destruct_ac.
intros (u₁, u₂, u₃) (v₁, v₂, v₃).
cbn; do 2 f_equal; apply (rngl_opp_involutive Hop).
Qed.

Theorem vec_sub_sub_distr : ∀ u v w, (u - (v - w) = u - v + w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); cbn.
f_equal; ring.
Qed.

Theorem vec_const_mul_cross_distr_l : ∀ k u v, k ⁎ (u × v) = (k ⁎ u) × v.
Proof.
intros k (u₁, u₂, u₃) (v₁, v₂, v₃); simpl.
f_equal; ring.
Qed.

Theorem vec_const_mul_cross_distr_r : ∀ k u v, k ⁎ (u × v) = u × (k ⁎ v).
Proof.
intros k (u₁, u₂, u₃) (v₁, v₂, v₃); simpl.
f_equal; ring.
Qed.

Theorem vec_dot_mul_0_l : ∀ v : vector T, 0 · v = 0%L.
Proof.
intros (x₁, y₁, z₁); simpl; ring.
Qed.

Theorem vec_dot_mul_0_r : ∀ v, (v · 0)%vec = 0%L.
Proof.
intros (x, y, z); simpl; ring.
Qed.

Theorem vec_dot_mul_sub_distr_l : ∀ u v w,
  u · (v - w) = (u · v - u · w)%L.
Proof.
intros (x₁, y₁, z₁) (x₂, y₂, z₂) (x₃, y₃, z₃); simpl; ring.
Qed.

Theorem Rmult_vec_dot_mul_distr_l : ∀ a u v, (a * (u · v))%L = a ⁎ u · v.
Proof.
intros a (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; ring.
Qed.

Theorem Rmult_vec_dot_mul_distr_r : ∀ a u v, (a * (u · v))%L = u · a ⁎ v.
Proof.
intros a (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; ring.
Qed.

Theorem vec_dot_mul_diag : ∀ v, v · v = ‖v‖².
Proof.
destruct_ac.
intros (x, y, z); simpl.
symmetry.
apply rngl_squ_sqrt.
apply (rngl_le_0_add Hos Hor).
apply (rngl_le_0_add Hos Hor).
apply (rngl_mul_diag_nonneg Hos Hto).
apply (rngl_mul_diag_nonneg Hos Hto).
apply (rngl_mul_diag_nonneg Hos Hto).
Qed.

Theorem vec_add_comm : ∀ u v, (u + v = v + u)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl.
f_equal; ring.
Qed.

Theorem vec_cross_mul_assoc_r : ∀ u v w,
  (u × (v × w) = (u · w) ⁎ v - (u · v) ⁎ w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; ring.
Qed.

Theorem vec_opp_dot_mul_distr_r : ∀ u v, (- (u · v))%L = u · - v.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; ring.
Qed.

Theorem vec_opp_const_mul_distr_l : ∀ a v, (- (a ⁎ v) = - a ⁎ v)%vec.
Proof.
intros a (v₁, v₂, v₃); simpl; f_equal; ring.
Qed.

Theorem vec_opp_const_mul_distr_r : ∀ a v, (- (a ⁎ v) = a ⁎ - v)%vec.
Proof.
intros a (v₁, v₂, v₃); simpl; f_equal; ring.
Qed.

Theorem vec_const_mul_add_distr_l : ∀ a u v,
  (a ⁎ (u + v) = a ⁎ u + a ⁎ v)%vec.
Proof.
intros a (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; f_equal; ring.
Qed.

Theorem vec_const_mul_sub_distr_l : ∀ a u v,
  (a ⁎ (u - v) = a ⁎ u - a ⁎ v)%vec.
Proof.
intros a (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; f_equal; ring.
Qed.

Theorem vec_const_mul_eq_reg_l : ∀ a u v, a ⁎ u = a ⁎ v → a ≠ 0%L → u = v.
Proof.
destruct_ac.
assert (Hip : rngl_has_inv_or_pdiv_and_comm T = true). {
  progress unfold rngl_has_inv_or_pdiv_and_comm.
  now rewrite Hiv.
}
intros a (u₁, u₂, u₃) (v₁, v₂, v₃) Hauv Ha.
simpl in Hauv.
injection Hauv; clear Hauv; intros H₃ H₂ H₁.
apply (rngl_mul_cancel_l Hip) in H₁; [ | easy ].
apply (rngl_mul_cancel_l Hip) in H₂; [ | easy ].
apply (rngl_mul_cancel_l Hip) in H₃; [ | easy ].
now subst.
Qed.

Theorem mat_vec_mul_0_r : ∀ M, (M * 0)%vec = 0%vec.
Proof.
destruct_ac.
intros; simpl.
do 9 rewrite (rngl_mul_0_r Hos).
now do 2 rewrite rngl_add_0_l.
Qed.

Theorem mat_pow_succ : ∀ M n, (M ^ S n)%mat = (M * M ^ n)%mat.
Proof. easy. Qed.

Theorem vec_sqr_0 : 0²%vec = 0%L.
Proof. cbn; ring. Qed.

Theorem vec_sqr_const_mul : ∀ a v, (a ⁎ v)²%vec = (a² * v²%vec)%L.
Proof.
intros a (v₁, v₂, v₃); simpl; unfold rngl_squ; ring.
Qed.

Theorem normalized_vector : ∀ u v, u ≠ 0%vec → v = ‖u‖⁻¹ ⁎ u → ‖v‖ = 1%L.
Proof.
destruct_ac.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) Hu Hv.
simpl in Hv; simpl.
injection Hv; clear Hv; intros H₃ H₂ H₁.
remember (√ (u₁² + u₂² + u₃²)) as ur eqn:Hur.
assert (H : ur ≠ 0%L). {
  intros H; subst ur.
  apply (eq_rl_sqrt_0 Hos) in H; [ | apply nonneg_sqr_vec_norm ].
  apply sqr_vec_norm_eq_0 in H.
  destruct H as (H1 & H2 & H3).
  now subst.
}
subst v₁ v₂ v₃.
do 3 rewrite (rngl_squ_mul Hic).
do 2 rewrite <- rngl_mul_add_distr_l.
rewrite rl_sqrt_mul; [ | | apply nonneg_sqr_vec_norm ]. 2: {
  apply (rngl_squ_nonneg Hos Hto).
}
rewrite <- Hur.
rewrite (rl_sqrt_squ Hop Hto).
rewrite (rngl_abs_nonneg_eq Hop Hor). 2: {
  apply rngl_lt_le_incl.
  apply (rngl_inv_pos Hop Hiv Hto).
  apply rngl_le_neq.
  split; [ | easy ].
  rewrite Hur.
  apply rl_sqrt_nonneg.
  apply nonneg_sqr_vec_norm.
}
now apply (rngl_mul_inv_diag_l Hiv).
Qed.

Theorem vec_div_vec_norm : ∀ v, v ≠ 0%vec → ‖(v ⁄ ‖v‖)‖ = 1%L.
Proof.
intros * Hv.
eapply normalized_vector; [ eassumption | easy ].
Qed.

(* Inversion of vectors and matrices *)

Definition vec_inv M '(V x y z) :=
  V (mat_det (mkrmat x (a₁₂ M) (a₁₃ M) y (a₂₂ M) (a₂₃ M) z (a₃₂ M) (a₃₃ M)))
    (mat_det (mkrmat (a₁₁ M) x (a₁₃ M) (a₂₁ M) y (a₂₃ M) (a₃₁ M) z (a₃₃ M)))
    (mat_det (mkrmat (a₁₁ M) (a₁₂ M) x (a₂₁ M) (a₂₂ M) y (a₃₁ M) (a₃₂ M) z)).

Definition mat_compl M :=
  let '(V b₁₁ b₂₁ b₃₁) := vec_inv M (V 1 0 0) in
  let '(V b₁₂ b₂₂ b₃₂) := vec_inv M (V 0 1 0) in
  let '(V b₁₃ b₂₃ b₃₃) := vec_inv M (V 0 0 1) in
  mkrmat b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃.

Theorem mat_mul_compl_l : ∀ M, (mat_compl M * M = mat_det M ⁎ mat_id)%mat.
Proof.
destruct_ac.
intros.
destruct M; simpl.
unfold mat_mul; simpl.
unfold mat_det; simpl.
unfold mat_const_mul; simpl.
do 9 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_diag Hos).
do 10 rewrite (rngl_mul_0_r Hos).
rewrite (rngl_sub_diag Hos).
do 3 rewrite (rngl_mul_0_r Hos).
do 9 rewrite rngl_mul_1_l.
do 7 rewrite rngl_mul_1_r.
do 5 rewrite rngl_add_0_l.
do 7 rewrite rngl_add_0_r.
do 6 rewrite (rngl_sub_0_r Hos).
do 6 rewrite (rngl_sub_0_l Hop).
f_equal; ring.
Qed.

Theorem mat_det_id : mat_det mat_id = 1%L.
Proof.
unfold mat_det, mat_id; simpl; ring.
Qed.

Theorem mat_det_mul_distr : ∀ M₁ M₂,
  mat_det (M₁ * M₂) = (mat_det M₁ * mat_det M₂)%L.
Proof.
intros; unfold mat_mul, mat_det; simpl; ring.
Qed.

Theorem mat_const_mul_assoc : ∀ a b M, (a ⁎ (b ⁎ M) = (a * b)%L ⁎ M)%mat.
Proof.
intros; unfold mat_const_mul; simpl; f_equal; apply rngl_mul_assoc.
Qed.

Theorem mat_const_mul_1_l : ∀ M, (1%L ⁎ M = M)%mat.
Proof.
destruct_ac.
intros; unfold mat_const_mul, mkrmat; destruct M; simpl.
now do 9 rewrite rngl_mul_1_l.
Qed.

Theorem mat_mul_id_comm : ∀ M M',
  (M * M')%mat = mat_id
  → (M' * M)%mat = mat_id.
Proof.
destruct_ac.
intros * HMM'.
generalize HMM'; intros H.
apply (f_equal (mat_mul (mat_compl M))) in H.
rewrite mat_mul_id_r in H.
rewrite mat_mul_assoc in H.
rewrite mat_mul_compl_l in H.
rewrite <- mat_const_mul_distr_l in H.
rewrite mat_mul_id_l in H.
apply (f_equal mat_det) in HMM'.
rewrite mat_det_id in HMM'.
rewrite mat_det_mul_distr in HMM'.
destruct (rngl_eqb_dec (mat_det M) 0) as [Hd| Hd]. {
  apply (rngl_eqb_eq Heo) in Hd.
  rewrite Hd, (rngl_mul_0_l Hos) in HMM'.
  symmetry in HMM'.
  now apply (rngl_1_neq_0 Hc1) in HMM'.
}
apply (rngl_eqb_neq Heo) in Hd.
apply (f_equal (mat_const_mul (mat_det M)⁻¹)) in H.
rewrite mat_const_mul_assoc in H.
rewrite (rngl_mul_inv_diag_l Hiv) in H; [ | easy ].
rewrite mat_const_mul_1_l in H.
rewrite H.
rewrite <- mat_const_mul_distr_l.
rewrite mat_mul_compl_l.
rewrite mat_const_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hiv); [ | easy ].
apply mat_const_mul_1_l.
Qed.

Theorem rotation_transp_is_rotation : ∀ M,
  is_rotation_matrix M → is_rotation_matrix (mat_transp M).
Proof.
intros M HM.
destruct HM as (Htr, Hdet).
split. {
  progress unfold is_ortho_matrix.
  rewrite mat_transp_involutive.
  now apply mat_mul_id_comm.
}
clear Htr.
unfold mat_det in Hdet; simpl in Hdet.
unfold mat_det, mat_transp; simpl.
rewrite <- Hdet.
ring.
Qed.

(* Cauchy-Schwarz inequality with vectors. *)

Theorem vec_Lagrange_identity : ∀ u v,
  (‖u‖² * ‖v‖² - (u · v)²)%L = (u × v)²%vec.
Proof.
destruct_ac.
intros (u₁, u₂, u₃) (v₁, v₂, v₃).
simpl.
rewrite rngl_squ_sqrt; [ | apply nonneg_sqr_vec_norm ].
rewrite rngl_squ_sqrt; [ | apply nonneg_sqr_vec_norm ].
unfold rngl_squ; ring.
Qed.

Arguments vec_Lagrange_identity u%_vec v%_vec.

Theorem vec_Cauchy_Schwarz_inequality : ∀ u v, ((u · v)² ≤ ‖u‖² * ‖v‖²)%L.
Proof.
destruct_ac.
intros.
apply (rngl_le_0_sub Hop Hor).
rewrite vec_Lagrange_identity.
rewrite vec_dot_mul_diag.
apply (rngl_squ_nonneg Hos Hto).
Qed.

(* *)

(* Non-nul vector belonging to the axis of rotation.
   Works for rotations angles different from 0 and π,
   i.e. transpositor ≠ 0 (a "transpositor" is a name I
   give to a vector which is nul iff the matrix is equal
   to its transpose; this name is inspired from the
   name "commutator") *)
Definition rotation_axis (M : matrix T) :=
  let x := (a₃₂ M - a₂₃ M)%L in
  let y := (a₁₃ M - a₃₁ M)%L in
  let z := (a₂₁ M - a₁₂ M)%L in
  V x y z.

Definition vec_normalize v := v ⁄ ‖v‖.

Definition rotation_unit_axis (M : matrix T) :=
  vec_normalize (rotation_axis M).

Definition rotation_fixpoint (m : matrix T) k :=
  k ⁎ rotation_unit_axis m.

Definition matrix_of_unit_axis_angle '(V x y z, s, c) :=
  mkrmat
    (x²*(1-c)+c) (x*y*(1-c)-z*s) (x*z*(1-c)+y*s)
    (x*y*(1-c)+z*s) (y²*(1-c)+c) (y*z*(1-c)-x*s)
    (x*z*(1-c)-y*s) (y*z*(1-c)+x*s) (z²*(1-c)+c).

Definition matrix_of_axis_angle '(V x y z) s c :=
  let r := √ (x² + y² + z²) in
  let ux := (x / r)%L in
  let uy := (y / r)%L in
  let uz := (z / r)%L in
  matrix_of_unit_axis_angle (V ux uy uz, s, c).

Arguments matrix_of_axis_angle pat%_vec (s c)%_L.

Theorem matrix_mul_axis : ∀ p c s k,
  p ≠ 0%vec
  → k ≠ 0%L
  → matrix_of_axis_angle p s c =
    matrix_of_axis_angle (k ⁎ p) (rngl_sign k * s) c.
Proof.
destruct_ac.
intros * Hpz Hk.
destruct p as (xp, yp, zp); simpl.
remember (√ ((k * xp)² + (k * yp)² + (k * zp)²)) as a eqn:Ha.
do 3 rewrite (rngl_squ_mul Hic) in Ha.
do 2 rewrite <- rngl_mul_add_distr_l in Ha.
rewrite rl_sqrt_mul in Ha; [ | | apply nonneg_sqr_vec_norm ]. 2: {
  apply (rngl_squ_nonneg Hos Hto).
}
remember (√ (xp² + yp² + zp²)) as b eqn:Hb.
assert (Hbz : b ≠ 0%L). {
  subst b; intros H.
  apply (eq_rl_sqrt_0 Hos) in H; [ | apply nonneg_sqr_vec_norm ].
  apply sqr_vec_norm_eq_0 in H.
  destruct H as (H1 & H2 & H3).
  now rewrite H1, H2, H3 in Hpz.
}
unfold rngl_sign, rngl_signp.
destruct (rngl_eqb_dec k 0) as [Hkz| Hkz]; rewrite Hkz; [ | clear Hkz ]. {
  now apply rngl_eqb_eq in Hkz.
}
rewrite (rl_sqrt_squ Hop Hto) in Ha.
destruct (rngl_leb_dec 0 k) as [H| H]; rewrite H. {
  rename H into Hkp.
  apply rngl_leb_le in Hkp.
  rewrite rngl_mul_1_l.
  assert (Hx : ∀ x, (k * x / a = x / b)%L). {
    intros x; subst a.
    rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
    do 2 rewrite (rngl_mul_comm Hic k).
    rewrite <- (rngl_div_div Hos Hiv); [ | easy | easy ].
    progress f_equal.
    now apply (rngl_mul_div Hi1).
  }
  now do 3 rewrite Hx.
} {
  rename H into Hkn.
  apply rngl_leb_nle in Hkn.
  apply (rngl_nle_gt_iff Hto) in Hkn.
  apply rngl_lt_le_incl in Hkn.
  assert (Hx : ∀ x, (k * x / a = - (x / b))%L). {
    intros x; subst a.
    rewrite (rngl_abs_nonpos_eq Hop Hto); [ | easy ].
    rewrite (rngl_mul_opp_l Hop).
    rewrite (rngl_div_opp_r Hop Hiv). 2: {
      now apply (rngl_neq_mul_0 Hos Hiq).
    }
    progress f_equal.
    do 2 rewrite (rngl_mul_comm Hic k).
    rewrite <- (rngl_div_div Hos Hiv); [ | easy | easy ].
    progress f_equal.
    now apply (rngl_mul_div Hi1).
  }
  do 3 rewrite Hx.
  do 3 rewrite (rngl_squ_opp Hop).
  do 3 rewrite rngl_mul_assoc.
  do 6 rewrite (rngl_mul_opp_opp Hop).
  do 3 rewrite rngl_mul_1_r.
  easy.
}
Qed.

Theorem unit_sphere_mat_mul_angle_add : ∀ a s₁ c₁ s₂ c₂ θ₁ θ₂,
  ‖a‖ = 1%L
  → (s₁² + c₁² = 1)%L
  → (s₂² + c₂² = 1)%L
  → θ₁ = angle_of_sin_cos s₁ c₁
  → θ₂ = angle_of_sin_cos s₂ c₂
  → (matrix_of_axis_angle a s₁ c₁ * matrix_of_axis_angle a s₂ c₂)%mat =
     matrix_of_axis_angle a (rngl_sin (θ₁ + θ₂)) (rngl_cos (θ₁ + θ₂)).
Proof.
destruct_ac.
intros * Ha Hsc₁ Hsc₂ Hθ₁ Hθ₂.
destruct a as (ax, ay, az); simpl.
simpl in Ha; rewrite Ha.
do 3 rewrite Rdiv_1_r.
unfold mat_mul; simpl.
apply (f_equal rngl_squ) in Ha.
rewrite rngl_squ_1 in Ha.
rewrite rngl_squ_sqrt in Ha; [ | apply nonneg_sqr_vec_norm ].
rewrite Hθ₁, Hθ₂.
rewrite rngl_cos_angle_of_sin_cos; [ | easy ].
rewrite rngl_cos_angle_of_sin_cos; [ | easy ].
rewrite rngl_sin_angle_of_sin_cos; [ | easy ].
rewrite rngl_sin_angle_of_sin_cos; [ | easy ].
clear θ₁ θ₂ Hθ₁ Hθ₂ Hsc₁ Hsc₂.
progress unfold mkrmat.
(**)
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H20.
f_equal; ring_simplify; fold_rngl. {
  do 4 rewrite <- (rngl_mul_assoc _ _ az).
  do 4 rewrite <- (rngl_mul_assoc _ _ ay).
  do 3 rewrite <- (rngl_mul_assoc _ _ ax).
  rewrite (fold_rngl_squ az).
  rewrite (fold_rngl_squ ay).
  rewrite (fold_rngl_squ ax).
  remember ax² as x eqn:H; clear H.
  remember ay² as y eqn:H; clear H.
  remember az² as z eqn:H; clear H.
  apply (rngl_add_move_l Hop) in Ha.
  subst z.
  ring.
} {
  rewrite (fold_rngl_squ ay).
  rewrite (fold_rngl_squ ax).
  do 4 rewrite <- (rngl_mul_assoc _ az az).
  rewrite (fold_rngl_squ az).
  rewrite <- (rngl_mul_assoc _ ax ax).
  rewrite (fold_rngl_squ ax).
  apply (rngl_add_move_l Hop) in Ha.
  rewrite Ha; clear Ha.
  ring.
} {
  rewrite (fold_rngl_squ ax).
  rewrite (fold_rngl_squ az).
  do 4 rewrite <- (rngl_mul_assoc _ ay ay).
  rewrite (fold_rngl_squ ay).
  rewrite <- (rngl_mul_assoc _ ax ax).
  rewrite (fold_rngl_squ ax).
  apply (rngl_add_move_l Hop) in Ha.
  rewrite Ha; clear Ha.
  ring.
} {
  rewrite (fold_rngl_squ ax).
  rewrite (fold_rngl_squ ay).
  do 2 rewrite <- (rngl_mul_assoc _ az az).
  rewrite (fold_rngl_squ az).
  apply (rngl_add_move_l Hop) in Ha.
  rewrite Ha; clear Ha.
  ring.
} {
  rewrite (fold_rngl_squ ax).
  rewrite (fold_rngl_squ ay).
  do 2 rewrite <- (rngl_mul_assoc _ az az).
  rewrite (fold_rngl_squ az).
  rewrite <- (rngl_mul_assoc _ ay ay).
  rewrite (fold_rngl_squ ay).
  apply (rngl_add_move_l Hop) in Ha.
  rewrite Ha; clear Ha.
  ring.
} {
  rewrite (fold_rngl_squ ax).
  rewrite <- (rngl_mul_assoc _ ay ay).
  rewrite <- (rngl_mul_assoc _ az az).
  rewrite (fold_rngl_squ ay).
  rewrite (fold_rngl_squ az).
  apply (rngl_add_move_l Hop) in Ha.
  rewrite Ha; clear Ha.
  ring.
} {
  do 7 rewrite (rngl_mul_opp_l Hop).
  rewrite (fold_rngl_squ ax).
  do 2 rewrite <- (rngl_mul_assoc _ ay ay).
  rewrite (fold_rngl_squ ay).
  rewrite (fold_rngl_squ az).
  apply (rngl_add_move_l Hop) in Ha.
  rewrite Ha; clear Ha.
  ring.
} {
  rewrite (fold_rngl_squ ax).
  rewrite <- (rngl_mul_assoc _ ay ay).
  rewrite <- (rngl_mul_assoc _ az az).
  rewrite (fold_rngl_squ ay).
  rewrite (fold_rngl_squ az).
  apply (rngl_add_move_l Hop) in Ha.
  rewrite Ha; clear Ha.
  ring.
} {
  rewrite (fold_rngl_squ ax).
  do 2 rewrite <- (rngl_mul_assoc _ ay ay).
  rewrite <- (rngl_mul_assoc _ az az).
  rewrite (fold_rngl_squ ay).
  rewrite (fold_rngl_squ az).
  apply (rngl_add_move_l Hop) in Ha.
  rewrite Ha; clear Ha.
  ring.
}
Qed.

Theorem unit_sphere_matrix_of_mul_angle : ∀ a s c θ s' c' n,
  ‖a‖ = 1%L
  → (s² + c² = 1)%L
  → θ = angle_of_sin_cos s c
  → s' = rngl_sin (n * θ)
  → c' = rngl_cos (n * θ)
  → matrix_of_axis_angle a s' c' = (matrix_of_axis_angle a s c ^ n)%mat.
Proof.
destruct_ac.
intros * Ha Hsc Hθ Hs' Hc'.
revert s' c' Hs' Hc'.
induction n; intros. {
  simpl in Hs', Hc'; simpl.
  subst s' c'.
  destruct a as (ax, ay, az); cbn.
  cbn in Ha; rewrite Ha.
  unfold mat_id, mkrmat.
  f_equal; ring.
}
cbn in Hs', Hc'.
rename s' into s''; rename c' into c''.
rename Hs' into Hs''; rename Hc' into Hc''.
remember (rngl_sin (n * θ)) as s' eqn:Hs' in Hs'', Hc''.
remember (rngl_cos (n * θ)) as c' eqn:Hc' in Hs'', Hc''.
specialize (IHn _ _ Hs' Hc').
rewrite mat_pow_succ, <- IHn.
assert (Hsc' : (c'² + s'² = 1)%L) by (subst s' c'; apply cos2_sin2_1).
rewrite rngl_add_comm in Hsc'.
erewrite unit_sphere_mat_mul_angle_add; try easy.
rewrite rngl_sin_add, rngl_cos_add.
rewrite rngl_sin_angle_of_sin_cos; [ | easy ].
rewrite rngl_sin_angle_of_sin_cos; [ | easy ].
rewrite rngl_cos_angle_of_sin_cos; [ | easy ].
rewrite rngl_cos_angle_of_sin_cos; [ | easy ].
rewrite Hs'', Hc'', Hs', Hc'.
rewrite Hθ.
rewrite rngl_sin_angle_of_sin_cos; [ | easy ].
rewrite rngl_cos_angle_of_sin_cos; [ | easy ].
 easy.
Qed.

Theorem fold_vec_norm : ∀ x y z, √(x² + y² + z²) = vec_norm (V x y z).
Proof. easy. Qed.

Theorem matrix_of_mul_angle : ∀ a s c θ s' c' n,
  a ≠ 0%vec
  → (s² + c² = 1)%L
  → θ = angle_of_sin_cos s c
  → s' = rngl_sin (n * θ)
  → c' = rngl_cos (n * θ)
  → matrix_of_axis_angle a s' c' =
     (matrix_of_axis_angle a s c ^ n)%mat.
Proof.
destruct_ac.
intros * Ha Hsc Hθ Hs' Hc'.
assert (Haz : ‖a‖ ≠ 0%L) by now apply vec_norm_neq_0.
assert (Haiz : ‖a‖⁻¹ ≠ 0%L) by now apply (rngl_inv_neq_0 Hos Hiv).
assert (Hap : (0 < ‖a‖)%L). {
  apply rngl_le_neq.
  split; [ apply (vec_norm_nonneg a) | easy ].
}
assert (Haa : (‖(a ⁄ ‖a‖)‖ = 1)%L) by now apply vec_div_vec_norm.
eapply unit_sphere_matrix_of_mul_angle in Haa; try eassumption.
remember (a ⁄ ‖a‖) as b eqn:Hb.
remember (matrix_of_axis_angle b s c) as M eqn:HM.
remember (matrix_of_axis_angle b s' c') as M' eqn:HM'.
move M' before M.
move b before a.
assert (Hbz : b ≠ 0%vec). {
  intros H.
  move H at top; subst b.
  symmetry in Hb.
  destruct a as (x, y, z).
  cbn in Hb.
  injection Hb; clear Hb; intros H3 H2 H1.
  rewrite fold_vec_norm in H1, H2, H3.
  apply (rngl_eq_mul_0_l Hos Hiq) in H1; [ easy | ].
  intros H; subst x.
  apply (rngl_eq_mul_0_l Hos Hiq) in H2; [ easy | ].
  intros H; subst y.
  apply (rngl_eq_mul_0_l Hos Hiq) in H3; [ easy | ].
  intros H; subst z.
  easy.
}
rewrite matrix_mul_axis with (k := ‖a‖) in HM; [ | easy | easy ].
rewrite matrix_mul_axis with (k := ‖a‖) in HM'; [ | easy | easy ].
rewrite Rsign_of_pos in HM, HM'; [ | easy | easy ].
rewrite rngl_mul_1_l in HM, HM'.
rewrite Hb in HM, HM'.
rewrite vec_const_mul_assoc in HM, HM'.
rewrite (rngl_mul_inv_diag_r Hiv _ Haz) in HM, HM'.
rewrite vec_const_mul_1_l in HM, HM'.
now rewrite HM, HM' in Haa.
Qed.

Theorem rotation_mat_mul_transp_l : ∀ M,
  is_rotation_matrix M →
  (mat_transp M * M)%mat = mat_id.
Proof. now intros M (Htr, Hdet). Qed.

Theorem rotation_mat_mul_transp_r : ∀ M,
  is_rotation_matrix M →
  (M * mat_transp M)%mat = mat_id.
Proof.
intros M (Htr, Hdet).
now apply mat_mul_id_comm in Htr.
Qed.

Theorem rot_mat_vec_mul_is_inj : ∀ M,
  is_rotation_matrix M
  → FinFun.Injective (mat_vec_mul M).
Proof.
intros M Hrm u v Huv.
apply (f_equal (mat_vec_mul (mat_transp M))) in Huv.
do 2 rewrite <- mat_vec_mul_assoc in Huv.
rewrite rotation_mat_mul_transp_l in Huv; [ | easy ].
now do 2 rewrite mat_vec_mul_id in Huv.
Qed.

Theorem mat_pow_0 : ∀ M, (M ^ 0)%mat = mat_id.
Proof. intros; easy. Qed.

Theorem z_of_xy : ∀ x y z r,
  r = √ (x² + y² + z²)
  → r ≠ 0%L
  → ((z / r) ^ 2 = 1 - (x / r) ^ 2 - (y / r) ^ 2)%L.
Proof.
destruct_ac.
intros * Hr Hrnz.
assert (H : (r ^ 2 ≠ 0 ∧ r ^ 2 - x ^ 2 - y ^ 2 = z ^ 2)%L). {
  split; [ now apply (rngl_pow_neq_0 Hos Hiq) | ].
  rewrite Hr, <- rngl_squ_pow_2.
  rewrite rngl_squ_sqrt; [ do 3 rewrite rngl_squ_pow_2; ring | ].
  apply nonneg_sqr_vec_norm.
}
destruct H as (Hr2nz & Hrxyz).
remember (x / r)%L as xr eqn:Hxr.
remember (y / r)%L as yr eqn:Hyr.
remember (z / r)%L as zr eqn:Hzr.
subst xr yr zr.
do 4 rewrite <- rngl_squ_pow_2 in Hrxyz.
do 3 rewrite <- rngl_squ_pow_2.
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite <- Hrxyz.
progress unfold rngl_div; rewrite Hiv.
do 2 rewrite (rngl_squ_mul Hic).
do 2 rewrite (rngl_mul_sub_distr_r Hop).
rewrite (rngl_squ_inv Hos Hiv); [ | easy ].
progress f_equal; f_equal.
apply (rngl_mul_inv_diag_r Hiv).
intros H; apply Hrnz.
apply (eq_rngl_squ_0 Hos); [ | easy ].
apply Bool.orb_true_iff; right.
now rewrite Hi1, Heo.
Qed.

Theorem matrix_of_axis_angle_mul_mat_transp_l :
  ∀ x y z sinθ cosθ,
  (sinθ * sinθ)%L = (1 - cosθ * cosθ)%L
  → (1 - x * x - y * y)%L = (z * z)%L
  → (mat_transp (matrix_of_unit_axis_angle (V x y z, sinθ, cosθ)) *
      matrix_of_unit_axis_angle (V x y z, sinθ, cosθ))%mat =
    mat_id.
Proof.
intros * Hsc Hrxyz2.
progress unfold mat_transp, mat_mul, mat_id; simpl.
f_equal;
  unfold rngl_squ;
  ring_simplify; fold_rngl;
  repeat rewrite <- (rngl_mul_assoc _ z z);
  rewrite <- Hrxyz2;
  repeat rewrite <- (rngl_mul_assoc _ sinθ sinθ);
  rewrite Hsc;
  ring.
Qed.

Theorem matrix_of_axis_angle_mul_mat_transp_r :
  ∀ x y z sinθ cosθ,
  (sinθ * sinθ)%L = (1 - cosθ * cosθ)%L
  → (1 - x * x - y * y)%L = (z * z)%L
  → (matrix_of_unit_axis_angle (V x y z, sinθ, cosθ) *
     mat_transp (matrix_of_unit_axis_angle (V x y z, sinθ, cosθ)))%mat =
    mat_id.
Proof.
intros * Hsc Hrxyz2.
progress unfold mat_transp, mat_mul, mat_id; simpl.
f_equal;
  unfold rngl_squ;
  ring_simplify; fold_rngl;
  repeat rewrite <- (rngl_mul_assoc _ z z);
  rewrite <- Hrxyz2;
  repeat rewrite <- (rngl_mul_assoc _ sinθ sinθ);
  rewrite Hsc;
  ring.
Qed.

Theorem mat_det_matrix_of_unit_axis_angle :
  ∀ x y z sinθ cosθ,
  (sinθ * sinθ)%L = (1 - cosθ * cosθ)%L
  → (1 - x * x - y * y)%L = (z * z)%L
  → mat_det (matrix_of_unit_axis_angle (V x y z, sinθ, cosθ)) = 1%L.
Proof.
intros * Hsc Hrxyz2.
progress unfold mat_det; simpl.
unfold rngl_squ.
ring_simplify; fold_rngl.
repeat rewrite <- (rngl_mul_assoc _ z z).
rewrite <- Hrxyz2.
repeat rewrite <- (rngl_mul_assoc _ sinθ sinθ).
rewrite Hsc.
ring.
Qed.

Theorem matrix_of_axis_angle_is_rotation_matrix : ∀ p cosθ sinθ,
  p ≠ 0%vec
  → (sinθ² + cosθ² = 1)%L
  → is_rotation_matrix (matrix_of_axis_angle p sinθ cosθ).
Proof.
destruct_ac.
specialize (rngl_2_neq_0 Hos Hc1 Hto) as H20.
intros * Hp Hsc.
rename Hsc into Hsc1.
assert (Hsc : sinθ² = (1 - cosθ²)%L) by now rewrite <- Hsc1, rngl_add_sub.
destruct p as (xp, yp, zp).
remember (√ (xp² + yp² + zp²)) as r eqn:Hr.
assert (Hrnz : r ≠ 0%L). {
  intros H; rewrite Hr in H.
  apply (eq_rl_sqrt_0 Hos) in H; [ | apply nonneg_sqr_vec_norm ].
  apply sqr_vec_norm_eq_0 in H.
  now destruct H as (Hx & Hy & Hz); subst xp yp zp.
}
remember (xp / r)%L as x eqn:Hx.
remember (yp / r)%L as y eqn:Hy.
remember (zp / r)%L as z eqn:Hz.
assert (Hrxyz2 : (1 - x ^ 2 - y ^ 2 = z ^ 2)%L). {
  subst x y z.
  now symmetry; apply z_of_xy.
}
progress unfold matrix_of_axis_angle.
rewrite <- Hr, <- Hx, <- Hy, <- Hz.
do 3 rewrite <- rngl_squ_pow_2 in Hrxyz2.
progress unfold rngl_squ in Hrxyz2.
progress unfold rngl_squ in Hsc.
split; [ | apply (mat_det_matrix_of_unit_axis_angle _ _ _ _ _ Hsc Hrxyz2) ].
apply (matrix_of_axis_angle_mul_mat_transp_l _ _ _ _ _ Hsc Hrxyz2).
Qed.

Theorem mat_of_path_cons : ∀ e el,
   mat_of_path (e :: el) = (mat_of_elem e * mat_of_path el)%mat.
Proof. easy. Qed.

Theorem mat_of_path_single : ∀ e p,
   (mat_of_path (e :: nil) * p)%vec = rotate e p.
Proof.
intros e p.
unfold mat_of_path; simpl.
now rewrite mat_mul_id_r.
Qed.

Theorem mat_of_elem_negf_mul_l : ∀ e,
  (mat_of_elem (negf e) * mat_of_elem e)%mat = mat_id.
Proof.
intros (t, d); simpl.
destruct t, d; simpl.
 apply rot_rot_inv_x.
 apply rot_inv_rot_x.
 apply rot_rot_inv_z.
 apply rot_inv_rot_z.
Qed.

Theorem mat_of_path_norm : ∀ el,
  mat_of_path (norm_list el) = mat_of_path el.
Proof.
intros.
induction el as [| e el]; [ easy | simpl ].
remember (norm_list el) as nel eqn:Hnel.
symmetry in Hnel.
destruct nel as [| e₁ nel].
 unfold mat_of_path in IHel at 1.
 simpl in IHel; symmetry.
 rewrite mat_of_path_cons.
 now rewrite <- IHel.

 destruct (letter_opp_dec e e₁) as [He| He].
  apply letter_opp_negf in He; subst e.
  rewrite mat_of_path_cons.
  rewrite <- IHel.
  rewrite mat_of_path_cons.
  rewrite mat_mul_assoc.
  now rewrite mat_of_elem_negf_mul_l, mat_mul_id_l.

  rewrite mat_of_path_cons; symmetry.
  rewrite mat_of_path_cons; symmetry.
  now rewrite IHel.
Qed.

Theorem rotate_rev_path : ∀ el p₁ p₂,
  (mat_of_path el * p₁)%vec = p₂
  → (mat_of_path (rev_path el) * p₂)%vec = p₁.
Proof.
intros el p₁ p₂ Hr.
revert p₁ p₂ Hr.
induction el as [| e]; intros.
 rewrite mat_vec_mul_id in Hr |-*.
 now symmetry.

 simpl in Hr.
 rewrite rev_path_cons, rev_path_single, mat_of_path_app.
 unfold mat_of_path at 2; simpl.
 rewrite mat_mul_id_r.
 rewrite mat_vec_mul_assoc.
 apply IHel; rewrite <- Hr.
 rewrite mat_of_path_cons.
 rewrite <- mat_vec_mul_assoc.
 rewrite mat_mul_assoc.
 now rewrite mat_of_elem_negf_mul_l, mat_mul_id_l.
Qed.

Theorem mat_of_path_negf : ∀ e el,
  mat_of_path (negf e :: e :: el) = mat_of_path el.
Proof.
intros.
rewrite mat_of_path_cons; simpl.
rewrite mat_of_path_cons; simpl.
rewrite mat_mul_assoc.
now rewrite mat_of_elem_mul_negf_l, mat_mul_id_l.
Qed.

Theorem vec_unit_cross_mul_eq_0_lemma :
   ∀ u₁ u₂ u₃ v₁ v₂ v₃,
  (u₁² + u₂² + u₃²)%L = 1%L
  → (v₁² + v₂² + v₃²)%L = 1%L
  → (u₃ * v₁)%L = (u₁ * v₃)%L
  → (u₁ * v₂)%L = (u₂ * v₁)%L
  → (u₂ * v₃)%L = (u₃ * v₂)%L
  → v₁ ≠ 0%L
  → V u₁ u₂ u₃ = V v₁ v₂ v₃ ∨ V u₁ u₂ u₃ = V (- v₁) (- v₂) (- v₃).
Proof.
destruct_ac.
intros * Hu Hv H1 H2 H3 Hv1z.
symmetry in H2.
rewrite (rngl_mul_comm Hic u₁) in H1, H2.
apply (rngl_mul_move_r Hi1) in H1, H2; [ | easy | easy ].
rewrite <- (rngl_mul_div_assoc Hiv) in H1, H2.
rewrite (rngl_mul_comm Hic) in H1, H2.
remember (u₁ / v₁)%L as k eqn:Hk.
apply (f_equal (rngl_mul v₁)) in Hk.
rewrite (rngl_mul_div_assoc Hiv) in Hk.
rewrite (rngl_mul_comm Hic _ u₁) in Hk.
rewrite (rngl_mul_div Hi1) in Hk; [ | easy ].
symmetry in Hk.
rewrite (rngl_mul_comm Hic _ k) in Hk.
clear H3; rename Hk into H3.
rewrite H1, H2, H3 in Hu.
do 3 rewrite (rngl_squ_mul Hic) in Hu.
do 2 rewrite <- rngl_mul_add_distr_l in Hu.
rewrite Hv, rngl_mul_1_r in Hu.
rewrite <- rngl_squ_1 in Hu.
apply (rngl_squ_eq_cases Hop Hiv Heo) in Hu. 2: {
  now rewrite rngl_mul_1_r, rngl_mul_1_l.
}
destruct Hu; subst k. {
  rewrite rngl_mul_1_l in H1, H2, H3.
  now subst; left.
} {
  rewrite (rngl_mul_opp_l Hop) in H1, H2, H3.
  rewrite rngl_mul_1_l in H1, H2, H3.
  now subst; right.
}
Qed.

Theorem vec_unit_cross_mul_eq_0 : ∀ u v,
  ‖u‖ = 1%L
  → ‖v‖ = 1%L
  → u × v = 0%vec
  → u = v ∨ u = (- v)%vec.
Proof.
destruct_ac.
intros * Hu Hv Huxv.
specialize (vec_Lagrange_identity u v) as H.
rewrite Hu, Hv, Huxv, vec_sqr_0 in H.
rewrite rngl_squ_1, rngl_mul_1_l in H.
apply -> (rngl_sub_move_0_r Hop) in H; symmetry in H.
destruct u as (u₁, u₂, u₃).
destruct v as (v₁, v₂, v₃).
simpl in Hu, Hv.
apply (f_equal rngl_squ) in Hu.
apply (f_equal rngl_squ) in Hv.
rewrite rngl_squ_1 in Hu, Hv.
rewrite rngl_squ_sqrt in Hu; [ | apply nonneg_sqr_vec_norm ].
rewrite rngl_squ_sqrt in Hv; [ | apply nonneg_sqr_vec_norm ].
simpl in *.
injection Huxv; clear Huxv; intros H3 H2 H1.
apply -> (rngl_sub_move_0_r Hop) in H1.
apply -> (rngl_sub_move_0_r Hop) in H2.
apply -> (rngl_sub_move_0_r Hop) in H3.
rewrite <- rngl_squ_1 in H.
apply (eq_rngl_squ_rngl_abs Hop Hto Hii) in H. 2: {
  now rewrite rngl_mul_1_r, rngl_mul_1_l.
}
rewrite (rngl_abs_1 Hos Hto) in H.
progress unfold rngl_abs in H.
clear H.
destruct (rngl_eqb_dec v₁ 0) as [Hv1z| Hv1z]. 2: {
  apply (rngl_eqb_neq Heo) in Hv1z.
  now apply vec_unit_cross_mul_eq_0_lemma.
}
destruct (rngl_eqb_dec v₂ 0) as [Hv2z| Hv2z]. 2: {
  apply (rngl_eqb_neq Heo) in Hv2z.
  rewrite <- rngl_add_assoc, rngl_add_comm in Hu, Hv.
  specialize (vec_unit_cross_mul_eq_0_lemma _ _ _ _ _ _ Hu Hv) as H.
  specialize (H H3 H1 H2 Hv2z).
  now destruct H as [H| H]; injection H; intros; subst; [ left | right ].
}
destruct (rngl_eqb_dec v₃ 0) as [Hv3z| Hv3z]. 2: {
  apply (rngl_eqb_neq Heo) in Hv3z.
  rewrite rngl_add_comm, rngl_add_assoc in Hu, Hv.
  specialize (vec_unit_cross_mul_eq_0_lemma _ _ _ _ _ _ Hu Hv) as H.
  specialize (H H1 H2 H3 Hv3z).
  now destruct H as [H| H]; injection H; intros; subst; [ left | right ].
}
apply (rngl_eqb_eq Heo) in Hv1z, Hv2z, Hv3z; subst v₁ v₂ v₃.
rewrite (rngl_squ_0 Hos) in Hv.
do 2 rewrite rngl_add_0_l in Hv.
symmetry in Hv.
now apply (rngl_1_neq_0 Hc1) in Hv.
Qed.

Theorem mat_vec_dot_mul_assoc : ∀ M u v, M * u · v = u · mat_transp M * v.
Proof.
intros.
destruct u as (x, y, z).
destruct v as (x', y', z').
cbn; ring.
Qed.

Theorem ortho_mat_vec_dot_mul :
  ∀ M, is_ortho_matrix M →
  ∀ x y, M * x · M * y = x · y.
Proof.
destruct_ac.
intros * Ho *.
progress unfold is_ortho_matrix in Ho.
rewrite mat_vec_dot_mul_assoc.
rewrite <- mat_vec_mul_assoc.
rewrite Ho.
progress f_equal.
apply mat_vec_mul_id.
Qed.

Definition Levi_Civita_symbol i j k :=
  match (i, j, k) with
  | (1, 2, 3) | (2, 3, 1) | (3, 1, 2) => 1%L
  | (3, 2, 1) | (1, 3, 2) | (2, 1, 3) => (-1)%L
  | _ => 0%L
  end.

Definition Kronecker_symbol i j := if i =? j then 1%L else 0%L.

Let δ := Kronecker_symbol.
Let ε := Levi_Civita_symbol.

Definition mat_nth M i j :=
  match (i, j) with
  | (1, 1) => a₁₁ M
  | (1, 2) => a₁₂ M
  | (1, 3) => a₁₃ M
  | (2, 1) => a₂₁ M
  | (2, 2) => a₂₂ M
  | (2, 3) => a₂₃ M
  | (3, 1) => a₃₁ M
  | (3, 2) => a₃₂ M
  | (3, 3) => a₃₃ M
  | _ => 0%L
  end.

Definition vec_nth '(V x y z) i :=
  match i with
  | 1 => x
  | 2 => y
  | 3 => z
  | _ => 0%L
  end.

Arguments vec_nth pat%_vec i%_nat.

Theorem vec_nth_cross_mul_from_Levi_Civita :
  ∀ u v i,
  vec_nth (u × v) i =
    ∑ (j = 1, 3), ∑ (k = 1, 3), ε i j k * vec_nth u j * vec_nth v k.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); cbn.
progress unfold iter_seq.
progress unfold iter_list; cbn.
destruct i; [ ring | ].
destruct i; [ ring | ].
destruct i; [ ring | ].
destruct i; ring.
Qed.

Theorem vec_nth_mul_const_l :
  ∀ k u i, vec_nth (k ⁎ u) i = (k * vec_nth u i)%L.
Proof.
destruct_ac.
intros.
destruct u as (u1, u2, u3).
destruct i; cbn; [ symmetry; apply (rngl_mul_0_r Hos) | ].
destruct i; [ easy | ].
destruct i; [ easy | ].
destruct i; [ easy | ].
symmetry; apply (rngl_mul_0_r Hos).
Qed.

Theorem vec_nth_mat_vec_mul :
  ∀ M u i, vec_nth (M * u) i = ∑ (l = 1, 3), vec_nth (mat_nth M i l ⁎ u) l.
Proof.
intros.
progress unfold iter_seq.
progress unfold iter_list.
progress unfold mat_vec_mul.
destruct u as (x, y, z); cbn.
destruct i; [ ring | ].
destruct i; [ ring | ].
destruct i; [ ring | ].
destruct i; ring.
Qed.

Theorem sum_Levi_Civita_symbol_mat :
  ∀ M m n o,
  ∑ (i = 1, 3), ∑ (j = 1, 3), ∑ (k = 1, 3),
    ε i j k * mat_nth M i m * mat_nth M j n * mat_nth M k o =
  (ε m n o * mat_det M)%L.
Proof.
intros.
progress unfold iter_seq.
progress unfold iter_list.
destruct m; [ destruct n; destruct o; cbn; ring | ].
destruct m. {
  destruct n; [ destruct o; cbn; ring | ].
  destruct n; [ destruct o; cbn; ring | ].
  destruct n. {
    destruct o; cbn; [ ring | ].
    destruct o; [ ring | ].
    destruct o; [ ring | ].
    progress unfold mat_det.
    destruct o; ring.
  }
  destruct n; cbn. {
    destruct o; [ ring | ].
    destruct o; [ ring | ].
    progress unfold mat_det.
    destruct o; [ ring | ].
    destruct o; ring.
  }
  ring.
}
destruct m; cbn. {
  destruct n; [ ring | ].
  destruct n. {
    destruct o; [ ring | ].
    destruct o; [ ring | ].
    destruct o; [ ring | ].
    destruct o; [ | ring ].
    progress unfold mat_det.
    ring.
  }
  destruct n; [ ring | ].
  destruct n; [ | ring ].
  progress unfold mat_det.
  destruct o; [ ring | ].
  destruct o; [ ring | ].
  destruct o; [ ring | ].
  destruct o; ring.
}
destruct m; [ | ring ].
destruct n; [ ring | ].
destruct n. {
  destruct o; [ ring | ].
  destruct o; [ ring | ].
  progress unfold mat_det.
  destruct o; [ ring | ].
  destruct o; ring.
}
destruct n. {
  destruct o; [ ring | ].
  progress unfold mat_det.
  destruct o; [ ring | ].
  destruct o; [ ring | ].
  destruct o; ring.
}
destruct n; ring.
Qed.

Theorem vector_ext : ∀ u v, u = v ↔ ∀ i, vec_nth u i = vec_nth v i.
Proof.
intros.
split; intros Huv; [ now subst | ].
destruct u as (u1, u2, u3).
destruct v as (v1, v2, v3).
f_equal.
now specialize (Huv 1); cbn in Huv.
now specialize (Huv 2); cbn in Huv.
now specialize (Huv 3); cbn in Huv.
Qed.

Notation "a ≤ b ≤ c" := (a ≤ b ∧ b ≤ c) : nat_scope.

Theorem matrix_add_mul_eq_Kronecker :
  ∀ M, is_ortho_matrix M →
  ∀ j k, 1 ≤ j ≤ 3 → 1 ≤ k ≤ 3 →
  ∑ (i = 1, 3), mat_nth M i j * mat_nth M i k = δ j k.
Proof.
intros * HM * Hj Hk.
progress unfold is_ortho_matrix in HM.
progress unfold δ, Kronecker_symbol.
remember (j =? k) as jk eqn:Hjk.
symmetry in Hjk.
destruct jk. {
  apply Nat.eqb_eq in Hjk; subst k; clear Hk.
  progress unfold iter_seq, iter_list; cbn.
  rewrite rngl_add_0_l.
  destruct j; [ easy | ].
  destruct j; [ now apply (f_equal (λ M, mat_nth M 1 1)) in HM | ].
  destruct j; [ now apply (f_equal (λ M, mat_nth M 2 2)) in HM | ].
  destruct j; [ now apply (f_equal (λ M, mat_nth M 3 3)) in HM | ].
  destruct Hj as (_, Hj).
  now do 3 apply Nat.succ_le_mono in Hj.
}
apply Nat.eqb_neq in Hjk.
progress unfold iter_seq, iter_list; cbn.
rewrite rngl_add_0_l.
destruct j; [ easy | ].
destruct k; [ easy | ].
destruct Hj as (_, Hj).
destruct Hk as (_, Hk).
destruct j. {
  destruct k; [ easy | ].
  destruct k; [ now apply (f_equal (λ M, mat_nth M 1 2)) in HM | ].
  destruct k; [ now apply (f_equal (λ M, mat_nth M 1 3)) in HM | ].
  now do 3 apply Nat.succ_le_mono in Hk.
}
destruct j. {
  destruct k; [ now apply (f_equal (λ M, mat_nth M 2 1)) in HM | ].
  destruct k; [ easy | ].
  destruct k; [ now apply (f_equal (λ M, mat_nth M 2 3)) in HM | ].
  now do 3 apply Nat.succ_le_mono in Hk.
}
destruct j. {
  destruct k; [ now apply (f_equal (λ M, mat_nth M 3 1)) in HM | ].
  destruct k; [ now apply (f_equal (λ M, mat_nth M 3 2)) in HM | ].
  destruct k; [ easy | ].
  now do 3 apply Nat.succ_le_mono in Hk.
}
now do 3 apply Nat.succ_le_mono in Hj.
Qed.

Theorem mat_vec_mul_cross_distr : ∀ M u v,
  is_rotation_matrix M
  → (M * (u × v))%vec = (M * u) × (M * v).
Proof.
destruct_ac.
intros * (Ht, Hd).
assert
  (Muv_i :
    ∀ i,
    vec_nth (M * (u × v)) i =
    ∑ (l = 1, 3), ∑ (j = 1, 3), ∑ (k = 1, 3),
    mat_nth M i l * ε l j k * vec_nth u j * vec_nth v k). {
  intros.
  rewrite (vec_nth_mat_vec_mul M (u × v)).
  apply rngl_summation_eq_compat.
  intros l Hl.
  rewrite vec_nth_mul_const_l.
  rewrite vec_nth_cross_mul_from_Levi_Civita.
  rewrite (rngl_mul_summation_distr_l Hos).
  apply rngl_summation_eq_compat.
  intros j Hj.
  rewrite (rngl_mul_summation_distr_l Hos).
  apply rngl_summation_eq_compat.
  intros k Hk.
  do 2 rewrite rngl_mul_assoc.
  easy.
}
assert
  (MuMv_i :
    ∀ i,
    vec_nth ((M * u) × (M * v)) i =
    ∑ (j = 1, 3), ∑ (k = 1, 3), ∑ (m = 1, 3), ∑ (n = 1, 3),
    ε i j k *
      mat_nth M j m * vec_nth u m *
      mat_nth M k n * vec_nth v n). {
  intros.
  rewrite vec_nth_cross_mul_from_Levi_Civita.
  apply rngl_summation_eq_compat.
  intros j Hj.
  apply rngl_summation_eq_compat.
  intros k Hk.
  do 2 rewrite vec_nth_mat_vec_mul.
  rewrite (rngl_mul_summation_distr_l Hos).
  rewrite rngl_summation_summation_exch.
  apply rngl_summation_eq_compat.
  intros m Hm.
  rewrite (rngl_mul_summation_distr_l Hos).
  rewrite (rngl_mul_summation_distr_r Hos).
  apply rngl_summation_eq_compat.
  intros n Hn.
  do 2 rewrite vec_nth_mul_const_l.
  do 2 rewrite rngl_mul_assoc.
  easy.
}
assert
  (Hlcs :
    ∀ m n o,
    ∑ (i = 1, 3), ∑ (j = 1, 3), ∑ (k = 1, 3),
    ε i j k * mat_nth M i m * mat_nth M j n * mat_nth M k o =
    ε m n o). {
  intros.
  specialize (sum_Levi_Civita_symbol_mat M m n o) as H3.
  now rewrite Hd, rngl_mul_1_r in H3.
}
specialize (matrix_add_mul_eq_Kronecker M Ht) as Hkro.
(**)
apply vector_ext.
intros i.
rewrite Muv_i, MuMv_i.
erewrite rngl_summation_eq_compat. 2: {
  intros l Hl.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    erewrite rngl_summation_eq_compat. 2: {
      intros k Hk.
      move j before i; move k before j.
      rewrite <- Hlcs.
      reflexivity.
    }
    reflexivity.
  }
  reflexivity.
}
cbn - [ ε mat_nth ].
remember
  (∑ (l = _, _), ∑ (m = _, _), ∑ (n = _, _),
     _ * (∑ (j = _, _), ∑ (k = _, _), ∑ (o = _, _), _) * _ * _)
  as x in |-*; subst x.
...
assert
  (H2 :
     ∀ i j k,
     ∑ (l = 1, 3), mat_nth M i l * ε l j k =
     ∑ (m = 1, 3), ∑ (n = 1, 3), ε i m n * mat_nth M m j * mat_nth M n k). {
  intros.
  erewrite rngl_summation_eq_compat. 2: {
    intros.
    rewrite <- H1.
    rewrite rngl_summation_summation_exch.
    rewrite (rngl_mul_summation_distr_l Hos).
    apply rngl_summation_eq_compat.
    intros.
    rewrite rngl_summation_summation_exch.
    rewrite (rngl_mul_summation_distr_l Hos).
    apply rngl_summation_eq_compat.
    intros.
    rewrite (rngl_mul_summation_distr_l Hos).
    apply rngl_summation_eq_compat.
    intros.
    do 3 rewrite rngl_mul_assoc.
    rewrite <- rngl_mul_assoc.
    reflexivity.
  }
  cbn - [ ε mat_nth ].
  rewrite rngl_summation_summation_exch.
  erewrite rngl_summation_eq_compat. 2: {
    intros.
    rewrite rngl_summation_summation_exch.
    reflexivity.
  }
  cbn - [ ε mat_nth ].
  erewrite rngl_summation_eq_compat. 2: {
    intros.
    erewrite rngl_summation_eq_compat. 2: {
      intros.
      erewrite rngl_summation_eq_compat. 2: {
        intros.
        rewrite <- (rngl_mul_summation_distr_r Hos).
        reflexivity.
      }
      cbn - [ ε mat_nth ].
      rewrite <- (rngl_mul_summation_distr_r Hos).
      reflexivity.
    }
    reflexivity.
  }
  cbn - [ ε mat_nth ].
  remember (∑ (m = 1, 3), ∑ (n = 1, 3), (∑ (l = _, _), ∑ (o = _, _), _) * _)
    as x; subst x.
  apply rngl_summation_eq_compat.
  intros m Hm.
  apply rngl_summation_eq_compat.
  intros n Hn.
  rewrite <- rngl_mul_assoc.
  progress f_equal.
...
assert
  (H4 :
    ∀ i j k, 1 ≤ i ≤ 3 →
    ∑ (l = 1, 3), mat_nth M i l * ε l j k =
    ∑ (m = 1, 3), ∑ (n = 1, 3), ε i m n * mat_nth M j m * mat_nth M k n). {
  intros * Hi.
  specialize (H3 i j k) as H.
  remember (∑ (m = _, _), ∑ (n = _, _), ∑ (o = _, _), _) as x in H.
  subst x.
  enough
    (H' :
      ∀ l,
      ∑ (i = 1, 3), mat_nth M l i * ε i j k =
      ∑ (i = 1, 3), ∑ (m = 1, 3), ∑ (n = 1, 3), ∑ (o = 1, 3),
        mat_nth M i l * ε m n o * mat_nth M i m *
          mat_nth M j n * mat_nth M k o). {
    assert
      (H'' :
        ∀ l,
        ∑ (i = 1, 3), mat_nth M l i * ε i j k =
        ∑ (m = 1, 3),
          (∑ (i = 1, 3), mat_nth M i l * mat_nth M i m) *
          (∑ (n = 1, 3), ∑ (o = 1, 3),
            ε m n o * mat_nth M j n * mat_nth M k o)). {
      intros.
      rewrite H'.
      rewrite rngl_summation_summation_exch.
      apply rngl_summation_eq_compat.
      intros m Hm.
      rewrite (rngl_mul_summation_distr_r Hos).
      apply rngl_summation_eq_compat.
      intros p Hp.
      rewrite (rngl_mul_summation_distr_l Hos).
      apply rngl_summation_eq_compat.
      intros q Hq.
      rewrite (rngl_mul_summation_distr_l Hos).
      apply rngl_summation_eq_compat.
      intros r Hr.
      ring.
    }
    clear H'; rename H'' into H'.
    assert
      (H'' :
        ∀ l, 1 ≤ l ≤ 3 →
        ∑ (i = 1, 3), mat_nth M l i * ε i j k =
        ∑ (m = 1, 3),
          δ l m *
          (∑ (n = 1, 3), ∑ (o = 1, 3),
            ε m n o * mat_nth M j n * mat_nth M k o)). {
      intros * Hl.
      rewrite H'.
      apply rngl_summation_eq_compat.
      intros m Hm.
      progress f_equal.
      now apply (matrix_add_mul_eq_Kronecker _ Ht).
    }
    clear H'; rename H'' into H'.
    assert
      (H'' :
        ∀ l : ℕ, 1 ≤ l ≤ 3 →
        ∑ (i = 1, 3), mat_nth M l i * ε i j k =
        ∑ (n = 1, 3), ∑ (o = 1, 3), ε l n o * mat_nth M j n * mat_nth M k o). {
      intros * Hl.
      rewrite H'; [ | easy ].
      progress unfold iter_seq at 1.
      progress unfold iter_list.
      cbn - [ ε mat_nth ].
      rewrite rngl_add_0_l.
      destruct l; [ easy | ].
      destruct l; cbn - [ ε mat_nth ]. {
        do 2 rewrite (rngl_mul_0_l Hos), rngl_add_0_r.
        apply rngl_mul_1_l.
      }
      destruct l; cbn - [ ε mat_nth ]. {
        do 2 rewrite (rngl_mul_0_l Hos).
        rewrite rngl_add_0_l, rngl_add_0_r.
        apply rngl_mul_1_l.
      }
      destruct l; cbn - [ ε mat_nth ]. {
        do 2 rewrite (rngl_mul_0_l Hos).
        do 2 rewrite rngl_add_0_l.
        apply rngl_mul_1_l.
      }
      destruct Hl as (_, Hl).
      now do 3 apply Nat.succ_le_mono in Hl.
    }
    clear H'; rename H'' into H'.
    now apply H'.
  }
  intros l.
  apply rngl_summation_eq_compat.
  intros p Hp.
...
  replace (ε p j k) with (ε j p k).
  rewrite <- H3.
  rewrite rngl_mul_summation_distr_l.
  apply rngl_summation_eq_compat.
  intros q Hq.
  rewrite rngl_mul_summation_distr_l.
  apply rngl_summation_eq_compat.
  intros r Hr.
  rewrite rngl_mul_summation_distr_l.
  erewrite rngl_summation_eq_compat. 2: {
    intros s Hs.
    do 3 rewrite rngl_mul_assoc.
    easy.
  }
  remember (∑ (o = 1, 3), _) as x in |-*; subst x.
  ============================
  ∑ (o = 1, 3), mat_nth M l p * ε q r o * mat_nth M q k * mat_nth M r p * mat_nth M o j =
  ∑ (o = 1, 3), mat_nth M p l * ε q r o * mat_nth M p q * mat_nth M j r * mat_nth M k o
  ============================
  ∑ (o = 1, 3), mat_nth M l p * ε q r o * mat_nth M q j * mat_nth M r k * mat_nth M o p =
  ∑ (o = 1, 3), mat_nth M p l * ε q r o * mat_nth M p q * mat_nth M j r * mat_nth M k o
Print ε.
Search ε.
...
    remember (∑ (m = 1, 3), ∑ (n = 1, 3), _) as x in |-*; subst x.
...
    rewrite H'.
...
  apply (f_equal (rngl_mul (mat_nth M i l))) in H.
...
apply vector_ext.
intros i.
rewrite H1.
erewrite rngl_summation_eq_compat. 2: {
  intros l Hl.
  erewrite rngl_summation_eq_compat. 2: {
    intros j Hj.
    erewrite rngl_summation_eq_compat. 2: {
      intros k Hk.
      rewrite <- H3.
      rewrite (rngl_mul_summation_distr_l Hos).
      erewrite rngl_summation_eq_compat. 2: {
        intros.
        rewrite (rngl_mul_summation_distr_l Hos).
        erewrite rngl_summation_eq_compat. 2: {
          intros.
          rewrite (rngl_mul_summation_distr_l Hos).
          reflexivity.
        }
        reflexivity.
      }
      reflexivity.
    }
    reflexivity.
  }
  reflexivity.
}
cbn - [ mat_nth ε ].
rewrite rngl_summation_summation_exch.
erewrite rngl_summation_eq_compat. 2: {
  intros.
  erewrite rngl_summation_eq_compat. 2: {
    intros.
    erewrite rngl_summation_eq_compat. 2: {
      intros.
      erewrite rngl_summation_eq_compat. 2: {
        intros.
        erewrite rngl_summation_eq_compat. 2: {
          intros.
          erewrite rngl_summation_eq_compat. 2: {
            intros.
            do 3 rewrite rngl_mul_assoc.
            rewrite (rngl_mul_mul_swap Hic _ (ε _ _ _)).
            do 2 rewrite <- rngl_mul_assoc.
            rewrite (rngl_mul_assoc (ε _ _ _)).
            reflexivity.
          }
          reflexivity.
        }
        reflexivity.
      }
      reflexivity.
    }
    reflexivity.
  }
  reflexivity.
}
cbn - [ mat_nth ε ].
erewrite rngl_summation_eq_compat. 2: {
  intros.
  erewrite rngl_summation_eq_compat. 2: {
    intros.
    erewrite rngl_summation_eq_compat. 2: {
      intros.
      do 2 rewrite (rngl_mul_summation_distr_r Hos).
      erewrite rngl_summation_eq_compat. 2: {
        intros.
        do 2 rewrite (rngl_mul_summation_distr_r Hos).
        erewrite rngl_summation_eq_compat. 2: {
          intros.
          do 2 rewrite (rngl_mul_summation_distr_r Hos).
          erewrite rngl_summation_eq_compat. 2: {
            intros.
            do 2 rewrite <- (rngl_mul_assoc (mat_nth M i i1 * _)).
            reflexivity.
          }
          reflexivity.
        }
        reflexivity.
      }
      reflexivity.
    }
    reflexivity.
  }
  reflexivity.
}
cbn - [ mat_nth ε ].
erewrite rngl_summation_eq_compat. 2: {
  intros.
  rewrite rngl_summation_summation_exch.
  erewrite rngl_summation_eq_compat. 2: {
    intros.
    erewrite rngl_summation_eq_compat. 2: {
      intros.
      rewrite rngl_summation_summation_exch.
      erewrite rngl_summation_eq_compat. 2: {
        intros.
        rewrite rngl_summation_summation_exch.
        erewrite rngl_summation_eq_compat. 2: {
          intros.
          erewrite rngl_summation_eq_compat. 2: {
            intros.
            do 4 rewrite <- rngl_mul_assoc.
            do 2 rewrite rngl_mul_assoc.
            remember (_ * _ * ε _ _ _)%L as x.
            rewrite (rngl_mul_assoc (mat_nth _ _ _)).
            rewrite (rngl_mul_assoc (mat_nth _ _ _ * _)).
            subst x.
            reflexivity.
          }
          cbn - [ mat_nth ε ].
          rewrite <- (rngl_mul_summation_distr_r Hos).
          reflexivity.
        }
        cbn - [ mat_nth ε ].
        reflexivity.
      }
      reflexivity.
    }
    reflexivity.
  }
  reflexivity.
}
cbn - [ mat_nth ε ].
erewrite rngl_summation_eq_compat. 2: {
  intros.
  erewrite rngl_summation_eq_compat. 2: {
    intros.
    rewrite rngl_summation_summation_exch.
    erewrite rngl_summation_eq_compat. 2: {
      intros.
      rewrite rngl_summation_summation_exch.
      erewrite rngl_summation_eq_compat. 2: {
        intros.
        rewrite <- (rngl_mul_summation_distr_r Hos).
        reflexivity.
      }
      reflexivity.
    }
    reflexivity.
  }
  reflexivity.
}
cbn - [ mat_nth ε ].
...
  rewrite rngl_summation_summation_exch.
erewrite rngl_summation_eq_compat. 2: {
  intros.
  rewrite rngl_summation_summation_exch.
erewrite rngl_summation_eq_compat. 2: {
  intros.
  rewrite rngl_summation_summation_exch.
...
      erewrite rngl_summation_eq_compat. 2: {
        intros.
        erewrite rngl_summation_eq_compat. 2: {
          intros.
          erewrite rngl_summation_eq_compat. 2: {
            intros.
            do 3 rewrite rngl_mul_assoc.
            rewrite (rngl_mul_mul_swap Hic _ (ε _ _ _)).
            do 2 rewrite <- rngl_mul_assoc.
            rewrite (rngl_mul_assoc (ε _ _ _)).
            reflexivity.
          }
          cbn - [ mat_nth ε ].
          rewrite <- (rngl_mul_summation_distr_l Hos).
          reflexivity.
        }
        cbn - [ mat_nth ε ].
        rewrite <- (rngl_mul_summation_distr_l Hos).
        reflexivity.
      }
      cbn - [ mat_nth ε ].
      reflexivity.
    }
    cbn - [ mat_nth ε ].
    reflexivity.
  }
  cbn - [ mat_nth ε ].
  reflexivity.
}
cbn - [ mat_nth ε ].

...
          rewrite <- rngl_mul_summation_distr_l.
...
        rewrite rngl_summation_summation_exch.
        erewrite rngl_summation_eq_compat. 2: {
          intros.
...
  erewrite rngl_summation_eq_compat. 2: {
    intros.
    erewrite rngl_summation_eq_compat. 2: {
      intros.
      rewrite rngl_summation_summation_exch.
      erewrite rngl_summation_eq_compat. 2: {
        intros.
        rewrite rngl_summation_summation_exch.
        erewrite rngl_summation_eq_compat. 2: {
          intros.
          replace (∑ (j = _, _), _) with
            (mat_nth M i i0 *
               (ε i i3 i4 * mat_nth M i i0 * mat_nth M i3 i1 *
               mat_nth M i4 i2))%L. 2: {
            progress unfold iter_seq.
            progress unfold iter_list.
            cbn - [ mat_nth ε ].
            rewrite rngl_add_0_l.
            destruct (Nat.eq_dec i 1) as [H1i| H1i]. {
              subst i.
              symmetry.
              rewrite <- rngl_add_assoc.
              apply (rngl_add_move_l Hop).
              rewrite (rngl_sub_diag Hos).
...
          erewrite rngl_summation_eq_compat. 2: {
            intros.

...
assert
  (H4 :
    ∀ i j k,
    ∑ (l = 1, 3), mat_nth M i l * ε l j k =
    ∑ (m = 1, 3), ∑ (n = 1, 3),
      ε i m n * mat_nth M j m * mat_nth M k n). {
  intros.
  erewrite rngl_summation_eq_compat. 2: {
    intros l Hl.
    rewrite <- H3.
    rewrite (rngl_mul_summation_distr_l Hos).
    erewrite rngl_summation_eq_compat. 2: {
      intros.
      rewrite (rngl_mul_summation_distr_l Hos).
      erewrite rngl_summation_eq_compat. 2: {
        intros.
        rewrite (rngl_mul_summation_distr_l Hos).
        erewrite rngl_summation_eq_compat. 2: {
          intros.
          do 3 rewrite rngl_mul_assoc.
          reflexivity.
        }
        reflexivity.
      }
      reflexivity.
    }
    reflexivity.
  }
  cbn - [ mat_nth ε ].
  remember
    (∑ (l = 1, 3), ∑ (m = 1, 3), ∑ (n = 1, 3), ∑ (o = 1, 3), _) as x.
  subst x.
...
  erewrite rngl_summation_eq_compat. 2: {
    intros l Hl.
    apply (f_equal (rngl_mul (mat_nth M i l))) in H3.
    rewrite <- H3.
...
assert
  (H4 :
    ∀ i,
    vec_nth (M * (u × v)) i =
    ∑ (m = 1, 3), ∑ (n = 1, 3),
    ε m n i * vec_nth u m * vec_nth v n). {
  intros.
  rewrite H1.
...
apply vector_ext.
intros i.
specialize (H1 i).
specialize (H2 i).
rewrite H1, H2.
specialize (sum_ε_mat M) as H3.
...
apply rngl_summation_eq_compat.
intros j Hj.
apply rngl_summation_eq_compat.
intros k Hk.
apply rngl_summation_eq_compat.
intros l Hl.
erewrite rngl_summation_eq_compat. 2: {
  intros m Hm.
  rewrite <- rngl_mul_assoc.
  reflexivity.
}
cbn - [ mat_nth vec_nth ε ].
rewrite <- (rngl_mul_summation_distr_l Hos).
rewrite (rngl_mul_comm Hic (mat_nth M i j)).
do 4 rewrite <- rngl_mul_assoc.
progress f_equal.
specialize (sum_ε_mat M) as H3.
rewrite Hd in H3.
specialize (H3 j k l).
rewrite rngl_mul_1_r in H3.
rewrite <- H3.
rewrite (rngl_mul_summation_distr_l Hos).
rewrite (rngl_mul_summation_distr_r Hos).
rewrite (rngl_mul_summation_distr_r Hos).
apply rngl_summation_eq_compat.
intros m Hm.
...
assert
  (H :
    ∀ i,
    vec_nth (M * (u × v)) i =
    ∑ (l = 1, 3), ∑ (j = 1, 3), ∑ (k = 1, 3),
    mat_nth M i l * ε l j k * vec_nth u j * vec_nth v k). {
  intros.
  erewrite rngl_summation_eq_compat. 2: {
    intros l Hl.
    erewrite rngl_summation_eq_compat. 2: {
      intros j Hj.
      erewrite rngl_summation_eq_compat. 2: {
        intros k Hk.
        specialize (H3 l j k) as H.
        rewrite rngl_mul_1_r in H.
        rewrite <- H.
        reflexivity.
      }
      reflexivity.
    }
    reflexivity.
  }
  cbn - [ vec_nth mat_nth ε ].
...
intros M (u₁, u₂, u₃) (v₁, v₂, v₃) (Ht, Hd); simpl.
unfold mat_mul, mat_id in Ht; simpl in Ht.
injection Ht; clear Ht; intros H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ H₉.
unfold mat_det in Hd.
destruct M as (a11, a12, a13, a21, a22, a23, a31, a32, a33); simpl in *.
f_equal. {
  ring_simplify in Hd.
  ring_simplify.
...
 clear H₁ H₂ H₃ H₄ H₅ H₆. nsatz.
 clear H₁ H₂ H₃ H₇ H₈ H₉. nsatz.
 clear H₄ H₅ H₆ H₇ H₈ H₉. nsatz.
Qed.
