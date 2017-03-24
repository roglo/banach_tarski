(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List.
Require Import Reals Psatz Nsatz.

Require Import Words Normalize Reverse MiscReals.

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

Definition mat_map {A B} (f : A → B) m :=
  mkmat
    (f (a₁₁ m)) (f (a₁₂ m)) (f (a₁₃ m))
    (f (a₂₁ m)) (f (a₂₂ m)) (f (a₂₃ m))
    (f (a₃₁ m)) (f (a₃₂ m)) (f (a₃₃ m)).

Definition mt i j :=
  match i with
  | 1%nat => match j with 1%nat => a₁₁ | 2 => a₁₂ | _ => a₁₃ end
  | 2%nat => match j with 1%nat => a₂₁ | 2 => a₂₂ | _ => a₂₃ end
  | _ => match j with 1%nat => a₃₁ | 2 => a₃₂ | _ => a₃₃ end
  end.
Arguments mt i%nat j%nat [A] m.

Definition mkrmat := @mkmat ℝ.

Definition mat_add M₁ M₂ :=
  mkrmat
    (a₁₁ M₁ + a₁₁ M₂) (a₁₂ M₁ + a₁₂ M₂) (a₁₃ M₁ + a₁₃ M₂)
    (a₂₁ M₁ + a₂₁ M₂) (a₂₂ M₁ + a₂₂ M₂) (a₂₃ M₁ + a₂₃ M₂)
    (a₃₁ M₁ + a₃₁ M₂) (a₃₂ M₁ + a₃₂ M₂) (a₃₃ M₁ + a₃₃ M₂).

Definition mat_opp M :=
  mkrmat
    (- a₁₁ M) (- a₁₂ M) (- a₁₃ M)
    (- a₂₁ M) (- a₂₂ M) (- a₂₃ M)
    (- a₃₁ M) (- a₃₂ M) (- a₃₃ M).

Definition mat_sub M₁ M₂ := mat_add M₁ (mat_opp M₂).

Inductive vector := V : ℝ → ℝ → ℝ → vector.

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
  x₁ * x₂ + y₁ * y₂ + z₁ * z₂.
Definition vec_cross_mul '(V u₁ u₂ u₃) '(V v₁ v₂ v₃) :=
  V (u₂ * v₃ - u₃ * v₂) (u₃ * v₁ - u₁ * v₃) (u₁ * v₂ - u₂ * v₁).
Definition vec_const_mul k '(V x y z) := V (k * x) (k * y) (k * z).
Definition mat_const_mul k (M : matrix ℝ) :=
  mkrmat
    (k * a₁₁ M) (k * a₁₂ M) (k * a₁₃ M)
    (k * a₂₁ M) (k * a₂₂ M) (k * a₂₃ M)
    (k * a₃₁ M) (k * a₃₂ M) (k * a₃₃ M).

Delimit Scope vec_scope with vec.

Arguments vec_norm _%vec.
Arguments vec_add _%vec _%vec.
Arguments vec_dot_mul _%vec _%vec.
Arguments vec_cross_mul _%vec _%vec.
Arguments vec_const_mul _%R _%vec.

Notation "0" := (V 0 0 0) : vec_scope.
Notation "k ⁎ v" := (vec_const_mul k v) (at level 40).
Notation "v ⁄ k" := (vec_const_mul (/ k) v) (at level 40).
Notation "M * v" := (mat_vec_mul M v) : vec_scope.
Notation "u + v" := (vec_add u v) : vec_scope.
Notation "u - v" := (vec_sub u v) : vec_scope.
Notation "- v" := (vec_opp v) : vec_scope.
Notation "u · v" := (vec_dot_mul u v) (at level 45, left associativity).
Notation "u × v" := (vec_cross_mul u v) (at level 40, no associativity).
Notation "v ²" := (vec_dot_mul v v) : vec_scope.
Notation "‖ v ‖" := (vec_norm v) (at level 0, v at level 0, format "‖ v ‖").

Definition vos a := V a a a.

(* https://en.wikipedia.org/wiki/Rotation_matrix
   #Rotation_matrix_from_axis_and_angle *)
Definition rot_mat_of_axis_cos '(V x y z) cosθ :=
  let sinθ := √ (1 - cosθ²) in mkrmat
  (cosθ+x²*(1-cosθ))    (x*y*(1-cosθ)-z*sinθ) (x*z*(1-cosθ)+y*sinθ)
  (y*x*(1-cosθ)+z*sinθ) (cosθ+y²*(1-cosθ))    (y*z*(1-cosθ)-x*sinθ)
  (z*x*(1-cosθ)-y*sinθ) (z*y*(1-cosθ)+x*sinθ) (cosθ+z²*(1-cosθ)).

Definition rot_x := mkrmat
  1         0         0
  0         (1/3)     (-2*√2/3)
  0         (2*√2/3)  (1/3).
Definition rot_inv_x := mkrmat
  1         0         0
  0         (1/3)     (2*√2/3)
  0         (-2*√2/3) (1/3).
Definition rot_z := mkrmat
  (1/3)     (-2*√2/3) 0
  (2*√2/3)  (1/3)     0
  0         0         1.
Definition rot_inv_z := mkrmat
  (1/3)     (2*√2/3)  0
  (-2*√2/3) (1/3)     0
  0         0         1.

Definition is_neg_vec '(V x y z) :=
  if Rlt_dec x 0 then true
  else if Rgt_dec x 0 then false
  else if Rlt_dec y 0 then true
  else if Rgt_dec y 0 then false
  else if Rlt_dec z 0 then true
  else if Rgt_dec z 0 then false
  else true.

Arguments is_neg_vec _%vec.

Theorem rot_x_means_rot_x : rot_x = rot_mat_of_axis_cos (V 1 0 0) (1/3).
Proof.
unfold rot_x; simpl.
setoid_rewrite Rsqr_pow2.
f_equal; try lra; ring_simplify.
 replace (1 - (1 / 3) ^ 2) with (2 * (2 / 3) ^ 2) by field.
 rewrite sqrt_mult; [ rewrite sqrt_pow2; lra | lra | lra ].

 replace (1 - (1 / 3) ^ 2) with (2 * (2 / 3) ^ 2) by field.
 rewrite sqrt_mult; [ rewrite sqrt_pow2; lra | lra | lra ].
Qed.

Definition mat_of_elem e :=
  match e with
  | ạ => rot_x
  | ạ⁻¹ => rot_inv_x
  | ḅ => rot_z
  | ḅ⁻¹ => rot_inv_z
  end.

Definition rotate e pt := mat_vec_mul (mat_of_elem e) pt.

Definition mat_mul M₁ M₂ :=
  mkrmat
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
  mkrmat
    1 0 0
    0 1 0
    0 0 1.

Fixpoint mat_pow M n :=
  match n with
  | O => mat_id
  | S n' => mat_mul M (mat_pow M n')
  end.

Definition mat_trace M := a₁₁ M + a₂₂ M + a₃₃ M.

Delimit Scope mat_scope with mat.
Notation "M₁ + M₂" := (mat_add M₁ M₂) : mat_scope.
Notation "M₁ - M₂" := (mat_sub M₁ M₂) : mat_scope.
Notation "M₁ * M₂" := (mat_mul M₁ M₂) : mat_scope.
Notation "k ⁎ M" := (mat_const_mul k M) : mat_scope.
Notation "M ⁄ k" := (mat_const_mul (/ k) M) : mat_scope.
Notation "- M" := (mat_opp M) : mat_scope.
Notation "M ^ n" := (mat_pow M n) : mat_scope.

Arguments mat_pow M%mat n%nat.
Arguments mat_mul M₁%mat M₂%mat.
Arguments mat_vec_mul M%mat _%vec.
Arguments mat_trace M%mat.

Theorem vec_eq_dec : ∀ u v : vector, { u = v } + { u ≠ v }.
Proof.
intros (x₁, y₁, z₁) (x₂, y₂, z₂).
destruct (Req_dec x₁ x₂) as [H₁| H₁]; [ subst x₂ | right ].
 destruct (Req_dec y₁ y₂) as [H₁| H₁]; [ subst y₂ | right ].
  destruct (Req_dec z₁ z₂) as [H₁| H₁]; [ now subst z₂; left | right ].
  now intros H; injection H; intros.

 now intros H; injection H; intros.

now intros H; injection H; intros.
Qed.

Arguments vec_eq_dec _%vec _%vec.

Theorem vec_zerop : ∀ v : vector, { v = 0%vec } + { v ≠ 0%vec }.
Proof.
intros.
now specialize (vec_eq_dec v 0).
Qed.

Theorem mat_eq_dec : ∀ m₁ m₂ : matrix ℝ, { m₁ = m₂ } + { m₁ ≠ m₂ }.
Proof.
intros.
destruct (Req_dec (a₁₁ m₁) (a₁₁ m₂)) as [H₁₁| H₁₁].
 destruct (Req_dec (a₁₂ m₁) (a₁₂ m₂)) as [H₁₂| H₁₂].
  destruct (Req_dec (a₁₃ m₁) (a₁₃ m₂)) as [H₁₃| H₁₃].
   destruct (Req_dec (a₂₁ m₁) (a₂₁ m₂)) as [H₂₁| H₂₁].
    destruct (Req_dec (a₂₂ m₁) (a₂₂ m₂)) as [H₂₂| H₂₂].
     destruct (Req_dec (a₂₃ m₁) (a₂₃ m₂)) as [H₂₃| H₂₃].
      destruct (Req_dec (a₃₁ m₁) (a₃₁ m₂)) as [H₃₁| H₃₁].
       destruct (Req_dec (a₃₂ m₁) (a₃₂ m₂)) as [H₃₂| H₃₂].
        destruct (Req_dec (a₃₃ m₁) (a₃₃ m₂)) as [H₃₃| H₃₃].
         now left; destruct m₁, m₂; simpl in *; subst.
         now right; intros H; subst m₁; apply H₃₃.
        now right; intros H; subst m₁; apply H₃₂.
       now right; intros H; subst m₁; apply H₃₁.
      now right; intros H; subst m₁; apply H₂₃.
     now right; intros H; subst m₁; apply H₂₂.
    now right; intros H; subst m₁; apply H₂₁.
   now right; intros H; subst m₁; apply H₁₃.
  now right; intros H; subst m₁; apply H₁₂.
 now right; intros H; subst m₁; apply H₁₁.
Qed.

Theorem mat_mul_id_l : ∀ m, (mat_id * m)%mat = m.
Proof.
intros m.
unfold mat_mul, mat_id; simpl.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
now destruct m.
Qed.

Theorem mat_mul_id_r : ∀ m, (m * mat_id)%mat = m.
Proof.
intros m.
unfold mat_mul, mat_id; simpl.
progress repeat rewrite Rmult_1_r.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
now destruct m.
Qed.

Theorem mat_vec_mul_id : ∀ p, (mat_id * p)%vec = p.
Proof.
intros (x, y, z).
unfold mat_vec_mul; simpl.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
easy.
Qed.

Theorem mat_const_mul_distr_l : ∀ k M₁ M₂,
  (k ⁎ (M₁ * M₂) = (k ⁎ M₁) * M₂)%mat.
Proof.
intros.
unfold mat_const_mul, mat_mul.
destruct M₁, M₂; simpl.
f_equal; lra.
Qed.

Theorem mat_const_mul_distr_r : ∀ k M₁ M₂,
  (k ⁎ (M₁ * M₂) = M₁ * (k ⁎ M₂))%mat.
Proof.
intros.
unfold mat_const_mul, mat_mul.
destruct M₁, M₂; simpl.
f_equal; lra.
Qed.

Theorem mat_vec_mul_assoc : ∀ m₁ m₂ p,
  ((m₁ * m₂)%mat * p = m₁ * (m₂ * p))%vec.
Proof.
intros m₁ m₂ (x, y, z).
unfold mat_vec_mul.
simpl; f_equal; lra.
Qed.

Theorem  mat_vec_mul_add_distr_l : ∀ M u v, (M * (u + v) = M * u + M * v)%vec.
Proof.
intros.
destruct u as (u₁, u₂, u₃).
destruct v as (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem mat_vec_mul_add_distr_r : ∀ M₁ M₂ v,
  ((M₁ + M₂)%mat * v = M₁ * v + M₂ * v)%vec.
Proof.
intros; destruct M₁, M₂, v; simpl; f_equal; lra.
Qed.

Theorem mat_vec_mul_sub_distr_r : ∀ M₁ M₂ v,
  ((M₁ - M₂)%mat * v = M₁ * v - M₂ * v)%vec.
Proof.
intros; destruct M₁, M₂, v; simpl; f_equal; lra.
Qed.

Theorem  mat_vec_mul_const_distr : ∀ M k v, (M * (k ⁎ v) = k ⁎ (M * v))%vec.
Proof.
intros.
destruct v as (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_mul_diag : ∀ x y z k,
  V (k * x) (k * y) (k * z) = (k ⁎ V x y z)%vec.
Proof. easy. Qed.

Theorem rot_rot_inv_x : (rot_x * rot_inv_x)%mat = mat_id.
Proof.
unfold mat_mul, mat_id, mkrmat; simpl.
unfold Rdiv.
progress repeat rewrite <- Rmult_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
f_equal; lra.
Qed.

Theorem rot_inv_rot_x : (rot_inv_x * rot_x)%mat = mat_id.
Proof.
unfold mat_mul, mat_id, mkrmat; simpl.
unfold Rdiv.
progress repeat rewrite <- Rmult_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
f_equal; lra.
Qed.

Theorem rot_rot_inv_z : (rot_z * rot_inv_z)%mat = mat_id.
Proof.
unfold mat_mul, mat_id, mkrmat; simpl.
unfold Rdiv.
progress repeat rewrite <- Rmult_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
f_equal; lra.
Qed.

Theorem rot_inv_rot_z : (rot_inv_z * rot_z)%mat = mat_id.
Proof.
unfold mat_mul, mat_id, mkrmat; simpl.
unfold Rdiv.
progress repeat rewrite <- Rmult_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
f_equal; lra.
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
  List.fold_right mat_mul mat_id (map mat_of_elem el).

Theorem rotate_vec_mul : ∀ el p,
  fold_right rotate p el = mat_vec_mul (mat_of_path el) p.
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

Theorem app_path_rev_path : ∀ p el,
  fold_right rotate p (rev_path el ++ el) = p.
Proof.
intros.
revert p.
induction el as [| e] using rev_ind; intros; [ easy | simpl ].
rewrite rev_path_app; simpl.
rewrite app_assoc, fold_right_app; simpl.
rewrite IHel; apply rotate_neg_rotate.
Qed.

Theorem rotate_cancel_in : ∀ el₁ el₂ e p,
  fold_right rotate p (el₁ ++ e :: negf e :: el₂) =
  fold_right rotate p (el₁ ++ el₂).
Proof.
intros.
do 2 rewrite fold_right_app; simpl.
now rewrite rotate_rotate_neg.
Qed.

Theorem rotate_rotate_norm : ∀ el p,
  fold_right rotate p el = fold_right rotate p (norm_list el).
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

Theorem rotate_rev_path : ∀ el p₁ p₂,
  fold_right rotate p₁ el = p₂
  → fold_right rotate p₂ (rev_path el) = p₁.
Proof.
intros el p₁ p₂ Hr.
revert p₁ p₂ Hr.
induction el as [| e]; intros; [ now symmetry | ].
simpl in Hr.
rewrite rev_path_cons, rev_path_single, fold_right_app; simpl.
apply IHel; rewrite <- Hr.
rewrite rotate_neg_rotate.
easy.
Qed.

Definition mat_transp m :=
  mkrmat
   (a₁₁ m) (a₂₁ m) (a₃₁ m)
   (a₁₂ m) (a₂₂ m) (a₃₂ m)
   (a₁₃ m) (a₂₃ m) (a₃₃ m).

Definition mat_det m :=
  a₁₁ m * (a₂₂ m * a₃₃ m - a₃₂ m * a₂₃ m) +
  a₁₂ m * (a₂₃ m * a₃₁ m - a₃₃ m * a₂₁ m) +
  a₁₃ m * (a₂₁ m * a₃₂ m - a₃₁ m * a₂₂ m).

Arguments mat_transp m%mat.
Arguments mat_det m%mat.

Theorem mat_transp_id : mat_transp mat_id = mat_id.
Proof. easy. Qed.

Theorem mat_transp_mul : ∀ m₁ m₂,
  mat_transp (mat_mul m₁ m₂) = mat_mul (mat_transp m₂) (mat_transp m₁).
Proof.
intros m₁ m₂.
unfold mat_transp, mat_mul; simpl; f_equal; ring.
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
  mat_det (m₁ * m₂) = mat_det m₂ * mat_det m₁.
Proof.
intros m₁ m₂.
unfold mat_det; simpl; ring.
Qed.

Definition is_rotation_matrix A :=
  mat_mul A (mat_transp A) = mat_id ∧
  mat_det A = 1.

Arguments is_rotation_matrix A%mat.

Theorem mat_id_is_rotation_matrix : is_rotation_matrix mat_id.
Proof.
split; [ now rewrite mat_transp_id, mat_mul_id_l | ].
unfold mat_det; simpl; ring.
Qed.

Theorem rot_x_is_rotation_matrix : is_rotation_matrix rot_x.
Proof.
unfold is_rotation_matrix, mat_transp, mat_mul, mat_det; simpl.
unfold mat_id, Rdiv.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite <- Rmult_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | lra ]).
split; [ f_equal; field | field ].
Qed.

Theorem rot_inv_x_is_rotation_matrix : is_rotation_matrix rot_inv_x.
Proof.
unfold is_rotation_matrix, rot_inv_x, mat_transp, mat_mul, mat_det; simpl.
unfold mat_id, Rdiv.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite <- Rmult_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | lra ]).
split; [ f_equal; field | field ].
Qed.

Theorem rot_z_is_rotation_matrix : is_rotation_matrix rot_z.
Proof.
unfold is_rotation_matrix, mat_transp, mat_mul, mat_det; simpl.
unfold mat_id, Rdiv.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rminus_0_l.
progress repeat rewrite Rminus_0_r.
progress repeat rewrite Ropp_mult_distr_l.
progress repeat rewrite <- Rmult_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | lra ]).
split; [ f_equal; field | field ].
Qed.

Theorem rot_inv_z_is_rotation_matrix : is_rotation_matrix rot_inv_z.
Proof.
unfold is_rotation_matrix, rot_inv_x, mat_transp, mat_mul, mat_det; simpl.
unfold mat_id, Rdiv.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rminus_0_l.
progress repeat rewrite Rminus_0_r.
progress repeat rewrite Ropp_mult_distr_l.
progress repeat rewrite <- Rmult_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | lra ]).
split; [ f_equal; field | field ].
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
intros * (Hm1, Hd1) (Hm2, Hd2).
unfold is_rotation_matrix.
rewrite mat_transp_mul.
rewrite mat_mul_assoc.
setoid_rewrite <- mat_mul_assoc at 2.
rewrite Hm2, mat_mul_id_r, Hm1.
split; [ easy | ].
rewrite mat_det_mul, Hd1, Hd2.
apply Rmult_1_r.
Qed.

Theorem mat_pow_is_rotation_matrix : ∀ M n,
  is_rotation_matrix M → is_rotation_matrix (M ^ n).
Proof.
intros * HM.
induction n; [ apply mat_id_is_rotation_matrix | simpl ].
now apply mat_mul_is_rotation_matrix.
Qed.

Theorem vec_const_mul_assoc : ∀ a b v, a ⁎ (b ⁎ v) = (a * b) ⁎ v.
Proof.
intros a b (x, y, z); simpl.
now do 3 rewrite Rmult_assoc.
Qed.

Theorem vec_const_mul_div : ∀ a b u v,
  a ≠ 0
  → a ⁎ u = b ⁎ v
  → u = (b / a) ⁎ v.
Proof.
intros * Ha Hm.
destruct u as (u₁, u₂, u₃).
destruct v as (v₁, v₂, v₃).
simpl in Hm; simpl.
injection Hm; clear Hm; intros H₃ H₂ H₁.
unfold Rdiv; setoid_rewrite Rmult_shuffle0.
rewrite <- H₁, <- H₂, <- H₃.
setoid_rewrite Rmult_shuffle0.
rewrite Rinv_r; [ | easy ].
now do 3 rewrite Rmult_1_l.
Qed.

Theorem vec_norm_nonneg : ∀ v, 0 ≤ ‖v‖.
Proof.
intros (x, y, z); simpl.
apply sqrt_pos.
Qed.

Theorem nonneg_sqr_vec_norm : ∀ x y z, 0 ≤ x² + y² + z².
Proof.
intros.
apply Rplus_le_le_0_compat; [ | apply Rle_0_sqr ].
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Theorem vec_norm_opp : ∀ v, ‖(- v)‖ = ‖v‖.
Proof.
intros (x, y, z); simpl.
now do 3 rewrite <- Rsqr_neg.
Qed.

Theorem vec_norm_vec_const_mul : ∀ a v,
  ‖(vec_const_mul a v)‖ = Rabs a * ‖v‖.
Proof.
intros a (x, y, z); simpl.
do 3 rewrite Rsqr_mult.
do 2 rewrite <- Rmult_plus_distr_l.
rewrite sqrt_mult; [ | apply Rle_0_sqr | apply nonneg_sqr_vec_norm ].
now rewrite sqrt_Rsqr_abs.
Qed.

Theorem sqr_vec_norm_eq_0 : ∀ x y z,
  x² + y² + z² = 0
  → x = 0 ∧ y = 0 ∧ z = 0.
Proof.
intros * H.
apply Rplus_eq_R0 in H; [ | | apply Rle_0_sqr ].
 destruct H as (H₁, H₂).
 apply Rplus_sqr_eq_0 in H₁.
 apply Rsqr_eq_0 in H₂.
 move H₁ at top; move H₂ at top; destruct H₁; subst x y z.
 now split; [ | split ].

 apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Theorem vec_norm_0 : ‖0‖ = 0.
Proof.
simpl; rewrite Rsqr_0.
do 2 rewrite Rplus_0_l.
apply sqrt_0.
Qed.

Theorem vec_norm_eq_0 : ∀ v, ‖v‖ = 0 ↔ v = 0%vec.
Proof.
intros.
split; intros Hv.
 destruct v as (v₁, v₂, v₃); simpl in Hv.
 apply sqrt_eq_0 in Hv; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in Hv.
 now destruct Hv as (H₁ & H₂ & H₃); subst.

 destruct v as (v₁, v₂, v₃); simpl.
 injection Hv; clear Hv; intros; subst.
 rewrite Rsqr_0, Rplus_0_r, Rplus_0_r.
 apply sqrt_0.
Qed.

Theorem vec_norm_neq_0 : ∀ v, ‖v‖ ≠ 0 ↔ v ≠ 0%vec.
Proof.
intros v.
now split; intros H1 H2; apply vec_norm_eq_0 in H2.
Qed.

Theorem vec_norm_pos : ∀ v, v ≠ 0%vec → 0 < ‖v‖.
Proof.
intros * Hv.
specialize (vec_norm_nonneg v) as H.
apply vec_norm_neq_0 in Hv; lra.
Qed.

Theorem vec_add_0_l : ∀ v, (0 + v = v)%vec.
Proof.
intros (x, y, z); simpl; f_equal; lra.
Qed.

Theorem vec_add_0_r : ∀ v, (v + 0 = v)%vec.
Proof.
intros (x, y, z); simpl; f_equal; lra.
Qed.

Theorem vec_sub_0_l : ∀ v, (0 - v = - v)%vec.
Proof.
intros (x, y, z); simpl; f_equal; lra.
Qed.

Theorem vec_sub_0_r : ∀ v, (v - 0 = v)%vec.
Proof.
intros (x, y, z); simpl; f_equal; lra.
Qed.

Theorem fold_vec_sub : ∀ u v, (u + - v = u - v)%vec.
Proof. intros; easy. Qed.

Theorem eq_vec_const_mul_0 : ∀ a v, (a ⁎ v = 0 → a = 0%R ∨ v = 0)%vec.
Proof.
intros a (x, y, z) Hv; simpl in Hv; simpl.
injection Hv; intros Hz Hy Hx.
apply Rmult_integral in Hx.
apply Rmult_integral in Hy.
apply Rmult_integral in Hz.
destruct Hx as [Hx| Hx]; [ now left | subst x ].
destruct Hy as [Hy| Hy]; [ now left | subst y ].
destruct Hz as [Hz| Hz]; [ now left | subst z ].
now right.
Qed.

Theorem vec_const_mul_0_l : ∀ v, (0 ⁎ v = 0)%vec.
Proof.
intros (x, y, z); simpl.
now do 3 rewrite Rmult_0_l.
Qed.

Theorem vec_const_mul_0_r : ∀ a, (a ⁎ 0 = 0)%vec.
Proof.
intros x; simpl.
now rewrite Rmult_0_r.
Qed.

Theorem vec_const_mul_1_l : ∀ v, 1 ⁎ v = v.
Proof.
intros (x, y, z).
unfold vec_const_mul.
now do 3 rewrite Rmult_1_l.
Qed.

Theorem neg_vec_involutive : ∀ p, (- - p)%vec = p.
Proof.
intros (x, y, z); simpl.
now do 3 rewrite Ropp_involutive.
Qed.

Theorem is_neg_vec_0 : is_neg_vec (V 0 0 0) = true.
Proof.
simpl.
destruct (Rlt_dec 0 0) as [H₁| H₁]; [ easy | clear H₁ ].
destruct (Rgt_dec 0 0) as [H₁| H₁]; [ | easy ].
now apply Rgt_irrefl in H₁.
Qed.

Theorem is_neg_vec_neg_vec : ∀ v,
  v ≠ 0%vec
  → is_neg_vec (- v) = negb (is_neg_vec v).
Proof.
intros (x, y, z) Hv; simpl.
destruct (Rlt_dec x 0) as [Hx| Hx].
 destruct (Rlt_dec (-x) 0) as [Hx'| Hx'].
  apply Ropp_lt_contravar in Hx'.
  rewrite Ropp_0, Ropp_involutive in Hx'.
  now apply Rlt_le, Rle_not_lt in Hx'.

  clear Hx'.
  destruct (Rgt_dec (-x) 0) as [Hx'| Hx']; [ easy | ].
  apply Ropp_lt_contravar in Hx.
  now rewrite Ropp_0 in Hx.

 apply Rnot_lt_le in Hx.
 destruct (Rlt_dec (-x) 0) as [Hx'| Hx'].
  apply Ropp_lt_contravar in Hx'.
  rewrite Ropp_0, Ropp_involutive in Hx'.
  now destruct (Rgt_dec x 0).

  apply Rnot_lt_le in Hx'.
  apply Ropp_le_contravar in Hx'.
  rewrite Ropp_0, Ropp_involutive in Hx'.
  apply Rle_antisym in Hx'; [ subst x | easy ].
  rewrite Ropp_0; clear Hx.
  destruct (Rgt_dec 0 0) as [Hx| Hx]; [ now apply Rgt_irrefl in Hx | ].
  clear Hx.
  destruct (Rlt_dec y 0) as [Hy| Hy].
   destruct (Rlt_dec (-y) 0) as [Hy'| Hy'].
    apply Ropp_lt_contravar in Hy'.
    rewrite Ropp_0, Ropp_involutive in Hy'.
    now apply Rlt_le, Rle_not_lt in Hy'.

    clear Hy'.
    destruct (Rgt_dec (-y) 0) as [Hy'| Hy']; [ easy | ].
    apply Ropp_lt_contravar in Hy.
    now rewrite Ropp_0 in Hy.

   apply Rnot_lt_le in Hy.
   destruct (Rlt_dec (-y) 0) as [Hy'| Hy'].
    apply Ropp_lt_contravar in Hy'.
    rewrite Ropp_0, Ropp_involutive in Hy'.
    now destruct (Rgt_dec y 0).

    apply Rnot_lt_le in Hy'.
    apply Ropp_le_contravar in Hy'.
    rewrite Ropp_0, Ropp_involutive in Hy'.
    apply Rle_antisym in Hy'; [ subst y | easy ].
    rewrite Ropp_0; clear Hy.
    destruct (Rgt_dec 0 0) as [Hy| Hy]; [ now apply Rgt_irrefl in Hy | ].
    clear Hy.
    destruct (Rlt_dec z 0) as [Hz| Hz].
     destruct (Rlt_dec (-z) 0) as [Hz'| Hz'].
      apply Ropp_lt_contravar in Hz'.
      rewrite Ropp_0, Ropp_involutive in Hz'.
      now apply Rlt_le, Rle_not_lt in Hz'.

      clear Hz'.
      destruct (Rgt_dec (-z) 0) as [Hz'| Hz']; [ easy | ].
      apply Ropp_lt_contravar in Hz.
      now rewrite Ropp_0 in Hz.

     apply Rnot_lt_le in Hz.
     destruct (Rlt_dec (-z) 0) as [Hz'| Hz'].
      apply Ropp_lt_contravar in Hz'.
      rewrite Ropp_0, Ropp_involutive in Hz'.
      now destruct (Rgt_dec z 0).

      apply Rnot_lt_le in Hz'.
      apply Ropp_le_contravar in Hz'.
      rewrite Ropp_0, Ropp_involutive in Hz'.
      apply Rle_antisym in Hz'; [ subst z | easy ].
      now exfalso; apply Hv.
Qed.

Theorem vec_add_assoc : ∀ u v w, (u + (v + w))%vec = (u + v + w)%vec.
Proof.
intros.
destruct u as (u₁, u₂, u₃).
destruct v as (v₁, v₂, v₃).
destruct w as (w₁, w₂, w₃).
simpl; f_equal; lra.
Qed.

Theorem vec_add_opp_diag_l : ∀ v, (- v + v = 0)%vec.
Proof.
intros (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_add_opp_diag_r : ∀ v, (v + - v = 0)%vec.
Proof.
intros (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_add_diag : ∀ v, (v + v = 2 ⁎ v)%vec.
Proof. intros (x, y, z); simpl. f_equal; lra. Qed.

Theorem vec_sub_diag : ∀ v, (v - v = 0)%vec.
intros (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_sub_diag_uniq : ∀ u v, (u - v = 0)%vec → u = v.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) Huv.
injection Huv; clear Huv; intros.
f_equal; lra.
Qed.

Theorem vec_sub_opp_r : ∀ u v, (u - - v = u + v)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_add_sub_distr : ∀ u v w, (u + (v - w) = u + v - w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; lra.
Qed.

Theorem vec_sub_add_distr : ∀ u v w, (u - (v + w) = u - v - w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; lra.
Qed.

Theorem vec_sub_sub_distr : ∀ u v w, (u - (v - w) = u - v + w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; lra.
Qed.

Theorem vec_add_move_l : ∀ u v w, (u + v = w ↔ v = w - u)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl.
split; intros H; injection H; intros; subst; f_equal; lra.
Qed.

Theorem vec_add_move_r : ∀ u v w, (u + v = w ↔ u = w - v)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl.
split; intros H; injection H; intros; subst; f_equal; lra.
Qed.

Theorem vec_add_cancel_l : ∀ u v w, (u + v = u + w)%vec → v = w.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃) H; simpl.
injection H; intros; subst; f_equal; lra.
Qed.

Theorem vec_add_cancel_r : ∀ u v w, (u + w = v + w)%vec → u = v.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃) H; simpl.
injection H; intros; subst; f_equal; lra.
Qed.

Theorem vec_sub_cancel_l : ∀ u v w, (u - v = u - w)%vec → v = w.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃) H; simpl.
injection H; intros; subst; f_equal; lra.
Qed.

Theorem vec_sub_cancel_r : ∀ u v w, (u - w = v - w)%vec → u = v.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃) H; simpl.
injection H; intros; subst; f_equal; lra.
Qed.

Theorem vec_sub_move_r : ∀ u v w, (u - v)%vec = w ↔ u = (w + v)%vec.
Proof.
intros.
split; intros H.
 rewrite <- H.
 unfold vec_sub.
 rewrite <- vec_add_assoc.
 rewrite vec_add_opp_diag_l.
 now rewrite vec_add_0_r.

 rewrite H.
 unfold vec_sub.
 rewrite <- vec_add_assoc.
 rewrite vec_add_opp_diag_r.
 now rewrite vec_add_0_r.
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

Theorem mat_const_vec_mul : ∀ M v k,
  mat_vec_mul (mat_const_mul k M) v = mat_vec_mul M (vec_const_mul k v).
Proof.
intros.
destruct v as (x, y, z); simpl; f_equal; ring.
Qed.

Theorem mat_vec_mat_const_mul : ∀ M v k,
  mat_vec_mul (mat_const_mul k M) v = vec_const_mul k (mat_vec_mul M v).
Proof.
intros.
destruct v as (x, y, z); simpl; f_equal; ring.
Qed.

Theorem vec_dot_cross_mul : ∀ u v, u · (u × v) = 0.
Proof.
intros.
destruct u, v; simpl; lra.
Qed.

Theorem vec_cross_dot_mul : ∀ u v, u × v · u = 0.
Proof.
intros.
destruct u, v; simpl; lra.
Qed.

Theorem vec_dot_mul_0_l : ∀ v, 0 · v = 0.
Proof.
intros (x₁, y₁, z₁); simpl; lra.
Qed.

Theorem vec_dot_mul_0_r : ∀ v, (v · 0)%vec = 0.
Proof.
intros (x, y, z); simpl.
do 3 rewrite Rmult_0_r.
now do 2 rewrite Rplus_0_r.
Qed.

Theorem vec_dot_mul_add_distr_l : ∀ u v w,
  u · (v + w) = u · v + u · w.
Proof.
intros (x₁, y₁, z₁) (x₂, y₂, z₂) (x₃, y₃, z₃); simpl; lra.
Qed.

Theorem vec_dot_mul_sub_distr_l : ∀ u v w,
  u · (v - w) = u · v - u · w.
Proof.
intros (x₁, y₁, z₁) (x₂, y₂, z₂) (x₃, y₃, z₃); simpl; lra.
Qed.

Theorem vec_dot_mul_add_distr_r : ∀ u v w, (u + v) · w = u · w + v · w.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; lra.
Qed.

Theorem vec_dot_mul_sub_distr_r : ∀ u v w, (u - v) · w = u · w - v · w.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; lra.
Qed.

Theorem Rmult_vec_dot_mul_distr_l : ∀ a u v, a * (u · v) = a ⁎ u · v.
Proof.
intros a (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; lra.
Qed.

Theorem Rmult_vec_dot_mul_distr_r : ∀ a u v, a * (u · v) = u · a ⁎ v.
Proof.
intros a (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; lra.
Qed.

Theorem vec_dot_mul_diag : ∀ v, v · v = ‖v‖².
Proof.
intros (x, y, z); simpl.
do 3 rewrite fold_Rsqr.
rewrite Rsqr_sqrt; [ easy | ].
apply nonneg_sqr_vec_norm.
Qed.

Theorem vec_add_comm : ∀ u v, (u + v = v + u)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl.
f_equal; lra.
Qed.

Theorem vec_dot_mul_comm : ∀ u v, u · v = v · u.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; lra.
Qed.

Theorem vec_cross_mul_0_l : ∀ v, 0 × v = 0%vec.
Proof.
intros (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_cross_mul_0_r : ∀ v, v × 0 = 0%vec.
Proof.
intros (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_cross_mul_anticomm : ∀ u v, (u × v = - (v × u))%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_cross_mul_add_distr_l : ∀ u v w,
  (u × (v + w) = u × v + u × w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; lra.
Qed.

Theorem vec_cross_mul_add_distr_r : ∀ u v w,
  ((u + v) × w = u × w + v × w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; lra.
Qed.

Theorem vec_cross_mul_sub_distr_l : ∀ u v w,
  (u × (v - w) = u × v - u × w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; lra.
Qed.

Theorem vec_cross_mul_sub_distr_r : ∀ u v w,
  ((u - v) × w = u × w - v × w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; lra.
Qed.

Theorem vec_cross_mul_diag : ∀ v, v × v = 0%vec.
Proof.
intros (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_cross_mul_assoc_l : ∀ u v w,
  ((u × v) × w = (u · w) ⁎ v - (v · w) ⁎ u)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; ring.
Qed.

Theorem vec_cross_mul_assoc_r : ∀ u v w,
  (u × (v × w) = (u · w) ⁎ v - (u · v) ⁎ w)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; ring.
Qed.

Theorem vec_opp_add_distr : ∀ u v, (- (u + v) = - u - v)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_opp_sub_distr : ∀ u v, (- (u - v) = - u + v)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_opp_dot_mul_distr_l : ∀ u v, - (u · v) = - u · v.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; lra.
Qed.

Theorem vec_opp_dot_mul_distr_r : ∀ u v, - (u · v) = u · - v.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; lra.
Qed.

Theorem vec_opp_const_mul_distr_l : ∀ a v, (- (a ⁎ v) = - a ⁎ v)%vec.
Proof.
intros a (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_opp_const_mul_distr_r : ∀ a v, (- (a ⁎ v) = a ⁎ - v)%vec.
Proof.
intros a (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_const_mul_add_distr_l : ∀ a u v,
  (a ⁎ (u + v) = a ⁎ u + a ⁎ v)%vec.
Proof.
intros a (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_const_mul_add_distr_r : ∀ a b v,
  ((a + b) ⁎ v = a ⁎ v + b ⁎ v)%vec.
Proof.
intros a b (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_const_mul_sub_distr_l : ∀ a u v,
  (a ⁎ (u - v) = a ⁎ u - a ⁎ v)%vec.
Proof.
intros a (u₁, u₂, u₃) (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_const_mul_sub_distr_r : ∀ a b v,
  ((a - b) ⁎ v = a ⁎ v - b ⁎ v)%vec.
Proof.
intros a b (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem vec_add_shuffle0 : ∀ u v w, (u + v + w = u + w + v)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (w₁, w₂, w₃); simpl; f_equal; lra.
Qed.

Theorem vec_const_mul_eq_reg_l : ∀ a u v, a ⁎ u = a ⁎ v → a ≠ 0 → u = v.
Proof.
intros a (u₁, u₂, u₃) (v₁, v₂, v₃) Hauv Ha.
simpl in Hauv.
injection Hauv; clear Hauv; intros H₃ H₂ H₁.
apply Rmult_eq_reg_l in H₁; [ | easy ].
apply Rmult_eq_reg_l in H₂; [ | easy ].
apply Rmult_eq_reg_l in H₃; [ | easy ].
now subst.
Qed.

Theorem mat_vec_mul_0_r : ∀ M, (M * 0)%vec = 0%vec.
Proof.
intros; simpl.
do 9 rewrite Rmult_0_r.
now do 2 rewrite Rplus_0_r.
Qed.

Theorem mat_opp_vec_mul_distr_r : ∀ M v, (M * - v = - (M * v))%vec.
Proof.
intros M (x, y, z); simpl; f_equal; lra.
Qed.

Theorem mat_trace_comm : ∀ A B, mat_trace (A * B) = mat_trace (B * A).
Proof. intros. unfold mat_trace; simpl; lra. Qed.

Theorem mat_trace_change_basis : ∀ A A' B,
  (A' * A = mat_id)%mat
  → mat_trace (A * B * A')%mat = mat_trace B.
Proof.
intros * HAA.
rewrite mat_trace_comm.
rewrite mat_mul_assoc.
rewrite HAA.
now rewrite mat_mul_id_l.
Qed.

Theorem mat_pow_succ : ∀ M n, (M ^ S n)%mat = (M * M ^ n)%mat.
Proof. easy. Qed.

Theorem vec_sqr_0 : 0²%vec = 0.
Proof. simpl; lra. Qed.

Theorem vec_sqr_eq_0 : ∀ v, (v² = 0%R → v = 0)%vec.
Proof.
intros (x, y, z) Hv; simpl in Hv |-*.
apply sqr_vec_norm_eq_0 in Hv.
now destruct Hv as (H1 & H2 & H3); subst.
Qed.

Theorem vec_sqr_const_mul : ∀ a v, (a ⁎ v)²%vec = a² * v²%vec.
Proof.
intros a (v₁, v₂, v₃); simpl; unfold Rsqr; lra.
Qed.

Theorem normalized_vector : ∀ u v, u ≠ 0%vec → v = / ‖u‖ ⁎ u → ‖v‖ = 1.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) Hu Hv.
simpl in Hv; simpl.
injection Hv; clear Hv; intros H₃ H₂ H₁.
remember (√ (u₁² + u₂² + u₃²)) as ur eqn:Hur.
assert (H : ur ≠ 0).
 intros H; subst ur.
 apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in H.
 destruct H as (H1 & H2 & H3).
 now subst.

 subst v₁ v₂ v₃.
 do 3 rewrite Rsqr_mult.
 do 2 rewrite <- Rmult_plus_distr_l.
 rewrite sqrt_mult; [ | apply Rle_0_sqr | apply nonneg_sqr_vec_norm ].
 rewrite <- Hur.
 rewrite sqrt_Rsqr; [ now rewrite Rinv_l | ].
 apply Rlt_le, Rinv_0_lt_compat.
 apply Rneq_le_lt; [ now intros HH; apply H | ].
 rewrite Hur; apply sqrt_pos.
Qed.

Theorem vec_div_vec_norm : ∀ v, v ≠ 0%vec → ‖(v ⁄ ‖v‖)‖ = 1.
Proof.
intros * Hv.
eapply normalized_vector; [ eassumption | easy ].
Qed.

(* Inversion of vectors and matrices *)

Definition vec_inv M '(V x y z) :=
  V (mat_det (mkrmat x (a₁₂ M) (a₁₃ M) y (a₂₂ M) (a₂₃ M) z (a₃₂ M) (a₃₃ M)))
    (mat_det (mkrmat (a₁₁ M) x (a₁₃ M) (a₂₁ M) y (a₂₃ M) (a₃₁ M) z (a₃₃ M)))
    (mat_det (mkrmat (a₁₁ M) (a₁₂ M) x (a₂₁ M) (a₂₂ M) y (a₃₁ M) (a₃₂ M) z)).

Theorem vec_inv_is_root : ∀ M v, (M * vec_inv M v = mat_det M ⁎ v)%vec.
Proof.
intros M v.
unfold mat_vec_mul, mat_vec_mul, vec_inv, mat_det, mkrmat; simpl.
destruct v as (x, y, z); simpl.
f_equal; lra.
Qed.

Definition mat_compl M :=
  let '(V b₁₁ b₂₁ b₃₁) := vec_inv M (V 1 0 0) in
  let '(V b₁₂ b₂₂ b₃₂) := vec_inv M (V 0 1 0) in
  let '(V b₁₃ b₂₃ b₃₃) := vec_inv M (V 0 0 1) in
  mkrmat b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃.

Definition mat_inv M := (mat_compl M ⁄ mat_det M)%mat.

Theorem mat_mul_compl_l : ∀ M, (mat_compl M * M = mat_det M ⁎ mat_id)%mat.
Proof.
intros.
destruct M; simpl.
unfold mat_mul; simpl.
unfold mat_det; simpl.
unfold mat_const_mul; simpl.
f_equal; lra.
Qed.

Theorem mat_mul_compl_r : ∀ M, (M * mat_compl M = mat_det M ⁎ mat_id)%mat.
Proof.
intros.
destruct M; simpl.
unfold mat_mul; simpl.
unfold mat_det; simpl.
unfold mat_const_mul; simpl.
f_equal; lra.
Qed.

Theorem mat_det_id : mat_det mat_id = 1.
Proof.
unfold mat_det, mat_id; simpl; lra.
Qed.

Theorem mat_det_mul_distr : ∀ M₁ M₂,
  mat_det (M₁ * M₂) = mat_det M₁ * mat_det M₂.
Proof.
intros; unfold mat_mul, mat_det; simpl; lra.
Qed.

Theorem mat_const_mul_assoc : ∀ a b M, (a ⁎ (b ⁎ M) = (a * b) ⁎ M)%mat.
Proof.
intros; unfold mat_const_mul; simpl; f_equal; lra.
Qed.

Theorem mat_const_mul_1_l : ∀ M, (1 ⁎ M = M)%mat.
Proof.
intros; unfold mat_const_mul, mkrmat; destruct M; simpl; f_equal; lra.
Qed.

Theorem mat_mul_id_comm : ∀ M M',
  (M * M')%mat = mat_id
  → (M' * M)%mat = mat_id.
Proof.
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
destruct (Req_dec (mat_det M) 0) as [Hd| Hd].
 rewrite Hd, Rmult_0_l in HMM'; lra.

 apply (f_equal (mat_const_mul (/ mat_det M))) in H.
 rewrite mat_const_mul_assoc in H.
 rewrite Rinv_l in H; [ | easy ].
 rewrite mat_const_mul_1_l in H.
 rewrite H.
 rewrite <- mat_const_mul_distr_l.
 rewrite mat_mul_compl_l.
 rewrite mat_const_mul_assoc.
 rewrite Rinv_l; [ | easy ].
 now rewrite mat_const_mul_1_l.
Qed.

Theorem rotation_transp_is_rotation : ∀ M,
  is_rotation_matrix M → is_rotation_matrix (mat_transp M).
Proof.
intros M HM.
destruct HM as (Htr, Hdet).
split.
 rewrite mat_transp_involutive.
 now apply mat_mul_id_comm.

 clear Htr.
 unfold mat_det in Hdet; simpl in Hdet.
 unfold mat_det, mat_transp; simpl; lra.
Qed.

(* Cauchy-Schwarz inequality with vectors. *)

Theorem vec_Lagrange_identity : ∀ u v,
  ‖u‖² * ‖v‖² - (u · v)² = (u × v)²%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃).
simpl.
rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
unfold Rsqr; lra.
Qed.

Arguments vec_Lagrange_identity u%vec v%vec.

Theorem vec_Cauchy_Schwarz_inequality : ∀ u v, (u · v)² ≤ ‖u‖² * ‖v‖².
Proof.
intros.
apply Rplus_le_reg_r with (r := -(u · v)²).
rewrite Rplus_opp_r.
rewrite fold_Rminus, vec_Lagrange_identity.
rewrite vec_dot_mul_diag.
apply Rle_0_sqr.
Qed.

(* *)

Theorem mat_rot_inv : ∀ M, is_rotation_matrix M → mat_inv M = mat_transp M.
Proof.
intros M Hr.
destruct Hr as (Htr, Hdet).
unfold mat_inv; rewrite Hdet.
rewrite Rinv_1.
rewrite mat_const_mul_1_l.
destruct M; simpl.
unfold mat_compl, mat_transp; simpl.
unfold mat_det; simpl.
do 9 rewrite Rmult_1_l, Rmult_0_l.
do 6 rewrite Rmult_0_r.
do 7 rewrite Rminus_0_r.
do 3 rewrite Rmult_0_r.
do 8 rewrite Rplus_0_r.
do 4 rewrite Rplus_0_l.
do 6 rewrite Rminus_0_l, Rmult_1_r.
unfold mat_det in Hdet; simpl in Hdet.
unfold mat_transp in Htr; simpl in Htr.
unfold mat_mul in Htr; simpl in Htr.
unfold mat_id, mkrmat in Htr; simpl in Htr.
injection Htr; clear Htr; intros H33 H32 H31 H23 H22 H21 H13 H12 H11.
unfold mkrmat; simpl.
clear H33 H23 H13 H12.
Time f_equal;
 [ clear H22 H32; nsatz | clear H11 H31; nsatz | nsatz |
   clear H22 H32; nsatz | clear H11 H31; nsatz | nsatz |
   clear H22 H32; nsatz | clear H11 H31; nsatz | nsatz ].
Qed.

(* *)

(* Non-nul vector belonging to the axis of rotation.
   Works for rotations angles different from 0 and π,
   i.e. transpositor ≠ 0 (a "transpositor" is a name I
   give to a vector which is nul iff the matrix is equal
   to its transpose; this name is inspired from the
   name "commutator") *)
Definition rotation_axis (M : matrix ℝ) :=
  let x := a₃₂ M - a₂₃ M in
  let y := a₁₃ M - a₃₁ M in
  let z := a₂₁ M - a₁₂ M in
  V x y z.

Definition vec_normalize v := v ⁄ ‖v‖.

Definition rotation_unit_axis (M : matrix ℝ) :=
  vec_normalize (rotation_axis M).

Definition rotation_fixpoint (m : matrix ℝ) k :=
  vec_const_mul k (rotation_unit_axis m).

Definition matrix_of_unit_axis_angle '(V x y z, s, c) :=
  mkrmat
    (x²*(1-c)+c) (x*y*(1-c)-z*s) (x*z*(1-c)+y*s)
    (x*y*(1-c)+z*s) (y²*(1-c)+c) (y*z*(1-c)-x*s)
    (x*z*(1-c)-y*s) (y*z*(1-c)+x*s) (z²*(1-c)+c).

Definition matrix_of_axis_angle '(V x y z, s, c) :=
  let r := √ (x² + y² + z²) in
  let ux := x / r in
  let uy := y / r in
  let uz := z / r in
  matrix_of_unit_axis_angle (V ux uy uz, s, c).

Definition axis_angle_of_matrix M :=
  let cosθ := (mat_trace M - 1) / 2 in
  let sinθ := √ (1 - cosθ²) in
  let v := rotation_unit_axis M in
  (v, sinθ, cosθ).

Arguments axis_angle_of_matrix M%mat.

(* https://en.wikipedia.org/wiki/Rotation_matrix#Determining_the_angle *)
Definition cos_rot_angle M := (mat_trace M - 1) / 2.

Theorem unit_sphere_mat_trace_eq : ∀ v s c,
  ‖v‖ = 1
  → mat_trace (matrix_of_axis_angle (v, s, c)) = 1 + 2 * c.
Proof.
intros * Hv.
remember (matrix_of_axis_angle (v, s, c)) as M eqn:HM.
unfold mat_trace.
unfold matrix_of_axis_angle in HM.
destruct v as (x, y, z).
simpl in Hv.
rewrite Hv in HM.
do 3 rewrite Rdiv_1_r in HM.
simpl in HM.
unfold mkrmat in HM.
apply (f_equal Rsqr) in Hv.
rewrite Rsqr_sqrt in Hv; [ | apply nonneg_sqr_vec_norm ].
rewrite Rsqr_1 in Hv.
destruct M; simpl in *.
injection HM; clear HM; intros H33 H32 H31 H23 H22 H21 H13 H12 H11.
subst.
Time nsatz.
Qed.

Theorem matrix_mul_axis : ∀ p c s k,
  k ≠ 0
  → matrix_of_axis_angle (p, s, c) =
    matrix_of_axis_angle (k ⁎ p, Rsign k * s, c).
Proof.
intros * Hk.
destruct (vec_eq_dec p 0%vec) as [Hpz| Hpz].
 subst p; simpl; rewrite Rmult_0_r.
 rewrite Rsqr_0; do 2 rewrite Rplus_0_l.
 rewrite Rdiv_0_l, Rsqr_0.
 now do 5 rewrite Rmult_0_l.

 destruct p as (xp, yp, zp); simpl.
 remember (√ ((k * xp)² + (k * yp)² + (k * zp)²)) as a eqn:Ha.
 do 3 rewrite Rsqr_mult in Ha.
 do 2 rewrite <- Rmult_plus_distr_l in Ha.
 rewrite sqrt_mult in Ha; [ | apply Rle_0_sqr | apply nonneg_sqr_vec_norm ].
 remember (√ (xp² + yp² + zp²)) as b eqn:Hb.
 assert (Hbz : b ≠ 0).
  subst b; intros H.
  apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
  apply sqr_vec_norm_eq_0 in H.
  destruct H as (H1 & H2 & H3).
  now rewrite H1, H2, H3 in Hpz.

  unfold Rsign.
  destruct (Req_dec k 0) as [Hkz| Hkz]; [ lra | clear Hkz ].
  destruct (Rle_dec 0 k) as [Hkp| Hkn].
   rewrite Rmult_1_l.
   rewrite sqrt_Rsqr in Ha; [ | lra ].
   assert (Hx : ∀ x, k * x / a = x / b).
    intros x; subst a; unfold Rdiv.
    rewrite Rinv_mult_distr; [ | lra | easy ].
    rewrite <- Rmult_assoc.
    progress replace (k * x * / k) with (/ k * k * x) by lra.
    rewrite Rinv_l; lra.

    now do 3 rewrite Hx.

   apply Rnot_le_lt in Hkn.
   rewrite sqrt_Rsqr_abs in Ha.
   unfold Rabs in Ha.
   destruct (Rcase_abs k) as [H| H]; [ clear H | lra ].
   assert (Hx : ∀ x, k * x / a = - (x / b)).
    intros x; subst a; unfold Rdiv.
    rewrite Rinv_mult_distr; [ | lra | easy ].
    rewrite <- Rmult_assoc.
    rewrite <- Ropp_inv_permute; [ | easy ].
    progress replace (k * x * - / k) with (/ k * k * - x) by lra.
    rewrite Rinv_l; lra.

    do 3 rewrite Hx, <- Rsqr_neg.
    f_equal; lra.
Qed.

Theorem mat_trace_eq : ∀ v s c,
  v ≠ 0%vec
  → mat_trace (matrix_of_axis_angle (v, s, c)) = 1 + 2 * c.
Proof.
intros * Hv.
specialize (vec_div_vec_norm v Hv) as Hvn.
specialize (unit_sphere_mat_trace_eq (v ⁄ ‖v‖) s c Hvn) as H.
rewrite matrix_mul_axis with (k := ‖v‖) in H; [ | now apply vec_norm_neq_0 ].
rewrite vec_const_mul_assoc in H.
rewrite Rinv_r in H; [ | now apply vec_norm_neq_0 ].
rewrite vec_const_mul_1_l in H.
rewrite Rsign_of_pos in H; [ now rewrite Rmult_1_l in H | ].
now apply vec_norm_pos.
Qed.

Theorem rotation_mat_mul_transp_l : ∀ M,
  is_rotation_matrix M →
  (mat_transp M * M)%mat = mat_id.
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

Theorem mat_pow_1 : ∀ M, (M ^ 1)%mat = M.
Proof. intros; apply mat_mul_id_r. Qed.
