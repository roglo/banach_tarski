(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List.
Require Import Reals Psatz.

Require Import Words Normalize Reverse MiscReals.

(* starting a new implementation *)

Record vector A n := mkvec
  { vec : list A;
    vprop : length vec = n }.

Record matrix' A m n := mkmat'
  { mat : list (vector A n);
    mprop : length mat = m }.

Theorem vprop_map : ∀ A B (f : A → B) n V, length (map f (vec A n V)) = n.
Proof.
intros A B f n (v, p); simpl.
now rewrite map_length.
Qed.

Definition vec_map A B n (f : A → B) V :=
  mkvec B n (map f (vec A n V)) (vprop_map A B f n V).

Theorem mprop_map : ∀ A B (f : A → B) m n M,
  length (map (vec_map A B n f) (mat A m n M)) = m.
Proof.
intros A B f m n (ma, pr); simpl.
now rewrite map_length.
Qed.

Definition mat_map' A B m n (f : A → B) M :=
  mkmat' B m n (map (vec_map A B n f) (mat A m n M)) (mprop_map A B f m n M).

Definition vecel {A n} d V i := List.nth (pred i) (vec A n V) d.

Definition matel {A m n} d (M : matrix' A m n) i j :=
  let V := List.nth (pred i) (map (vec A n) (mat A m n M)) (repeat d n) in
  List.nth (pred j) V d.

Import ListNotations.

Definition mkrvec (a b c : ℝ) :=
  mkvec _ 3 [a; b; c] eq_refl.

Definition mkrmat' (a b c d e f g h i : ℝ) :=
  mkmat' _ 3 _ [mkrvec a b c; mkrvec d e f; mkrvec g h i] eq_refl.

Definition rvecel (V : vector ℝ 3) := vecel 0%R V.
Definition rmatel (M : matrix' ℝ 3 3) := matel 0%R M.

Definition m₁₁ M := rmatel M 1 1.
Definition m₁₂ M := rmatel M 1 2.
Definition m₁₃ M := rmatel M 1 3.
Definition m₂₁ M := rmatel M 2 1.
Definition m₂₂ M := rmatel M 2 2.
Definition m₂₃ M := rmatel M 2 3.
Definition m₃₁ M := rmatel M 3 1.
Definition m₃₂ M := rmatel M 3 2.
Definition m₃₃ M := rmatel M 3 3.
Definition xv V := rvecel V 1.
Definition yv V := rvecel V 2.
Definition zv V := rvecel V 3.

Definition mat_vec_mul' (M : matrix' ℝ 3 3) (V : vector ℝ 3) :=
  mkrvec
    (m₁₁ M * xv V + m₁₂ M * yv V + m₁₃ M * zv V)
    (m₂₁ M * xv V + m₂₂ M * yv V + m₂₃ M * zv V)
    (m₃₁ M * xv V + m₃₂ M * yv V + m₃₃ M * zv V).

Definition vec_norm' V :=
  √ ((xv V)² + (yv V)² + (zv V)²).
Definition vec_add' U V :=
  mkrvec (xv U * xv V) (yv U * yv V) (zv U * zv V).
Definition vec_dot_mul' U V :=
  (xv U * xv V + yv U * yv V + zv U * zv V)%R.
Definition vec_cross_mul' U V :=
  mkrvec
    (yv U * zv V - zv U * yv V)
    (zv U * xv V - xv U * zv V)
    (xv U * yv V - yv U * xv V).
Definition mul_const_vec' k V := mkrvec (k * xv V) (k * yv V) (k * zv V).
Definition mul_const_mat' k M :=
  mkrmat'
    (k * m₁₁ M) (k * m₁₂ M) (k * m₁₃ M)
    (k * m₂₁ M) (k * m₂₂ M) (k * m₂₃ M)
    (k * m₃₁ M) (k * m₃₂ M) (k * m₃₃ M).

Delimit Scope vec_scope' with vec'.
Notation "0" := (mkrvec 0 0 0) : vec_scope'.
Notation "k ⁎ V" := (mul_const_vec' k V) (at level 40) : vec_scope'.
Notation "M * V" := (mat_vec_mul' M V) : vec_scope'.
Notation "U + V" := (vec_add' U V) : vec_scope'.
Notation "U • V" := (vec_dot_mul' U V) (at level 40, left associativity) :
  vec_scope'.
Notation "U × V" := (vec_cross_mul' U V) (at level 40, left associativity) :
  vec_scope'.
Notation "∥ V ∥" := (vec_norm' V) (at level 0, V at level 0, format "∥ V ∥") :
  vec_scope'.

Definition rot_x' := mkrmat'
  1         0         0
  0         (1/3)     (-2*√2/3)
  0         (2*√2/3)  (1/3).
Definition rot_inv_x' := mkrmat'
  1         0         0
  0         (1/3)     (2*√2/3)
  0         (-2*√2/3) (1/3).
Definition rot_z' := mkrmat'
  (1/3)     (-2*√2/3) 0
  (2*√2/3)  (1/3)     0
  0         0         1.
Definition rot_inv_z' := mkrmat'
  (1/3)     (2*√2/3)  0
  (-2*√2/3) (1/3)     0
  0         0         1.

Definition is_neg_vec V :=
  if Rlt_dec (xv V) 0 then true
  else if Rgt_dec (xv V) 0 then false
  else if Rlt_dec (yv V) 0 then true
  else if Rgt_dec (yv V) 0 then false
  else if Rlt_dec (zv V) 0 then true
  else if Rgt_dec (zv V) 0 then false
  else true.

Definition mat_of_elem' e :=
  match e with
  | ạ => rot_x'
  | ạ⁻¹ => rot_inv_x'
  | ḅ => rot_z'
  | ḅ⁻¹ => rot_inv_z'
  end.

Definition rotate' e pt := mat_vec_mul' (mat_of_elem' e) pt.

Definition mat_mul' m₁ m₂ :=
  mkrmat'
    (m₁₁ m₁ * m₁₁ m₂ + m₁₂ m₁ * m₂₁ m₂ + m₁₃ m₁ * m₃₁ m₂)
    (m₁₁ m₁ * m₁₂ m₂ + m₁₂ m₁ * m₂₂ m₂ + m₁₃ m₁ * m₃₂ m₂)
    (m₁₁ m₁ * m₁₃ m₂ + m₁₂ m₁ * m₂₃ m₂ + m₁₃ m₁ * m₃₃ m₂)
    (m₂₁ m₁ * m₁₁ m₂ + m₂₂ m₁ * m₂₁ m₂ + m₂₃ m₁ * m₃₁ m₂)
    (m₂₁ m₁ * m₁₂ m₂ + m₂₂ m₁ * m₂₂ m₂ + m₂₃ m₁ * m₃₂ m₂)
    (m₂₁ m₁ * m₁₃ m₂ + m₂₂ m₁ * m₂₃ m₂ + m₂₃ m₁ * m₃₃ m₂)
    (m₃₁ m₁ * m₁₁ m₂ + m₃₂ m₁ * m₂₁ m₂ + m₃₃ m₁ * m₃₁ m₂)
    (m₃₁ m₁ * m₁₂ m₂ + m₃₂ m₁ * m₂₂ m₂ + m₃₃ m₁ * m₃₂ m₂)
    (m₃₁ m₁ * m₁₃ m₂ + m₃₂ m₁ * m₂₃ m₂ + m₃₃ m₁ * m₃₃ m₂).

Definition mat_id' :=
  mkrmat'
    1 0 0
    0 1 0
    0 0 1.

Delimit Scope mat_scope' with mat'.
Notation "m₁ * m₂" := (mat_mul' m₁ m₂) : mat_scope'.

(* P.M. Pédrot's code *)

Definition inj {n m} (p : n = m) : S n = S m.
Proof. now destruct p. Defined.

Lemma uip_nat : ∀ (n : nat) (p q : n = n), p = q.
Proof.
induction n.
 destruct p; intros q.
 now refine (match q in _ = m with eq_refl => _ end).

 destruct p; intros q.
 refine (
   match q in _ = m return
     match m return ∀ (q : S n = m), Type with
     | 0 => fun _ => unit
     | S i => fun q => ∀ (p : n = i), inj p = q
     end q
   with
   | eq_refl => _
   end eq_refl).
 intros p.
 now rewrite (IHn p eq_refl).
Qed.

(* end P.M. Pédrot's code *)

Theorem eq_vec_list : ∀ A n (U V : vector A n),
  U = V ↔ vec A n U = vec A n V.
Proof.
intros.
split; [ now intros; subst | ].
intros HUV.
destruct U as (vu, pu).
destruct V as (vv, pv); simpl in HUV; simpl.
subst vv; f_equal.
destruct pu; apply uip_nat.
Qed.

Theorem eq_vec_dec : ∀ U V : vector ℝ 3, { U = V } + { U ≠ V }.
Proof.
intros.
destruct (Req_dec (xv U) (xv V)) as [Hx| Hx].
 destruct (Req_dec (yv U) (yv V)) as [Hy| Hy].
  destruct (Req_dec (zv U) (zv V)) as [Hz| Hz].
   left.
   apply eq_vec_list.
   destruct U as (vu, pu).
   destruct V as (vv, pv); simpl in Hx, Hy, Hz; simpl.
   unfold xv in Hx; unfold yv in Hy; unfold zv in Hz.
   unfold rvecel, vecel in Hx, Hy, Hz; simpl in Hx, Hy, Hz.
Abort. (* to be completed *)

(* end of new implementation *)

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

Inductive point := P : ℝ → ℝ → ℝ → point.

Definition neg_point '(P x y z) := P (-x) (-y) (-z).

Definition mat_vec_mul mat '(P x y z) :=
  P (a₁₁ mat * x + a₁₂ mat * y + a₁₃ mat * z)
    (a₂₁ mat * x + a₂₂ mat * y + a₂₃ mat * z)
    (a₃₁ mat * x + a₃₂ mat * y + a₃₃ mat * z).

Definition vec_norm '(P x y z) := √ (x² + y² + z²).
Definition vec_add '(P u₁ u₂ u₃) '(P v₁ v₂ v₃) :=
  P (u₁ + v₁) (u₂ + v₂) (u₃ + v₃).
Definition vec_dot_mul '(P x₁ y₁ z₁) '(P x₂ y₂ z₂) :=
  (x₁ * x₂ + y₁ * y₂ + z₁ * z₂)%R.
Definition vec_cross_mul '(P u₁ u₂ u₃) '(P v₁ v₂ v₃) :=
  P (u₂ * v₃ - u₃ * v₂) (u₃ * v₁ - u₁ * v₃) (u₁ * v₂ - u₂ * v₁).
Definition mul_const_vec k '(P x y z) := P (k * x) (k * y) (k * z).
Definition mul_const_mat k (M : matrix ℝ) :=
  mkrmat
    (k * a₁₁ M) (k * a₁₂ M) (k * a₁₃ M)
    (k * a₂₁ M) (k * a₂₂ M) (k * a₂₃ M)
    (k * a₃₁ M) (k * a₃₂ M) (k * a₃₃ M).

Delimit Scope vec_scope with vec.
Notation "0" := (P 0 0 0) : vec_scope.
Notation "k ⁎ V" := (mul_const_vec k V) (at level 40) : vec_scope.
Notation "M * V" := (mat_vec_mul M V) : vec_scope.
Notation "U + V" := (vec_add U V) : vec_scope.
Notation "U • V" := (vec_dot_mul U V) (at level 40, left associativity).
Notation "U × V" := (vec_cross_mul U V) (at level 40, left associativity).
Notation "∥ V ∥" := (vec_norm V) (at level 0, V at level 0, format "∥ V ∥").

(* https://en.wikipedia.org/wiki/Rotation_matrix
   #Rotation_matrix_from_axis_and_angle *)
Definition rot_mat_of_axis_cos '(P x y z) cosθ :=
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

Definition is_neg_point '(P x y z) :=
  if Rlt_dec x 0 then true
  else if Rgt_dec x 0 then false
  else if Rlt_dec y 0 then true
  else if Rgt_dec y 0 then false
  else if Rlt_dec z 0 then true
  else if Rgt_dec z 0 then false
  else true.

Theorem rot_x_means_rot_x : rot_x = rot_mat_of_axis_cos (P 1 0 0) (1/3).
Proof.
unfold rot_x; simpl.
setoid_rewrite Rsqr_pow2.
f_equal; try lra; ring_simplify.
 replace (1 - (1 / 3) ^ 2)%R with (2 * (2 / 3) ^ 2)%R by field.
 rewrite sqrt_mult; [ rewrite sqrt_pow2; lra | lra | lra ].

 replace (1 - (1 / 3) ^ 2)%R with (2 * (2 / 3) ^ 2)%R by field.
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

Definition mat_mul m₁ m₂ :=
  mkrmat
    (a₁₁ m₁ * a₁₁ m₂ + a₁₂ m₁ * a₂₁ m₂ + a₁₃ m₁ * a₃₁ m₂)
    (a₁₁ m₁ * a₁₂ m₂ + a₁₂ m₁ * a₂₂ m₂ + a₁₃ m₁ * a₃₂ m₂)
    (a₁₁ m₁ * a₁₃ m₂ + a₁₂ m₁ * a₂₃ m₂ + a₁₃ m₁ * a₃₃ m₂)
    (a₂₁ m₁ * a₁₁ m₂ + a₂₂ m₁ * a₂₁ m₂ + a₂₃ m₁ * a₃₁ m₂)
    (a₂₁ m₁ * a₁₂ m₂ + a₂₂ m₁ * a₂₂ m₂ + a₂₃ m₁ * a₃₂ m₂)
    (a₂₁ m₁ * a₁₃ m₂ + a₂₂ m₁ * a₂₃ m₂ + a₂₃ m₁ * a₃₃ m₂)
    (a₃₁ m₁ * a₁₁ m₂ + a₃₂ m₁ * a₂₁ m₂ + a₃₃ m₁ * a₃₁ m₂)
    (a₃₁ m₁ * a₁₂ m₂ + a₃₂ m₁ * a₂₂ m₂ + a₃₃ m₁ * a₃₂ m₂)
    (a₃₁ m₁ * a₁₃ m₂ + a₃₂ m₁ * a₂₃ m₂ + a₃₃ m₁ * a₃₃ m₂).

Definition mat_id :=
  mkrmat
    1 0 0
    0 1 0
    0 0 1.

Delimit Scope mat_scope with mat.
Notation "m₁ * m₂" := (mat_mul m₁ m₂) : mat_scope.

Theorem eq_point_dec : ∀ p₁ p₂ : point, { p₁ = p₂ } + { p₁ ≠ p₂ }.
Proof.
intros (x₁, y₁, z₁) (x₂, y₂, z₂).
destruct (Req_dec x₁ x₂) as [H₁| H₁]; [ subst x₂ | right ].
 destruct (Req_dec y₁ y₂) as [H₁| H₁]; [ subst y₂ | right ].
  destruct (Req_dec z₁ z₂) as [H₁| H₁]; [ now subst z₂; left | right ].
  now intros H; injection H; intros.

 now intros H; injection H; intros.

now intros H; injection H; intros.
Qed.

Theorem rmat_eq_dec : ∀ m₁ m₂ : matrix ℝ, { m₁ = m₂ } + { m₁ ≠ m₂ }.
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

Theorem mat_mul_id_l : ∀ m, mat_mul mat_id m = m.
Proof.
intros m.
unfold mat_mul, mat_id; simpl.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
now destruct m.
Qed.

Theorem mat_mul_id_r : ∀ m, mat_mul m mat_id = m.
Proof.
intros m.
unfold mat_mul, mat_id; simpl.
progress repeat rewrite Rmult_1_r.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
now destruct m.
Qed.

Theorem mat_vec_mul_id : ∀ p, mat_vec_mul mat_id p = p.
Proof.
intros (x, y, z).
unfold mat_vec_mul; simpl.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
easy.
Qed.

Theorem mat_vec_mul_assoc : ∀ m₁ m₂ p,
  mat_vec_mul (m₁ * m₂)%mat p = mat_vec_mul m₁ (mat_vec_mul m₂ p).
Proof.
intros m₁ m₂ (x, y, z).
unfold mat_vec_mul.
simpl; f_equal; lra.
Qed.

Theorem  mat_vec_add_cross_distr : ∀ M U V, (M * (U + V) = M * U + M * V)%vec.
Proof.
intros.
destruct U as (u₁, u₂, u₃).
destruct V as (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem  mat_vec_mul_const_distr : ∀ M k V, (M * (k ⁎ V) = k ⁎ (M * V))%vec.
Proof.
intros.
destruct V as (v₁, v₂, v₃); simpl; f_equal; lra.
Qed.

Theorem rot_rot_inv_x : ∀ pt,
  mat_vec_mul rot_x (mat_vec_mul rot_inv_x pt) = pt.
Proof.
intros.
unfold mat_vec_mul; simpl.
destruct pt as (x, y, z).
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rplus_0_l.
f_equal.
 field_simplify; simpl.
 unfold Rdiv.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite RMicromega.Rinv_1.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 now field_simplify.

 unfold Rdiv.
 field_simplify; simpl.
 progress repeat rewrite Rmult_1_r.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 now field_simplify.
Qed.

Theorem rot_inv_rot_x : ∀ pt,
  mat_vec_mul rot_inv_x (mat_vec_mul rot_x pt) = pt.
Proof.
intros.
unfold mat_vec_mul; simpl.
destruct pt as (x, y, z).
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rplus_0_l.
f_equal.
 field_simplify; simpl.
 unfold Rdiv.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite RMicromega.Rinv_1.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 now field_simplify.

 unfold Rdiv.
 field_simplify; simpl.
 progress repeat rewrite Rmult_1_r.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 now field_simplify.
Qed.

Theorem rot_rot_inv_z : ∀ pt,
  mat_vec_mul rot_z (mat_vec_mul rot_inv_z pt) = pt.
Proof.
intros.
unfold mat_vec_mul; simpl.
destruct pt as (x, y, z).
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rplus_0_l.
f_equal.
 field_simplify; simpl.
 unfold Rdiv.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite RMicromega.Rinv_1.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 now field_simplify.

 unfold Rdiv.
 field_simplify; simpl.
 progress repeat rewrite Rmult_1_r.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 now field_simplify.
Qed.

Theorem rot_inv_rot_z : ∀ pt,
  mat_vec_mul rot_inv_z (mat_vec_mul rot_z pt) = pt.
Proof.
intros.
unfold mat_vec_mul; simpl.
destruct pt as (x, y, z).
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rplus_0_l.
f_equal.
 field_simplify; simpl.
 unfold Rdiv.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite RMicromega.Rinv_1.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 now field_simplify.

 unfold Rdiv.
 field_simplify; simpl.
 progress repeat rewrite Rmult_1_r.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 now field_simplify.
Qed.

Theorem rotate_rotate_neg : ∀ e p, rotate e (rotate (negf e) p) = p.
Proof.
intros (t, d) p; simpl.
destruct t, d; simpl.
 apply rot_inv_rot_x.
 apply rot_rot_inv_x.
 apply rot_inv_rot_z.
 apply rot_rot_inv_z.
Qed.

Theorem rotate_neg_rotate : ∀ e p, rotate (negf e) (rotate e p) = p.
Proof.
intros (t, d) p; simpl.
destruct t, d; simpl.
 apply rot_rot_inv_x.
 apply rot_inv_rot_x.
 apply rot_rot_inv_z.
 apply rot_inv_rot_z.
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
  (a₁₁ m * (a₂₂ m * a₃₃ m - a₃₂ m * a₂₃ m) +
   a₁₂ m * (a₂₃ m * a₃₁ m - a₃₃ m * a₂₁ m) +
   a₁₃ m * (a₂₁ m * a₃₂ m - a₃₁ m * a₂₂ m))%R.

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

Theorem mat_mul_assoc : ∀ m₁ m₂ m₃,
  (m₁ * (m₂ * m₃) = m₁ * m₂ * m₃)%mat.
Proof.
intros m₁ m₂ m₃.
unfold mat_mul; simpl; f_equal; ring.
Qed.

Theorem mat_det_mul : ∀ m₁ m₂,
  mat_det (m₁ * m₂) = (mat_det m₂ * mat_det m₁)%R.
Proof.
intros m₁ m₂.
unfold mat_det; simpl; ring.
Qed.

Definition is_rotation_matrix A :=
  mat_mul A (mat_transp A) = mat_id ∧
  mat_det A = 1%R.

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

Theorem mul_const_vec_assoc : ∀ a b V,
  mul_const_vec a (mul_const_vec b V) = mul_const_vec (a * b) V.
Proof.
intros a b (x, y, z); simpl.
now do 3 rewrite Rmult_assoc.
Qed.

Theorem mul_const_vec_div : ∀ a b U V,
  a ≠ 0%R
  → mul_const_vec a U = mul_const_vec b V
  → U = mul_const_vec (b / a) V.
Proof.
intros * Ha Hm.
destruct U as (u₁, u₂, u₃).
destruct V as (v₁, v₂, v₃).
simpl in Hm; simpl.
injection Hm; clear Hm; intros H₃ H₂ H₁.
unfold Rdiv; setoid_rewrite Rmult_shuffle0.
rewrite <- H₁, <- H₂, <- H₃.
setoid_rewrite Rmult_shuffle0.
rewrite Rinv_r; [ | easy ].
now do 3 rewrite Rmult_1_l.
Qed.

Theorem vec_norm_nonneg : ∀ V, (0 ≤ ∥V∥)%R.
Proof.
intros (x, y, z); simpl.
apply sqrt_pos.
Qed.

Theorem nonneg_sqr_vec_norm : ∀ x y z, (0 ≤ x² + y² + z²)%R.
Proof.
intros.
apply Rplus_le_le_0_compat; [ | apply Rle_0_sqr ].
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Theorem vec_norm_mul_const_vec : ∀ a V,
  ∥(mul_const_vec a V)∥ = (Rabs a * ∥V∥)%R.
Proof.
intros a (x, y, z); simpl.
do 3 rewrite Rsqr_mult.
do 2 rewrite <- Rmult_plus_distr_l.
rewrite sqrt_mult; [ | apply Rle_0_sqr | apply nonneg_sqr_vec_norm ].
now rewrite sqrt_Rsqr_abs.
Qed.

Theorem vec_add_0_l : ∀ V, (0 + V = V)%vec.
Proof.
intros (x, y, z); simpl.
now do 3 rewrite Rplus_0_l.
Qed.

Theorem eq_mul_const_vec_0 : ∀ a V, (a ⁎ V = 0 → a = 0%R ∨ V = 0)%vec.
Proof.
intros a (x, y, z) HV; simpl in HV; simpl.
injection HV; intros Hz Hy Hx.
apply Rmult_integral in Hx.
apply Rmult_integral in Hy.
apply Rmult_integral in Hz.
destruct Hx as [Hx| Hx]; [ now left | subst x ].
destruct Hy as [Hy| Hy]; [ now left | subst y ].
destruct Hz as [Hz| Hz]; [ now left | subst z ].
now right.
Qed.

Theorem mul_const_vec_0_l : ∀ V, (0 ⁎ V = 0)%vec.
Proof.
intros (x, y, z); simpl.
now do 3 rewrite Rmult_0_l.
Qed.

Theorem mul_const_vec_1 : ∀ V, mul_const_vec 1 V = V.
Proof.
intros (x, y, z).
unfold mul_const_vec.
now do 3 rewrite Rmult_1_l.
Qed.

Theorem is_neg_point_0 : is_neg_point (P 0 0 0) = true.
Proof.
simpl.
destruct (Rlt_dec 0 0) as [H₁| H₁]; [ easy | clear H₁ ].
destruct (Rgt_dec 0 0) as [H₁| H₁]; [ | easy ].
now apply Rgt_irrefl in H₁.
Qed.

Theorem is_neg_point_neg_point : ∀ V,
  V ≠ 0%vec
  → is_neg_point (neg_point V) = negb (is_neg_point V).
Proof.
intros (x, y, z) HV; simpl.
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
      now exfalso; apply HV.
Qed.
