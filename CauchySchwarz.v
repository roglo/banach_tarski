(* Cauchy-Schwarz in any dimension *)
(* Compiled with Coq 8.6 *)

Require Import Utf8 List Reals Psatz.
Import ListNotations.

Notation "x '≤' y" := (Rle x y) : R_scope.

Fixpoint dot_mul u v :=
  match u with
  | [] => 0%R
  | u₁ :: ul =>
      match v with
      | [] => 0%R
      | v₁ :: vl => (u₁ * v₁ + dot_mul ul vl)%R
      end
  end.

Theorem Rle_0_sqr_dot_mul : ∀ u, (0 ≤ dot_mul u u)%R.
Proof.
intros.
induction u as [| u₁ ul]; simpl; [ lra | ].
fold (Rsqr u₁).
apply Rplus_le_le_0_compat; [ apply Rle_0_sqr | easy ].
Qed.

Theorem Cauchy_Schwarz_inequality : ∀ (u v : list R),
  ((dot_mul u v)² ≤ dot_mul u u * dot_mul v v)%R.
Proof.
intros.
revert v.
induction u as [| u₁ ul]; intros; [ simpl; rewrite Rsqr_0, Rmult_0_l; lra | ].
simpl.
destruct v as [| v₁ vl]; [ simpl; rewrite Rsqr_0, Rmult_0_r; lra | ].
unfold Rsqr; simpl.
ring_simplify.
progress repeat rewrite Rplus_assoc.
apply Rplus_le_compat_l.
progress repeat rewrite <- Rsqr_pow2.
rewrite <- Rplus_assoc.
eapply Rle_trans; [ apply Rplus_le_compat_l, IHul | ].
apply Rplus_le_compat_r.
destruct (Rle_dec (2 * u₁ * v₁ * dot_mul ul vl) 0) as [Hneg| Hpos].
 eapply Rle_trans; [ eexact Hneg | ].
 apply Rplus_le_le_0_compat.
  apply Rmult_le_pos; [ apply Rle_0_sqr | apply Rle_0_sqr_dot_mul ].
  apply Rmult_le_pos; [ apply Rle_0_sqr | apply Rle_0_sqr_dot_mul ].

 apply Rnot_le_lt in Hpos.
 apply Rsqr_incr_0; [ | now apply Rlt_le | ].
  progress repeat rewrite Rsqr_pow2.
  ring_simplify.
  progress repeat rewrite <- Rsqr_pow2.
  eapply Rle_trans.
   apply Rmult_le_compat_l; [ | apply IHul ].
   apply Rmult_le_pos; [ | apply Rle_0_sqr ].
   apply Rmult_le_pos; [ lra | apply Rle_0_sqr ].

   replace (4 * u₁² * v₁² * (dot_mul ul ul * dot_mul vl vl))%R
   with (4 * (u₁² * v₁² * dot_mul ul ul * dot_mul vl vl))%R
     by lra.
   replace (2 * u₁² * v₁² * dot_mul vl vl * dot_mul ul ul)%R
   with (2 * (u₁² * v₁² * dot_mul ul ul * dot_mul vl vl))%R by lra.
   remember (u₁² * v₁² * dot_mul ul ul * dot_mul vl vl)%R as a eqn:Ha.
   apply Rplus_le_reg_r with (r := (- 4 * a)%R).
   replace (4 * a + -4 * a)%R with 0%R by lra.
   ring_simplify.
   replace (u₁ ^ 4 * (dot_mul vl vl)² - 2 * a + v₁ ^ 4 * (dot_mul ul ul)²)%R
   with ((u₁² * dot_mul vl vl - v₁² * dot_mul ul ul)²)%R.
    apply Rle_0_sqr.

    progress repeat rewrite Rsqr_pow2.
    subst a; ring_simplify.
    progress repeat rewrite <- Rsqr_pow2.
    lra.

  apply Rplus_le_le_0_compat.
   apply Rmult_le_pos; [ apply Rle_0_sqr | apply Rle_0_sqr_dot_mul ].
   apply Rmult_le_pos; [ apply Rle_0_sqr | apply Rle_0_sqr_dot_mul ].
Qed.

Check Cauchy_Schwarz_inequality.

Definition small_det u v i j :=
  (nth i u 0%R * nth j v 0%R - nth j u 0%R * nth i v 0%R)%R.

Fixpoint sqr_sum_det_ij u v i j :=
  match j with
  | O => 0%R
  | S j' => ((small_det u v i j')² + sqr_sum_det_ij u v i j')%R
  end.

Fixpoint sqr_sum_det_i u v i :=
  match i with
  | 0 => 0%R
  | S i' => (sqr_sum_det_ij u v i' (length u) + sqr_sum_det_i u v i')%R
  end.

Definition sqr_sum_det u v := (sqr_sum_det_i u v (length u) / 2)%R.

Theorem nth_nil : ∀ A (d : A) n, nth n [] d = d.
Proof.
intros.
rewrite nth_overflow; [ easy | apply Nat.le_0_l ].
Qed.

Theorem small_det_nil_r : ∀ u i j, small_det u [] i j = 0%R.
Proof.
intros.
unfold small_det.
do 2 rewrite nth_nil, Rmult_0_r.
now rewrite Rminus_0_r.
Qed.

Theorem sqr_sum_det_ij_nil_r : ∀ u i j, sqr_sum_det_ij u [] i j = 0%R.
Proof.
intros.
induction j; simpl; [ easy | ].
rewrite IHj, Rplus_0_r.
now rewrite small_det_nil_r, Rsqr_0.
Qed.

Theorem sqr_sum_det_i_nil_r :  ∀ u i, sqr_sum_det_i u [] i = 0%R.
Proof.
intros.
induction i; simpl; [ easy | ].
now rewrite sqr_sum_det_ij_nil_r, IHi, Rplus_0_r.
Qed.

Theorem small_det_same : ∀ u v i, small_det u v i i = 0%R.
Proof.
intros.
unfold small_det.
now rewrite Rminus_diag_eq.
Qed.

Theorem Lagrange_identity : ∀ (u v : list R),
  (dot_mul u u * dot_mul v v - (dot_mul u v)² = sqr_sum_det u v)%R.
Proof.
intros.
unfold sqr_sum_det.
remember (length u) as len eqn:Hlen; symmetry in Hlen.
revert u v Hlen.
induction len; intros; simpl.
 apply length_zero_iff_nil in Hlen; subst u; simpl.
 rewrite Rmult_0_l, Rsqr_0, Rminus_0_r; lra.

 destruct u as [| u₁ u]; [ easy | simpl in Hlen ].
 apply Nat.succ_inj in Hlen.
 remember (length (u₁ :: u)) as len2 eqn:Hlen2; simpl.
 simpl in Hlen2; rewrite Hlen in Hlen2.
 destruct v as [| v₁ v]; simpl.
  rewrite Rmult_0_r, Rsqr_0, Rminus_0_r.
  rewrite sqr_sum_det_ij_nil_r, Rplus_0_l.
  rewrite sqr_sum_det_i_nil_r; lra.

  unfold Rsqr.
  replace
    ((u₁ * u₁ + dot_mul u u) * (v₁ * v₁ + dot_mul v v) -
     (u₁ * v₁ + dot_mul u v) * (u₁ * v₁ + dot_mul u v))%R
  with
    (dot_mul u u * dot_mul v v - (dot_mul u v) ^ 2 +
     (u₁ * u₁ * dot_mul v v + v₁ * v₁ * dot_mul u u -
      2 * u₁ * v₁ * dot_mul u v))%R
    by lra.
  rewrite <- Rsqr_pow2, IHlen; [ | easy ].
  subst len2; simpl.
  rewrite small_det_same, Rsqr_0, Rplus_0_l.
  apply Rmult_eq_reg_r with (r := 2%R); [ | lra ].
  rewrite Rmult_plus_distr_r.
  unfold Rdiv.
  rewrite Rmult_assoc, Rinv_l; [ rewrite Rmult_1_r | lra ].
  symmetry.
  rewrite Rmult_assoc, Rinv_l; [ rewrite Rmult_1_r | lra ].
bbb.
