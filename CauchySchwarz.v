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
