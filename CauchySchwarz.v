(* Cauchy-Schwarz in any dimension *)
(* Compiled with Coq 8.6 *)

Require Import Utf8 List Reals Psatz.
Import ListNotations.

Require Import SummationR.

Fixpoint dot_mul u v :=
  match u with
  | [] => 0%R
  | u₁ :: ul =>
      match v with
      | [] => 0%R
      | v₁ :: vl => (u₁ * v₁ + dot_mul ul vl)%R
      end
  end.

Theorem fold_Rminus : ∀ x y, (x + - y = x - y)%R.
Proof. intros. now fold (Rminus x y). Qed.

Theorem Rplus_shuffle0 : ∀ n m p : R, (n + m + p)%R = (n + p + m)%R.
Proof.
intros.
rewrite Rplus_comm, <- Rplus_assoc.
f_equal; apply Rplus_comm.
Qed.

Theorem Binet_Cauchy_identity : ∀ (a b c d : list R) n,
  (Σ (i = 1, n), (a.[i] * c.[i]) * Σ (j = 1, n), (b.[j] * d.[j]) =
   Σ (i = 1, n), (a.[i] * d.[i]) * Σ (j = 1, n), (b.[j] * c.[j]) +
   Σ (i = 1, n), Σ (j = i + 1, n),
     ((a.[i] * b.[j] - a.[j] * b.[i]) *
      (c.[i] * d.[j] - c.[j] * d.[i])))%R.
Proof.
intros.
remember (Σ (i = 1, n), (a.[i] * c.[i]) * Σ (j = 1, n), (b.[j] * d.[j]))%R
as x eqn:Hx.
remember (Σ (i = 1, n), (a.[i] * d.[i]) * Σ (j = 1, n), (b.[j] * c.[j]))%R
as y eqn:Hy.
remember
  (Σ (i = 1, n),
   Σ (j = i + 1, n),
   ((a.[i] * b.[j] - a.[j] * b.[i]) * (c.[i] * d.[j] - c.[j] * d.[i])))
as z eqn:Hz.
apply Rplus_eq_reg_r with (r := (- y)%R).
replace (y + z + - y)%R with z by lra.
replace (x + - y)%R with (x - y)%R by lra.
symmetry.
remember
  (Σ (i = 1, n), Σ (j = i + 1, n),
   (a.[i]*c.[i]*b.[j]*d.[j]+a.[j]*c.[j]*b.[i]*d.[i]))
  as u₁.
remember
  (Σ (i = 1, n), Σ (j = i + 1, n),
   (a.[i]*d.[i]*b.[j]*c.[j]+a.[j]*d.[j]*b.[i]*c.[i]))
  as u₂.
remember (Σ (i = 1, n), (a.[i]*c.[i]*b.[i]*d.[i])) as v₁.
remember (Σ (i = 1, n), (a.[i]*d.[i]*b.[i]*c.[i])) as v₂.
replace z with ((u₁ + v₁) - (u₂ + v₂))%R.
 assert
   (H : ∀ a b c d n,
    Σ (i = 1, n), Σ (j = 1, n), (a.[i] * c.[i] * b.[j] * d.[j]) =
   (Σ (i = 1, n),
    Σ (j = i + 1, n),
    (a.[i] * c.[i] * b.[j] * d.[j] + a.[j] * c.[j] * b.[i] * d.[i]) +
    Σ (i = 1, n), (a.[i] * c.[i] * b.[i] * d.[i]))%R).
  clear; intros.
  rewrite <- summation_add_distr.
  induction n.
   rewrite summation_empty; [ | lia ].
   rewrite summation_empty; [ lra | lia ].

   rewrite summation_split_last; [ | lia ].
   rewrite summation_split_last; [ | lia ].
   rewrite summation_split_last; [ | lia ].
   replace (Σ (i = 1, n), Σ (j = 1, S n), (a.[i] * c.[i] * b.[j] * d.[j]))
   with
     (Σ (i = 1, n), Σ (j = 1, n), (a.[i] * c.[i] * b.[j] * d.[j]) +
      Σ (i = 1, n), (a.[i] * c.[i] * b.[S n] * d.[S n]))%R.
    rewrite IHn.
    do 2 rewrite <- Rplus_assoc; f_equal.
    rewrite summation_add_distr; symmetry.
    rewrite summation_add_distr; symmetry.
    replace
      (Σ (i = 1, n),
       Σ (j = i + 1, S n),
        (a.[i] * c.[i] * b.[j] * d.[j] + a.[j] * c.[j] * b.[i] * d.[i]))
    with
      (Σ (i = 1, n),
       (Σ (j = i + 1, n),
          (a.[i] * c.[i] * b.[j] * d.[j] + a.[j] * c.[j] * b.[i] * d.[i]) +
       (a.[i] * c.[i] * b.[S n] * d.[S n] +
        a.[S n] * c.[S n] * b.[i] * d.[i]))).
     rewrite summation_add_distr.
     do 4 rewrite Rplus_assoc; f_equal.
     symmetry; rewrite Rplus_comm.
     rewrite Rplus_assoc; f_equal.
     rewrite summation_empty; [ | lia ].
     rewrite Rplus_0_l.
     now rewrite summation_add_distr.

     apply summation_eq_compat; intros i (Hi, Hin).
     rewrite summation_split_last; [ easy | lia ].

    rewrite <- summation_add_distr.
    apply summation_eq_compat; intros i (Hi, Hin).
    rewrite summation_split_last; [ easy | lia ].

  f_equal; subst; rewrite <- H.
   rewrite summation_summation_mul_distr.
   apply summation_eq_compat; intros i Hi.
   apply summation_eq_compat; intros j Hj.
   lra.

   rewrite summation_summation_mul_distr.
   apply summation_eq_compat; intros i Hi.
   apply summation_eq_compat; intros j Hj.
   lra.

 assert (Hvv : v₁ = v₂).
  subst v₁ v₂.
  apply summation_eq_compat.
  intros i Hi; lra.

  symmetry.
  replace ((u₁ + v₁) - (u₂ + v₂))%R with (u₁ - u₂)%R by lra.
  subst u₁ u₂; clear v₁ v₂ Heqv₁ Heqv₂ Hvv.
  subst z.
  rewrite <- summation_sub_distr.
  apply summation_eq_compat.
  intros i (Hi, Hin).
  rewrite <- summation_sub_distr.
  apply summation_eq_compat.
  intros j (Hj, Hjn); lra.

Qed.

Theorem Lagrange_identity : ∀ (a b : list R) n,
  ((Σ (k = 1, n), (a.[k]²)) * (Σ (k = 1, n), (b.[k]²)) -
     (Σ (k = 1, n), (a.[k] * b.[k]))² =
   Σ (i = 1, n), Σ (j = i + 1, n), ((a.[i] * b.[j] - a.[j] * b.[i])²))%R.
Proof.
intros.
specialize (Binet_Cauchy_identity a b a b n) as H.
assert (Ha : ∀ a,
  (Σ (k = 1, n), ((a.[k])²))%R = (Σ (k = 1, n), (a.[k] * a.[k]))%R).
 clear; intros.
 apply summation_eq_compat; intros.
 now fold (Rsqr a.[i]).

 rewrite <- Ha in H.
 rewrite <- Ha in H.
 rewrite H.
 unfold Rminus.
 rewrite Rplus_shuffle0.
 replace (Σ (j = 1, n), (b.[j] * a.[j])) with (Σ (i = 1, n), (a.[i] * b.[i])).
  unfold Rsqr.
  now rewrite fold_Rminus, Rminus_diag_eq, Rplus_0_l.

  apply summation_eq_compat; intros.
  apply Rmult_comm.
Qed.

Theorem Cauchy_Schwarz_inequality2 : ∀ (u v : list R) n,
  ((Σ (k = 1, n), (u.[k] * v.[k]))² ≤
   Σ (k = 1, n), (u.[k]²) * Σ (k = 1, n), (v.[k]²))%R.
Proof.
intros.
specialize (Lagrange_identity u v n) as H.
remember ((Σ (k = 1, n), (u.[k] * v.[k]))²)%R as x eqn:Hx.
apply Rplus_eq_compat_r with (r := x) in H.
unfold Rminus in H.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r in H.
rewrite H.
apply Rplus_le_reg_r with (r := (-x)%R).
rewrite Rplus_assoc, Rplus_opp_r.
rewrite Rplus_0_r.
clear.
induction n.
 rewrite summation_empty; [ lra | lia ].

 eapply Rle_trans; [ apply IHn | ].
 rewrite summation_split_last; [ | lia ].
 remember (Σ (j = S n + 1, S n), ((u.[S n] * v.[j] + - (u.[j] * v.[S n]))²))%R
  as r eqn:Hr.
 rewrite summation_empty in Hr; [ | lia ].
 subst r; rewrite Rplus_0_r.
 apply summation_le_compat; intros.
 rewrite summation_split_last; [ | lia ].
 remember (Σ (j = i + 1, n), ((u.[i] * v.[j] + - (u.[j] * v.[i]))²)) as r
  eqn:Hr.
 apply Rplus_le_reg_l with (r := (-r)%R).
 rewrite <- Rplus_assoc.
 rewrite Rplus_opp_l, Rplus_0_l.
 apply Rle_0_sqr.
Qed.

Theorem dot_mul_summation : ∀ u v n,
  (min (length u) (length v) ≤ n)
  → dot_mul u v = Σ (i = 1, n), (u.[i] * v.[i]).
Proof.
intros * Hn.
revert v n Hn.
induction u as [| u₁ u]; intros.
 rewrite all_0_summation_0; [ easy | ].
 intros i Hi; simpl.
 destruct (pred i); lra.

 destruct v as [| v₁ v].
  rewrite all_0_summation_0; [ easy | intros i Hi; simpl ].
  destruct (pred i); lra.

  simpl in Hn.
  remember nth as f; simpl; subst f.
  rewrite summation_split_first; [ f_equal | lia ].
  destruct n; [ lia | ].
  apply Nat.succ_le_mono in Hn.
  destruct n.
   rewrite summation_empty; [ | lia ].
   apply Nat.le_0_r in Hn.
   now destruct u, v.

   rewrite summation_shift; [ | lia ].
   rewrite IHu with (n := S n); [ | easy ].
   rewrite summation_shift; [ easy | lia ].
Qed.

Theorem Cauchy_Schwarz_inequality : ∀ (u v : list R),
  ((dot_mul u v)² ≤ dot_mul u u * dot_mul v v)%R.
Proof.
intros.
remember (min (length u) (length v)) as n eqn:Hn.
specialize (Cauchy_Schwarz_inequality2 u v n) as H.
rewrite dot_mul_summation with (n := n); [ | lia ].
rewrite dot_mul_summation with (n := n); [ | ].
Search (min _ _ = _).
2: rewrite Nat.min_id.
bbb.

Search (min _ _ ≤ _)%nat.

do 3 rewrite dot_mul_summation.
rewrite <- Hn.
rewrite min_l; [ | lia ].
rewrite min_l; [ | lia ].
eapply Rle_trans; [ apply H | ].
unfold Rsqr.
apply Rmult_le_compat; [ | | | ].
 apply summation_nonneg; intros i Hi.
 apply Rle_0_sqr.

 apply summation_nonneg; intros i Hi.
 apply Rle_0_sqr.

 clear H.
 assert (H : ∃ a, length u = n + a) by (exists (length u - n); lia).
 destruct H as (a, H); rewrite H.
 rewrite summation_ub_add; [ | lia ].
 eapply Rplus_le_reg_l.
 rewrite <- Rplus_assoc.
 rewrite Rplus_opp_l, Rplus_0_l.
 apply summation_nonneg; intros i Hi.
 apply Rle_0_sqr.

 clear H.
 assert (H : ∃ a, length v = n + a) by (exists (length v - n); lia).
 destruct H as (a, H); rewrite H.
 rewrite summation_ub_add; [ | lia ].
 eapply Rplus_le_reg_l.
 rewrite <- Rplus_assoc.
 rewrite Rplus_opp_l, Rplus_0_l.
 apply summation_nonneg; intros i Hi.
 apply Rle_0_sqr.
Qed.

Check Cauchy_Schwarz_inequality.
