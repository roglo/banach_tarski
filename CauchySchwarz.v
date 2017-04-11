(* Cauchy-Schwarz in any dimension *)
(* Compiled with Coq 8.6 *)
Require Import Utf8 List Reals Psatz.
Import ListNotations.

Require Import SummationR.

Theorem fold_Rminus : ∀ x y, (x + - y = x - y)%R.
Proof. intros. now fold (Rminus x y). Qed.

Theorem Rplus_shuffle0 : ∀ n m p : R, (n + m + p)%R = (n + p + m)%R.
Proof.
intros.
rewrite Rplus_comm, <- Rplus_assoc.
f_equal; apply Rplus_comm.
Qed.

Definition dot_mul n a b := Σ (k = 1, n), (a.[k] * b.[k]).
Definition sqr_cross_mul n a b :=
   Σ (i = 1, n), Σ (j = i + 1, n), ((a.[i] * b.[j] - a.[j] * b.[i])²).

Theorem Binet_Cauchy_identity : ∀ (a b c d : list R) n,
  (dot_mul n a c * dot_mul n b d =
   dot_mul n a d * dot_mul n b c +
   Σ (i = 1, n), Σ (j = i + 1, n),
     ((a.[i] * b.[j] - a.[j] * b.[i]) *
      (c.[i] * d.[j] - c.[j] * d.[i])))%R.
Proof.
intros.
unfold dot_mul.
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

Theorem Lagrange_identity : ∀ n a b,
  (dot_mul n a a * dot_mul n b b = (dot_mul n a b)² + sqr_cross_mul n a b)%R.
Proof.
intros.
specialize (Binet_Cauchy_identity a b a b n) as H.
fold (dot_mul n a a) in H.
fold (dot_mul n b b) in H.
fold (dot_mul n a b) in H.
fold (dot_mul n b a) in H.
rewrite H; clear H.
unfold Rsqr.
f_equal; f_equal.
apply summation_eq_compat; intros.
apply Rmult_comm.
Qed.

Theorem Lagrange_identity_bis : ∀ n (a b : list R),
  ((Σ (k = 1, n), (a.[k]²)) * (Σ (k = 1, n), (b.[k]²)) -
     (Σ (k = 1, n), (a.[k] * b.[k]))² =
   Σ (i = 1, n), Σ (j = i + 1, n), ((a.[i] * b.[j] - a.[j] * b.[i])²))%R.
Proof.
intros.
specialize (Binet_Cauchy_identity a b a b n) as H.
unfold dot_mul in H.
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
