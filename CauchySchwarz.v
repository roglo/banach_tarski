(* Cauchy-Schwarz in any dimension *)
(* Compiled with Coq 8.6 *)

Require Import Utf8 List Reals Psatz.
Import ListNotations.

Notation "x '≤' y" := (Rle x y) : R_scope.
Notation "x ≤ y < z" := (x <= y ∧ y < z)%nat (at level 70, y at next level).
Notation "x ≤ y ≤ z" := (x <= y ∧ y ≤ z)%nat (at level 70, y at next level).

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

Fixpoint summation_aux b len g :=
  match len with
  | O => 0%R
  | S len₁ => (g b + summation_aux (S b) len₁ g)%R
  end.

Definition summation b e g := summation_aux b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, (g)%R))
  (at level 0, i at level 0, b at level 60, e at level 60, g at level 20).

Notation "u .[ i ]" := (List.nth (pred i) u 0%R)
  (at level 1, format "'[' u '[' .[ i ] ']' ']'").

Theorem summation_aux_compat : ∀ g h b₁ b₂ len,
  (∀ i, 0 ≤ i < len → (g (b₁ + i)%nat = h (b₂ + i)%nat)%R)
  → (summation_aux b₁ len g = summation_aux b₂ len h)%R.
Proof.
intros g h b₁ b₂ len Hgh.
revert b₁ b₂ Hgh.
induction len; intros; [ easy | simpl ].
erewrite IHlen.
 f_equal.
 assert (0 ≤ 0 < S len) as H.
  split; [ easy | apply Nat.lt_0_succ ].

  apply Hgh in H.
  now do 2 rewrite Nat.add_0_r in H.

 intros i Hi.
 do 2 rewrite Nat.add_succ_l, <- Nat.add_succ_r.
 apply Hgh.
 split; [ apply Nat.le_0_l | ].
 apply lt_n_S.
 now destruct Hi.
Qed.

Theorem summation_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%R)
  → (Σ (i = b, k), g i = Σ (i = b, k), h i)%R.
Proof.
intros g h b k Hgh.
apply summation_aux_compat.
intros i (_, Hi).
apply Hgh.
split; [ apply Nat.le_add_r | idtac ].
apply Nat.lt_add_lt_sub_r, le_S_n in Hi.
now rewrite Nat.add_comm.
Qed.

Theorem summation_empty : ∀ g b k, (k < b)%nat → (Σ (i = b, k), (g i) = 0%R).
Proof.
intros.
unfold summation.
now replace (S k - b)%nat with O by lia.
Qed.

Theorem summation_only_one : ∀ g n, (Σ (i = n, n), g i = g n)%R.
Proof.
intros g n.
unfold summation.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite Nat.sub_diag; simpl.
now rewrite Rplus_0_r.
Qed.

Theorem summation_aux_succ_last : ∀ g b len,
  (summation_aux b (S len) g =
   summation_aux b len g + g (b + len)%nat)%R.
Proof.
intros g b len.
revert b.
induction len; intros.
 simpl.
 now rewrite Rplus_0_l, Rplus_0_r, Nat.add_0_r.

 remember (S len) as x; simpl; subst x.
 rewrite IHlen.
 simpl.
 now rewrite Rplus_assoc, Nat.add_succ_r.
Qed.

Theorem summation_aux_succ_first : ∀ g b len,
  summation_aux b (S len) g = (g b + summation_aux (S b) len g)%R.
Proof. easy. Qed.

Theorem summation_split_first : ∀ g b k,
  b ≤ k
  → Σ (i = b, k), g i = (g b + Σ (i = S b, k), g i)%R.
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ.
rewrite <- summation_aux_succ_first.
now rewrite <- Nat.sub_succ_l.
Qed.

Theorem summation_split_last : ∀ g b k,
  (b ≤ S k)
  → (Σ (i = b, S k), g i = Σ (i = b, k), g i + g (S k))%R.
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ_l; [ | easy ].
rewrite summation_aux_succ_last.
rewrite Nat.add_sub_assoc; [ idtac | assumption ].
rewrite Nat.add_comm, Nat.add_sub.
reflexivity.
Qed.

Theorem summation_add_distr : ∀ g h b k,
  (Σ (i = b, k), (g i + h i) =
   Σ (i = b, k), g i + Σ (i = b, k), h i)%R.
Proof.
intros g h b k.
destruct (le_dec b k) as [Hbk| Hbk].
 revert b Hbk.
 induction k; intros.
  destruct b.
   now do 3 rewrite summation_only_one.

   now unfold summation; simpl; rewrite Rplus_0_r.

  rewrite summation_split_last; [ idtac | easy ].
  rewrite summation_split_last; [ idtac | easy ].
  rewrite summation_split_last; [ idtac | easy ].
  destruct (eq_nat_dec b (S k)) as [H₂| H₂].
   subst b.
   unfold summation; simpl.
   rewrite Nat.sub_diag; simpl.
   now do 3 rewrite Rplus_0_l.

   assert (H : (b ≤ k)%nat) by lia.
   clear Hbk; rename H into Hbk.
   rewrite IHk; [ lra | easy ].

 unfold summation.
 apply Nat.nle_gt in Hbk.
 replace (S k - b) with O by lia; simpl.
 now rewrite Rplus_0_r.
Qed.

Theorem summation_opp_distr : ∀ g b k,
  (- Σ (i = b, k), g i = Σ (i = b, k), (- g i))%R.
Proof.
intros.
destruct (le_dec b k) as [Hbk| Hbk].
 revert b Hbk.
 induction k; intros.
  destruct b.
   now do 2 rewrite summation_only_one.

   unfold summation; simpl; lra.

  rewrite summation_split_last; [ | easy ].
  rewrite summation_split_last; [ | easy ].
  rewrite Ropp_plus_distr.
  destruct (eq_nat_dec b (S k)) as [H₂| H₂].
   subst b.
   unfold summation; simpl.
   rewrite Nat.sub_diag; simpl; lra.

   assert (H : (b ≤ k)%nat) by lia.
   clear Hbk; rename H into Hbk.
   now rewrite IHk.

 unfold summation.
 apply Nat.nle_gt in Hbk.
 replace (S k - b) with O by lia; simpl.
 now rewrite Ropp_0.
Qed.

Theorem summation_sub_distr : ∀ g h b k,
  (Σ (i = b, k), (g i - h i) =
   Σ (i = b, k), g i - Σ (i = b, k), h i)%R.
Proof.
intros g h b k.
unfold Rminus.
rewrite summation_add_distr.
f_equal.
now rewrite summation_opp_distr.
Qed.

Theorem summation_succ_succ : ∀ b k g,
  (Σ (i = S b, S k), g i = Σ (i = b, k), g (S i))%R.
Proof.
intros b k g.
unfold summation.
rewrite Nat.sub_succ.
remember (S k - b)%nat as len; clear Heqlen.
revert b.
induction len; intros; [ easy | simpl ].
now rewrite IHlen.
Qed.

Theorem Binet_Cauchy_identity : ∀ (a b c d : list R),
  let n := length a in
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
 Focus 2.
 assert (Hvv : v₁ = v₂).
  subst v₁ v₂.
  apply summation_compat.
  intros i Hi; lra.

  replace ((u₁ + v₁) - (u₂ + v₂))%R with (u₁ - u₂)%R by lra.
  subst u₁ u₂; clear v₁ v₂ Heqv₁ Heqv₂ Hvv.
  subst z; symmetry.
  set (h i :=
    (Σ (j = i + 1, n), (a.[i]*c.[i]*b.[j]*d.[j]+a.[j]*c.[j]*b.[i]*d.[i])-
     Σ (j = i + 1, n), (a.[i]*d.[i]*b.[j]*c.[j]+a.[j]*d.[j]*b.[i]*c.[i]))%R).
  rewrite summation_compat with (h := h).
   subst h; simpl.
   now rewrite <- summation_sub_distr.

   intros i Hi; subst h; simpl.
   rewrite <- summation_sub_distr.
   apply summation_compat.
   intros j Hj; lra.

 f_equal.
  subst x u₁ v₁; clear.
  induction n; [ unfold summation; simpl; lra | ].
  rewrite summation_split_last; [ | lia ].
  rewrite summation_split_last; [ | lia ].
  rewrite summation_split_last; [ | lia ].
  rewrite Rmult_plus_distr_r, Rmult_plus_distr_l.
  rewrite IHn.
  remember
    (Σ (i = 1, n),
     Σ (j = i + 1, n),
     (a.[i] * c.[i] * b.[j] * d.[j] + a.[j] * c.[j] * b.[i] * d.[i]) +
     Σ (i = 1, n), (a.[i] * c.[i] * b.[i] * d.[i]))%R as x eqn:Hx.
  remember
    (Σ (i = 1, n),
     Σ (j = i + 1, S n),
     (a.[i] * c.[i] * b.[j] * d.[j] + a.[j] * c.[j] * b.[i] * d.[i]))
    as y eqn:Hy.
bbb.
  assert (Hxy : x = y).
   subst x y.
   rewrite <- summation_add_distr.
   apply summation_compat.
   intros i (Hi, Hin).
   rewrite summation_split_last; [ | lia ].
   f_equal.

bbb.
   rewrite Hxy.
   do 2 rewrite Rplus_assoc.
   f_equal.
bbb.
  induction n; simpl.
   do 4 rewrite summation_only_one.
   rewrite summation_empty; [ lra | lia ].
bbb.

Theorem Lagrange_identity : ∀ (a b : list R),
  let n := length a in
  ((Σ (k = 1, n), a.[k]²) * (Σ (k = 1, n), b.[k]²) -
     (Σ (k = 1, n), a.[k] * b.[k])² =
   Σ (i = 1, n), Σ (j = i + 1, n), (a.[i] * b.[j] - a.[j] * b.[i])²)%R.
Proof.
intros.
bbb.

unfold sqr_sum_det.
remember (length u) as len eqn:Hlen; symmetry in Hlen.
unfold gen_sqr_sum_det.
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
  subst len2; simpl; rewrite Hlen.
  rewrite small_det_same, Rsqr_0, Rplus_0_l.
  apply Rmult_eq_reg_r with (r := 2%R); [ | lra ].
  rewrite Rmult_plus_distr_r.
  unfold Rdiv.
  rewrite Rmult_assoc, Rinv_l; [ rewrite Rmult_1_r | lra ].
  symmetry.
  rewrite Rmult_assoc, Rinv_l; [ rewrite Rmult_1_r | lra ].
bbb.
