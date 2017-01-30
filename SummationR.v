(* Borrowed from my proof of Puiseux' theorem, file Fsummation.v
   with some changes, applied only on ℝ, not any ring and with
   some theorems more. The two versions should be unified one day. *)
(* Compiled with Coq 8.6 *)

Require Import Utf8 Reals Psatz.

Notation "x '≤' y" := (Rle x y) : R_scope.
Notation "x ≤ y < z" := (x <= y ∧ y < z)%nat (at level 70, y at next level).
Notation "x ≤ y ≤ z" := (x <= y ∧ y ≤ z)%nat (at level 70, y at next level).

Fixpoint summation_aux b len g :=
  match len with
  | O => 0%R
  | S len₁ => (g b + summation_aux (S b) len₁ g)%R
  end.

Definition summation b e g := summation_aux b (S e - b) g.

Notation "'Σ' ( i = b , e ) , g" := (summation b e (λ i, (g)%R))
  (at level 0, i at level 0, b at level 60, e at level 60, g at level 0).

Notation "u .[ i ]" := (List.nth (pred i) u 0%R)
  (at level 1, format "'[' u '[' .[ i ] ']' ']'").

Theorem summation_aux_eq_compat : ∀ g h b₁ b₂ len,
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

Theorem summation_eq_compat : ∀ g h b k,
  (∀ i, b ≤ i ≤ k → (g i = h i)%R)
  → (Σ (i = b, k), (g i) = Σ (i = b, k), (h i))%R.
Proof.
intros g h b k Hgh.
apply summation_aux_eq_compat.
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

Theorem summation_only_one : ∀ g n, (Σ (i = n, n), (g i) = g n)%R.
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
  → Σ (i = b, k), (g i) = (g b + Σ (i = S b, k), (g i))%R.
Proof.
intros g b k Hbk.
unfold summation.
rewrite Nat.sub_succ.
rewrite <- summation_aux_succ_first.
now rewrite <- Nat.sub_succ_l.
Qed.

Theorem summation_split_last : ∀ g b k,
  (b ≤ S k)
  → (Σ (i = b, S k), (g i) = Σ (i = b, k), (g i) + g (S k))%R.
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
   Σ (i = b, k), (g i) + Σ (i = b, k), (h i))%R.
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
  (- Σ (i = b, k), (g i) = Σ (i = b, k), (- g i))%R.
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
   Σ (i = b, k), (g i) - Σ (i = b, k), (h i))%R.
Proof.
intros g h b k.
unfold Rminus.
rewrite summation_add_distr.
f_equal.
now rewrite summation_opp_distr.
Qed.

Theorem summation_swap : ∀ b₁ k₁ b₂ k₂ f,
  Σ (i = b₁, k₁), Σ (j = b₂, k₂), (f i j) =
  Σ (j = b₂, k₂), Σ (i = b₁, k₁), (f i j).
Proof.
intros.
unfold summation.
remember (S k₁ - b₁) as len₁ eqn:Hlen₁.
remember (S k₂ - b₂) as len₂ eqn:Hlen₂.
clear Hlen₁ Hlen₂; clear.
revert b₁ b₂ len₂.
induction len₁; intros; simpl.
 revert b₂.
 induction len₂; intros; [ easy | simpl ].
 rewrite <- IHlen₂; lra.

 rewrite IHlen₁.
 clear.
 revert b₁ b₂ len₁.
 induction len₂; intros; simpl; [ lra | ].
 rewrite <- IHlen₂; lra.
Qed.

Theorem summation_mul_distr_r : ∀ f b k a,
  (Σ (i = b, k), (f i) * a)%R =
  Σ (i = b, k), (f i * a).
Proof.
intros.
unfold summation.
remember (S k - b) as len eqn:Hlen.
clear; revert b.
induction len; intros; simpl; [ lra | ].
rewrite Rmult_plus_distr_r.
now rewrite IHlen.
Qed.

Theorem summation_mul_distr_l : ∀ f b k a,
  (a * Σ (i = b, k), (f i))%R =
  Σ (i = b, k), (a * f i).
Proof.
intros.
rewrite Rmult_comm, summation_mul_distr_r.
apply summation_eq_compat; intros; apply Rmult_comm.
Qed.

Theorem summation_summation_mul_distr : ∀ f g b k,
  (Σ (i = b, k), (f i) * Σ (i = b, k), (g i))%R =
  Σ (i = b, k), Σ (j = b, k), (f i * g j).
Proof.
intros.
revert b.
induction k; intros.
 destruct b.
  now do 4 rewrite summation_only_one.

  rewrite summation_empty; [ | lia ].
  rewrite summation_empty; [ | lia ].
  rewrite summation_empty; [ lra | lia ].

 destruct (le_dec b (S k)) as [Hbk| Hbk].
  rewrite summation_split_last; [ idtac | easy ].
  rewrite summation_split_last; [ idtac | easy ].
  rewrite summation_split_last; [ idtac | easy ].
  rewrite summation_split_last; [ idtac | easy ].
  rewrite Rmult_plus_distr_l.
  do 2 rewrite Rmult_plus_distr_r.
  rewrite IHk.
  rewrite summation_swap; symmetry.
  rewrite summation_swap; symmetry.
  rewrite summation_split_last; [ | easy ].
  do 2 rewrite Rplus_assoc; f_equal.
  rewrite Rplus_comm, Rplus_assoc.
  f_equal; [ apply summation_mul_distr_r | ].
  rewrite Rplus_comm; f_equal.
  apply summation_mul_distr_l.

  apply Nat.nle_gt in Hbk.
  rewrite summation_empty; [ | lia ].
  rewrite summation_empty; [ | lia ].
  rewrite summation_empty; [ lra | lia ].
Qed.

Theorem summation_succ_succ : ∀ b k g,
  (Σ (i = S b, S k), (g i) = Σ (i = b, k), (g (S i)))%R.
Proof.
intros b k g.
unfold summation.
rewrite Nat.sub_succ.
remember (S k - b)%nat as len; clear Heqlen.
revert b.
induction len; intros; [ easy | simpl ].
now rewrite IHlen.
Qed.

Theorem summation_aux_le_compat : ∀ g h b₁ b₂ len,
  (∀ i, 0 ≤ i < len → (g (b₁ + i)%nat ≤ h (b₂ + i)%nat)%R)
  → (summation_aux b₁ len g ≤ summation_aux b₂ len h)%R.
Proof.
intros g h b₁ b₂ len Hgh.
revert b₁ b₂ Hgh.
induction len; intros; simpl; [ lra | ].
apply Rplus_le_compat.
 assert (H : 0 ≤ 0 < S len) by lia.
 apply Hgh in H.
 now do 2 rewrite Nat.add_0_r in H.

 apply IHlen; intros i Hi.
 do 2 rewrite Nat.add_succ_comm.
 apply Hgh; lia.
Qed.

Theorem summation_le_compat : ∀ b k f g,
  (∀ i, (b ≤ i ≤ k) → (f i ≤ g i)%R)
  → (Σ (i = b, k), (f i) ≤ Σ (i = b, k), (g i))%R.
Proof.
intros * Hfg.
unfold summation.
apply summation_aux_le_compat; intros i Hi.
apply Hfg; lia.
Qed.

Theorem all_0_summation_aux_0 : ∀ g b len,
  (∀ i, (b ≤ i < b + len) → (g i = 0)%R)
  → (summation_aux b len (λ i, g i) = 0)%R.
Proof.
intros g b len H.
revert b H.
induction len; intros; [ easy | simpl ].
rewrite H; [ idtac | split; auto ].
 rewrite Rplus_0_l, IHlen; [ easy | ].
 intros i (Hbi, Hib); apply H.
 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 split; [ now apply Nat.lt_le_incl | easy ].

 rewrite Nat.add_succ_r.
 apply le_n_S, le_plus_l.
Qed.

Theorem all_0_summation_0 : ∀ g i₁ i₂,
  (∀ i, i₁ ≤ i ≤ i₂ → (g i = 0)%R)
  → (Σ (i = i₁, i₂), (g i) = 0)%R.
Proof.
intros g i₁ i₂ H.
apply all_0_summation_aux_0.
intros i (H₁, H₂).
apply H.
split; [ easy | ].
destruct (le_dec i₁ (S i₂)) as [H₃| H₃].
 rewrite Nat.add_sub_assoc in H₂; [ | easy ].
 rewrite minus_plus in H₂.
 now apply le_S_n.

 apply not_le_minus_0 in H₃.
 rewrite H₃, Nat.add_0_r in H₂.
 now apply Nat.nle_gt in H₂.
Qed.

Theorem summation_shift : ∀ b g k,
  b ≤ k
  → (Σ (i = b, k), (g i) =
     Σ (i = 0, k - b), (g (b + i)%nat))%R.
Proof.
intros b g k Hbk.
unfold summation.
rewrite Nat.sub_0_r.
rewrite Nat.sub_succ_l; [ idtac | assumption ].
now apply summation_aux_eq_compat; intros j Hj.
Qed.

Theorem summation_aux_ub_add : ∀ g b k₁ k₂,
  (summation_aux b (k₁ + k₂) g =
   summation_aux b k₁ g + summation_aux (b + k₁) k₂ g)%R.
Proof.
intros g b k₁ k₂.
revert b k₁.
induction k₂; intros.
 simpl.
 now rewrite Nat.add_0_r, Rplus_0_r.

 rewrite Nat.add_succ_r, <- Nat.add_succ_l.
 rewrite IHk₂; simpl.
 rewrite <- Nat.add_succ_r.
 rewrite <- Rplus_assoc.
 apply Rplus_eq_compat_r.
 clear k₂ IHk₂.
 revert b.
 induction k₁; intros; simpl.
  rewrite Nat.add_0_r.
  apply Rplus_comm.

  rewrite Rplus_assoc.
  rewrite IHk₁.
  rewrite Nat.add_succ_r, <- Nat.add_succ_l; reflexivity.
Qed.

Theorem summation_ub_add : ∀ g b k₁ k₂,
  b ≤ S k₁
  → (Σ (i = b, k₁ + k₂), (g i) =
     Σ (i = b, k₁), (g i) + Σ (i = S k₁, k₁ + k₂), (g i))%R.
Proof.
intros g b k₁ k₂ Hbk.
unfold summation.
replace (S (k₁ + k₂) - b) with (S k₁ - b + k₂) by lia.
rewrite summation_aux_ub_add; f_equal.
f_equal; lia.
Qed.

Theorem summation_nonneg : ∀ b k f,
  (∀ i, b ≤ i ≤ k → 0 ≤ f i)%R
  → (0 ≤ Σ (i = b, k), (f i))%R.
Proof.
intros * Hbk.
unfold summation.
remember (S k - b) as n eqn:Hn.
revert b Hbk Hn.
induction n; intros; simpl; [ lra | ].
apply Rplus_le_le_0_compat; [ apply Hbk; lia | ].
apply IHn; [ intros; apply Hbk; lia | lia ].
Qed.