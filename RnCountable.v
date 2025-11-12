(* Banach-Tarski paradox. *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith ZArith.
From Stdlib Require Import Field.

Require Import RingLike.Core.
Require Import RingLike.IntermVal.
Require Import RingLike.Misc.
Require Import TrigoWithoutPi.Core.
From a Require Import MiscReals Countable.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {ac : angle_ctx T}.
Context {Hch : rngl_characteristic T = 0}.
Context {Hc1 : rngl_characteristic T ≠ 1}.
Context {Har : rngl_is_archimedean T = true}.

Add Ring rngl_ring : (rngl_ring_theory ac_ic ac_op ac_on).
Add Field rngl_field : (rngl_field_theory ac_ic ac_op ac_on ac_iv Hc1).

Definition ter_bin_of_frac_part x n := (1 / 3 ≤? frac_part Hc1 Har (x * 3 ^ n))%L.
(*
Definition ter_bin_of_frac_part x n :=
  if (frac_part (x * 3 ^ n) <? (1 / 3))%L then false else true.
*)

Fixpoint partial_sum3_aux k (u : nat → bool) pow i :=
  match k with
  | 0 => 0%L
  | S k' =>
      if u i then (pow / 3 + partial_sum3_aux k' u (pow / 3) (S i))%L
      else partial_sum3_aux k' u (pow / 3)%L (S i)
  end.

Definition partial_sum3 u k := partial_sum3_aux k u 1%L 0.

(* Σ (i=0,c-1) 3^(c-1-i)ui *)
Fixpoint n_partial_sum3 (u : ℕ → bool) c :=
  match c with
  | O => O
  | S c' => (3 * n_partial_sum3 u c' + Nat.b2n (u c'))%nat
  end.

Definition b2r b := INR (Nat.b2n b).

Theorem partial_sum3_aux_le_half_pow :
  ∀ u k pow pow2 i,
  (0 ≤ pow)%L
  → pow2 = (pow / 2)%L
  → (partial_sum3_aux k u pow i ≤ pow2)%L.
Proof.
destruct_ac.
specialize (rngl_2_neq_0 Hos Hc1 Hor) as H20.
assert (H30 : (3 ≠ 0)%L). {
  replace 3%L with (rngl_of_nat 3). 2: {
    now cbn; rewrite rngl_add_0_r, rngl_add_comm.
  }
  rewrite <- rngl_of_nat_0.
  intros H.
  apply (rngl_of_nat_inj Hos) in H.
  now rewrite Hch in H.
}
intros * Hpow Hpow2; subst pow2.
revert pow i Hpow.
induction k; intros; simpl. {
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ easy | ].
  apply (rngl_0_lt_2 Hos Hc1 Hor).
}
destruct (u i). {
  apply (rngl_le_add_le_sub_l Hop Hor).
  eapply (rngl_le_trans Hor). {
    apply IHk.
    apply (rngl_div_nonneg Hon Hop Hiv Hor); [ easy | ].
    apply (rngl_lt_le_trans Hor _ 1).
    apply (rngl_0_lt_1 Hos Hc1 Hor).
    apply (rngl_le_add_l Hor).
    apply (rngl_0_le_2 Hos Hor).
  }
  rewrite <- (@Rdiv_mult_simpl_r _ _ _ ac pow 2 3)%L; [ | easy | easy ].
  rewrite <- (@Rdiv_mult_simpl_r _ _ _ ac pow 3 2)%L at 2;
    [ | easy | easy ].
  rewrite (rngl_mul_comm Hic 3 2).
  rewrite <- (rngl_div_sub_distr_r Hop Hiv).
  rewrite <- (rngl_mul_sub_distr_l Hop).
  rewrite (rngl_add_comm 2 1) at 2.
  rewrite (rngl_add_sub Hos).
  rewrite rngl_mul_1_r.
  rewrite (rngl_div_div Hon Hos Hiv); [ | easy | easy ].
  apply (rngl_le_refl Hor).
}
eapply (rngl_le_trans Hor); [ apply IHk | ]. {
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ easy | ].
  apply (rngl_lt_le_trans Hor _ 1).
  apply (rngl_0_lt_1 Hos Hc1 Hor).
  apply (rngl_le_add_l Hor).
  apply (rngl_0_le_2 Hos Hor).
}
apply (rngl_div_le_mono_pos_r Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hos Hc1 Hor).
apply (rngl_le_div_l Hon Hop Hiv Hor).
apply (rngl_lt_le_trans Hor _ 1).
apply (rngl_0_lt_1 Hos Hc1 Hor).
apply (rngl_le_add_l Hor).
apply (rngl_0_le_2 Hos Hor).
rewrite rngl_mul_add_distr_l.
rewrite rngl_mul_1_r.
apply (rngl_le_add_l Hor).
apply (rngl_mul_nonneg_nonneg Hos Hor); [ easy | ].
apply (rngl_0_le_2 Hos Hor).
Qed.

Theorem partial_sum3_aux_succ : ∀ u n pow i,
  partial_sum3_aux (S n) u pow i =
  (partial_sum3_aux n u pow i +
   INR (Nat.b2n (u (i + n)%nat)) * pow / 3 ^ S n)%L.
Proof.
destruct_ac.
intros.
revert pow i.
induction n; intros. {
  simpl; rewrite rngl_add_0_r, rngl_add_0_l, rngl_mul_1_r, Nat.add_0_r.
  destruct (u i); simpl.
  now rewrite rngl_of_nat_1, rngl_mul_1_l.
  rewrite rngl_of_nat_0, (rngl_mul_0_l Hos).
  symmetry; apply (rngl_div_0_l Hos Hi1).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
}
remember (S n) as sn; simpl; subst sn.
remember (u i) as bi eqn:Hbi; symmetry in Hbi.
destruct bi. {
  remember (3 ^ S n)%L as sn3 eqn:Hsn3.
  rewrite IHn; simpl; rewrite Hbi.
  rewrite rngl_add_assoc.
  progress f_equal.
  rewrite Nat.add_succ_r.
  rewrite (rngl_mul_div_assoc Hiv).
  rewrite (rngl_div_div Hon Hos Hiv).
  rewrite <- rngl_of_nat_3.
  now rewrite (rngl_mul_nat_comm Hon Hos 3).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  rewrite Hsn3.
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
} {
  remember (3 ^ S n)%L as sn3 eqn:Hsn3.
  rewrite IHn; simpl; rewrite Hbi.
  rewrite Nat.add_succ_r.
  rewrite (rngl_mul_div_assoc Hiv).
  rewrite (rngl_div_div Hon Hos Hiv).
  rewrite <- rngl_of_nat_3.
  now rewrite (rngl_mul_nat_comm Hon Hos 3).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  rewrite Hsn3.
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
}
Qed.

Theorem partial_sum3_succ : ∀ u n,
  (partial_sum3 u (S n) =
   partial_sum3 u n + INR (Nat.b2n (u n)) / 3 ^ S n)%L.
Proof.
destruct_ac.
intros.
unfold partial_sum3.
rewrite partial_sum3_aux_succ.
now rewrite rngl_mul_1_r.
Qed.

Theorem partial_sum3_aux_add : ∀ u k₁ k₂ pow i,
  partial_sum3_aux (k₁ + k₂) u pow i =
  (partial_sum3_aux k₁ u pow i +
   partial_sum3_aux k₂ u (pow / 3 ^ k₁) (i + k₁))%L.
Proof.
destruct_ac.
intros.
revert k₂ pow i.
induction k₁; intros. {
  simpl.
  now rewrite rngl_add_0_l, Nat.add_0_r, (rngl_div_1_r Hon Hiq); [ | left ].
}
simpl.
remember (u i) as bi eqn:Hbi; symmetry in Hbi.
rewrite <- Nat.add_succ_comm.
progress unfold rngl_div at 7.
rewrite Hiv.
rewrite <- rngl_of_nat_3.
rewrite (rngl_mul_nat_comm Hon Hos).
rewrite rngl_of_nat_3.
rewrite (rngl_inv_mul_distr Hon Hos Hiv); cycle 1. {
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
} {
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
}
rewrite rngl_mul_assoc.
do 2 rewrite (rngl_mul_inv_r Hiv).
destruct bi; [ | apply IHk₁ ].
rewrite <- (rngl_add_assoc (pow / 3)).
progress f_equal.
apply IHk₁.
Qed.

Theorem partial_sum3_aux_nonneg : ∀ u k pos i,
  (0 ≤ pos)%L
  → (0 ≤ partial_sum3_aux k u pos i)%L.
Proof.
destruct_ac.
intros * Hpos.
revert pos i Hpos.
induction k; intros; simpl; [ apply (rngl_le_refl Hor) | ].
assert (H : (0 ≤ pos / 3)%L). {
  apply (rngl_div_nonneg Hon Hop Hiv Hor); [ easy | ].
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
}
destruct (u i); [ | now apply IHk ].
apply (rngl_le_0_add Hos Hor); [ easy | ].
now apply IHk.
Qed.

Theorem partial_sum3_upper_bound : ∀ u n k,
  (partial_sum3 u k ≤ partial_sum3 u n + (2 * 3 ^ n)⁻¹)%L.
Proof.
destruct_ac.
intros.
assert (Hzi : ∀ i, (0 ≤ (2 * 3 ^ i)⁻¹)%L). {
  intros.
  rewrite (rngl_inv_mul_distr Hon Hos Hiv); cycle 1.
  apply (rngl_2_neq_0 Hos Hc1 Hor).
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  apply (rngl_mul_nonneg_nonneg Hos Hor).
  rewrite (rngl_inv_pow Hon Hos Hiv).
  apply (rngl_lt_le_incl Hor).
  apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
  apply (rngl_inv_pos Hon Hop Hiv Hor).
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  apply (rngl_lt_le_incl Hor).
  apply (rngl_inv_pos Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hos Hc1 Hor).
}
unfold partial_sum3.
destruct (le_dec k n) as [Hkn| Hkn]. {
  remember (n - k)%nat as nk eqn:Hnk.
  assert (Hn : (n = k + nk)%nat). {
    now subst nk; rewrite Nat.add_comm, Nat.sub_add.
  }
  subst n.
  rewrite partial_sum3_aux_add, Nat.add_0_l, <- rngl_add_assoc.
  apply (rngl_le_add_r Hor).
  apply (rngl_le_0_add Hos Hor); [ | apply Hzi ].
  apply partial_sum3_aux_nonneg.
  apply (rngl_div_nonneg Hon Hop Hiv Hor).
  apply (rngl_0_le_1 Hos Hor).
  apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
}
apply Nat.nle_gt in Hkn.
remember (k - n)%nat as nk eqn:Hnk.
assert (Hn : (k = n + nk)%nat). {
  subst nk; rewrite Nat.add_comm, Nat.sub_add; [ easy | ].
  now apply Nat.lt_le_incl.
}
subst k; clear Hnk Hkn; rename nk into k.
rewrite partial_sum3_aux_add, Nat.add_0_l.
apply (rngl_add_le_mono_l Hor).
revert n.
induction k; intros; simpl; [ apply Hzi | ].
remember (u n) as b eqn:Hb; symmetry in Hb.
destruct b. {
  apply (rngl_le_add_le_sub_l Hop Hor).
  assert (H : (1 / (2 * (1 + 2) * 3 ^ n))%L = (1 / 3 ^ n / 3 / 2)%L). {
    rewrite (rngl_add_comm 1 2).
    rewrite (rngl_div_div Hon Hos Hiv).
    symmetry.
    apply (rngl_div_div Hon Hos Hiv).
    apply (rngl_pow_neq_0 Hon Hos Hiq).
    apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
    apply (rngl_neq_mul_0 Hon Hos Hiq).
    apply (rngl_2_neq_0 Hos Hc1 Hor).
    apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
    apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
    apply (rngl_2_neq_0 Hos Hc1 Hor).
  }
  field_simplify. {
    apply partial_sum3_aux_le_half_pow; [ | easy ].
    apply (rngl_div_nonneg Hon Hop Hiv Hor).
    apply (rngl_div_nonneg Hon Hop Hiv Hor).
    apply (rngl_0_le_1 Hos Hor).
    apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
    apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
    apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  }
  split. {
    apply (rngl_pow_neq_0 Hon Hos Hiq).
    apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  }
  split. {
    assert (1 + 2 ≠ 0)%L by now rewrite rngl_add_comm; apply rngl_3_neq_0.
    easy.
  }
  apply (rngl_2_neq_0 Hos Hc1 Hor).
}
replace (1 / 3 ^ n / 3)%L with (1 / (3 ^ S n))%L. {
  eapply (rngl_le_trans Hor); [ apply IHk | ].
  apply (rngl_le_inv_inv Hon Hop Hiv Hor).
  apply (rngl_mul_pos_pos Hop Hiq Hor).
  apply (rngl_0_lt_2 Hos Hc1 Hor).
  apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  apply (rngl_mul_pos_pos Hop Hiq Hor).
  apply (rngl_0_lt_2 Hos Hc1 Hor).
  apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  apply (rngl_mul_le_mono_pos_l Hop Hiq Hor).
  apply (rngl_0_lt_2 Hos Hc1 Hor).
  cbn.
  apply (rngl_le_div_l Hon Hop Hiv Hor).
  apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  rewrite (rngl_div_diag Hon Hiq).
  apply (rngl_le_add_l Hor).
  apply (rngl_0_le_2 Hos Hor).
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
}
simpl; symmetry.
apply (rngl_div_div Hon Hos Hiv).
apply (rngl_pow_neq_0 Hon Hos Hiq).
apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
Qed.

Ltac fold_rngl :=
  replace (let (_, _, rngl_mul, _, _, _, _, _, _) := ro in rngl_mul)
    with rngl_mul by easy;
  replace (let (_, rngl_add, _, _, _, _, _, _, _) := ro in rngl_add)
    with rngl_add by easy;
  replace (let (rngl_zero, _, _, _, _, _, _, _, _) := ro in rngl_zero)
    with rngl_zero by easy;
  replace
    (match
        (let (_, _, _, rngl_opt_one, _, _, _, _, _) := ro in rngl_opt_one)
     with
     | Some a => a
     | None => 0%L
     end) with 1%L by easy.

Theorem partial_sum3_aux_shift_seq : ∀ u k pow i,
  partial_sum3_aux (S k) u pow i =
  ((pow * b2r (u i) + partial_sum3_aux k (λ n, u (S n)) pow i) / 3)%L.
Proof.
destruct_ac.
intros.
set (v := λ n, u (S n)).
revert pow i.
induction k; intros; [ simpl; destruct (u i); unfold b2r; simpl | ]. {
  field_simplify; fold_rngl.
  now rewrite rngl_of_nat_1, rngl_mul_1_r.
  rewrite rngl_add_comm; apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  rewrite rngl_add_comm; apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
} {
  rewrite rngl_of_nat_0.
  rewrite (rngl_mul_0_r Hos).
  rewrite rngl_add_0_l; symmetry.
  apply (rngl_div_0_l Hos Hi1).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
}
rewrite partial_sum3_aux_succ.
rewrite IHk.
rewrite partial_sum3_aux_succ.
do 3 rewrite (rngl_div_add_distr_r Hiv).
rewrite <- (rngl_add_assoc (_ / _)).
progress f_equal; cbn.
progress f_equal.
progress unfold v.
rewrite Nat.add_succ_r.
rewrite (rngl_div_div Hon Hos Hiv); [ easy | | ].
apply (rngl_neq_mul_0 Hon Hos Hiq).
apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
apply (rngl_pow_neq_0 Hon Hos Hiq).
apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
Qed.

Theorem n_partial_sum3_succ2 : ∀ u n,
  n_partial_sum3 u (S n) =
  (3 ^ n * Nat.b2n (u O) + n_partial_sum3 (λ n, u (S n)) n)%nat.
Proof.
destruct_ac.
intros.
set (v n := u (S n)).
induction n; [ now simpl; do 2 rewrite Nat.add_0_r | ].
remember (S n) as sn; simpl; subst sn.
rewrite IHn; simpl.
set (m := n_partial_sum3 v n).
subst v.
do 3 rewrite Nat.add_0_r.
ring.
Qed.

Theorem n_partial_sum3_succ : ∀ u n,
  n_partial_sum3 u (S n) = (3 * n_partial_sum3 u n + Nat.b2n (u n))%nat.
Proof.
destruct_ac. easy. Qed.

Theorem partial_sum3_n_partial_sum3 : ∀ u n,
  (3 ^ n * partial_sum3 u n = INR (n_partial_sum3 u n))%L.
Proof.
destruct_ac.
intros.
unfold partial_sum3.
induction n; [ cbn; ring | ].
rewrite partial_sum3_aux_succ, n_partial_sum3_succ.
(**)
field_simplify. 2: {
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
}
rewrite rngl_pow_succ_r, <- rngl_mul_assoc.
rewrite IHn.
rewrite rngl_of_nat_add.
rewrite (rngl_of_nat_mul Hon Hos).
now rewrite rngl_of_nat_3.
Qed.

Theorem le_partial_sum3_lt_n_partial_sum3 : ∀ u r n,
  (r ≤ partial_sum3 u (S n) + (2 * 3 ^ S n)⁻¹)%L
  → (r * 3 ^ n < INR (n_partial_sum3 u n) + 1)%L.
Proof.
destruct_ac.
intros * Hr2.
rewrite <- partial_sum3_n_partial_sum3.
apply (rngl_lt_sub_lt_add_l Hop Hor).
rewrite (rngl_mul_comm Hic (3 ^ n)).
rewrite <- (rngl_mul_sub_distr_r Hop).
apply (rngl_lt_div_r Hon Hop Hiv Hor).
apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
apply (rngl_lt_sub_lt_add_l Hop Hor).
eapply (rngl_le_lt_trans Hor); [ apply Hr2 | ].
rewrite partial_sum3_succ.
rewrite <- rngl_add_assoc.
apply (rngl_add_lt_mono_l Hos Hor).
rewrite (rngl_inv_mul_distr Hon Hos Hiv).
rewrite (rngl_mul_comm Hic _ 2⁻¹).
rewrite (rngl_mul_inv_r Hiv).
rewrite <- (rngl_div_add_distr_r Hiv); cbn.
rewrite <- (rngl_div_div Hon Hos Hiv).
rewrite (rngl_div_div_swap Hic Hiv).
apply (rngl_div_lt_mono_pos_r Hon Hop Hiv Hor).
apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
apply (rngl_lt_div_l Hon Hop Hiv Hor).
apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
rewrite rngl_mul_1_l.
apply (rngl_lt_add_lt_sub_r Hop Hor).
progress unfold INR.
apply (rngl_le_lt_trans Hor _ 1).
rewrite <- rngl_of_nat_1.
apply (rngl_of_nat_inj_le Hos Hc1 Hor).
apply Nat.b2n_le_1.
field_simplify; fold_rngl.
apply (rngl_lt_div_r Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hos Hc1 Hor).
rewrite rngl_mul_1_l.
apply (rngl_add_lt_mono_l Hos Hor).
rewrite rngl_mul_add_distr_r.
rewrite rngl_mul_1_l.
rewrite <- rngl_add_assoc.
apply (rngl_lt_add_r Hos Hor).
rewrite rngl_add_comm.
apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
apply (rngl_2_neq_0 Hos Hc1 Hor).
apply (rngl_pow_neq_0 Hon Hos Hiq).
apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
apply (rngl_2_neq_0 Hos Hc1 Hor).
apply (rngl_pow_neq_0 Hon Hos Hiq).
apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
Qed.

Theorem Int_part_n_partial_sum3 : ∀ u r n,
  (∀ k, (partial_sum3 u k ≤ r)%L)
  → (∀ b, (∀ k, (partial_sum3 u k ≤ b)%L) → (r ≤ b)%L)
  → Int_part Hc1 Har (r * 3 ^ n) = Z.of_nat (n_partial_sum3 u n).
Proof.
destruct_ac.
intros * Hr1 Hr2.
specialize (Hr1 (S n)).
assert (H : (r ≤ partial_sum3 u (S n) + (2 * 3 ^ S n)⁻¹)%L). {
  apply Hr2, partial_sum3_upper_bound.
}
clear Hr2; rename H into Hr2.
specialize (Int_part_interv Hc1 Har (Z.of_nat (n_partial_sum3 u n))) as H1.
apply (proj1 (H1 (r * 3 ^ n)%L)); clear H1.
rewrite rngl_of_Z_add.
rewrite rngl_of_Z_of_nat.
rewrite rngl_of_Z_1.
split. {
  revert u r Hr1 Hr2.
  induction n; intros. {
    unfold partial_sum3 in Hr1, Hr2; simpl in Hr1, Hr2; simpl.
    rewrite rngl_mul_1_r, rngl_of_nat_0.
    rewrite rngl_add_0_r in Hr1.
    destruct (u 0); [ | easy ].
    apply (rngl_le_trans Hor _ (1 / 3)); [ | easy ].
    apply (rngl_div_nonneg Hon Hop Hiv Hor).
    apply (rngl_0_le_1 Hos Hor).
    apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  }
  progress unfold partial_sum3 in Hr1, Hr2.
  rewrite partial_sum3_aux_shift_seq in Hr1, Hr2.
  rewrite rngl_mul_1_l in Hr1, Hr2.
  rewrite n_partial_sum3_succ2.
  remember (u O) as b eqn:Hb; symmetry in Hb.
  unfold b2r in Hr1, Hr2.
  destruct b. {
    remember (S n) as sn; simpl in Hr1, Hr2; subst sn.
    simpl; rewrite Nat.mul_1_r.
    set (v n := u (S n)) in *.
    rewrite rngl_of_nat_add.
    rewrite (rngl_of_nat_pow Hon Hos).
    rewrite rngl_of_nat_3.
    apply (rngl_le_add_le_sub_l Hop Hor).
    rewrite rngl_mul_assoc.
    rewrite (rngl_sub_mul_l_diag_r Hon Hop).
    apply IHn.
    progress unfold partial_sum3.
    rewrite rngl_of_nat_1 in Hr1.
    apply (rngl_le_div_l Hon Hop Hiv Hor) in Hr1.
    now apply (rngl_le_add_le_sub_l Hop Hor) in Hr1.
    apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
    apply (rngl_le_sub_le_add_r Hop Hor).
    rewrite rngl_mul_assoc, (rngl_mul_comm Hic 2) in Hr2.
    rewrite <- rngl_mul_assoc in Hr2.
    rewrite (rngl_inv_mul_distr Hon Hos Hiv) in Hr2.
    rewrite (rngl_mul_inv_r Hiv) in Hr2.
    rewrite <- (rngl_div_add_distr_r Hiv) in Hr2.
    apply (rngl_le_div_r Hon Hop Hiv Hor) in Hr2.
    rewrite rngl_of_nat_1 in Hr2.
    remember 3%L as x.
    rewrite <- rngl_add_assoc in Hr2.
    now rewrite rngl_add_comm in Hr2.
    apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
    apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
    apply (rngl_neq_mul_0 Hon Hos Hiq).
    apply (rngl_2_neq_0 Hos Hc1 Hor).
    apply (rngl_pow_neq_0 Hon Hos Hiq).
    apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  }
  remember (S n) as sn; simpl in Hr1, Hr2; subst sn.
  simpl; rewrite Nat.mul_0_r, Nat.add_0_l.
  progress unfold INR in Hr1, Hr2.
  rewrite rngl_of_nat_0 in Hr1, Hr2.
  rewrite rngl_add_0_l in Hr1, Hr2.
  set (v n := u (S n)) in *.
  rewrite rngl_mul_assoc.
  apply IHn. {
    unfold partial_sum3.
    apply (rngl_le_div_l Hon Hop Hiv Hor) in Hr1; [ easy | ].
    apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  }
  progress unfold partial_sum3.
  set (x := partial_sum3_aux (S n) v 1%L 0) in *.
  apply (rngl_le_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  rewrite (rngl_div_add_distr_r Hiv).
  rewrite (rngl_div_eq_inv_r Hiv _⁻¹).
  rewrite <- (rngl_inv_mul_distr Hon Hos Hiv).
  rewrite rngl_mul_assoc.
  rewrite (rngl_mul_comm Hic 3).
  now rewrite <- rngl_mul_assoc.
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  apply (rngl_neq_mul_0 Hon Hos Hiq).
  apply (rngl_2_neq_0 Hos Hc1 Hor).
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
}
now apply le_partial_sum3_lt_n_partial_sum3.
Qed.

Theorem IZR_Int_part_mult_pow_succ : ∀ u r n,
  (∀ k, (partial_sum3 u k ≤ r)%L)
  → (∀ b, (∀ k, (partial_sum3 u k ≤ b)%L) → (r ≤ b)%L)
  → IZR (Int_part Hc1 Har (r * 3 ^ S n)) =
    (3 * IZR (Int_part Hc1 Har (r * 3 ^ n)) + INR (Nat.b2n (u n)))%L.
Proof.
destruct_ac.
intros * Hr1 Hr2.
rewrite Int_part_n_partial_sum3 with (u := u); [ | easy | easy ].
rewrite Int_part_n_partial_sum3 with (u := u); [ | easy | easy ].
do 2 rewrite rngl_of_Z_of_nat.
rewrite n_partial_sum3_succ.
rewrite rngl_of_nat_add, (rngl_of_nat_mul Hon Hos).
do 2 progress f_equal.
apply rngl_of_nat_3.
Qed.

Theorem Int_part_eq_partial_sum3 : ∀ u r n,
  (∀ k : nat, (partial_sum3 u k ≤ r)%L)
  → (∀ b, (∀ k : nat, (partial_sum3 u k ≤ b)%L) → (r ≤ b)%L)
  → IZR (Int_part Hc1 Har (r * 3 ^ n)) = (partial_sum3 u n * 3 ^ n)%L.
Proof.
destruct_ac.
intros * Hk1 Hk2.
induction n. {
  unfold partial_sum3; simpl.
  do 2 rewrite rngl_mul_1_r.
  specialize (Hk1 O); simpl in Hk1.
  unfold partial_sum3 in Hk1; simpl in Hk1.
  assert (H : ∀ k, (partial_sum3 u k ≤ 1 / 2)%L). {
    intros k; apply partial_sum3_aux_le_half_pow; [ | easy ].
    apply (rngl_0_le_1 Hos Hor).
  }
  specialize (Hk2 (1 / 2)%L H).
  replace 0%L with (IZR 0) by easy.
  progress f_equal.
  apply Int_part_interv.
  split; [ easy | ].
  rewrite rngl_of_Z_1.
  apply (rngl_le_lt_trans Hor _ (1 / 2)); [ easy | ].
  apply (rngl_lt_div_l Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hos Hc1 Hor).
  rewrite rngl_mul_1_l.
  apply (rngl_lt_add_r Hos Hor).
  apply (rngl_0_lt_1 Hos Hc1 Hor).
}
rewrite partial_sum3_succ.
rewrite rngl_mul_add_distr_r.
rewrite (rngl_div_eq_inv_r Hiv).
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hon Hiv).
rewrite rngl_mul_1_r.
remember (r * 3 ^ S n)%L as x; simpl; subst x.
rewrite rngl_mul_assoc, (rngl_mul_mul_swap Hic), <- IHn.
rewrite (rngl_mul_comm Hic _ 3).
now apply IZR_Int_part_mult_pow_succ.
apply (rngl_pow_neq_0 Hon Hos Hiq).
apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
Qed.

Definition rngl_is_upper_bound (E : T → Prop) m := ∀ x, E x → (x ≤ m)%L.
Definition rngl_bound E := ∃ₜ m, rngl_is_upper_bound E m.

Theorem rngl_completeness {em : excl_midd} :
  is_complete T rngl_dist →
  ∀ E, rngl_bound E → (∃ₜ x, E x) → ∃ m, is_supremum E m.
Proof.
destruct_ac.
intros Hco * (b, Hb) (x, Hx).
progress unfold is_supremum.
progress unfold rngl_is_upper_bound in Hb.
generalize Hb; intros H.
apply (upper_bound_property em Hop Hor Hon Hiv Har Hco _ x _ Hx) in H.
destruct H as (m & Hm & Hmb).
exists m.
apply Hm.
Qed.

Theorem ter_bin_of_frac_part_surj {em : excl_midd} :
  is_complete T rngl_dist →
  ∀ u : nat → bool,
  ∃ r, (0 ≤ r < 1)%L ∧ (∀ n, ter_bin_of_frac_part r n = u n).
Proof.
destruct_ac.
intros Hco *.
set (E x := ∃ k, partial_sum3 u k = x).
(**)
assert (Hb : rngl_bound E). {
  exists (1 / 2)%L; subst E; simpl.
  intros r (k & H); subst r.
  apply partial_sum3_aux_le_half_pow; [ | easy ].
  apply (rngl_0_le_1 Hos Hor).
}
assert (He : ∃ₜ r, E r). {
  exists 0%L; subst E; simpl.
  now exists O; unfold partial_sum3.
}
(**)
destruct (rngl_completeness Hco E Hb He) as (r & Hr1 & Hr2).
remember (is_bound _ _ _) as bnd eqn:Hbnd in Hr1.
symmetry in Hbnd.
destruct bnd as [H1| ]; [ clear Hr1; rename H1 into Hr1 | easy ].
assert (Hr3 : (∀ k, partial_sum3 u k ≤ r)%L). {
  now intros k; apply Hr1; exists k.
}
clear Hbnd.
assert (Hr4 : (∀ b, (∀ k, partial_sum3 u k ≤ b) → (r ≤ b))%L). {
  intros b H.
  specialize (Hr2 b).
  remember (is_bound _ _ _) as bnd eqn:Hbnd in Hr2.
  symmetry in Hbnd.
  destruct bnd as [| H1]; [ easy | clear Hr2 ].
  destruct H1 as (x, Hx).
  exfalso; apply Hx; clear Hx Hbnd; intros Hx.
  progress unfold E in Hx.
  destruct Hx as (k, Hx); rewrite <- Hx.
  apply H.
}
assert (Hh : (r ≤ 1 / 2)%L). {
  specialize (Hr2 (1 / 2))%L.
  remember (is_bound _ _ _) as bnd eqn:Hbnd in Hr2.
  symmetry in Hbnd.
  destruct bnd as [| H1]; [ easy | clear Hr2 ].
  destruct H1 as (x, Hx).
  exfalso; apply Hx; clear Hx Hbnd; intros Hx.
  progress unfold E in Hx.
  destruct Hx as (k, Hx); rewrite <- Hx.
  apply partial_sum3_aux_le_half_pow; [ | easy ].
  apply (rngl_0_le_1 Hos Hor).
}
exists r; clear Hb He.
split. {
  split. {
    apply Hr1; unfold E; simpl.
    now exists 0.
  }
  apply (rngl_le_lt_trans Hor _ (1 / 2)); [ easy | ].
  apply (rngl_lt_div_l Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hos Hc1 Hor).
  rewrite rngl_mul_1_l.
  apply (rngl_lt_add_l Hos Hor).
  apply (rngl_0_lt_1 Hos Hc1 Hor).
}
intros n.
clear E Hr1 Hr2.
unfold ter_bin_of_frac_part; symmetry.
destruct (rngl_ltb_dec (frac_part Hc1 Har (r * 3 ^ n)) (1 / 3)) as [H1| H1]. {
  apply rngl_ltb_lt in H1.
  generalize H1; intros H.
  apply rngl_nle_gt in H.
  apply rngl_leb_nle in H.
  rewrite H; clear H.
  progress unfold frac_part in H1.
  rewrite (Int_part_eq_partial_sum3 u) in H1; [ | easy | easy ].
  rewrite <- (rngl_mul_sub_distr_r Hop) in H1.
  apply -> (rngl_lt_div_r Hon Hop Hiv Hor) in H1. {
    rewrite (rngl_div_div Hon Hos Hiv) in H1.
    rewrite <- (rngl_pow_succ_l Hon) in H1.
    specialize (Hr3 (S n)).
    rewrite partial_sum3_succ in Hr3.
    destruct (u n); [ exfalso | easy ].
    simpl in Hr3, H1.
    rewrite rngl_of_nat_1 in Hr3.
    apply (rngl_le_add_le_sub_l Hop Hor) in Hr3.
    now apply rngl_nlt_ge in Hr3.
    apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
    apply (rngl_pow_neq_0 Hon Hos Hiq).
    apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  }
  apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
}
apply (rngl_ltb_ge_iff Hor) in H1.
apply rngl_leb_le in H1.
rewrite H1.
apply rngl_leb_le in H1.
unfold frac_part in H1.
rewrite (Int_part_eq_partial_sum3 u) in H1; [ | easy | easy ].
rewrite <- (rngl_mul_sub_distr_r Hop) in H1.
apply -> (rngl_le_div_l Hon Hop Hiv Hor) in H1. {
  rewrite (rngl_div_div Hon Hos Hiv) in H1.
  rewrite <- (rngl_pow_succ_l Hon) in H1.
  specialize (partial_sum3_upper_bound u (S n)); intros H.
  apply Hr4 in H.
  rewrite partial_sum3_succ in H.
  destruct (u n); [ easy | exfalso ].
  simpl in H1, H.
  rewrite (rngl_div_1_l Hon Hiv) in H1.
  rewrite rngl_of_nat_0 in H.
  rewrite (rngl_div_0_l Hos Hi1), rngl_add_0_r in H.
  rewrite (rngl_inv_mul_distr Hon Hos Hiv) in H.
  set (s := partial_sum3 u n) in H1, H.
  set (t := ((3 * 3 ^ n))⁻¹) in H1, H.
  enough (H2 : (0 < t)%L). {
    apply rngl_nlt_ge in H.
    apply H; clear H.
    apply (rngl_lt_add_lt_sub_l Hop Hor).
    apply (rngl_lt_le_trans Hor _ t); [ | easy ].
    rewrite (rngl_mul_inv_r Hiv).
    apply (rngl_lt_div_l Hon Hop Hiv Hor).
    apply (rngl_0_lt_2 Hos Hc1 Hor).
    rewrite (rngl_mul_2_r Hon).
    now apply (rngl_lt_add_l Hos Hor).
  }
  progress unfold t.
  apply (rngl_inv_pos Hon Hop Hiv Hor).
  apply (rngl_mul_pos_pos Hop Hiq Hor).
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
  apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
  apply (rngl_2_neq_0 Hos Hc1 Hor).
  apply (rngl_neq_mul_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  apply (rngl_neq_mul_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
  apply (rngl_pow_neq_0 Hon Hos Hiq).
  apply (rngl_3_neq_0 Hon Hos Hc1 Hor).
}
apply (rngl_pow_pos_pos Hon Hop Hiv Hor).
apply (rngl_0_lt_3 Hon Hos Hc1 Hor).
Qed.

Definition id {A} (a : A) := a.

Theorem id_nat : ∀ e : ℕ, ∃ x : ℕ, id x = e.
Proof. now intros; exists e. Qed.

Theorem Cantor_ℕ_T {em : excl_midd} :
  is_complete T rngl_dist →
  ∀ f : nat → T, ∃ x : T, ∀ n : nat, x ≠ f n.
Proof.
destruct_ac.
intros Hco.
specialize
  (Cantor_gen ℕ ℕ T (λ x, (0 ≤ x < 1)%L) id ter_bin_of_frac_part id_nat
     (ter_bin_of_frac_part_surj Hco)).
intros H f.
specialize (H f).
destruct H as (x, H); exists x.
intros n; apply H.
Qed.

End a.
