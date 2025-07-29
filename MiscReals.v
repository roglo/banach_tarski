(* Banach-Tarski paradox. *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 List Relations Wf_nat.
From Stdlib Require Import ZArith.
Import ListNotations.

Require Import Misc Words Normalize Reverse.
Require Import RingLike.Core.
Require Import RingLike.RealLike.

Notation "'ℤ'" := Z.
Notation "'ℕ'" := nat.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {Hic : rngl_mul_is_comm T = true}.
Context {Hon : rngl_has_1 T = true}.
Context {Hop : rngl_has_opp T = true}.
Context {Hiv : rngl_has_inv T = true}.
Context {Hor : rngl_is_ordered T = true}.
Context {Hch : rngl_characteristic T = 0}.
Context {Har : rngl_is_archimedean T = true}.

Definition Hos := rngl_has_opp_has_opp_or_subt Hop.
Definition Heo := rngl_has_eq_dec_or_is_ordered_r Hor.
Definition Hiq := rngl_has_inv_has_inv_or_quot Hiv.
Definition Hc1 := eq_ind_r (λ n, n ≠ 1) (Nat.neq_succ_diag_r 0) Hch.
Definition Hi1 := rngl_has_inv_and_1_has_inv_and_1_or_quot Hon Hiv.
Definition Hii := rngl_int_dom_or_inv_1_quo Hiv Hon.

Theorem fold_Rminus : ∀ x y, (x + - y = x - y)%L.
Proof. apply (rngl_add_opp_r Hop). Qed.

Theorem fold_Rdiv : ∀ x y, (x * y⁻¹ = x / y)%L.
Proof. apply (rngl_mul_inv_r Hiv). Qed.

Theorem fold_Rsqr : ∀ x, (x * x = x²)%L.
Proof. apply fold_rngl_squ. Qed.

Theorem Rmult_div : ∀ x y z, (x * y / z = x / z * y)%L.
Proof. intros; symmetry; apply (rngl_div_mul_mul_div Hic Hiv). Qed.

Theorem Rdiv_mult : ∀ x y z, (x * (y / z) = x * y / z)%L.
Proof. apply (rngl_mul_div_assoc Hiv). Qed.

Theorem Rminus_plus_distr : ∀ x y z, (x - (y + z) = x - y - z)%L.
Proof. apply (rngl_sub_add_distr Hos). Qed.

Theorem Rminus_opp : ∀ x y, (x - - y = x + y)%L.
Proof. apply (rngl_sub_opp_r Hop). Qed.

Theorem Ropp_div_r : ∀ x y, y ≠ 0%L → (x / - y = - (x / y))%L.
Proof.
intros * Hyz.
progress unfold rngl_div.
rewrite Hiv.
rewrite <- (rngl_opp_inv Hon Hop Hiv); [ | easy ].
apply (rngl_mul_opp_r Hop).
Qed.

Theorem Rmult_div_same : ∀ x y, (y ≠ 0 → x / y * y = x)%L.
Proof.
intros * Hy.
progress unfold rngl_div.
rewrite Hiv.
rewrite <- rngl_mul_assoc.
rewrite (rngl_mul_inv_diag_l Hon Hiv); [ | easy ].
apply (rngl_mul_1_r Hon).
Qed.

Theorem Rplus_shuffle0 : ∀ n m p, (n + m + p = n + p + m)%L.
Proof. apply rngl_add_add_swap. Qed.

Theorem Rmult_shuffle0 : ∀ n m p, (n * m * p = n * p * m)%L.
Proof. apply (rngl_mul_mul_swap Hic). Qed.

Theorem Rdiv_mult_simpl_l : ∀ x y z,
  x ≠ 0%L
  → z ≠ 0%L
  → ((x * y) / (x * z) = y / z)%L.
Proof.
intros * Hx Hz.
progress unfold rngl_div.
rewrite Hiv.
rewrite (rngl_inv_mul_distr Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_mul_comm Hic _⁻¹).
rewrite rngl_mul_assoc.
progress f_equal.
rewrite (rngl_mul_mul_swap Hic).
rewrite (rngl_mul_inv_diag_r Hon Hiv); [ | easy ].
apply (rngl_mul_1_l Hon).
Qed.

Theorem Rdiv_mult_simpl_r : ∀ x y z,
  y ≠ 0%L
  → z ≠ 0%L
  → ((x * z) / (y * z) = x / y)%L.
Proof.
intros * Hy Hz.
specialize (Rdiv_mult_simpl_l z x y Hz Hy) as H.
rewrite <- H.
do 2 rewrite (rngl_mul_comm Hic z).
easy.
Qed.

Theorem Req_dec : ∀ x y : T, { x = y } + { x ≠ y }.
Proof.
intros x y.
destruct (rngl_le_dec Hor x y) as [H₁| H₁]. {
  destruct (rngl_le_dec Hor y x) as [H₂| H₂]. {
    left; now apply rngl_le_antisymm.
  } {
    right; intros H; subst y; apply H₂, (rngl_le_refl Hor).
  }
} {
  right; intros H; subst y.
  apply H₁, (rngl_le_refl Hor).
}
Qed.

Theorem Rmult5_sqrt2_sqrt5 : ∀ a b c d, (0 ≤ b)%L →
  (a * √ b * c * d * √ b = a * b * c * d)%L.
Proof.
intros a b c d Hb.
rewrite (rngl_mul_comm Hic), rngl_mul_assoc; f_equal.
rewrite rngl_mul_assoc; f_equal.
rewrite (rngl_mul_comm Hic), <- rngl_mul_assoc; f_equal.
rewrite <- rl_sqrt_mul; [ | easy | easy ].
rewrite fold_rngl_squ.
rewrite (rl_sqrt_squ Hon Hop Hor).
now apply (rngl_abs_nonneg_eq Hop Hor).
Qed.

Theorem Rdiv_0_l : ∀ x, (x ≠ 0 → 0 / x = 0)%L.
Proof.
now intros * Hx; apply (rngl_div_0_l Hos Hi1).
Qed.

Theorem Rdiv_1_r : ∀ x, (x / 1 = x)%L.
Proof. apply (rngl_div_1_r' Hon Hos Hiq). Qed.

Theorem Rdiv_same : ∀ x, (x ≠ 0 → x / x = 1)%L.
Proof. apply (rngl_div_diag Hon Hiq). Qed.

Fixpoint rngl_of_pos_2 a :=
  match a with
  | xI n => (2 * (1 + rngl_of_pos_2 n))%L
  | xO n => (2 * rngl_of_pos_2 n)%L
  | xH => 2%L
  end.

Definition rngl_of_pos a :=
  match a with
  | xI n => (1 + rngl_of_pos_2 n)%L
  | xO n => rngl_of_pos_2 n
  | xH => 1%L
  end.

Definition rngl_of_Z a :=
  match a with
  | 0%Z => 0%L
  | Z.pos n => rngl_of_pos n
  | Z.neg n => (- rngl_of_pos n)%L
  end.

Definition Int_part (x : T) :=
  let (n, a) := int_part Hon Hop Hc1 Hor Har x in
  if rngl_le_dec Hor 0 x then Z.of_nat n else (- Z.of_nat n)%Z.

Definition frac_part (x : T) :=
  (x - rngl_of_Z (Int_part x))%L.

Arguments Int_part x%_L.
Arguments frac_part x%_L.

(*
End a.

From Stdlib Require Import ZArith.
Require Import RingLike.Z_algebra.
Open Scope Z_scope.

Compute (Int_part 3).
Compute (rngl_of_Z 3).
Compute (rngl_of_Z 239 * rngl_of_Z 4649)%L.
*)

(* INR = rngl_of_nat *)

Theorem Int_part_close_to_1 : ∀ (r : T) n,
  (rngl_of_nat n / rngl_of_nat (n + 1) ≤ r < 1)%L
  → Int_part (r * rngl_of_nat (n + 1)) = Z.of_nat n.
Proof.
intros * (Hnr, Hr1).
apply (rngl_mul_le_mono_nonneg_r Hop Hor _ _ (rngl_of_nat (n + 1)))
  in Hnr. 2: {
  apply (rngl_of_nat_nonneg Hon Hos Hor).
}
rewrite <- Rmult_div in Hnr.
unfold rngl_div in Hnr.
rewrite Hiv in Hnr.
rewrite <- rngl_mul_assoc in Hnr.
rewrite (rngl_mul_inv_diag_r Hon Hiv) in Hnr. 2: {
  rewrite Nat.add_comm.
  now apply (rngl_characteristic_0 Hon).
}
rewrite (rngl_mul_1_r Hon) in Hnr.
apply (rngl_mul_lt_mono_pos_r Hop Hor Hii (rngl_of_nat (n + 1))) in Hr1. 2: {
  rewrite Nat.add_1_r.
  apply (rngl_lt_iff Hor).
  split; [ apply (rngl_of_nat_nonneg Hon Hos Hor) | ].
  symmetry.
  apply (rngl_characteristic_0 Hon Hch).
}
rewrite (rngl_mul_1_l Hon) in Hr1.
remember (r * rngl_of_nat (n + 1))%L as x eqn:Hx.
rewrite rngl_of_nat_add in Hr1; cbn in Hr1.
rewrite rngl_add_0_r in Hr1.
progress unfold Int_part.
remember (int_part Hon Hop Hc1 Hor Har x) as y eqn:Hy.
symmetry in Hy.
destruct y as (m, Hm).
clear Hy.
destruct (rngl_le_dec Hor 0 x) as [Hzx| Hzx]. {
  rewrite (rngl_abs_nonneg_eq Hop Hor) in Hm; [ | easy ].
  progress f_equal.
  apply Nat.le_antisymm. {
    apply Nat.lt_succ_r.
    apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
    apply (rngl_le_lt_trans Hor _ x); [ easy | ].
    now rewrite rngl_of_nat_succ, rngl_add_comm.
  } {
    apply Nat.lt_succ_r.
    apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor).
    apply (rngl_le_lt_trans Hor _ x); [ easy | ].
    now rewrite <- Nat.add_1_r.
  }
}
exfalso; apply Hzx.
apply (rngl_le_trans Hor _ (rngl_of_nat n)); [ | easy ].
apply (rngl_of_nat_nonneg Hon Hos Hor).
Qed.

Theorem Int_part_small : ∀ x, (0 ≤ x < 1)%L → Int_part x = 0%Z.
Proof.
intros * Hx.
assert ((rngl_of_nat 0 / rngl_of_nat (0 + 1) ≤ x < 1)%L). {
  now cbn; rewrite rngl_add_0_r, (rngl_div_1_r Hon Hiq Hc1).
}
specialize (Int_part_close_to_1 x 0 H) as H1.
cbn in H1.
now rewrite rngl_add_0_r, (rngl_mul_1_r Hon) in H1.
Qed.

Theorem frac_part_small : ∀ x, (0 ≤ x < 1)%L → frac_part x = x.
Proof.
intros * Hx.
unfold frac_part.
rewrite Int_part_small; [ | easy ].
apply (rngl_sub_0_r Hos).
Qed.

Theorem pow_INR : ∀ n k, rngl_of_nat (n ^ k) = (rngl_of_nat n ^ k)%L.
Proof.
intros.
induction k; [ cbn; apply rngl_add_0_r | ].
simpl; rewrite <- IHk.
apply (rngl_of_nat_mul Hon Hos).
Qed.

Theorem Int_part_rngl_of_nat : ∀ a, Int_part (rngl_of_nat a) = Z.of_nat a.
Proof.
intros.
progress unfold Int_part.
remember (int_part Hon Hop Hc1 Hor Har (rngl_of_nat a)) as n eqn:Hn.
destruct n as (n, Hna).
clear Hn.
rewrite (rngl_abs_nonneg_eq Hop Hor) in Hna. 2: {
  apply (rngl_of_nat_nonneg Hon Hos Hor).
}
destruct Hna as (H1, H2).
apply (rngl_of_nat_inj_le Hon Hop Hc1 Hor) in H1.
apply (rngl_of_nat_inj_lt Hon Hop Hc1 Hor) in H2.
rewrite Nat.add_1_r in H2.
apply -> Nat.lt_succ_r in H2.
apply Nat.le_antisymm in H1; [ subst | easy ].
destruct (rngl_le_dec Hor 0 (rngl_of_nat n)) as [H1| H1]; [ easy | ].
exfalso; apply H1, (rngl_of_nat_nonneg Hon Hos Hor).
Qed.

Theorem rngl_of_pos_2_succ :
  ∀ a, rngl_of_pos_2 (Pos.succ a) = (2 + rngl_of_pos_2 a)%L.
Proof.
intros.
induction a as [a| a| ]; cbn. {
  rewrite <- (rngl_mul_1_r Hon 2) at 2.
  rewrite <- rngl_mul_add_distr_l.
  progress f_equal.
  rewrite rngl_add_assoc.
  apply IHa.
} {
  rewrite rngl_mul_add_distr_l.
  now rewrite (rngl_mul_1_r Hon).
} {
  rewrite rngl_mul_add_distr_l.
  now rewrite (rngl_mul_1_r Hon).
}
Qed.

Theorem Pos_pred_inj :
  ∀ a b, a ≠ 1%positive → b ≠ 1%positive → Pos.pred a = Pos.pred b → a = b.
Proof.
intros * Ha Hb Hab.
apply (f_equal Pos.succ) in Hab.
rewrite Pos.succ_pred in Hab; [ | easy ].
rewrite Pos.succ_pred in Hab; [ | easy ].
easy.
Qed.

Theorem Pos_pred_double_inj :
  ∀ a b, Pos.pred_double a = Pos.pred_double b → a = b.
Proof.
intros * Hab.
do 2 rewrite Pos.pred_double_spec in Hab.
apply Pos_pred_inj in Hab; [ | easy | easy ].
now injection Hab; clear Hab; intros.
Qed.

Theorem rngl_of_pos_2_pred :
  ∀ a,
  (1 < a)%positive
  → rngl_of_pos_2 (Pos.pred a) = (rngl_of_pos_2 a - 2)%L.
Proof.
intros * H1a.
induction a as [a| a| ]; cbn. {
  rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
  rewrite (rngl_add_comm 2); symmetry.
  apply (rngl_add_sub Hos).
} {
  remember (Pos.pred_double a) as b eqn:Hb.
  symmetry in Hb.
  destruct b as [b| b| ]; [ | now destruct a | ]. {
    cbn.
    rewrite <- Pos.pred_double_succ in Hb.
    apply Pos_pred_double_inj in Hb; subst.
    rewrite rngl_of_pos_2_succ.
    rewrite <- (rngl_mul_1_r Hon 2) at 4.
    rewrite <- (rngl_mul_sub_distr_l Hop).
    progress f_equal.
    rewrite (rngl_add_comm 2).
    rewrite <- (rngl_add_sub_assoc Hop).
    rewrite (rngl_add_sub Hos).
    apply rngl_add_comm.
  } {
    destruct a as [a| a| ]; [ easy | easy | cbn ].
    symmetry.
    rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
    apply (rngl_add_sub Hos).
  }
} {
  now apply Pos.lt_irrefl in H1a.
}
Qed.

Theorem rngl_of_pos_pred :
  ∀ a,
  (1 < a)%positive
  → rngl_of_pos (Pos.pred a) = (rngl_of_pos a - 1)%L.
Proof.
intros * H1a.
destruct a as [a| a| ]; cbn. {
  rewrite rngl_add_comm; symmetry.
  apply (rngl_add_sub Hos).
} {
  destruct a as [a| a| ]; cbn. {
    rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
    rewrite (rngl_add_sub_swap Hop).
    progress f_equal; symmetry.
    apply (rngl_add_sub Hos).
  } {
    rewrite Pos.pred_double_spec.
    rewrite rngl_of_pos_2_pred; [ cbn | easy ].
    rewrite rngl_add_comm.
    rewrite <- (rngl_sub_sub_distr Hop).
    progress f_equal.
    apply (rngl_add_sub Hos).
  } {
    symmetry; apply (rngl_add_sub Hos).
  }
} {
  now apply Pos.lt_irrefl in H1a.
}
Qed.

Theorem rngl_of_pos_2_add : ∀ a b,
  rngl_of_pos_2 (a + b) = (rngl_of_pos_2 a + rngl_of_pos_2 b)%L.
Proof.
intros.
revert b.
induction a as [a| a| ]; intros; cbn. {
  destruct b as [b| b| ]; cbn. {
    rewrite <- rngl_mul_add_distr_l.
    progress f_equal.
    rewrite rngl_add_assoc.
    rewrite (rngl_add_add_swap 1).
    rewrite Pos.add_carry_spec.
    rewrite Pplus_one_succ_l.
    rewrite Pos.add_comm.
    rewrite <- Pos.add_assoc.
    rewrite IHa.
    rewrite (rngl_add_comm 2).
    rewrite <- rngl_add_assoc.
    progress f_equal.
    rewrite Pos.add_1_r.
    apply rngl_of_pos_2_succ.
  } {
    rewrite <- rngl_mul_add_distr_l.
    progress f_equal.
    rewrite <- rngl_add_assoc.
    progress f_equal.
    apply IHa.
  } {
    rewrite <- (rngl_mul_1_r Hon 2) at 3.
    rewrite <- rngl_mul_add_distr_l.
    progress f_equal.
    rewrite rngl_add_add_swap.
    apply rngl_of_pos_2_succ.
  }
} {
  destruct b as [b| b| ]; cbn. {
    rewrite <- rngl_mul_add_distr_l.
    progress f_equal.
    rewrite rngl_add_assoc.
    rewrite (rngl_add_comm _ 1).
    rewrite <- rngl_add_assoc.
    progress f_equal.
    apply IHa.
  } {
    rewrite <- rngl_mul_add_distr_l.
    progress f_equal.
    apply IHa.
  } {
    rewrite <- (rngl_mul_1_r Hon 2) at 3.
    rewrite <- rngl_mul_add_distr_l.
    progress f_equal.
    apply rngl_add_comm.
  }
} {
  destruct b as [b| b| ]; cbn. {
    rewrite <- (rngl_mul_1_r Hon 2) at 2.
    rewrite <- rngl_mul_add_distr_l.
    progress f_equal.
    rewrite rngl_add_assoc.
    apply rngl_of_pos_2_succ.
  } {
    rewrite rngl_mul_add_distr_l.
    progress f_equal.
    apply (rngl_mul_1_r Hon).
  } {
    rewrite rngl_mul_add_distr_l.
    f_equal; apply (rngl_mul_1_r Hon).
  }
}
Qed.

Theorem rngl_of_pos_2_sub : ∀ a b,
  (b < a)%positive
  → rngl_of_pos_2 (a - b) = (rngl_of_pos_2 a - rngl_of_pos_2 b)%L.
Proof.
intros * Hba.
revert b Hba.
induction a as [a| a| ]; intros; cbn; [ | | now apply Pos.nlt_1_r in Hba ]. {
  destruct b as [b| b| ]; cbn. {
    apply Pos.compare_lt_iff in Hba.
    cbn in Hba.
    apply -> Pos.compare_lt_iff in Hba.
    rewrite Pos.sub_xI_xI; [ cbn | easy ].
    rewrite <- (rngl_mul_sub_distr_l Hop).
    progress f_equal.
    rewrite (rngl_sub_add_distr Hos).
    rewrite (rngl_add_comm 1 (rngl_of_pos_2 _)).
    rewrite (rngl_add_sub Hos).
    now apply IHa.
  } {
    apply Pos.compare_lt_iff in Hba.
    cbn in Hba.
    apply Pos.compare_cont_Lt_Lt in Hba.
    apply Pos.lt_eq_cases in Hba.
    rewrite Pos.xI_succ_xO.
    rewrite Pplus_one_succ_l.
    destruct Hba as [Hba| ]; [ | subst ]. 2: {
      rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
      rewrite (rngl_add_sub Hos).
      now rewrite Pos.add_sub.
    }
    rewrite <- Pos.add_sub_assoc; [ | now apply -> Pos.compare_lt_iff ].
    rewrite rngl_of_pos_2_add; cbn.
    rewrite Pos.sub_xO_xO; [ cbn | easy ].
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite <- (rngl_add_sub_assoc Hop).
    rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
    now rewrite IHa.
  } {
    rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
    now rewrite (rngl_add_comm 2), (rngl_add_sub Hos).
  }
} {
  destruct b as [b| b| ]; cbn. {
    generalize Hba; intros Hba'.
    apply Pos.compare_lt_iff in Hba'.
    cbn in Hba'.
    apply Pos.compare_cont_Gt_Lt in Hba'.
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite (rngl_add_comm 1 (rngl_of_pos_2 _)).
    rewrite (rngl_sub_add_distr Hos).
    rewrite <- IHa; [ | easy ].
    rewrite Pos.xI_succ_xO.
    rewrite Pplus_one_succ_l.
    rewrite Pos.add_comm.
    rewrite Pos.sub_add_distr; [ | easy ].
    rewrite Pos.sub_xO_xO; [ | easy ].
    rewrite <- Pos.pred_sub.
    rewrite rngl_of_pos_2_pred; [ cbn | easy ].
    rewrite (rngl_mul_sub_distr_l Hop).
    f_equal; symmetry.
    apply (rngl_mul_1_r Hon).
  } {
    apply Pos.compare_lt_iff in Hba.
    cbn in Hba.
    apply -> Pos.compare_lt_iff in Hba.
    rewrite Pos.sub_xO_xO; [ cbn | easy ].
    rewrite <- (rngl_mul_sub_distr_l Hop).
    progress f_equal.
    now apply IHa.
  } {
    rewrite Pos.pred_double_spec.
    now apply rngl_of_pos_2_pred.
  }
}
Qed.

Theorem rngl_of_pos_add :
  ∀ a b, rngl_of_pos (a + b) = (rngl_of_pos a + rngl_of_pos b)%L.
Proof.
intros.
destruct a as [a| a| ]; cbn. {
  destruct b as [b| b| ]; cbn. {
    rewrite rngl_add_assoc.
    rewrite (rngl_add_add_swap 1).
    rewrite Pos.add_carry_spec.
    rewrite Pplus_one_succ_l.
    rewrite rngl_of_pos_2_add; cbn.
    rewrite <- (rngl_add_assoc 2).
    progress f_equal.
    apply rngl_of_pos_2_add.
  } {
    rewrite <- rngl_add_assoc.
    progress f_equal.
    apply rngl_of_pos_2_add.
  } {
    rewrite rngl_add_add_swap.
    apply rngl_of_pos_2_succ.
  }
} {
  destruct b as [b| b| ]; cbn. {
    rewrite rngl_add_assoc.
    rewrite (rngl_add_comm _ 1).
    rewrite <- rngl_add_assoc.
    progress f_equal.
    apply rngl_of_pos_2_add.
  } {
    apply rngl_of_pos_2_add.
  } {
    apply rngl_add_comm.
  }
} {
  destruct b as [b| b| ]; cbn; [ | easy | easy ].
  rewrite rngl_add_assoc.
  apply rngl_of_pos_2_succ.
}
Qed.

Theorem rngl_of_pos_sub :
  ∀ a b,
  (b < a)%positive
  → rngl_of_pos (a - b) = (rngl_of_pos a - rngl_of_pos b)%L.
Proof.
intros * Hba.
destruct a as [a| a| ]; cbn. {
  destruct b as [b| b| ]; cbn. {
    rewrite (rngl_sub_add_distr Hos).
    rewrite rngl_add_comm, (rngl_add_sub Hos).
    apply Pos.compare_lt_iff in Hba.
    cbn in Hba.
    apply -> Pos.compare_lt_iff in Hba.
    rewrite Pos.sub_xI_xI; [ cbn | easy ].
    now apply rngl_of_pos_2_sub.
  } {
    apply Pos.compare_lt_iff in Hba.
    cbn in Hba.
    apply Pos.compare_cont_Lt_Lt in Hba.
    apply Pos.lt_eq_cases in Hba.
    rewrite Pos.xI_succ_xO.
    rewrite Pplus_one_succ_l.
    destruct Hba as [Hba| Hba]. {
      rewrite <- Pos.add_sub_assoc. 2: {
        apply -> Pos.compare_lt_iff; cbn.
        now apply Pos.compare_lt_iff.
      }
      rewrite rngl_of_pos_add; cbn.
      rewrite <- (rngl_add_sub_assoc Hop).
      progress f_equal.
      rewrite Pos.sub_xO_xO; [ cbn | easy ].
      now apply rngl_of_pos_2_sub.
    }
    subst.
    rewrite Pos.add_sub; symmetry.
    apply (rngl_add_sub Hos).
  } {
    rewrite rngl_add_comm; symmetry.
    apply (rngl_add_sub Hos).
  }
} {
  destruct b as [b| b| ]; cbn. {
    generalize Hba; intros Hba'.
    apply Pos.compare_lt_iff in Hba.
    cbn in Hba.
    apply Pos.compare_cont_Gt_Lt in Hba.
    rewrite Pos.sub_xO_xI.
    rewrite (rngl_sub_add_distr Hos).
    rewrite (rngl_sub_sub_swap Hop).
    rewrite <- rngl_of_pos_2_sub; [ | easy ].
    destruct (a - b)%positive as [c| c| ]; cbn. {
      rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
      rewrite (rngl_add_sub_swap Hop).
      now rewrite (rngl_add_sub Hos).
    } {
      rewrite Pos.pred_double_spec.
      rewrite rngl_of_pos_2_pred; [ cbn | easy ].
      rewrite rngl_add_comm.
      rewrite <- (rngl_sub_sub_distr Hop).
      progress f_equal.
      apply (rngl_add_sub Hos).
    } {
      symmetry; apply (rngl_add_sub Hos).
    }
  } {
    apply Pos.compare_lt_iff in Hba.
    cbn in Hba.
    apply -> Pos.compare_lt_iff in Hba.
    rewrite Pos.sub_xO_xO; [ cbn | easy ].
    now apply rngl_of_pos_2_sub.
  } {
    rewrite Pos.pred_double_spec.
    now apply rngl_of_pos_pred.
  }
} {
  now apply Pos.nlt_1_r in Hba.
}
Qed.

Theorem rngl_of_Z_of_nat : ∀ a, rngl_of_Z (Z.of_nat a) = rngl_of_nat a.
Proof.
intros.
progress unfold rngl_of_Z.
remember (Z.of_nat a) as za eqn:Hza.
symmetry in Hza.
destruct za as [| n| n]; [ now destruct a | | ]. {
  revert n Hza.
  induction a; intros; [ easy | ].
  rewrite rngl_of_nat_succ.
  rewrite Nat2Z.inj_succ in Hza.
  progress unfold Z.succ in Hza.
  destruct n as [n| n| ]. {
    cbn; f_equal.
    rewrite Pos2Z.inj_xI in Hza.
    apply Z.add_cancel_r in Hza.
    rewrite <- Pos2Z.inj_mul in Hza.
    now apply IHa in Hza.
  } {
    cbn.
    rewrite Pos2Z.inj_xO in Hza.
    rewrite <- Pos2Z.inj_mul in Hza.
    apply Z.add_move_r in Hza.
    assert (H12n : (1 < 2 * n)%positive). {
      apply Pos.le_succ_l.
      cbn - [ Pos.mul ].
      rewrite <- (Pos.mul_1_r 2) at 1.
      apply Pos.mul_le_mono_l.
      apply Pos.le_1_l.
    }
    rewrite <- Pos2Z.inj_sub in Hza; [ | easy ].
    apply IHa in Hza.
    rewrite <- Hza.
    replace 1%L with (rngl_of_pos 1) by easy.
    rewrite <- rngl_of_pos_add.
    now rewrite Pos.add_sub_assoc.
  } {
    apply Z.add_move_r in Hza.
    rewrite Z.sub_diag in Hza.
    symmetry; cbn.
    apply (rngl_add_move_l Hop).
    rewrite (rngl_sub_diag Hos).
    now destruct a.
  }
}
specialize (Nat2Z.is_nonneg a) as H1.
rewrite Hza in H1.
exfalso; apply Z.nlt_ge in H1.
now apply H1.
Qed.

Theorem frac_part_INR : ∀ n, frac_part (rngl_of_nat n) = 0%L.
Proof.
intros.
unfold frac_part.
rewrite Int_part_rngl_of_nat.
rewrite rngl_of_Z_of_nat.
apply (rngl_sub_diag Hos).
Qed.

Theorem rngl_of_Z_add_1_l : ∀ a, rngl_of_Z (1 + a) = (1 + rngl_of_Z a)%L.
Proof.
intros.
destruct a as [| a| a]; cbn. {
  symmetry; apply rngl_add_0_r.
} {
  destruct a as [a| a| ]; cbn; [ | easy | easy ].
  rewrite rngl_add_assoc.
  apply rngl_of_pos_2_succ.
} {
  induction a as [a| a| ]. {
    cbn.
    rewrite (rngl_add_opp_r Hop).
    rewrite (rngl_sub_add_distr Hos).
    rewrite (rngl_sub_diag Hos).
    symmetry; apply (rngl_sub_0_l Hop).
  } {
    cbn.
    rewrite Pos.pred_double_spec.
    rewrite Pos.pred_sub.
    rewrite rngl_of_pos_sub; [ cbn | easy ].
    rewrite (rngl_add_opp_r Hop).
    apply (rngl_opp_sub_distr Hop).
  } {
    symmetry; cbn.
    apply (rngl_add_opp_diag_r Hop).
  }
}
Qed.

Theorem rngl_of_Z_pred : ∀ a, rngl_of_Z (Z.pred a) = (rngl_of_Z a - 1)%L.
Proof.
intros.
destruct a as [| a| a]; cbn. {
  symmetry; apply (rngl_sub_0_l Hop).
} {
  destruct a as [a| a| ]; cbn. {
    symmetry; rewrite rngl_add_comm.
    apply (rngl_add_sub Hos).
  } {
    rewrite Pos.pred_double_spec.
    now apply rngl_of_pos_pred.
  } {
    symmetry; apply (rngl_sub_diag Hos).
  }
} {
  rewrite rngl_of_pos_add, rngl_add_comm.
  apply (rngl_opp_add_distr Hop).
}
Qed.

Theorem Pos_dec : ∀ a b, ({a < b} + {b < a} + {a = b})%positive.
Proof.
intros.
progress unfold Pos.lt.
rewrite (Pos.compare_antisym a).
remember (a ?= b)%positive as ab eqn:Hab.
symmetry in Hab.
destruct ab; [ right | now left; left | now left; right ].
now apply Pos.compare_eq_iff in Hab.
Qed.

Theorem rngl_of_Z_succ : ∀ a, rngl_of_Z (Z.succ a) = (1 + rngl_of_Z a)%L.
Proof.
intros.
symmetry.
destruct a as [| a| a]; cbn; [ apply rngl_add_0_r | | ]. {
  rewrite rngl_of_pos_add.
  apply rngl_add_comm.
} {
  rewrite (rngl_add_opp_r Hop).
  destruct a as [a| a| ]; cbn. {
    rewrite (rngl_sub_add_distr Hos).
    rewrite (rngl_sub_diag Hos).
    apply (rngl_sub_0_l Hop).
  } {
    rewrite Pos.pred_double_spec.
    rewrite rngl_of_pos_pred; [ symmetry | easy ].
    apply (rngl_opp_sub_distr Hop).
  } {
    apply (rngl_sub_diag Hos).
  }
}
Qed.

Theorem rngl_of_Z_add :
  ∀ a b, rngl_of_Z (a + b) = (rngl_of_Z a + rngl_of_Z b)%L.
Proof.
intros.
induction a as [| a| a]. {
  symmetry; apply rngl_add_0_l.
} {
  destruct b as [| b| b]. {
    symmetry; apply rngl_add_0_r.
  } {
    apply rngl_of_pos_add.
  } {
    cbn.
    rewrite <- Pos2Z.add_pos_neg.
    rewrite (rngl_add_opp_r Hop).
    revert b.
    induction a as [a| a| ]; cbn; intros. {
      destruct b as [b| b| ]. {
        cbn.
        rewrite (rngl_sub_add_distr Hos).
        rewrite rngl_add_comm, (rngl_add_sub Hos).
        rewrite Z.double_spec.
        destruct (Pos_dec a b) as [[Hab| Hab]| Hab]. {
          rewrite Z.pos_sub_lt; [ cbn | easy ].
          apply (rngl_opp_inj Hop).
          rewrite (rngl_opp_involutive Hop).
          rewrite (rngl_opp_sub_distr Hop).
          now apply rngl_of_pos_2_sub.
        } {
          rewrite Z.pos_sub_gt; [ cbn | easy ].
          now apply rngl_of_pos_2_sub.
        } {
          subst.
          rewrite Z.pos_sub_diag, Z.mul_0_r; symmetry.
          apply (rngl_sub_diag Hos).
        }
      } {
        cbn.
        rewrite Z.succ_double_spec, Z.add_1_r.
        rewrite rngl_of_Z_succ.
        rewrite <- (rngl_add_sub_assoc Hop).
        progress f_equal.
        destruct (Pos_dec a b) as [[Hab| Hab]| Hab]. {
          rewrite Z.pos_sub_lt; [ cbn | easy ].
          apply (rngl_opp_inj Hop).
          rewrite (rngl_opp_involutive Hop).
          rewrite (rngl_opp_sub_distr Hop).
          now apply rngl_of_pos_2_sub.
        } {
          rewrite Z.pos_sub_gt; [ cbn | easy ].
          now apply rngl_of_pos_2_sub.
        } {
          subst.
          rewrite Z.pos_sub_diag, Z.mul_0_r; symmetry.
          apply (rngl_sub_diag Hos).
        }
      } {
        cbn; symmetry.
        rewrite rngl_add_comm.
        apply (rngl_add_sub Hos).
      }
    } {
      destruct b as [b| b| ]. {
        cbn.
        rewrite rngl_add_comm.
        rewrite (rngl_sub_add_distr Hos).
        rewrite Z.pred_double_spec.
        destruct (Pos_dec a b) as [[Hab| Hab]| Hab]. {
          rewrite Z.pos_sub_lt; [ cbn | easy ].
          apply (rngl_opp_inj Hop).
          rewrite (rngl_opp_involutive Hop).
          rewrite (rngl_opp_sub_distr Hop).
          rewrite (rngl_sub_sub_distr Hop).
          rewrite <- (rngl_add_sub_swap Hop).
          rewrite <- (rngl_add_sub_assoc Hop).
          progress f_equal.
          now apply rngl_of_pos_2_sub.
        } {
          rewrite Z.pos_sub_gt; [ | easy ].
          rewrite Z.sub_1_r.
          rewrite rngl_of_Z_pred.
          progress f_equal; cbn.
          now apply rngl_of_pos_2_sub.
        } {
          subst.
          rewrite Z.pos_sub_diag, Z.mul_0_r; symmetry; cbn.
          rewrite (rngl_sub_diag Hos).
          apply (rngl_sub_0_l Hop).
        }
      } {
        cbn.
        rewrite Z.double_spec.
        destruct (Pos_dec a b) as [[Hab| Hab]| Hab]. {
          rewrite Z.pos_sub_lt; [ cbn | easy ].
          apply (rngl_opp_inj Hop).
          rewrite (rngl_opp_involutive Hop).
          rewrite (rngl_opp_sub_distr Hop).
          now apply rngl_of_pos_2_sub.
        } {
          rewrite Z.pos_sub_gt; [ cbn | easy ].
          now apply rngl_of_pos_2_sub.
        } {
          subst.
          rewrite Z.pos_sub_diag, Z.mul_0_r; symmetry.
          apply (rngl_sub_diag Hos).
        }
      } {
        cbn.
        rewrite Pos.pred_double_spec.
        now apply rngl_of_pos_pred.
      }
    } {
      rewrite <- Pos2Z.add_pos_neg.
      rewrite rngl_of_Z_add_1_l; cbn.
      apply (rngl_add_opp_r Hop).
    }
  }
} {
  destruct b as [| b| b]. {
    symmetry; apply rngl_add_0_r.
  } {
    cbn.
    rewrite (rngl_add_opp_l Hop).
...
    rewrite Z.pos_sub_gt.
Check rngl_of_pos_add.
...
    apply rngl_of_pos_add.
  } {
    cbn.
    rewrite <- Pos2Z.add_pos_neg.
    rewrite (rngl_add_opp_r Hop).
    revert b.
    induction a as [a| a| ]; cbn; intros. {
...
      destruct b as [b| b| ]; cbn. {
        rewrite Z.pred_double_spec.
        rewrite Z.sub_1_r.
        rewrite rngl_of_Z_pred.
        rewrite <- Pos2Z.add_pos_neg.
...
        rewrite Z.pos_sub_spec.
        cbn.
      rewrite Z.pos_sub_spec.

      rewrite <- Pos2Z.add_pos_neg.
...
Search (Z.succ _ = _ + _)%Z.
      rewrite Z.succ.
...

Theorem rngl_of_Z_sub :
  ∀ a b, rngl_of_Z (a - b) = (rngl_of_Z a - rngl_of_Z b)%L.
Proof.
intros.
progress unfold Z.sub.
progress unfold rngl_sub.
rewrite Hop.
...

Theorem rngl_sub_Int_part : ∀ a b,
  (frac_part b ≤ frac_part a)%L
  → Int_part (a - b) = (Int_part a - Int_part b)%Z.
Proof.
intros * Hba.
progress unfold frac_part in Hba.
apply (rngl_le_add_le_sub_r Hop Hor) in Hba.
rewrite <- (rngl_add_sub_swap Hop) in Hba.
rewrite <- (rngl_add_sub_assoc Hop) in Hba.
apply (rngl_le_add_le_sub_l Hop Hor) in Hba.
Search (rngl_of_Z (_ + _)).
Search (rngl_of_Z (_ - _)).
...

Theorem rngl_of_nat_Pos_to_nat :
  ∀ a, rngl_of_pos a = rngl_of_nat (Pos.to_nat a).
Proof.
intros.
induction a as [a| a| ]; cbn. {
  rewrite Pos2Nat.inj_xI.
  rewrite rngl_of_nat_succ.
  progress f_equal.
  rewrite (rngl_of_nat_mul Hon Hos).
  rewrite rngl_of_nat_2.
  rewrite <- IHa.
  clear IHa.
  induction a as [a| a| ]; cbn; [ easy | easy | ].
  symmetry; apply (rngl_mul_1_r Hon).
} {
  rewrite Pos2Nat.inj_xO.
  rewrite (rngl_of_nat_mul Hon Hos).
  rewrite rngl_of_nat_2.
  rewrite <- IHa.
  clear IHa.
  induction a as [a| a| ]; cbn; [ easy | easy | ].
  symmetry; apply (rngl_mul_1_r Hon).
} {
  rewrite Pos2Nat.inj_1; symmetry.
  apply rngl_of_nat_1.
}
Qed.

Theorem Int_part_IZR : ∀ z, Int_part (rngl_of_Z z) = z.
Proof.
intros.
destruct (Z_le_dec 0 z) as [Hz| Hz]. {
  apply Z2Nat.id in Hz.
  rewrite <- Hz at 1.
  rewrite rngl_of_Z_of_nat.
  now rewrite Int_part_rngl_of_nat.
}
apply Z.nle_gt in Hz.
destruct z as [| p| p]; [ easy | easy | ].
cbn.
rewrite <- (rngl_sub_0_l Hop).
rewrite rngl_sub_Int_part. 2: {
  cbn.
  rewrite rngl_of_nat_Pos_to_nat.
...
Require Import Reals.
Check INR_IPR.
...
Search (Int_part (_ - _)).
...
Rminus_Int_part1
     : ∀ r1 r2 : R,
         (frac_part r1 >= frac_part r2)%R → Int_part (r1 - r2) = (Int_part r1 - Int_part r2)%Z
...
rewrite Rminus_Int_part1. {
  rewrite Int_part_small; [ | lra ].
  rewrite <- INR_IPR.
  rewrite Int_part_INR.
  now rewrite positive_nat_Z.
}
rewrite <- INR_IPR, frac_part_INR; apply base_fp.
Qed.

Theorem frac_part_IZR : ∀ z, frac_part (IZR z) = 0.
Proof.
intros.
unfold frac_part.
rewrite Int_part_IZR; lra.
Qed.

Theorem Rpow_div_sub : ∀ x i j,
  x ≠ 0
  → (j ≤ i)%nat
  → x ^ i / x ^ j = x ^ (i - j).
Proof.
intros * Hx Hij.
unfold Rdiv.
replace i with ((i - j) + j)%nat at 1 by now rewrite Nat.sub_add.
now symmetry; apply pow_RN_plus.
Qed.

Theorem frac_part_interv : ∀ x, 0 ≤ frac_part x < 1.
Proof.
intros.
unfold frac_part.
specialize (base_Int_part x); intros Hx; lra.
Qed.

Theorem Int_part_interv : ∀ z x, IZR z ≤ x < IZR (z + 1) → Int_part x = z.
Proof.
intros * (Hzx, Hxz).
rewrite plus_IZR in Hxz; simpl in Hxz.
assert (H : 0 ≤ x - IZR z < 1) by lra.
apply Int_part_small in H.
rewrite Rminus_Int_part1 in H. {
  rewrite Int_part_IZR in H.
  now apply -> Z.sub_move_0_r in H.
} {
  rewrite frac_part_IZR.
  apply Rle_ge, frac_part_interv.
}
Qed.

Theorem Rabs_or : ∀ x y, Rabs x = y → x = y ∨ x = - y.
Proof.
intros * Hxy; subst y.
unfold Rabs.
destruct (Rcase_abs x) as [H₁| H₁]; [ right | now left ].
symmetry; apply Ropp_involutive.
Qed.

Theorem Rabs_eq_0 : ∀ x, Rabs x = 0 → x = 0.
Proof.
intros * Hx.
unfold Rabs in Hx.
destruct (Rcase_abs x); [ | easy ].
apply Ropp_eq_0_compat in Hx.
now rewrite Ropp_involutive in Hx.
Qed.

Theorem Rabs_lt : ∀ x y, Rabs x < y ↔ - y < x < y.
Proof.
intros; split. {
  intros Hxy.
  unfold Rabs in Hxy.
  destruct (Rcase_abs x); lra.
} {
  intros (Hyx, Hxy).
  unfold Rabs.
  destruct (Rcase_abs x); [ lra | easy ].
}
Qed.

Theorem Rabs_le : ∀ x y, Rabs x ≤ y ↔ - y ≤ x ≤ y.
Proof.
intros; split. {
  intros Hxy.
  unfold Rabs in Hxy.
  destruct (Rcase_abs x); lra.
} {
  intros (Hyx, Hxy).
  unfold Rabs.
  destruct (Rcase_abs x); [ lra | easy ].
}
Qed.

Theorem Rabs_sqr : ∀ x, Rabs (x²) = x².
Proof.
intros.
unfold Rabs.
destruct (Rcase_abs x²) as [Hx| Hx]; [ | easy ].
exfalso; apply Rlt_not_le in Hx; apply Hx, Rle_0_sqr.
Qed.

Theorem Rabs_sqrt : ∀ x, Rabs (√ x) = √ x.
Proof.
intros.
unfold Rabs.
destruct (Rcase_abs (√ x)) as [Hx| Hx]; [ exfalso | easy ].
apply Rlt_not_le in Hx; apply Hx, sqrt_pos.
Qed.

Theorem Rmult_minus_distr_r : ∀ r1 r2 r3,
  (r1 - r2) * r3 = r1 * r3 - r2 * r3.
Proof.
intros.
unfold Rminus.
rewrite Rmult_plus_distr_r; lra.
Qed.

Theorem Rminus_plus : ∀ x y, x - y + y = x.
Proof. intros; lra. Qed.

Theorem Rdiv_div : ∀ x y z, x / y / z = x / (y * z).
Proof.
intros.
unfold Rdiv.
rewrite Rinv_mult; lra.
Qed.

Theorem Rmult_div_r : ∀ x y, y ≠ 0 → y * (x / y) = x.
Proof.
intros * Hy.
unfold Rdiv; rewrite Rmult_comm, Rmult_assoc.
rewrite Rinv_l; [ lra | easy ].
Qed.

Theorem Rinv_div : ∀ x, / x = 1 / x.
Proof. intros; lra. Qed.

Theorem nonneg_plus_sqr : ∀ x y, 0 ≤ x² + y².
Proof.
intros.
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Definition Rsignp x := if Rle_dec 0 x then 1 else -1.
Definition Rsign x := if Req_dec x 0 then 0 else Rsignp x.

Theorem Rsignp_of_pos : ∀ x, 0 ≤ x → Rsignp x = 1.
Proof.
intros * Hx.
unfold Rsignp.
destruct (Rle_dec 0 x); [ easy | lra ].
Qed.

Theorem Rsignp_of_neg : ∀ x, x < 0 → Rsignp x = -1.
Proof.
intros * Hx.
unfold Rsignp.
destruct (Rle_dec 0 x); [ lra | easy ].
Qed.

Theorem Rsign_of_pos : ∀ x, 0 < x → Rsign x = 1.
Proof.
intros * Hx.
unfold Rsign, Rsignp.
destruct (Req_dec x 0); [ lra | ].
destruct (Rle_dec 0 x); [ easy | lra ].
Qed.

Theorem Rsign_of_neg : ∀ x, x < 0 → Rsign x = -1.
Proof.
intros * Hx.
unfold Rsign, Rsignp.
destruct (Req_dec x 0); [ lra | ].
destruct (Rle_dec 0 x); [ lra | easy ].
Qed.

Theorem Rsign_mul_distr : ∀ x y, Rsign (x * y) = Rsign x * Rsign y.
Proof.
intros.
unfold Rsign, Rsignp.
destruct (Req_dec (x * y) 0) as [Hxyz| Hxyz]. {
  destruct (Req_dec x 0) as [Hx| Hx]; [ lra | ].
  destruct (Req_dec y 0) as [Hy| Hy]; [ lra | ].
  apply Rmult_integral in Hxyz; lra.
}
destruct (Req_dec x 0) as [Hxz| Hxz]; [ rewrite Hxz in Hxyz; lra | ].
destruct (Req_dec y 0) as [Hyz| Hyz]; [ rewrite Hyz in Hxyz; lra | ].
destruct (Rle_dec 0 (x * y)) as [Hxy| Hxy]. {
  destruct (Rle_dec 0 x) as [Hx| Hx]. {
    destruct (Rle_dec 0 y) as [Hy| Hy]; [ lra | exfalso ].
    apply Hy; clear Hy.
    apply Rmult_le_reg_l with (r := x); [ lra | ].
    now rewrite Rmult_0_r.
  }
  destruct (Rle_dec 0 y) as [Hy| Hy]; [ exfalso | lra ].
  apply Hx; clear Hx.
  apply Rmult_le_reg_r with (r := y); [ lra | ].
  now rewrite Rmult_0_l.
}
destruct (Rle_dec 0 x) as [Hx| Hx]. {
  destruct (Rle_dec 0 y) as [Hy| Hy]; [ exfalso | lra ].
  apply Hxy; clear Hxy.
  now apply Rmult_le_pos.
} {
  destruct (Rle_dec 0 y) as [Hy| Hy]; [ lra | exfalso ].
  apply Hxy; clear Hxy.
  rewrite <- Rmult_opp_opp.
  apply Rmult_le_pos; lra.
}
Qed.

Theorem Rneq_le_lt : ∀ x y, x ≠ y → x ≤ y → x < y.
Proof.
intros * Hnxy Hxy.
apply Rnot_le_lt; intros H.
now apply Rle_antisym in H.
Qed.

Theorem sqrt_diff_sqr_eq_0 : ∀ x y,
  0 ≤ x ≤ y
  → √ (y² - x²) = 0
  → x = y.
Proof.
intros * Hxy Hyx.
apply sqrt_eq_0 in Hyx; [ apply Rsqr_inj; lra | ].
enough (x² ≤ y²) by lra.
apply Rsqr_incr_1; lra.
Qed.

Definition Rediv_mod x y :=
  let k :=
    match Rcase_abs y with
    | left _ => (- Int_part (x / - y))%Z
    | right _ => Int_part (x / y)
    end
  in
  (k, x - IZR k * y).

Definition Rediv x y := fst (Rediv_mod x y).
Definition Rmod x y := snd (Rediv_mod x y).

Notation "x '//' y" := (Rediv x y) (at level 40).
Notation "x 'rmod' y" := (Rmod x y) (at level 40).

Theorem Rmod_interv : ∀ x y, 0 < y → 0 ≤ x rmod y < y.
Proof.
intros * Hy.
unfold Rmod, Rediv_mod, snd.
destruct (Rcase_abs y) as [Hya| Hya]; [ lra | ].
split. {
  apply Rmult_le_reg_r with (r := / y); [ now apply Rinv_0_lt_compat | ].
  rewrite Rmult_0_l, fold_Rdiv, Rdiv_minus_distr, Rmult_div.
  rewrite Rmult_div_same; [ | lra ].
  specialize (base_Int_part (x / y)); lra.
} {
  apply Rmult_lt_reg_r with (r := / y); [ now apply Rinv_0_lt_compat | ].
  rewrite fold_Rdiv, fold_Rdiv, Rdiv_minus_distr, Rmult_div.
  rewrite Rmult_div_same; [ | lra ].
  rewrite Rdiv_same; [ | lra ].
  specialize (base_Int_part (x / y)); lra.
}
Qed.

Theorem Rmod_from_ediv : ∀ x y, x rmod y = x - IZR (x // y) * y.
Proof.
intros.
unfold Rmod, Rediv, fst, snd.
remember (Rediv_mod x y) as rdm eqn:Hrdm.
symmetry in Hrdm.
destruct rdm as (q, r).
unfold Rediv_mod in Hrdm.
destruct (Rcase_abs y) as [Hy| Hy]. {
  remember Z.sub as f.
  injection Hrdm; clear Hrdm; intros Hr Hq; subst f.
  now rewrite Hq in Hr.
} {
  remember Z.sub as f.
  injection Hrdm; clear Hrdm; intros Hr Hq; subst f.
  now rewrite Hq in Hr.
}
Qed.

Theorem Int_part_neg : ∀ x,
  Int_part (- x) =
    (- Int_part x - if Req_dec x (IZR (Int_part x)) then 0 else 1)%Z.
Proof.
intros.
destruct (Req_dec x (IZR (Int_part x))) as [Hx| Hx]. {
  rewrite Hx at 1.
  now rewrite <- opp_IZR, Int_part_IZR, Z.sub_0_r.
}
apply Int_part_interv.
rewrite Z.sub_simpl_r, opp_IZR.
unfold Z.sub; rewrite <- Z.opp_add_distr.
rewrite opp_IZR, plus_IZR; simpl (IZR 1).
specialize (base_Int_part x) as H; lra.
Qed.

Theorem Rediv_add_1 : ∀ x y, y ≠ 0 → (x + y) // y = (x // y + 1)%Z.
Proof.
intros * Hyz.
unfold Rediv, Rediv_mod, fst.
destruct (Rcase_abs y) as [Hy| Hy]. {
  unfold Rdiv.
  rewrite Rinv_opp.
  rewrite <- Ropp_mult_distr_r.
  rewrite Rmult_plus_distr_r.
  rewrite Rinv_r; [ | lra ].
  rewrite Ropp_plus_distr.
  rewrite fold_Rminus.
  rewrite <- Ropp_mult_distr_r.
  ring_simplify.
  rewrite Rminus_Int_part1. {
    rewrite Z.opp_sub_distr.
    replace 1 with (IZR 1) by lra.
    now rewrite Int_part_IZR.
  } {
    replace 1 with (IZR 1) by lra.
    rewrite frac_part_IZR.
    specialize (frac_part_interv (- (x * / y))) as (Hn, Hp); lra.
  }
}
rewrite Rdiv_plus_distr.
rewrite Rdiv_same; [ | easy ].
rewrite plus_Int_part2. {
  replace 1 with (IZR 1) by lra.
  now rewrite Int_part_IZR.
} {
  replace 1 with (IZR 1) at 1 by lra.
  rewrite frac_part_IZR, Rplus_0_r.
  apply frac_part_interv.
}
Qed.

Theorem Rediv_opp_r : ∀ x y, y ≠ 0 → x // - y = (- (x // y))%Z.
Proof.
intros * Hyz.
unfold "//", fst, Rediv_mod.
destruct (Rcase_abs (- y)) as [Hy| Hy]. {
  destruct (Rcase_abs y); [ lra | now rewrite Ropp_involutive ].
} {
  destruct (Rcase_abs y); [ now rewrite Z.opp_involutive | lra ].
}
Qed.

Theorem Rediv_add_nat : ∀ x y n,
  y ≠ 0
  → (x + INR n * y) // y = (x // y + Z.of_nat n)%Z.
Proof.
intros * Hyz.
induction n; [ now simpl; rewrite Rmult_0_l, Rplus_0_r, Z.add_0_r | ].
rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, <- Rplus_assoc.
rewrite Rediv_add_1; [ | easy ].
rewrite IHn; lia.
Qed.

Theorem Rediv_add_Z : ∀ x y a,
  y ≠ 0
  → (x + IZR a * y) // y = (x // y + a)%Z.
Proof.
intros * Hyz.
destruct (Z_le_dec 0 a) as [Ha| Ha]. {
  apply IZN in Ha.
  destruct Ha as (n, Hn); subst a.
  rewrite <- INR_IZR_INZ.
  now apply Rediv_add_nat.
}
remember (- a)%Z as b eqn:Hb.
assert (a = (- b)%Z) by lia.
subst a; clear Hb.
rename b into a.
assert (Hb : (0 < a)%Z) by lia.
clear Ha; rename Hb into Ha.
apply Z.lt_le_incl in Ha.
apply IZN in Ha.
destruct Ha as (n, Hn); subst a.
rewrite opp_IZR.
rewrite <- INR_IZR_INZ.
rewrite <- Ropp_mult_distr_l, Ropp_mult_distr_r.
symmetry; rewrite <- Z.opp_involutive; symmetry.
rewrite <- Rediv_opp_r; [ | easy ].
rewrite Rediv_add_nat; [ | lra ].
rewrite Z.opp_add_distr.
rewrite Rediv_opp_r; [ | easy ].
now rewrite Z.opp_involutive.
Qed.

Theorem Rmod_add_Z : ∀ x y a,
  y ≠ 0
  → (x + IZR a * y) rmod y = x rmod y.
Proof.
intros * Hy.
rewrite Rmod_from_ediv.
rewrite Rediv_add_Z; [ | easy ].
rewrite plus_IZR.
rewrite Rmult_plus_distr_r.
remember (IZR a * y) as u.
remember (IZR (x // y) * y) as v.
now replace (x + u - (v + u)) with (x - v) by lra; subst u v.
Qed.

Theorem Int_part_0 : Int_part 0 = 0%Z.
Proof. rewrite Int_part_small; [ easy | lra ]. Qed.

Theorem Rmod_0_l : ∀ x, 0 rmod x = 0.
Proof.
intros x.
unfold Rmod, snd, Rediv_mod.
do 2 rewrite Rdiv_0_l.
rewrite Int_part_0, Z.opp_0.
destruct (Rcase_abs x); lra.
Qed.

Theorem Rmod_mul_same : ∀ x a, (IZR a * x) rmod x = 0.
Proof.
intros.
destruct (Req_dec x 0) as [Hx| Hx]. {
  rewrite Hx, Rmult_0_r; apply Rmod_0_l.
}
specialize (Rmod_add_Z 0 x a Hx) as H.
rewrite Rplus_0_l in H; rewrite H.
apply Rmod_0_l.
Qed.

Theorem Rmod_small : ∀ x y, 0 ≤ x < y → x rmod y = x.
Proof.
intros * (Hx, Hxy).
unfold Rmod, snd, Rediv_mod.
destruct (Rcase_abs y) as [Hyn| Hyp]; [ lra | ].
assert (H : 0 ≤ x / y < 1). {
  split. {
    apply Rmult_le_reg_r with (r := y); [ lra | ].
    rewrite Rmult_0_l, Rmult_div_same; [ easy | lra ].
  } {
    apply Rmult_lt_reg_r with (r := y); [ lra | ].
    rewrite Rmult_1_l, Rmult_div_same; [ easy | lra ].
  }
}
apply Int_part_small in H.
rewrite H; simpl.
now rewrite Rmult_0_l, Rminus_0_r.
Qed.

Theorem Rediv_mul_r : ∀ x y z,
  x // (y * z) =
    (Int_part (x / (y * z)) +
       if Rcase_abs (y * z) then
         if Req_dec (x / (y * z)) (IZR (Int_part (x / (y * z)))) then 0
         else 1
       else 0)%Z.
Proof.
intros.
unfold "//", fst, Rediv_mod.
destruct (Rcase_abs (y * z)) as [Hyz| Hyz]; [ | now rewrite Z.add_0_r ].
rewrite Ropp_div_r.
rewrite Int_part_neg.
rewrite Z.opp_sub_distr.
rewrite Z.opp_involutive.
destruct (Req_dec (x / (y * z)) (IZR (Int_part (x / (y * z))))); [ | easy ].
now rewrite Z.add_0_r.
Qed.

Theorem frac_part_double : ∀ x,
  frac_part (2 * x) =
    2 * frac_part x - if Rlt_dec (frac_part x) (1 / 2) then 0 else 1.
Proof.
intros.
do 2 rewrite <- Rplus_diag.
destruct (Rlt_dec (frac_part x) (1 / 2)) as [Hx| Hx]. {
  rewrite Rminus_0_r; apply plus_frac_part2; lra.
}
apply plus_frac_part1; lra.
Qed.

Theorem Int_part_double : ∀ x,
  Int_part (2 * x) =
    (2 * Int_part x + if Rlt_dec (frac_part x) (1 / 2) then 0 else 1)%Z.
Proof.
intros.
rewrite <- Rplus_diag.
destruct (Rlt_dec (frac_part x) (1 / 2)) as [Hx| Hx]. {
  rewrite plus_Int_part2; [ lia | lra ].
} {
  rewrite plus_Int_part1; [ lia | lra ].
}
Qed.

Theorem pow_1_abs_nat_odd : ∀ n, (-1) ^ Z.abs_nat (2 * n + 1) = -1.
Proof.
intros n.
destruct n as [| n| n]. {
  rewrite Z.mul_0_r, Z.add_0_l.
  simpl (Z.abs_nat _); unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).
  now rewrite pow_1.
} {
  rewrite Zabs2Nat.inj_add; [ | lia | lia ].
  rewrite Zabs2Nat.inj_mul.
  simpl (Z.abs_nat _); unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).
  now rewrite Nat.add_1_r, pow_1_odd.
} {
  replace (Z.neg n) with (- Z.pos n)%Z by apply Pos2Z.opp_pos.
  rewrite <- Zopp_mult_distr_r, <- Z.opp_sub_distr.
  rewrite <- Zabs_N_nat, Zabs2N.inj_opp, Zabs_N_nat.
  rewrite Zabs2Nat.inj_sub; [ | lia ].
  simpl (Z.abs_nat 1); unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).
  rewrite <- Rpow_div_sub; [ | lra | lia ].
  rewrite pow_1, Zabs2Nat.inj_mul.
  simpl (Z.abs_nat 2); unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).
  rewrite pow_1_even; lra.
}
Qed.

Theorem Rdiv_mod : ∀ x y, y ≠ 0 → x = y * IZR (x // y) + x rmod y.
Proof.
intros x y Hy.
rewrite Rmod_from_ediv.
lra.
Qed.
