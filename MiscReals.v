(* Banach-Tarski paradox. *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 List Relations Wf_nat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Ring.
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

Definition Hos := rngl_has_opp_has_opp_or_psub Hop.
Definition Heo := rngl_has_eq_dec_or_is_ordered_r Hor.
Definition Hiq := rngl_has_inv_has_inv_or_pdiv Hiv.
Definition Hc1 := eq_ind_r (λ n, n ≠ 1) (Nat.neq_succ_diag_r 0) Hch.
Definition Hi1 := rngl_has_inv_and_1_has_inv_and_1_or_pdiv Hon Hiv.
Definition Hii := rngl_int_dom_or_inv_1_quo Hiv Hon.
Definition Hio := rngl_integral_or_inv_1_pdiv_eq_dec_order Hon Hiv Hor.

Tactic Notation "pauto" := progress auto.
Hint Resolve rngl_le_refl : core.

Add Ring rngl_ring : (rngl_ring_theory Hic Hop Hon).

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

Definition Rle_dec := rngl_le_dec Hor.
Definition Rlt_dec := rngl_lt_dec Hor.
Definition Req_dec := rngl_eq_dec Heo.

Theorem Rcase_abs : ∀ a, {(a < 0)%L} + {(0 ≤ a)%L}.
Proof.
intros.
destruct (rngl_lt_dec Hor a 0) as [Haz| Haz]; [ now left | right ].
now apply (rngl_nlt_ge_iff Hor).
Qed.

Arguments Rle_dec (a b)%_L.
Arguments Rlt_dec (a b)%_L.
Arguments Req_dec (a b)%_L.
Arguments Rcase_abs a%_L.

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

Definition rngl_of_pos a := rngl_of_nat (Pos.to_nat a).

Definition rngl_of_Z a :=
  match a with
  | 0%Z => 0%L
  | Z.pos n => rngl_of_pos n
  | Z.neg n => (- rngl_of_pos n)%L
  end.

Theorem rngl_of_pos_add :
  ∀ a b, rngl_of_pos (a + b) = (rngl_of_pos a + rngl_of_pos b)%L.
Proof.
intros.
progress unfold rngl_of_pos.
rewrite Pos2Nat.inj_add.
apply rngl_of_nat_add.
Qed.

Theorem rngl_of_Z_of_nat : ∀ a, rngl_of_Z (Z.of_nat a) = rngl_of_nat a.
Proof.
intros.
progress unfold rngl_of_Z.
remember (Z.of_nat a) as za eqn:Hza.
symmetry in Hza.
destruct za as [| n| n]; [ now destruct a | | ]. {
  progress unfold rngl_of_pos.
  f_equal.
  apply Nat2Z.inj; rewrite Hza.
  apply positive_nat_Z.
}
specialize (Nat2Z.is_nonneg a) as H1.
rewrite Hza in H1.
exfalso; apply Z.nlt_ge in H1.
now apply H1.
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

Theorem rngl_of_pos_pred :
  ∀ a,
  (1 < a)%positive
  → rngl_of_pos (Pos.pred a) = (rngl_of_pos a - 1)%L.
Proof.
intros * H1a.
progress unfold rngl_of_pos.
rewrite Pos2Nat.inj_pred; [ | easy ].
rewrite <- Nat.sub_1_r.
rewrite (rngl_of_nat_sub Hos). {
  progress f_equal.
  apply rngl_of_nat_1.
}
apply Pos2Nat.inj_lt in H1a.
now apply Nat.lt_le_incl.
Qed.

Theorem rngl_of_pos_xO : ∀ a, rngl_of_pos a~0 = (2 * rngl_of_pos a)%L.
Proof.
intros.
progress unfold rngl_of_pos.
rewrite Pos2Nat.inj_xO.
rewrite (rngl_of_nat_mul Hon Hos).
progress f_equal.
apply rngl_of_nat_2.
Qed.

Theorem rngl_of_pos_xI : ∀ a, rngl_of_pos a~1 = (2 * rngl_of_pos a + 1)%L.
Proof.
intros.
progress unfold rngl_of_pos.
rewrite Pos2Nat.inj_xI.
rewrite rngl_of_nat_succ.
rewrite (rngl_of_nat_mul Hon Hos).
rewrite rngl_add_comm.
progress f_equal.
progress f_equal.
apply rngl_of_nat_2.
Qed.

Theorem rngl_of_nat_Pos_to_nat :
  ∀ a, rngl_of_pos a = rngl_of_nat (Pos.to_nat a).
Proof.
intros.
destruct a as [a| a| ]; cbn. {
  rewrite rngl_of_pos_xI.
  rewrite Pos2Nat.inj_xI.
  rewrite rngl_of_nat_succ.
  rewrite rngl_add_comm.
  progress f_equal.
  rewrite (rngl_of_nat_mul Hon Hos).
  now rewrite rngl_of_nat_2.
} {
  rewrite rngl_of_pos_xO.
  rewrite Pos2Nat.inj_xO.
  rewrite (rngl_of_nat_mul Hon Hos).
  now rewrite rngl_of_nat_2.
} {
  rewrite Pos2Nat.inj_1.
  rewrite rngl_of_nat_1.
  progress unfold rngl_of_pos.
  rewrite Pos2Nat.inj_1.
  apply rngl_of_nat_1.
}
Qed.

Theorem rngl_of_pos_1 : rngl_of_pos 1 = 1%L.
Proof.
progress unfold rngl_of_pos.
rewrite Pos2Nat.inj_1.
apply rngl_of_nat_1.
Qed.

Theorem rngl_of_pos_2 : rngl_of_pos 2 = 2%L.
Proof.
progress unfold rngl_of_pos.
rewrite Pos2Nat.inj_xO.
rewrite Pos2Nat.inj_1.
rewrite Nat.mul_1_r.
apply rngl_of_nat_2.
Qed.

Theorem rngl_of_Z_succ : ∀ a, rngl_of_Z (Z.succ a) = (1 + rngl_of_Z a)%L.
Proof.
intros.
symmetry.
destruct a as [| a| a]; cbn. {
  progress unfold rngl_of_pos.
  now rewrite Pos2Nat.inj_1.
} {
  rewrite rngl_of_pos_add.
  rewrite rngl_of_pos_1.
  apply rngl_add_comm.
} {
  rewrite (rngl_add_opp_r Hop).
  progress unfold rngl_of_pos.
  destruct a as [a| a| ]; cbn. {
    progress unfold rngl_of_pos.
    rewrite Pos2Nat.inj_xI.
    rewrite Pos2Nat.inj_xO.
    rewrite rngl_of_nat_succ.
    rewrite (rngl_sub_add_distr Hos).
    rewrite (rngl_sub_diag Hos).
    now rewrite (rngl_sub_0_l Hop).
  } {
    rewrite Pos.pred_double_spec.
    rewrite rngl_of_pos_pred; [ symmetry | easy ].
    apply (rngl_opp_sub_distr Hop).
  } {
    rewrite Pos2Nat.inj_1.
    rewrite rngl_of_nat_1.
    apply (rngl_sub_diag Hos).
  }
}
Qed.

Theorem rngl_of_Z_opp : ∀ a, rngl_of_Z (- a) = (- rngl_of_Z a)%L.
Proof.
intros.
symmetry.
destruct a as [| a| a]; cbn; [ | easy | ]. {
  apply (rngl_opp_0 Hop).
} {
  apply (rngl_opp_involutive Hop).
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

Theorem rngl_of_Z_pred : ∀ a, rngl_of_Z (Z.pred a) = (rngl_of_Z a - 1)%L.
Proof.
intros.
destruct a as [| a| a]; cbn. {
  rewrite rngl_of_pos_1.
  symmetry; apply (rngl_sub_0_l Hop).
} {
  progress unfold rngl_of_pos.
  destruct a as [a| a| ]; cbn. {
    progress unfold rngl_of_pos.
    rewrite Pos2Nat.inj_xO.
    rewrite Pos2Nat.inj_xI.
    rewrite (rngl_of_nat_succ).
    symmetry; rewrite rngl_add_comm.
    apply (rngl_add_sub Hos).
  } {
    rewrite Pos.pred_double_spec.
    now apply rngl_of_pos_pred.
  } {
    rewrite Pos2Nat.inj_1, rngl_of_nat_1.
    symmetry; apply (rngl_sub_diag Hos).
  }
} {
  rewrite rngl_of_pos_add.
  rewrite rngl_of_pos_1.
  apply (rngl_opp_add_distr Hop).
}
Qed.

Theorem rngl_of_pos_sub :
  ∀ a b,
  (b < a)%positive
  → rngl_of_pos (a - b) = (rngl_of_pos a - rngl_of_pos b)%L.
Proof.
intros * Hba.
progress unfold rngl_of_pos.
rewrite Pos2Nat.inj_sub; [ | easy ].
apply (rngl_of_nat_sub Hos).
apply Pos2Nat.inj_le.
now apply Pos.lt_le_incl.
Qed.

Theorem Pos2Nat_ge_1 : ∀ a, 1 ≤ Pos.to_nat a.
Proof.
intros.
induction a as [a| a| ]; [ | | easy ]. {
  rewrite Pos2Nat.inj_xI.
  apply -> Nat.succ_le_mono.
  apply Nat.le_0_l.
} {
  rewrite Pos2Nat.inj_xO.
  cbn; rewrite Nat.add_0_r.
  transitivity (Pos.to_nat a); [ easy | ].
  apply Nat.le_add_l.
}
Qed.

Theorem Pos_le_neq : ∀ a b, (a < b ↔ a <= b ∧ a ≠ b)%positive.
Proof.
intros.
split; intros Hab. {
  split; [ now apply Pos.lt_le_incl | ].
  intros H; subst.
  now apply Pos.lt_irrefl in Hab.
}
destruct Hab as (H1, H2).
destruct (Pos_dec a b) as [[Hab| Hab]| Hab]; [ easy | | easy ].
now apply Pos.lt_nle in Hab.
Qed.

Theorem Pos_le_add_l : ∀ a b, (a <= b + a)%positive.
Proof.
intros.
apply Pos.lt_le_incl.
rewrite Pos.add_comm.
apply Pos.lt_add_r.
Qed.

Theorem rngl_of_Z_add_1_l : ∀ a, rngl_of_Z (1 + a) = (1 + rngl_of_Z a)%L.
Proof.
intros.
destruct a as [| a| a]; cbn; [ easy | | ]. {
  destruct a as [a| a| ]; cbn; [ | easy | easy ].
  progress unfold rngl_of_pos.
  rewrite Pos2Nat.inj_xO, Pos2Nat.inj_xI.
  rewrite Pos2Nat.inj_succ.
  rewrite rngl_of_nat_succ.
  do 2 rewrite (rngl_of_nat_mul Hon Hos).
  rewrite (rngl_of_nat_succ (Pos.to_nat _)).
  rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
  rewrite rngl_add_assoc.
  progress f_equal; cbn.
  now rewrite rngl_add_0_r.
} {
  progress unfold rngl_of_pos.
  rewrite (rngl_add_opp_r Hop).
  destruct a as [a| a| ]. {
    cbn.
    progress unfold rngl_of_pos; cbn.
    rewrite Pos2Nat.inj_xO, Pos2Nat.inj_xI.
    rewrite rngl_of_nat_succ.
    rewrite (rngl_sub_add_distr Hos).
    rewrite (rngl_sub_diag Hos); symmetry.
    apply (rngl_sub_0_l Hop).
  } {
    cbn.
    progress unfold rngl_of_pos; cbn.
    rewrite Pos.pred_double_spec.
    rewrite Pos.pred_sub.
    rewrite Pos2Nat.inj_sub; [ | easy ].
    rewrite Pos2Nat.inj_xO, Pos2Nat.inj_1.
    rewrite (rngl_of_nat_sub Hos). 2: {
      transitivity (Pos.to_nat a).
      apply Pos2Nat_ge_1.
      cbn; rewrite Nat.add_0_r.
      apply Nat.le_add_l.
    }
    rewrite rngl_of_nat_1.
    apply (rngl_opp_sub_distr Hop).
  } {
    cbn.
    rewrite Pos2Nat.inj_1.
    rewrite rngl_of_nat_1; symmetry.
    apply (rngl_sub_diag Hos).
  }
}
Qed.

Theorem rngl_of_Z_add_1_r : ∀ a, rngl_of_Z (a + 1) = (rngl_of_Z a + 1)%L.
Proof.
intros.
rewrite Z.add_comm, rngl_add_comm.
apply rngl_of_Z_add_1_l.
Qed.

Theorem rngl_of_pos_mul :
  ∀ a b, rngl_of_pos (a * b) = (rngl_of_pos a * rngl_of_pos b)%L.
Proof.
intros.
revert b.
induction a as [a| a| ]; intros; cbn. {
  rewrite rngl_of_pos_add.
  rewrite rngl_of_pos_xO, rngl_of_pos_xI.
  rewrite IHa.
  rewrite (rngl_mul_add_distr_r _ _ (rngl_of_pos _)), (rngl_mul_1_l Hon).
  rewrite rngl_mul_assoc.
  apply rngl_add_comm.
} {
  do 2 rewrite rngl_of_pos_xO.
  rewrite <- rngl_mul_assoc.
  progress f_equal.
  apply IHa.
} {
  rewrite rngl_of_pos_1.
  symmetry; apply (rngl_mul_1_l Hon).
}
Qed.

Theorem rngl_of_Z_mul :
  ∀ a b, rngl_of_Z (a * b) = (rngl_of_Z a * rngl_of_Z b)%L.
Proof.
intros.
destruct a as [| a| a]; cbn. {
  symmetry; apply (rngl_mul_0_l Hos).
} {
  destruct b as [| b| b]; cbn. {
    symmetry; apply (rngl_mul_0_r Hos).
  } {
    apply rngl_of_pos_mul.
  } {
    rewrite (rngl_mul_opp_r Hop).
    progress f_equal.
    apply rngl_of_pos_mul.
  }
} {
  destruct b as [| b| b]; cbn. {
    symmetry; apply (rngl_mul_0_r Hos).
  } {
    rewrite (rngl_mul_opp_l Hop).
    progress f_equal.
    apply rngl_of_pos_mul.
  } {
    rewrite (rngl_mul_opp_opp Hop).
    apply rngl_of_pos_mul.
  }
}
Qed.

Theorem rngl_of_Z_2 : rngl_of_Z 2 = 2%L.
Proof.
cbn; progress unfold rngl_of_pos.
progress unfold Pos.to_nat; cbn.
now rewrite rngl_add_0_r.
Qed.

Theorem rngl_of_Z_sub_1 : ∀ a, rngl_of_Z (a - 1) = (rngl_of_Z a - 1)%L.
Proof.
intros.
destruct a as [| a| a]. {
  cbn.
  rewrite rngl_of_pos_1; symmetry.
  apply (rngl_sub_0_l Hop).
} {
  destruct a as [a| a| ]; cbn. {
    rewrite rngl_of_pos_xO, rngl_of_pos_xI; symmetry.
    apply (rngl_add_sub Hos).
  } {
    rewrite rngl_of_pos_xO.
    rewrite Pos.pred_double_spec.
    rewrite rngl_of_pos_pred; [ | easy ].
    progress f_equal.
    apply rngl_of_pos_xO.
  } {
    symmetry.
    rewrite rngl_of_pos_1.
    apply (rngl_sub_diag Hos).
  }
} {
  cbn.
  rewrite <- (rngl_opp_add_distr Hop).
  progress f_equal.
  rewrite rngl_of_pos_add.
  now rewrite rngl_of_pos_1.
}
Qed.

Theorem rngl_of_Z_add_pos_neg :
  ∀ a b,
  rngl_of_Z (Z.pos a + Z.neg b) =
    (rngl_of_Z (Z.pos a) + rngl_of_Z (Z.neg b))%L.
Proof.
intros.
cbn.
rewrite <- Pos2Z.add_pos_neg.
rewrite (rngl_add_opp_r Hop).
revert b.
induction a as [a| a| ]; cbn; intros. {
  destruct b as [b| b| ]. {
    cbn.
    rewrite Z.double_spec.
    do 2 rewrite rngl_of_pos_xI.
    rewrite (rngl_sub_add_distr Hos).
    rewrite (rngl_sub_sub_swap Hop).
    rewrite (rngl_add_sub Hos).
    rewrite <- (rngl_mul_sub_distr_l Hop).
    destruct (Pos_dec a b) as [[Hab| Hab]| Hab]. {
      rewrite Z.pos_sub_lt; [ cbn | easy ].
      rewrite rngl_of_pos_xO.
      rewrite rngl_of_pos_sub; [ | easy ].
      rewrite <- (rngl_mul_opp_r Hop).
      progress f_equal.
      apply (rngl_opp_sub_distr Hop).
    } {
      rewrite Z.pos_sub_gt; [ cbn | easy ].
      rewrite rngl_of_pos_xO.
      progress f_equal.
      now apply rngl_of_pos_sub.
    } {
      subst.
      rewrite Z.pos_sub_diag, Z.mul_0_r; symmetry.
      rewrite (rngl_sub_diag Hos).
      apply (rngl_mul_0_r Hos).
    }
  } {
    cbn.
    rewrite Z.succ_double_spec, Z.add_1_r.
    rewrite rngl_of_Z_succ.
    rewrite rngl_of_pos_xI, rngl_of_pos_xO.
    rewrite (rngl_add_comm _ 1).
    rewrite <- (rngl_add_sub_assoc Hop).
    progress f_equal.
    rewrite rngl_of_Z_mul.
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite rngl_of_Z_2.
    progress f_equal.
    apply IHa.
  } {
    cbn.
    rewrite rngl_of_pos_xO, rngl_of_pos_xI.
    rewrite rngl_of_pos_1; symmetry.
    apply (rngl_add_sub Hos).
  }
} {
  destruct b as [b| b| ]; cbn. {
    rewrite Z.pred_double_spec.
    rewrite rngl_of_pos_xO, rngl_of_pos_xI.
    rewrite (rngl_sub_add_distr Hos).
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite rngl_of_Z_sub_1.
    progress f_equal.
    rewrite rngl_of_Z_mul, rngl_of_Z_2.
    progress f_equal.
    apply IHa.
  } {
    do 2 rewrite rngl_of_pos_xO.
    rewrite <- (rngl_mul_sub_distr_l Hop).
    rewrite Z.double_spec.
    rewrite rngl_of_Z_mul, rngl_of_Z_2.
    progress f_equal.
    apply IHa.
  } {
    rewrite Pos.pred_double_spec.
    rewrite rngl_of_pos_xO, rngl_of_pos_1.
    rewrite rngl_of_pos_pred; [ | easy ].
    progress f_equal.
    apply rngl_of_pos_xO.
  }
} {
  rewrite rngl_of_pos_1.
  rewrite <- Pos2Z.add_neg_pos.
  rewrite Z.add_comm.
  rewrite rngl_of_Z_add_1_l; cbn.
  apply (rngl_add_opp_r Hop).
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
    apply rngl_of_Z_add_pos_neg.
  }
} {
  destruct b as [| b| b]. {
    symmetry; apply rngl_add_0_r.
  } {
    rewrite Z.add_comm, rngl_add_comm.
    apply rngl_of_Z_add_pos_neg.
  } {
    cbn.
    rewrite (rngl_add_opp_r Hop).
    rewrite <- (rngl_opp_add_distr Hop).
    progress f_equal.
    apply rngl_of_pos_add.
  }
}
Qed.

Theorem z_int_part : ∀ a, ∃ₜ n, (rngl_of_Z n ≤ a < rngl_of_Z (n + 1))%L.
Proof.
intros.
specialize (int_part Hon Hop Hiq Hc1 Hor Har a) as (n, Hn).
destruct (rngl_le_dec Hor 0 a)%L as [Hza| Hza]. {
  rewrite (rngl_abs_nonneg_eq Hop Hor) in Hn; [ | easy ].
  exists (Z.of_nat n).
  rewrite rngl_of_Z_of_nat.
  rewrite Z.add_1_r.
  rewrite rngl_of_Z_succ.
  rewrite rngl_of_Z_of_nat.
  rewrite rngl_of_nat_add, rngl_add_comm in Hn.
  now rewrite rngl_of_nat_1 in Hn.
}
apply (rngl_nle_gt_iff Hor) in Hza.
rewrite (rngl_abs_nonpos_eq Hop Hor) in Hn. 2: {
  now apply (rngl_lt_le_incl Hor) in Hza.
}
destruct Hn as (H1, H2).
destruct (rngl_eq_dec Heo a (- rngl_of_nat n)) as [Han| Han]. {
  exists (- Z.of_nat n)%Z.
  rewrite rngl_of_Z_opp.
  rewrite rngl_of_Z_of_nat.
  split; [ rewrite Han; apply (rngl_le_refl Hor) | ].
  rewrite rngl_of_Z_add; cbn.
  rewrite rngl_of_Z_opp, rngl_of_Z_of_nat, <- Han.
  apply (rngl_lt_add_r Hos Hor).
  rewrite rngl_of_pos_1.
  apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
}
exists (- Z.of_nat (n + 1))%Z.
rewrite rngl_of_Z_opp.
rewrite rngl_of_Z_of_nat.
split. {
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  now apply (rngl_lt_le_incl Hor).
} {
  rewrite Nat2Z.inj_add; cbn.
  rewrite Z.opp_add_distr; cbn.
  rewrite <- Z.add_assoc; cbn.
  rewrite Z.add_0_r.
  rewrite rngl_of_Z_opp.
  apply (rngl_opp_lt_compat Hop Hor).
  rewrite (rngl_opp_involutive Hop).
  rewrite rngl_of_Z_of_nat.
  apply (rngl_le_neq Hor).
  split; [ easy | ].
  intros H; apply Han.
  rewrite H; symmetry.
  apply (rngl_opp_involutive Hop).
}
Qed.

Definition Int_part (x : T) := let (n, _) := z_int_part x in n.
Definition frac_part (x : T) := (x - rngl_of_Z (Int_part x))%L.

Arguments z_int_part a%_L.
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

Definition INR := rngl_of_nat.
Definition IZR := rngl_of_Z.

Theorem rngl_of_pos_pos : ∀ a, (0 < rngl_of_pos a)%L.
Proof.
intros.
induction a as [a| a| ]; cbn. {
  apply (rngl_le_lt_trans Hor _ 1).
  apply (rngl_0_le_1 Hon Hos Hiq Hor).
  rewrite rngl_of_pos_xI.
  apply (rngl_lt_add_l Hos Hor).
  apply (rngl_mul_pos_pos Hon Hop Hiq Hor); [ | easy ].
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
} {
  rewrite rngl_of_pos_xO.
  apply (rngl_mul_pos_pos Hon Hop Hiq Hor); [ | easy ].
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
} {
  rewrite rngl_of_pos_1.
  apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
}
Qed.

Theorem rngl_of_pos_neq_0 : ∀ a, rngl_of_pos a ≠ 0%L.
Proof.
intros * Ha.
specialize (rngl_of_pos_pos a) as H1.
rewrite Ha in H1.
now apply (rngl_lt_irrefl Hor) in H1.
Qed.

Theorem rngl_of_pos_eq_1 : ∀ a, rngl_of_pos a = 1%L → a = 1%positive.
Proof.
intros * Ha1.
destruct a as [a| a| ]; [ | | easy ]. {
  exfalso.
  rewrite rngl_of_pos_xI in Ha1.
  apply (rngl_add_move_r Hop) in Ha1.
  rewrite (rngl_sub_diag Hos) in Ha1.
  apply (rngl_eq_mul_0_l Hon Hos Hiq) in Ha1; [ | apply rngl_of_pos_neq_0 ].
  revert Ha1.
  apply (rngl_2_neq_0 Hon Hos Hiq Hc1 Hor).
} {
  exfalso.
  rewrite <- rngl_of_pos_1 in Ha1.
  apply (rngl_of_nat_inj Hon Hos Hch) in Ha1.
  now apply Pos2Nat.inj in Ha1.
}
Qed.

Theorem rngl_of_pos_inj : ∀ a b, rngl_of_pos a = rngl_of_pos b → a = b.
Proof.
intros * Hab.
apply (rngl_of_nat_inj Hon Hos Hch) in Hab.
now apply Pos2Nat.inj in Hab.
Qed.

Theorem rngl_of_pos_le_1_l : ∀ a, (1 ≤ rngl_of_pos a)%L.
Proof.
intros.
progress unfold rngl_of_pos.
rewrite <- rngl_of_nat_1.
apply (rngl_of_nat_inj_le Hon Hos Hiq Hc1 Hor).
apply Pos2Nat_ge_1.
Qed.

Theorem rngl_of_pos_nonneg : ∀ a, (0 ≤ rngl_of_pos a)%L.
Proof.
intros.
apply (rngl_le_trans Hor _ 1); [ | apply rngl_of_pos_le_1_l ].
apply (rngl_0_le_1 Hon Hos Hiq Hor).
Qed.

Theorem rngl_of_pos_le_inj :
  ∀ a b, (rngl_of_pos a ≤ rngl_of_pos b)%L → (a <= b)%positive.
Proof.
intros * Hab.
revert b Hab.
induction a as [a| a| ]; intros; [ | | apply Pos.le_1_l ]. {
  destruct b as [b| b| ]. {
    do 2 rewrite rngl_of_pos_xI in Hab.
    apply (rngl_add_le_mono_r Hos Hor) in Hab.
    apply (rngl_mul_le_mono_pos_l Hon Hop Hiq Hor) in Hab. 2: {
      now apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
    }
    progress unfold Pos.le; cbn.
    apply Pos.compare_le_iff.
    now apply IHa.
  } {
    progress unfold Pos.le; cbn.
    intros H.
    apply Pos.compare_cont_Gt_Gt in H.
    apply Pos.ge_le in H.
    apply Pos.le_nlt in H.
    apply H; clear H.
    rewrite rngl_of_pos_xI, rngl_of_pos_xO in Hab.
    destruct (Pos_dec a b) as [[Hdab| Hdab]| Hdab]; [ easy | | ]. 2: {
      subst b; exfalso.
      apply rngl_nlt_ge in Hab.
      apply Hab; clear Hab.
      apply (rngl_lt_add_r Hos Hor).
      apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
    }
    exfalso.
    apply Pos.lt_nle in Hdab.
    apply Hdab; clear Hdab.
    apply IHa.
    progress unfold rngl_of_pos in Hab |-*.
    clear IHa.
    remember (Pos.to_nat a) as a'.
    remember (Pos.to_nat b) as b'.
    clear a b Heqa' Heqb'.
    rename a' into a; rename b' into b.
    revert b Hab.
    induction a; intros; [ apply (rngl_of_nat_nonneg Hon Hos Hiq Hor) | ].
    rewrite rngl_of_nat_succ in Hab |-*.
    destruct b. {
      exfalso; cbn in Hab.
      rewrite (rngl_mul_0_r Hos) in Hab.
      apply rngl_nlt_ge in Hab.
      apply Hab; clear Hab.
      apply (rngl_add_nonneg_pos Hos Hor). 2: {
        apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
      }
      apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
        apply (rngl_0_le_2 Hon Hos Hiq Hor).
      }
      apply (rngl_le_0_add Hos Hor).
      apply (rngl_0_le_1 Hon Hos Hiq Hor).
      apply (rngl_of_nat_nonneg Hon Hos Hiq Hor).
    }
    rewrite rngl_of_nat_succ in Hab |-*.
    apply (rngl_add_le_mono_l Hos Hor).
    apply IHa.
    do 2 rewrite rngl_mul_add_distr_l in Hab.
    rewrite (rngl_mul_1_r Hon) in Hab.
    rewrite <- rngl_add_assoc in Hab.
    apply (rngl_add_le_mono_l Hos Hor) in Hab.
    easy.
  }
  exfalso.
  apply rngl_nlt_ge in Hab.
  apply Hab; clear Hab.
  rewrite rngl_of_pos_1.
  rewrite rngl_of_pos_xI.
  apply (rngl_lt_add_l Hos Hor).
  apply (rngl_mul_pos_pos Hon Hop Hiq Hor).
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  apply rngl_of_pos_pos.
}
destruct b as [b| b| ]. {
  rewrite rngl_of_pos_xI, rngl_of_pos_xO in Hab.
  progress unfold Pos.le; cbn.
  intros H1.
  apply Pos.compare_cont_Lt_Gt in H1.
  apply Pos.gt_lt in H1.
  apply Pos.lt_nle in H1.
  apply H1; clear H1.
  apply IHa.
  clear IHa.
  progress unfold rngl_of_pos in Hab |-*.
  remember (Pos.to_nat a) as a'.
  remember (Pos.to_nat b) as b'.
  clear a b Heqa' Heqb'.
  rename a' into a; rename b' into b.
  revert b Hab.
  induction a; intros; [ apply (rngl_of_nat_nonneg Hon Hos Hiq Hor) | ].
  rewrite rngl_of_nat_succ in Hab |-*.
  destruct b. {
    exfalso; cbn in Hab.
    apply rngl_nlt_ge in Hab.
    apply Hab; clear Hab.
    rewrite (rngl_mul_0_r Hos), rngl_add_0_l.
    rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
    rewrite <- rngl_add_assoc.
    apply (rngl_lt_add_r Hos Hor).
    apply (rngl_lt_0_add Hos Hor). {
      apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
    }
    apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor). {
      apply (rngl_0_le_2 Hon Hos Hiq Hor).
    }
    apply (rngl_of_nat_nonneg Hon Hos Hiq Hor).
  }
  rewrite rngl_of_nat_succ in Hab |-*.
  apply (rngl_add_le_mono_l Hos Hor).
  apply IHa.
  do 2 rewrite rngl_mul_add_distr_l in Hab.
  rewrite (rngl_mul_1_r Hon) in Hab.
  rewrite <- (rngl_add_assoc _ _ 1) in Hab.
  apply (rngl_add_le_mono_l Hos Hor) in Hab.
  easy.
} {
  do 2 rewrite rngl_of_pos_xO in Hab.
  apply (rngl_mul_le_mono_pos_l Hon Hop Hiq Hor) in Hab. 2: {
    apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  }
  progress unfold Pos.le; cbn.
  apply Pos.compare_le_iff.
  now apply IHa.
}
exfalso.
apply rngl_nlt_ge in Hab.
apply Hab; clear Hab.
rewrite rngl_of_pos_xO.
rewrite rngl_of_pos_1.
rewrite (rngl_mul_2_l Hon).
apply (rngl_le_lt_trans Hor _ (rngl_of_pos a)).
apply rngl_of_pos_le_1_l.
apply (rngl_lt_add_l Hos Hor).
apply rngl_of_pos_pos.
Qed.

Theorem rngl_of_pos_inj_le :
  ∀ a b, (a <= b)%positive → (rngl_of_pos a ≤ rngl_of_pos b)%L.
Proof.
intros * Hab.
revert b Hab.
induction a as [a| a| ]; intros. {
  destruct b as [b| b| ]; [ | | easy ]. {
    apply Pos.compare_le_iff in Hab; cbn in Hab.
    apply -> Pos.compare_le_iff in Hab.
    do 2 rewrite rngl_of_pos_xI.
    apply (rngl_add_le_mono_r Hos Hor).
    apply (rngl_mul_le_mono_pos_l Hon Hop Hiq Hor); [ | now apply IHa ].
    apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  } {
    apply Pos.compare_le_iff in Hab; cbn in Hab.
    apply Pos.compare_cont_Gt_not_Gt in Hab.
    apply Pos2Nat.inj_lt in Hab.
    rewrite rngl_of_pos_xI, rngl_of_pos_xO.
    progress unfold rngl_of_pos.
    remember (Pos.to_nat a) as i.
    remember (Pos.to_nat b) as j.
    clear a b IHa Heqi Heqj.
    (* lemma to do *)
    revert i Hab.
    induction j; intros; [ easy | ].
    rewrite rngl_of_nat_succ.
    destruct i. {
      rewrite (rngl_mul_0_r Hos).
      rewrite rngl_add_0_l.
      rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
      rewrite <- rngl_add_assoc.
      apply (rngl_le_add_r Hos Hor).
      apply (rngl_le_0_add Hos Hor).
      apply (rngl_0_le_1 Hon Hos Hiq Hor).
      apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
      apply (rngl_0_le_2 Hon Hos Hiq Hor).
      apply (rngl_of_nat_nonneg Hon Hos Hiq Hor).
    }
    apply Nat.succ_lt_mono in Hab.
    rewrite rngl_of_nat_succ.
    rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
    rewrite rngl_mul_add_distr_l, (rngl_mul_1_r Hon).
    rewrite <- rngl_add_assoc.
    apply (rngl_add_le_mono_l Hos Hor).
    now apply IHj.
  }
} {
  destruct b as [b| b| ]; [ | | easy ]. {
    apply Pos.compare_le_iff in Hab; cbn in Hab.
    apply Pos.compare_cont_Lt_not_Gt in Hab.
    rewrite rngl_of_pos_xI, rngl_of_pos_xO.
    eapply (rngl_le_trans Hor). 2: {
      apply (rngl_le_add_r Hos Hor).
      apply (rngl_0_le_1 Hon Hos Hiq Hor).
    }
    apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor).
    apply (rngl_0_le_2 Hon Hos Hiq Hor).
    now apply IHa.
  } {
    apply Pos.compare_le_iff in Hab; cbn in Hab.
    apply -> Pos.compare_le_iff in Hab.
    do 2 rewrite rngl_of_pos_xO.
    apply (rngl_mul_le_mono_nonneg_l Hon Hop Hiq Hor).
    apply (rngl_0_le_2 Hon Hos Hiq Hor).
    now apply IHa.
  }
}
rewrite rngl_of_pos_1.
apply rngl_of_pos_le_1_l.
Qed.

Theorem rngl_of_Z_le_inj : ∀ a b, (rngl_of_Z a ≤ rngl_of_Z b)%L → (a <= b)%Z.
Proof.
intros * Hab.
destruct a as [| a| a]. {
  cbn in Hab.
  destruct b as [| b| b]; cbn in Hab; [ easy | easy | ].
  exfalso; apply rngl_nlt_ge in Hab; apply Hab; clear Hab.
  apply (rngl_opp_lt_compat Hop Hor).
  rewrite (rngl_opp_0 Hop), (rngl_opp_involutive Hop).
  apply rngl_of_pos_pos.
} {
  destruct b as [| b| b]; cbn. {
    exfalso; apply rngl_nlt_ge in Hab; apply Hab; clear Hab; cbn.
    apply rngl_of_pos_pos.
  } {
    cbn in Hab.
    apply Pos2Z.pos_le_pos.
    now apply rngl_of_pos_le_inj.
  }
  exfalso.
  apply rngl_nlt_ge in Hab.
  apply Hab; clear Hab; cbn.
  apply (rngl_le_lt_trans Hor _ 0); [ | apply rngl_of_pos_pos ].
  apply (rngl_opp_le_compat Hop Hor).
  rewrite (rngl_opp_0 Hop), (rngl_opp_involutive Hop).
  apply (rngl_lt_le_incl Hor).
  apply rngl_of_pos_pos.
} {
  destruct b as [| b| b]; cbn; [ easy | easy | ].
  cbn in Hab.
  apply (rngl_opp_le_compat Hop Hor) in Hab.
  apply Z.opp_le_mono; cbn.
  progress unfold rngl_of_pos in Hab.
  apply (rngl_of_nat_inj_le Hon Hos Hiq Hc1 Hor) in Hab.
  progress unfold Z.le; cbn.
  apply Pos.compare_le_iff.
  now apply Pos2Nat.inj_le.
}
Qed.

Theorem rngl_of_Z_inj : ∀ a b, rngl_of_Z a = rngl_of_Z b → a = b.
Proof.
intros * Hab.
apply Z.le_antisymm. {
  apply rngl_of_Z_le_inj.
  rewrite Hab; apply (rngl_le_refl Hor).
} {
  apply rngl_of_Z_le_inj.
  rewrite Hab; apply (rngl_le_refl Hor).
}
Qed.

(** *** generic theorems: work for pair (≤, <) and for pair (<, ≤) *)

Theorem gen_between_rngl_of_nat_and_succ {l1 l2} :
  rngl_order_compatibility l1 l2 →
  ∀ a b i j,
  (a ≤ b)%L
  → l1 (rngl_of_nat i) a ∧ l2 a (rngl_of_nat (i + 1))%L
  → l1 (rngl_of_nat j) b ∧ l2 b (rngl_of_nat (j + 1))%L
  → i ≤ j.
Proof.
intros Hroc * Hab Hi Hj.
generalize Hroc; intros Hroc'.
move Hroc' before Hroc.
apply (rngl_order_compatibility_comm Hor) in Hroc'.
revert a b j Hab Hi Hj.
induction i; intros; cbn; [ apply Nat.le_0_l | ].
destruct j. {
  exfalso; cbn in Hj.
  rewrite rngl_add_0_r in Hj.
  destruct Hj as (_, Hj).
  rewrite Nat.add_1_r in Hi.
  do 2 rewrite rngl_of_nat_succ in Hi.
  destruct Hi as (H1, H2).
  apply roc_dual_1 in H1.
  apply H1; clear H1.
  apply (roc_mono_l _ b); [ easy | ].
  apply (roc_mono_r _ 1%L); [ easy | ].
  apply (rngl_le_add_r Hos Hor).
  apply (rngl_of_nat_nonneg Hon Hos Hiq Hor).
}
apply -> Nat.succ_le_mono.
apply (IHi (a - 1) (b - 1))%L. {
  now apply (rngl_sub_le_mono_r Hop Hor).
} {
  rewrite Nat.add_1_r in Hi.
  do 2 rewrite rngl_of_nat_succ in Hi.
  split; [ now apply (rngl_le_or_lt_add_sub_l Hroc Hop Hor) | ].
  apply (rngl_le_or_lt_sub_add_l Hroc' Hop Hor).
  now rewrite Nat.add_1_r.
} {
  rewrite Nat.add_1_r in Hj.
  do 2 rewrite rngl_of_nat_succ in Hj.
  split; [ now apply (rngl_le_or_lt_add_sub_l Hroc Hop Hor) | ].
  apply (rngl_le_or_lt_sub_add_l Hroc' Hop Hor).
  now rewrite Nat.add_1_r.
}
Qed.

Theorem rngl_of_nat_le_or_lt_prop {l1 l2} :
  rngl_order_compatibility l1 l2 →
  ∀ x m n,
  l1 (rngl_of_nat m) x ∧ l2 x (rngl_of_nat (m + 1))
  → l1 (rngl_of_nat n) x ∧ l2 x (rngl_of_nat (n + 1))
  → m = n.
Proof.
intros Hroc * (Hmx, Hxm) (Hnx, Hxn).
apply Nat.le_antisymm.
apply (gen_between_rngl_of_nat_and_succ Hroc x x); [ | easy | easy ].
apply (rngl_le_refl Hor).
apply (gen_between_rngl_of_nat_and_succ Hroc x x); [ | easy | easy ].
apply (rngl_le_refl Hor).
Qed.

Theorem rngl_of_pos_le_or_lt_prop {l1 l2} :
  rngl_order_compatibility l1 l2 →
  ∀ x m n,
  l1 (rngl_of_pos m) x ∧ l2 x (rngl_of_pos (m + 1))
  → l1 (rngl_of_pos n) x ∧ l2 x (rngl_of_pos (n + 1))
  → m = n.
Proof.
intros Hroc * Hm Hn.
rewrite rngl_of_pos_add in Hm, Hn.
rewrite rngl_of_pos_1 in Hm, Hn.
progress unfold rngl_of_pos in Hm.
progress unfold rngl_of_pos in Hn.
rewrite <- rngl_of_nat_1 in Hm, Hn.
rewrite <- rngl_of_nat_add in Hm, Hn.
apply Pos2Nat.inj.
now apply (rngl_of_nat_le_or_lt_prop Hroc x).
Qed.

(** *** specific theorems: version for ≤, followed with version for < *)

Theorem between_rngl_of_nat_and_succ :
  ∀ a b i j,
  (a ≤ b)%L
  → (rngl_of_nat i ≤ a < rngl_of_nat (i + 1))%L
  → (rngl_of_nat j ≤ b < rngl_of_nat (j + 1))%L
  → i ≤ j.
Proof.
intros * Hab Hi Hj.
now apply (gen_between_rngl_of_nat_and_succ (rngl_le_lt_comp Hor) a b).
Qed.

Theorem between_rngl_of_nat_and_succ2 :
  ∀ a b i j,
  (a ≤ b)%L
  → (rngl_of_nat i < a ≤ rngl_of_nat (i + 1))%L
  → (rngl_of_nat j < b ≤ rngl_of_nat (j + 1))%L
  → i ≤ j.
Proof.
intros * Hab Hi Hj.
now apply (gen_between_rngl_of_nat_and_succ (rngl_lt_le_comp Hor) a b).
Qed.

Theorem rngl_of_nat_prop :
  ∀ x m n,
  (rngl_of_nat m ≤ x < rngl_of_nat (m + 1))%L
  → (rngl_of_nat n ≤ x < rngl_of_nat (n + 1))%L
  → m = n.
Proof.
intros *.
now apply (rngl_of_nat_le_or_lt_prop (rngl_le_lt_comp Hor) x).
Qed.

Theorem rngl_of_nat_prop2 :
  ∀ x m n,
  (rngl_of_nat m < x ≤ rngl_of_nat (m + 1))%L
  → (rngl_of_nat n < x ≤ rngl_of_nat (n + 1))%L
  → m = n.
Proof.
intros *.
now apply (rngl_of_nat_le_or_lt_prop (rngl_lt_le_comp Hor) x).
Qed.

Theorem rngl_of_pos_prop :
  ∀ x m n,
  (rngl_of_pos m ≤ x < rngl_of_pos (m + 1))%L
  → (rngl_of_pos n ≤ x < rngl_of_pos (n + 1))%L
  → m = n.
Proof.
intros *.
now apply (rngl_of_pos_le_or_lt_prop (rngl_le_lt_comp Hor) x).
Qed.

Theorem rngl_of_pos_prop2 :
  ∀ x m n,
  (rngl_of_pos m < x ≤ rngl_of_pos (m + 1))%L
  → (rngl_of_pos n < x ≤ rngl_of_pos (n + 1))%L
  → m = n.
Proof.
intros *.
now apply (rngl_of_pos_le_or_lt_prop (rngl_lt_le_comp Hor) x).
Qed.

(** *** other theorems *)

Theorem rngl_of_nat_Z_to_nat :
  ∀ a, (0 <= a)%Z → rngl_of_nat (Z.to_nat a) = rngl_of_Z a.
Proof.
intros * Hza.
destruct a as [| a| a]; [ easy | | easy ].
rewrite Z2Nat.inj_pos.
now rewrite <- rngl_of_nat_Pos_to_nat.
Qed.

(**)
Theorem Int_part_small_lemma :
  ∀ x n,
  (0 ≤ x < 1)%L
  → (rngl_of_Z n ≤ x < rngl_of_Z (n + 1))%L
  → n = 0%Z.
Proof.
intros * Hx Hn.
destruct Hx as (Hzx, Hx1).
destruct Hn as (Hnx, Hxn).
destruct n as [| p| p]; [ easy | | ]; exfalso. {
  cbn in Hnx.
  apply rngl_nlt_ge in Hnx.
  apply Hnx; clear Hnx.
  apply (rngl_lt_le_trans Hor _ 1); [ easy | ].
  apply rngl_of_pos_le_1_l.
} {
  apply rngl_nle_gt in Hxn.
  apply Hxn; clear Hxn.
  apply (rngl_le_trans Hor _ 0); [ | easy ].
  rewrite rngl_of_Z_add_1_r; cbn.
  rewrite (rngl_add_opp_l Hop).
  apply (rngl_le_sub_0 Hop Hor).
  apply rngl_of_pos_le_1_l.
}
Qed.
(**)

(*
Theorem gen_rngl_of_pos_xI_interval {l1 l2} :
  rngl_order_compatibility l1 l2 →
  ∀ p a,
  l1 (rngl_of_pos p~1) a ∧ l2 a (rngl_of_pos (p~1 + 1))
  → (l1 (rngl_of_pos p) (a / 2) ∧ l2 (a / 2) (rngl_of_pos (p + 1)))%L.
Proof.
intros * Hp.
split. {
...
Check rngl_le_div_r.
About rngl_lt_div_r.
Print rngl_order_compatibility.
...
  apply (rngl_le_div_r Hon Hon Hop Hiv Hiq Hor).
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hiq Hor).
  eapply (rngl_le_trans Hor); [ | apply Hp ].
  rewrite (rngl_mul_2_r Hon).
  rewrite <- (rngl_mul_2_l Hon).
  replace 2%L with (rngl_of_pos 2). 2: {
    rewrite rngl_of_nat_Pos_to_nat.
    now rewrite <- rngl_of_nat_2.
  }
  rewrite <- rngl_of_pos_mul; cbn.
  apply rngl_of_pos_inj_le.
  rewrite Pos.xI_succ_xO.
  rewrite <- Pos.add_1_l.
  apply Pos_le_add_l.
}
apply (rngl_lt_div_l Hon Hon Hop Hiv Hiq Hor).
apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hiq Hor).
rewrite rngl_of_pos_add.
rewrite rngl_of_pos_1.
rewrite rngl_mul_add_distr_r, (rngl_mul_1_l Hon).
rewrite <- rngl_of_pos_2 at 1.
rewrite <- rngl_of_pos_mul.
rewrite Pos.mul_comm.
rewrite rngl_add_assoc.
rewrite <- rngl_of_pos_1.
rewrite <- rngl_of_pos_add; cbn.
rewrite <- rngl_of_pos_add.
easy.
...
*)

Theorem rngl_of_pos_xI_interval :
  ∀ p a,
  (rngl_of_pos p~1 ≤ a < rngl_of_pos (p~1 + 1))%L
  → (rngl_of_pos p ≤ a / 2 < rngl_of_pos (p + 1))%L.
Proof.
(*
intros * Hp.
now apply (gen_rngl_of_pos_xI_interval (rngl_le_lt_comp Hor)).
*)
intros * Hp.
split. {
  apply (rngl_le_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  eapply (rngl_le_trans Hor); [ | apply Hp ].
  rewrite (rngl_mul_2_r Hon).
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- rngl_of_pos_2.
  rewrite <- rngl_of_pos_mul; cbn.
  apply rngl_of_pos_inj_le.
  rewrite Pos.xI_succ_xO.
  rewrite <- Pos.add_1_l.
  apply Pos_le_add_l.
}
apply (rngl_lt_div_l Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
rewrite rngl_of_pos_add.
rewrite rngl_of_pos_1.
rewrite rngl_mul_add_distr_r, (rngl_mul_1_l Hon).
rewrite <- rngl_of_pos_2 at 1.
rewrite <- rngl_of_pos_mul.
rewrite Pos.mul_comm.
rewrite rngl_add_assoc.
rewrite <- rngl_of_pos_1.
rewrite <- rngl_of_pos_add; cbn.
rewrite <- rngl_of_pos_add.
easy.
Qed.

Theorem rngl_of_pos_xI_interval2 :
  ∀ p a,
  (rngl_of_pos p~1 < a ≤ rngl_of_pos (p~1 + 1))%L
  → (rngl_of_pos p < a / 2 ≤ rngl_of_pos (p + 1))%L.
Proof.
(*
intros * Hp.
now apply (gen_rngl_of_pos_xI_interval (rngl_lt_le_comp Hor)).
*)
intros * Hp.
split. {
  apply (rngl_lt_div_r Hon Hop Hiv Hor).
  apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
  eapply (rngl_le_lt_trans Hor); [ | apply Hp ].
  rewrite (rngl_mul_2_r Hon).
  rewrite <- (rngl_mul_2_l Hon).
  rewrite <- rngl_of_pos_2.
  rewrite <- rngl_of_pos_mul; cbn.
  apply rngl_of_pos_inj_le.
  rewrite Pos.xI_succ_xO.
  rewrite <- Pos.add_1_l.
  apply Pos_le_add_l.
}
apply (rngl_le_div_l Hon Hop Hiv Hor).
apply (rngl_0_lt_2 Hon Hos Hiq Hc1 Hor).
rewrite rngl_of_pos_add.
rewrite rngl_of_pos_1.
rewrite rngl_mul_add_distr_r, (rngl_mul_1_l Hon).
rewrite <- rngl_of_pos_2 at 1.
rewrite <- rngl_of_pos_mul.
rewrite Pos.mul_comm.
rewrite rngl_add_assoc.
rewrite <- rngl_of_pos_1.
rewrite <- rngl_of_pos_add; cbn.
rewrite <- rngl_of_pos_add.
easy.
Qed.

Theorem Int_part_prop :
  ∀ x m n,
  (rngl_of_Z m ≤ x < rngl_of_Z (m + 1))%L
  → (rngl_of_Z n ≤ x < rngl_of_Z (n + 1))%L
  → m = n.
Proof.
intros * Hm Hn.
destruct n as [| n| n]. {
  cbn in Hn.
  rewrite rngl_of_pos_1 in Hn.
  now apply (Int_part_small_lemma x).
} {
  cbn in Hn.
  destruct m as [| m| m]. {
    cbn in Hm.
    rewrite rngl_of_pos_1 in Hm.
    symmetry.
    now apply (Int_part_small_lemma x).
  } {
    progress f_equal.
    now apply (rngl_of_pos_prop x).
  } {
    exfalso.
    destruct Hm as (Hmx, Hxm).
    apply rngl_nle_gt in Hxm.
    apply Hxm; clear Hxm.
    apply (rngl_le_trans Hor _ (rngl_of_pos n)); [ | easy ].
    rewrite rngl_of_Z_add_1_r; cbn.
    apply (rngl_le_trans Hor _ 1); [ | apply rngl_of_pos_le_1_l ].
    rewrite (rngl_add_opp_l Hop).
    apply (rngl_le_sub_l Hop Hor).
    apply rngl_of_pos_nonneg.
  }
} {
  destruct m as [| m| m]. {
    exfalso.
    cbn in Hm.
    rewrite rngl_of_pos_1 in Hm.
    rewrite rngl_of_Z_add_1_r in Hn.
    cbn in Hn.
    destruct Hn as (Hnx, Hxn).
    apply rngl_nle_gt in Hxn.
    apply Hxn; clear Hxn.
    apply (rngl_le_trans Hor _ 0); [ | easy ].
    rewrite (rngl_add_opp_l Hop).
    apply (rngl_le_sub_0 Hop Hor).
    apply rngl_of_pos_le_1_l.
  } {
    exfalso.
    rewrite rngl_of_Z_add_1_r in Hn.
    cbn in Hm, Hn.
    destruct Hn as (Hnx, Hxn).
    apply rngl_nle_gt in Hxn.
    apply Hxn; clear Hxn.
    apply (rngl_le_trans Hor _ 1). {
      rewrite (rngl_add_opp_l Hop).
      apply (rngl_le_sub_l Hop Hor).
      apply rngl_of_pos_nonneg.
    }
    apply (rngl_le_trans Hor _ (rngl_of_pos m)); [ | easy ].
    apply rngl_of_pos_le_1_l.
  } {
    rewrite rngl_of_Z_add_1_r in Hm, Hn.
    cbn in Hm, Hn.
    progress f_equal.
    apply (rngl_of_pos_prop2 (- (x - 1))%L). {
      split. {
        apply (rngl_opp_lt_compat Hop Hor).
        rewrite (rngl_opp_involutive Hop).
        now apply (rngl_lt_sub_lt_add_r Hop Hor).
      } {
        apply (rngl_opp_le_compat Hop Hor).
        rewrite (rngl_opp_involutive Hop).
        apply (rngl_le_add_le_sub_r Hop Hor).
        rewrite rngl_of_pos_add.
        rewrite rngl_of_pos_1.
        rewrite (rngl_opp_add_distr Hop).
        now rewrite (rngl_sub_add Hop).
      }
    } {
      split. {
        apply (rngl_opp_lt_compat Hop Hor).
        rewrite (rngl_opp_involutive Hop).
        now apply (rngl_lt_sub_lt_add_r Hop Hor).
      } {
        apply (rngl_opp_le_compat Hop Hor).
        rewrite (rngl_opp_involutive Hop).
        apply (rngl_le_add_le_sub_r Hop Hor).
        rewrite rngl_of_pos_add.
        rewrite rngl_of_pos_1.
        rewrite (rngl_opp_add_distr Hop).
        now rewrite (rngl_sub_add Hop).
      }
    }
  }
}
Qed.

Theorem Int_part_small : ∀ x, (0 ≤ x < 1)%L ↔ Int_part x = 0%Z.
Proof.
intros.
progress unfold Int_part.
remember (z_int_part x) as m eqn:Hm.
symmetry in Hm.
destruct m as (n, Hn); clear Hm.
split; intros Hx. {
  apply (Int_part_prop x); [ easy | cbn ].
  now rewrite rngl_of_pos_1.
} {
  subst; cbn in Hn.
  now rewrite rngl_of_pos_1 in Hn.
}
Qed.

Theorem Int_part_pos_interv :
  ∀ p x, (rngl_of_pos p ≤ x < rngl_of_pos (p + 1))%L ↔ Int_part x = Z.pos p.
Proof.
intros.
progress unfold Int_part.
remember (z_int_part x) as m eqn:Hm.
symmetry in Hm.
destruct m as (n, Hn); clear Hm.
destruct n as [| q| q]. {
  split; intros Hx; [ | easy ].
  now symmetry; apply (Int_part_prop x).
} {
  split; intros Hx; [ now apply (Int_part_prop x) | ].
  now injection Hx; clear Hx; intros; subst.
} {
  split; intros Hx; [ now apply (Int_part_prop x) | easy ].
}
Qed.

Theorem Int_part_interv :
  ∀ z x, (rngl_of_Z z ≤ x < rngl_of_Z (z + 1))%L ↔ Int_part x = z.
Proof.
intros.
progress unfold Int_part.
remember (z_int_part x) as m eqn:Hm.
symmetry in Hm.
destruct m as (n, Hn); clear Hm.
split; intros Hx; [ now apply (Int_part_prop x) | ].
now subst; cbn in Hn.
Qed.

Theorem frac_part_small : ∀ x, (0 ≤ x < 1)%L → frac_part x = x.
Proof.
intros * Hx.
unfold frac_part.
rewrite (proj1 (Int_part_small _)); [ | easy ].
apply (rngl_sub_0_r Hos).
Qed.

Theorem pow_INR : ∀ n k, INR (n ^ k) = (INR n ^ k)%L.
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
remember (z_int_part (rngl_of_nat a)) as m eqn:Hm.
symmetry in Hm.
destruct m as (n, Hn).
clear Hm.
apply (Int_part_prop (rngl_of_nat a)); [ easy | ].
rewrite rngl_of_Z_add_1_r.
rewrite rngl_of_Z_of_nat.
split; [ apply (rngl_le_refl Hor) | ].
apply (rngl_lt_add_r Hos Hor).
apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
Qed.

Theorem frac_part_INR : ∀ n, frac_part (INR n) = 0%L.
Proof.
intros.
unfold frac_part.
rewrite Int_part_rngl_of_nat.
rewrite rngl_of_Z_of_nat.
apply (rngl_sub_diag Hos).
Qed.

Theorem rngl_of_Z_sub :
  ∀ a b, rngl_of_Z (a - b) = (rngl_of_Z a - rngl_of_Z b)%L.
Proof.
intros.
progress unfold Z.sub.
progress unfold rngl_sub.
rewrite Hop.
rewrite rngl_of_Z_add.
progress f_equal.
apply rngl_of_Z_opp.
Qed.

Definition nat_Int_part a :=
  match Int_part a with
  | 0%Z => 0
  | Z.pos p => Pos.to_nat p
  | Z.neg p => Pos.to_nat p
  end.

Theorem Int_part_nonneg : ∀ a, (0 ≤ a)%L → (0 <= Int_part a)%Z.
Proof.
intros * Hza.
progress unfold Int_part.
remember (z_int_part a) as z eqn:H; clear H.
destruct z as (z, Hz).
progress unfold rngl_of_Z in Hz.
destruct z as [| p| p]; [ easy | easy | exfalso ].
destruct Hz as (_, Hz).
apply rngl_nle_gt in Hz.
apply Hz; clear Hz.
remember (Z.neg p + 1)%Z as q eqn:Hq.
symmetry in Hq.
destruct q as [| q| q]; [ easy | | ]. {
  apply Z.add_move_l in Hq.
  cbn in Hq; symmetry in Hq.
  injection Hq; clear Hq; intros Hq.
  now destruct p, q.
}
apply (rngl_le_trans Hor _ 0); [ | easy ].
apply (rngl_opp_le_compat Hop Hor).
rewrite (rngl_opp_0 Hop).
rewrite (rngl_opp_involutive Hop).
apply rngl_of_pos_nonneg.
Qed.

Theorem Int_part_nonpos : ∀ a, (a < 0)%L → (Int_part a <= 0)%Z.
Proof.
intros * Hza.
progress unfold Int_part.
remember (z_int_part a) as z eqn:H; clear H.
destruct z as (z, Hz).
progress unfold rngl_of_Z in Hz.
destruct z as [| p| p]; [ easy | exfalso | easy ].
destruct Hz as (Hz, _).
apply rngl_nlt_ge in Hz.
apply Hz; clear Hz.
apply (rngl_lt_le_trans Hor _ 0); [ easy | ].
apply rngl_of_pos_nonneg.
Qed.

Theorem rngl_of_Z_Int_part :
  ∀ a,
  rngl_of_Z (Int_part a) =
    (if rngl_le_dec Hor 0 a then rngl_of_nat (nat_Int_part a)
     else (- rngl_of_nat (nat_Int_part a))%L).
Proof.
intros.
progress unfold nat_Int_part.
remember (Int_part a) as z eqn:Hz.
symmetry in Hz.
destruct (rngl_le_dec Hor 0 a) as [Hza| Hza]. {
  destruct z as [| p| p]; [ easy | easy | exfalso ].
  assert (H : (Int_part a < 0)%Z) by now rewrite Hz.
  apply Z.nle_gt in H.
  apply H; clear p H Hz.
  now apply Int_part_nonneg.
} {
  destruct z as [| p| p]; [ symmetry; apply (rngl_opp_0 Hop) | exfalso | easy ].
  assert (H : (0 < Int_part a)%Z) by now rewrite Hz.
  apply Z.nle_gt in H.
  apply H; clear p H Hz.
  apply (rngl_nle_gt_iff Hor) in Hza.
  now apply Int_part_nonpos.
}
Qed.

(*
Theorem nat_Int_part_le :
  ∀ a b, (0 ≤ a ≤ b)%L → nat_Int_part a ≤ nat_Int_part b.
Proof.
intros * Hab.
progress unfold nat_Int_part.
remember (int_part _ _ _ _ _ a) as x eqn:H1.
remember (int_part _ _ _ _ _ b) as y eqn:H2.
destruct x as (x, Hx).
destruct y as (y, Hy).
clear H1 H2.
rewrite (rngl_abs_nonneg_eq Hon Hop Hiq Hor) in Hx; [ | easy ].
rewrite (rngl_abs_nonneg_eq Hon Hop Hiq Hor) in Hy. 2: {
  now apply (rngl_le_trans Hor _ a).
}
now apply (between_rngl_of_nat_and_succ a b).
Qed.

Theorem nat_Int_part_0 : nat_Int_part 0%L = 0.
Proof.
progress unfold nat_Int_part.
remember (int_part _ _ _ _ _ _) as x eqn:Hx.
symmetry in Hx.
destruct x as (n, Hn).
clear Hx.
rewrite (rngl_abs_0 Hop) in Hn.
destruct Hn as (Hn, _).
rewrite <- rngl_of_nat_0 in Hn.
apply (rngl_of_nat_inj_le Hon Hon Hop Hiq Hc1 Hiq Hor) in Hn.
now apply Nat.le_0_r in Hn.
Qed.

Theorem nat_Int_part_opp : ∀ a, nat_Int_part (- a)%L = nat_Int_part a.
Proof.
intros.
progress unfold nat_Int_part.
remember (int_part _ _ _ _ _ (- a)%L) as b eqn:Hb.
remember (int_part _ _ _ _ _ a) as c eqn:Hc.
clear Hb Hc.
destruct b as (b, Hb).
destruct c as (c, Hc).
move c before b.
rewrite (rngl_abs_opp Hon Hop Hiq Hor) in Hb.
apply Nat.le_antisymm. {
  apply (between_rngl_of_nat_and_succ (∣ a ∣) (∣ a ∣)); [ | easy | easy ].
  apply (rngl_le_refl Hiq Hor).
} {
  apply (between_rngl_of_nat_and_succ (∣ a ∣) (∣ a ∣)); [ | easy | easy ].
  apply (rngl_le_refl Hiq Hor).
}
Qed.

Theorem rngl_of_nat_int_part_le :
  ∀ a, (rngl_of_nat (nat_Int_part a) ≤ ∣ a ∣)%L.
Proof.
intros.
progress unfold nat_Int_part.
remember (int_part _ _ _ _ _ _) as b eqn:Hb.
clear Hb.
now destruct b as (b, Hb).
Qed.
*)

Theorem rngl_of_Z_1 : rngl_of_Z 1 = 1%L.
Proof.
progress unfold rngl_of_Z; cbn.
apply rngl_of_pos_1.
Qed.

Theorem Int_part_0 : Int_part 0 = 0%Z.
Proof.
rewrite (proj1 (Int_part_small _)); [ easy | ].
split; [ pauto | ].
apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
Qed.

Theorem frac_part_0 : frac_part 0 = 0%L.
Proof.
progress unfold frac_part.
rewrite Int_part_0; cbn.
apply (rngl_sub_diag Hos).
Qed.

Theorem Int_part_1 : Int_part 1 = 1%Z.
Proof.
apply Int_part_interv.
rewrite rngl_of_Z_add, rngl_of_Z_1.
split; [ pauto | ].
apply (rngl_lt_add_l Hos Hor).
apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
Qed.

(*
Theorem Int_part_opp :
  ∀ a, Int_part (- a) = (- Int_part a)%Z.
Proof.
intros.
progress unfold Int_part.
remember (z_int_part (- a)) as m eqn:Hm.
symmetry in Hm.
destruct m as (m, Hma).
remember (z_int_part a) as n eqn:Hn.
symmetry in Hn.
destruct n as (n, Hna).
move n before m; move Hna before Hma.
clear Hm Hn.
apply Z.eq_opp_r.
apply (Int_part_prop a); [ | easy ].
rewrite rngl_of_Z_opp.
destruct Hma as (H1, H2).
apply (rngl_opp_le_compat Hon Hop Hiq Hor) in H1.
rewrite (rngl_opp_involutive Hop) in H1.
split. {
...
*)

Theorem rngl_sub_between_0_and_1 : ∀ a b, (0 ≤ b - a < 1 ↔ a ≤ b < a + 1)%L.
Proof.
intros.
split; intros (H1, H2). {
  apply -> (rngl_le_0_sub Hop Hor) in H1.
  split; [ easy | ].
  now apply (rngl_lt_sub_lt_add_l Hop Hor) in H2.
} {
  split; [ now apply (rngl_le_0_sub Hop Hor) | ].
  now apply (rngl_lt_sub_lt_add_l Hop Hor).
}
Qed.

Theorem Int_part_eq_sub :
  ∀ a b,
  (frac_part b ≤ frac_part a)%L
  → Int_part a = Int_part b
  → Int_part (a - b) = 0%Z.
Proof.
intros * Hba Hab.
progress unfold frac_part in Hba.
progress unfold Int_part in Hba.
progress unfold Int_part in Hab.
remember (z_int_part a) as m eqn:H; clear H.
destruct m as (m, Hm).
remember (z_int_part b) as n eqn:H; clear H.
destruct n as (n, Hn).
subst m.
apply (rngl_sub_le_mono_r Hop Hor) in Hba.
apply Int_part_small.
apply rngl_sub_between_0_and_1.
split; [ easy | ].
eapply (rngl_lt_le_trans Hor); [ apply Hm | ].
rewrite rngl_of_Z_add; cbn.
rewrite rngl_of_pos_1.
now apply (rngl_add_le_mono_r Hos Hor).
Qed.

Theorem rngl_sub_Int_part : ∀ a b,
  (frac_part b ≤ frac_part a)%L
  → Int_part (a - b) = (Int_part a - Int_part b)%Z.
Proof.
intros * Hba.
progress unfold frac_part in Hba.
progress unfold Int_part in Hba.
progress unfold Int_part at 2 3.
remember (z_int_part a) as m eqn:H; clear H.
destruct m as (m, Hm).
remember (z_int_part b) as n eqn:H; clear H.
destruct n as (n, Hn).
move n before m.
apply Int_part_interv.
rewrite rngl_of_Z_add.
rewrite rngl_of_Z_sub.
rewrite rngl_of_Z_1.
apply (rngl_le_add_le_sub_r Hop Hor) in Hba.
rewrite <- (rngl_add_sub_swap Hop) in Hba.
rewrite <- (rngl_add_sub_assoc Hop) in Hba.
apply (rngl_le_add_le_sub_l Hop Hor) in Hba.
split; [ easy | ].
apply (rngl_lt_sub_lt_add_r Hop Hor).
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- rngl_of_Z_1.
rewrite <- rngl_of_Z_add.
rewrite <- (rngl_add_sub_swap Hop).
rewrite <- (rngl_add_sub_assoc Hop).
eapply (rngl_lt_le_trans Hor).
apply Hm.
apply (rngl_le_add_r Hos Hor).
now apply (rngl_le_0_sub Hop Hor).
Qed.

Theorem Int_part_rngl_of_pos :
  ∀ p, Int_part (rngl_of_pos p) = Z.pos p.
Proof.
intros.
progress unfold rngl_of_pos.
rewrite Int_part_rngl_of_nat.
apply positive_nat_Z.
Qed.

Theorem frac_part_rngl_of_pos : ∀ p, frac_part (rngl_of_pos p) = 0%L.
Proof.
intros.
progress unfold frac_part.
rewrite Int_part_rngl_of_pos.
apply (rngl_sub_diag Hos).
Qed.

Theorem Int_part_IZR : ∀ z, Int_part (IZR z) = z.
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
clear Hz.
progress unfold IZR.
progress unfold rngl_of_Z.
rewrite <- (rngl_sub_0_l Hop).
rewrite rngl_sub_Int_part. 2: {
  rewrite frac_part_0.
  rewrite frac_part_rngl_of_pos.
  apply (rngl_le_refl Hor).
}
rewrite Int_part_0.
now rewrite Int_part_rngl_of_pos.
Qed.

Theorem frac_part_IZR : ∀ z, frac_part (IZR z) = 0%L.
Proof.
intros.
unfold frac_part.
rewrite Int_part_IZR.
apply (rngl_sub_diag Hos).
Qed.

Theorem Rpow_div_sub : ∀ x i j,
  x ≠ 0
  → (j ≤ i)%nat
  → x ^ i / x ^ j = x ^ (i - j).
Proof.
intros * Hx Hij.
now symmetry; apply Nat.pow_sub_r.
Qed.

Theorem frac_part_interv : ∀ x, (0 ≤ frac_part x < 1)%L.
Proof.
intros.
unfold frac_part.
progress unfold Int_part.
remember (z_int_part x) as z eqn:H; clear H.
destruct z as (z, (Hzx, Hxz)).
apply (rngl_le_0_sub Hop Hor) in Hzx.
rewrite rngl_of_Z_add, rngl_of_Z_1 in Hxz.
apply (rngl_lt_sub_lt_add_l Hop Hor) in Hxz.
easy.
Qed.

Theorem Rabs_or : ∀ x y, rngl_abs x = y → x = y ∨ x = (- y)%L.
Proof.
intros * Hxy; subst y.
unfold rngl_abs.
remember (x ≤? 0)%L as xz eqn:Hxz.
symmetry in Hxz.
destruct xz; [ | now left ].
rewrite (rngl_opp_involutive Hop).
now right.
Qed.

Theorem Rabs_eq_0 : ∀ x, rngl_abs x = 0%L → x = 0%L.
Proof.
intros * Hx.
now apply (eq_rngl_abs_0 Hop).
Qed.

Theorem Rabs_lt : ∀ x y, (rngl_abs x < y ↔ - y < x < y)%L.
Proof.
intros.
apply iff_sym.
apply (rngl_abs_lt Hop Hor).
Qed.

Theorem Rabs_le : ∀ x y, (rngl_abs x ≤ y ↔ - y ≤ x ≤ y)%L.
Proof.
intros.
apply iff_sym.
apply (rngl_abs_le Hop Hor).
Qed.

Theorem Rabs_sqr : ∀ x, rngl_abs (x²) = x².
Proof.
intros.
apply (rngl_abs_nonneg_eq Hop Hor).
apply (rngl_squ_nonneg Hon Hos Hiq Hor).
Qed.

Theorem Rabs_sqrt : ∀ x, (0 ≤ x)%L → rngl_abs (√ x) = √ x.
Proof.
intros * Hzx.
apply (rngl_abs_nonneg_eq Hop Hor).
now apply rl_sqrt_nonneg.
Qed.

Theorem Rmult_minus_distr_r : ∀ r1 r2 r3,
  ((r1 - r2) * r3 = r1 * r3 - r2 * r3)%L.
Proof.
intros.
apply (rngl_mul_sub_distr_r Hop).
Qed.

Theorem Rminus_plus : ∀ x y, (x - y + y = x)%L.
Proof.
intros.
apply (rngl_sub_add Hop).
Qed.

Theorem Rdiv_div : ∀ x y z, (y ≠ 0 → z ≠ 0 → x / y / z = x / (y * z))%L.
Proof.
intros.
rewrite (rngl_mul_comm Hic).
now apply (rngl_div_div Hon Hos Hiv).
Qed.

Theorem Rmult_div_r : ∀ x y, (y ≠ 0 → y * (x / y) = x)%L.
Proof.
intros * Hy.
rewrite (rngl_mul_div_assoc Hiv).
rewrite (rngl_mul_comm Hic).
now apply (rngl_mul_div Hi1).
Qed.

Theorem Rinv_div : ∀ x, (x⁻¹ = 1 / x)%L.
Proof.
intros.
symmetry.
apply (rngl_div_1_l Hon Hiv).
Qed.

Theorem nonneg_plus_sqr : ∀ x y, (0 ≤ x² + y²)%L.
Proof.
intros.
apply (rngl_add_squ_nonneg Hon Hos Hiq Hor).
Qed.

Definition Rsignp x := (if Rle_dec 0 x then 1 else -1)%L.
Definition Rsign x := (if Req_dec x 0 then 0 else Rsignp x)%L.

Arguments Rsign x%_L.

Theorem Rsignp_of_pos : ∀ x, (0 ≤ x → Rsignp x = 1)%L.
Proof.
intros * Hx.
unfold Rsignp.
now destruct (Rle_dec 0 x).
Qed.

Theorem Rsignp_of_neg : ∀ x, (x < 0 → Rsignp x = -1)%L.
Proof.
intros * Hx.
unfold Rsignp.
apply rngl_nle_gt in Hx.
now destruct (Rle_dec 0 x).
Qed.

Theorem Rsign_of_pos : ∀ x, (0 < x → Rsign x = 1)%L.
Proof.
intros * Hx.
unfold Rsign, Rsignp.
destruct (Req_dec x 0) as [H | H]. {
  now subst; apply (rngl_lt_irrefl Hor) in Hx.
}
apply (rngl_lt_le_incl Hor) in Hx.
now destruct (Rle_dec 0 x).
Qed.

Theorem Rsign_of_neg : ∀ x, (x < 0 → Rsign x = -1)%L.
Proof.
intros * Hx.
unfold Rsign, Rsignp.
destruct (Req_dec x 0). {
  now subst; apply (rngl_lt_irrefl Hor) in Hx.
}
apply rngl_nle_gt in Hx.
now destruct (Rle_dec 0 x).
Qed.

Theorem Rsign_mul_distr : ∀ x y, Rsign (x * y) = (Rsign x * Rsign y)%L.
Proof.
intros.
unfold Rsign, Rsignp.
destruct (Req_dec (x * y) 0) as [Hxyz| Hxyz]. {
  symmetry.
  destruct (Req_dec x 0) as [Hx| Hx]; [ apply (rngl_mul_0_l Hos) | ].
  destruct (Req_dec y 0) as [Hy| Hy]; [ apply (rngl_mul_0_r Hos) | ].
  apply (rngl_integral Hos Hio) in Hxyz.
  now destruct Hxyz.
}
destruct (Req_dec x 0) as [Hxz| Hxz]. {
  now subst; rewrite (rngl_mul_0_l Hos) in Hxyz.
}
destruct (Req_dec y 0) as [Hyz| Hyz]. {
  now subst; rewrite (rngl_mul_0_r Hos) in Hxyz.
}
destruct (Rle_dec 0 (x * y)) as [Hxy| Hxy]. {
  destruct (Rle_dec 0 x) as [Hx| Hx]. {
    symmetry.
    destruct (Rle_dec 0 y) as [Hy| Hy]; [ apply (rngl_mul_1_l Hon) | ].
    apply (rngl_le_0_mul Hon Hop Hiq Hor) in Hxy.
    destruct Hxy as [| (H, _)]; [ easy | ].
    apply (rngl_le_antisymm Hor) in H; [ | easy ].
    now symmetry in H.
  }
  destruct (Rle_dec 0 y) as [Hy| Hy]. 2: {
    symmetry.
    apply (rngl_squ_opp_1 Hon Hop).
  }
  exfalso.
  apply Hx; clear Hx.
  apply (rngl_le_0_mul Hon Hop Hiq Hor) in Hxy.
  destruct Hxy as [| (_, H)]; [ easy | ].
  apply (rngl_le_antisymm Hor) in H; [ | easy ].
  now symmetry in H.
}
destruct (Rle_dec 0 x) as [Hx| Hx]. {
  destruct (Rle_dec 0 y) as [Hy| Hy]. 2: {
    now symmetry; apply (rngl_mul_1_l Hon).
  }
  exfalso.
  apply Hxy; clear Hxy.
  now apply (rngl_mul_nonneg_nonneg Hon Hos Hiq Hor).
} {
  destruct (Rle_dec 0 y) as [Hy| Hy]. {
    now symmetry; apply (rngl_mul_1_r Hon).
  }
  exfalso.
  apply Hxy; clear Hxy.
  apply (rngl_nle_gt_iff Hor) in Hx, Hy.
  apply (rngl_lt_le_incl Hor).
  now apply (rngl_mul_neg_neg Hon Hop Hiq Hor).
}
Qed.

Theorem Rneq_le_lt : ∀ x y, (x ≠ y → x ≤ y → x < y)%L.
Proof.
intros * Hnxy Hxy.
now apply (rngl_le_neq Hor).
Qed.

Theorem sqrt_diff_sqr_eq_0 : ∀ x y,
  (0 ≤ x ≤ y)%L
  → √ (y² - x²) = 0%L
  → x = y.
Proof.
intros * Hxy Hyx.
apply (eq_rl_sqrt_0 Hon Hos) in Hyx. {
  apply -> (rngl_sub_move_0_r Hop) in Hyx.
  symmetry in Hyx.
  apply (eq_rngl_squ_rngl_abs Hop Hor Hii _ _ (rngl_mul_comm Hic _ _)) in Hyx.
  rewrite (rngl_abs_nonneg_eq Hop Hor x) in Hyx; [ | easy ].
  rewrite (rngl_abs_nonneg_eq Hop Hor y) in Hyx; [ easy | ].
  now apply (rngl_le_trans Hor _ x).
}
apply (rngl_le_0_sub Hop Hor).
now apply (rngl_le_le_squ Hon Hop Hiq Hor).
Qed.

Definition Rediv_mod x y :=
  let k :=
    match Rcase_abs y with
    | left _ => (- Int_part (x / - y))%Z
    | right _ => Int_part (x / y)
    end
  in
  (k, x - IZR k * y)%L.

Definition Rediv x y := fst (Rediv_mod x y).
Definition Rmod x y := snd (Rediv_mod x y).

Arguments Rediv (x y)%_L.
Arguments Rmod (x y)%_L.

Notation "x '//' y" := (Rediv x y) (at level 40).
Notation "x 'rmod' y" := (Rmod x y) (at level 40).

Theorem Rmod_interv : ∀ x y, (0 < y → 0 ≤ x rmod y < y)%L.
Proof.
intros * Hy.
unfold Rmod, Rediv_mod, snd.
destruct (Rcase_abs y) as [Hya| Hya]. {
  now apply (rngl_lt_asymm Hor) in Hy.
}
split. {
  apply (rngl_mul_le_mono_pos_r Hon Hop Hiq Hor _ _ (y⁻¹)). {
    now apply (rngl_inv_pos Hon Hop Hiv Hor).
  }
  rewrite (rngl_mul_0_l Hos).
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_inv_diag_r Hon Hiv). 2: {
    now symmetry; apply (rngl_lt_neq Hor).
  }
  rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_mul_inv_r Hiv).
  apply (rngl_le_0_sub Hop Hor).
  progress unfold Int_part.
  remember (z_int_part _) as z eqn:H; clear H.
  destruct z as (z, Hz).
  easy.
} {
  apply (rngl_mul_lt_mono_pos_r Hon Hop Hiq Hor (y⁻¹)). {
    now apply (rngl_inv_pos Hon Hop Hiv Hor).
  }
  rewrite (rngl_mul_sub_distr_r Hop).
  rewrite <- rngl_mul_assoc.
  rewrite (rngl_mul_inv_diag_r Hon Hiv). 2: {
    now symmetry; apply (rngl_lt_neq Hor).
  }
  rewrite (rngl_mul_1_r Hon).
  rewrite (rngl_mul_inv_r Hiv).
  apply (rngl_lt_sub_lt_add_l Hop Hor).
  rewrite <- rngl_of_Z_1.
  rewrite <- rngl_of_Z_add.
  progress unfold Int_part.
  remember (z_int_part _) as z eqn:H; clear H.
  destruct z as (z, Hz).
  easy.
}
Qed.

Theorem Rmod_from_ediv : ∀ x y, x rmod y = (x - IZR (x // y) * y)%L.
Proof.
intros.
unfold Rmod, Rediv, fst, snd.
remember (Rediv_mod x y) as rdm eqn:Hrdm.
symmetry in Hrdm.
destruct rdm as (q, r).
unfold Rediv_mod in Hrdm.
destruct (Rlt_dec y 0) as [Hy| Hy]. {
  remember Z.sub as f.
  injection Hrdm; clear Hrdm; intros Hr Hq; subst f.
  now rewrite Hq in Hr.
} {
  remember Z.sub as f.
  injection Hrdm; clear Hrdm; intros Hr Hq; subst f.
  now rewrite Hq in Hr.
}
Qed.

Theorem base_Int_part :
  ∀ a, (rngl_of_Z (Int_part a) ≤ a)%L ∧ (-1 < rngl_of_Z (Int_part a) - a)%L.
Proof.
intros.
split. {
  progress unfold Int_part.
  remember (z_int_part _) as z eqn:H; clear H.
  destruct z as (z, Hz).
  easy.
} {
  progress unfold Int_part.
  remember (z_int_part _) as z eqn:H; clear H.
  destruct z as (z, Hz).
  apply (rngl_lt_add_lt_sub_r Hop Hor).
  rewrite (rngl_add_opp_l Hop).
  apply (rngl_lt_sub_lt_add_r Hop Hor).
  rewrite <- rngl_of_Z_1.
  now rewrite <- rngl_of_Z_add.
}
Qed.

Theorem Int_part_opp_rngl_of_pos : ∀ p, Int_part (- rngl_of_pos p) = Z.neg p.
Proof.
intros.
progress unfold Int_part.
remember (z_int_part _) as z eqn:H; clear H.
destruct z as (z, Hz).
destruct z as [| q| q]. {
  exfalso.
  cbn in Hz.
  destruct Hz as (Hz, _).
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hz.
  apply rngl_nlt_ge in Hz.
  apply Hz; clear Hz.
  apply rngl_of_pos_pos.
} {
  exfalso.
  cbn in Hz.
  destruct Hz as (Hz, _).
  apply rngl_nlt_ge in Hz.
  apply Hz; clear Hz.
  apply (rngl_le_lt_trans Hor _ 0); [ | apply rngl_of_pos_pos ].
  apply (rngl_opp_nonpos_nonneg Hop Hor).
  apply rngl_of_pos_nonneg.
} {
  f_equal.
  rewrite rngl_of_Z_add in Hz.
  rewrite rngl_of_Z_1 in Hz.
  cbn in Hz.
  destruct Hz as (H1, H2).
  apply (rngl_opp_le_compat Hop Hor) in H1.
  rewrite (rngl_add_opp_l Hop) in H2.
  rewrite <- (rngl_opp_sub_distr Hop) in H2.
  apply (rngl_opp_lt_compat Hop Hor) in H2.
  apply (rngl_lt_sub_lt_add_r Hop Hor) in H2.
  apply (rngl_of_pos_prop2 (rngl_of_pos p + 1)%L). {
    rewrite rngl_of_pos_add, rngl_of_pos_1.
    split; [ easy | ].
    now apply (rngl_add_le_mono_r Hos Hor).
  }
  rewrite rngl_of_pos_add, rngl_of_pos_1.
  split; [ | pauto ].
  apply (rngl_lt_add_r Hos Hor).
  apply (rngl_0_lt_1 Hon Hos Hiq Hc1 Hor).
}
Qed.

Theorem Int_part_opp_of_Int :
  ∀ x,
  x = rngl_of_Z (Int_part x)
  → Int_part (- x) = (- Int_part x)%Z.
Proof.
intros * Hx.
progress unfold Int_part in Hx.
progress unfold Int_part.
remember (z_int_part _) as y eqn:H; clear H.
destruct y as (y, Hy).
remember (z_int_part _) as z eqn:H; clear H.
destruct z as (z, Hz).
rewrite Hx in Hz.
rewrite <- rngl_of_Z_opp in Hz.
apply Int_part_interv in Hz; subst z.
apply Int_part_IZR.
Qed.

Theorem Int_part_opp_of_not_Int :
  ∀ x,
  x ≠ rngl_of_Z (Int_part x)
  → Int_part (-x) = (- Int_part x - 1)%Z.
Proof.
intros * Hx.
progress unfold Int_part in Hx.
progress unfold Int_part.
remember (z_int_part _) as y eqn:H; clear H.
destruct y as (y, Hy).
remember (z_int_part _) as z eqn:H; clear H.
destruct z as (z, Hz).
apply (Int_part_prop _ (- (z + 1))) in Hy. {
  subst y; symmetry.
  rewrite Z.opp_involutive.
  apply Z.add_simpl_r.
}
rewrite (Z.add_comm (- _) 1).
rewrite Z.add_opp_r.
rewrite Z.add_comm.
rewrite Z.sub_add_distr.
rewrite Z.add_comm.
rewrite Z.sub_diag.
rewrite (Z.sub_0_l z).
do 2 rewrite rngl_of_Z_opp.
destruct Hz as (H1, H2).
apply (rngl_opp_le_compat Hop Hor) in H1.
apply (rngl_opp_lt_compat Hop Hor) in H2.
rewrite (rngl_opp_involutive Hop) in H1, H2.
split; [ now apply (rngl_lt_le_incl Hor) | ].
apply (rngl_le_neq Hor).
split; [ easy | ].
intros H; subst x.
apply (rngl_opp_lt_compat Hop Hor) in H2.
clear H1 H2.
apply Int_part_interv in Hy.
apply Hx; clear Hx.
subst y; symmetry.
destruct z as [| p| p]; cbn. {
  now rewrite (rngl_opp_0 Hop), Int_part_0.
} {
  rewrite rngl_of_Z_Int_part.
  destruct (rngl_le_dec Hor 0 (- _)) as [Hzp| Hzp]. {
    exfalso.
    apply (rngl_opp_le_compat Hop Hor) in Hzp.
    rewrite (rngl_opp_involutive Hop) in Hzp.
    rewrite (rngl_opp_0 Hop) in Hzp.
    apply rngl_nlt_ge in Hzp.
    apply Hzp, rngl_of_pos_pos.
  }
  clear Hzp.
  f_equal.
  progress unfold nat_Int_part.
  now rewrite Int_part_opp_rngl_of_pos.
} {
  rewrite (rngl_opp_involutive Hop).
  now rewrite Int_part_rngl_of_pos.
}
Qed.

Theorem Int_part_opp : ∀ x,
  Int_part (- x) =
    (- Int_part x - if Req_dec x (rngl_of_Z (Int_part x)) then 0 else 1)%Z.
Proof.
intros.
destruct (Req_dec x (rngl_of_Z (Int_part x))) as [Hx| Hx]. {
  rewrite Z.sub_0_r.
  now apply Int_part_opp_of_Int.
} {
  now apply Int_part_opp_of_not_Int.
}
Qed.

Theorem Int_part_add :
  ∀ a b n,
  b = rngl_of_Z n
  → Int_part (a + b) = (Int_part a + n)%Z.
Proof.
intros * Hbn.
progress unfold Int_part.
remember (z_int_part _) as y eqn:H; clear H.
destruct y as (y, Hy).
remember (z_int_part _) as z eqn:H; clear H.
destruct z as (z, Hz).
move y before n; move z before y.
apply (Int_part_prop (a + b))%L; [ easy | ].
rewrite Z.add_shuffle0.
do 2 rewrite rngl_of_Z_add.
rewrite <- Hbn.
split.
now apply (rngl_add_le_mono_r Hos Hor).
now apply (rngl_add_lt_mono_r Hos Hor).
Qed.

Theorem Rediv_add_1 :
  ∀ x y,
  y ≠ 0%L
  → (x + y)%L // y = (x // y + 1)%Z.
Proof.
intros * Hyz.
unfold Rediv, Rediv_mod, fst.
destruct (Rcase_abs y) as [Hy| Hy]. {
  do 2 rewrite (Ropp_div_r _ _ Hyz).
  rewrite (rngl_div_add_distr_r Hiv).
  rewrite (rngl_div_diag Hon Hiq); [ | easy ].
  do 2 rewrite Int_part_opp.
  rewrite (Int_part_add _ _ 1); [ | symmetry; apply rngl_of_Z_1 ].
  rewrite rngl_of_Z_add, rngl_of_Z_1.
  destruct (Req_dec _ _) as [Hxy1| Hxy1]. {
    apply (rngl_add_cancel_r Hos) in Hxy1.
    rewrite Z.sub_0_r, Z.opp_involutive.
    destruct (Req_dec _ _) as [H| ]; [ clear H | easy ].
    rewrite Z.sub_0_r; f_equal.
    symmetry; apply Z.opp_involutive.
  }
  rewrite <- Z.opp_sub_distr.
  progress f_equal.
  rewrite Z.opp_add_distr.
  rewrite Z.add_opp_r.
  progress f_equal.
  progress f_equal.
  symmetry.
  destruct (Req_dec _ _) as [H| ]; [ | easy ].
  exfalso.
  apply Hxy1; clear Hxy1.
  now f_equal.
} {
  apply (rngl_nlt_ge_iff Hor) in Hy.
  rewrite (rngl_div_add_distr_r Hiv).
  rewrite (rngl_div_diag Hon Hiq); [ | easy ].
  rewrite (Int_part_add _ _ 1); [ easy | symmetry; apply rngl_of_Z_1 ].
}
Qed.

Theorem Rediv_opp_r : ∀ x y, y ≠ 0%L → x // - y = (- (x // y))%Z.
Proof.
intros * Hyz.
unfold "//", fst, Rediv_mod.
destruct (Rcase_abs (- y)) as [Hy| Hy]. {
  rewrite (rngl_opp_involutive Hop).
  destruct (Rcase_abs y) as [Hzy| Hzy]; [ | easy ].
  exfalso.
  apply (rngl_opp_neg_pos Hop Hor) in Hy.
  now apply (rngl_lt_asymm Hor) in Hy.
} {
  destruct (Rcase_abs y) as [Hzy| Hzy]; [ now rewrite Z.opp_involutive | ].
  apply (rngl_opp_nonneg_nonpos Hop Hor) in Hy.
  now apply (rngl_le_antisymm Hor) in Hzy.
}
Qed.

Theorem Rediv_add_nat : ∀ x y n,
  y ≠ 0%L
  → (x + INR n * y) // y = (x // y + Z.of_nat n)%Z.
Proof.
intros * Hyz.
progress unfold INR.
induction n. {
  now cbn; rewrite (rngl_mul_0_l Hos), rngl_add_0_r, Z.add_0_r.
}
rewrite rngl_of_nat_succ, (rngl_add_comm 1).
rewrite rngl_mul_add_distr_r, (rngl_mul_1_l Hon), rngl_add_assoc.
rewrite Rediv_add_1; [ | easy ].
rewrite IHn, <- Z.add_assoc.
progress f_equal.
rewrite <- Nat.add_1_r.
now rewrite Nat2Z.inj_add.
Qed.

Theorem IZN : ∀ n, (0 <= n)%Z → ∃ m, n = Z.of_nat m.
Proof.
intros * Hn.
destruct n as [| p| ]; [ now exists 0 | | easy ].
exists (Pos.to_nat p).
symmetry.
apply positive_nat_Z.
Qed.

Theorem Rediv_add_Z : ∀ x y a,
  y ≠ 0%L
  → (x + IZR a * y) // y = (x // y + a)%Z.
Proof.
intros * Hyz.
destruct (Z_le_dec 0 a) as [Ha| Ha]. {
  progress unfold IZR.
  apply IZN in Ha.
  destruct Ha as (n, Hn); subst a.
  rewrite rngl_of_Z_of_nat.
  now apply Rediv_add_nat.
}
apply Z.nle_gt in Ha.
remember (- a)%Z as b eqn:Hb.
apply Z.eq_opp_l in Hb; subst a.
apply Z.opp_neg_pos in Ha.
rename b into a.
apply Z.lt_le_incl in Ha.
apply IZN in Ha.
destruct Ha as (n, Hn); subst a.
rewrite rngl_of_Z_opp.
rewrite rngl_of_Z_of_nat.
rewrite (rngl_mul_opp_l Hop), <- (rngl_mul_opp_r Hop).
symmetry; rewrite <- Z.opp_involutive; symmetry.
rewrite <- Rediv_opp_r; [ | easy ].
(**)
rewrite Rediv_add_nat. 2: {
  intros H.
  apply (f_equal rngl_opp) in H.
  now rewrite (rngl_opp_involutive Hop), (rngl_opp_0 Hop) in H.
}
rewrite Z.opp_add_distr.
rewrite Rediv_opp_r; [ | easy ].
now rewrite Z.opp_involutive.
Qed.

Theorem Rmod_add_Z : ∀ x y a,
  y ≠ 0%L
  → (x + IZR a * y) rmod y = x rmod y.
Proof.
intros * Hy.
rewrite Rmod_from_ediv.
rewrite Rediv_add_Z; [ | easy ].
rewrite rngl_of_Z_add.
rewrite rngl_mul_add_distr_r.
rewrite Rmod_from_ediv.
progress unfold IZR.
rewrite (rngl_sub_add_distr Hos).
rewrite (rngl_sub_sub_swap Hop).
progress f_equal.
apply (rngl_add_sub Hos).
Qed.

Theorem Rmod_0_l : ∀ x, 0 rmod x = 0%L.
Proof.
intros x.
destruct (rngl_eq_dec Heo x 0) as [Hzx| Hzx]. {
  subst x; rewrite Rmod_from_ediv.
  rewrite (rngl_mul_0_r Hos).
  apply (rngl_sub_diag Hos).
}
unfold Rmod, snd, Rediv_mod.
rewrite (rngl_div_0_l Hos Hi1). 2: {
  intros H.
  apply (f_equal rngl_opp) in H.
  now rewrite (rngl_opp_involutive Hop), (rngl_opp_0 Hop) in H.
}
rewrite Int_part_0, Z.opp_0.
destruct (Rcase_abs x). {
  cbn; rewrite (rngl_mul_0_l Hos).
  apply (rngl_sub_diag Hos).
}
rewrite (rngl_div_0_l Hos Hi1); [ | easy ].
rewrite Int_part_0.
cbn; rewrite (rngl_mul_0_l Hos).
apply (rngl_sub_diag Hos).
Qed.

Theorem Rmod_mul_same : ∀ x a, (IZR a * x) rmod x = 0%L.
Proof.
intros.
destruct (Req_dec x 0) as [Hx| Hx]. {
  rewrite Hx, (rngl_mul_0_r Hos); apply Rmod_0_l.
}
specialize (Rmod_add_Z 0%L x a Hx) as H.
rewrite rngl_add_0_l in H; rewrite H.
apply Rmod_0_l.
Qed.

Theorem Rmod_small : ∀ x y, (0 ≤ x < y)%L → x rmod y = x.
Proof.
intros * (Hx, Hxy).
unfold Rmod, snd, Rediv_mod.
destruct (Rcase_abs y) as [Hyn| Hyp]. {
...
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
