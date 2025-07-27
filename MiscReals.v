(* Banach-Tarski paradox. *)

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

Definition Int_part (x : T) :=
  let (n, a) := int_part Hon Hop Hc1 Hor Har x in
  if rngl_le_dec Hor 0 x then Z.of_nat n else (- Z.of_nat n)%Z.

Arguments Int_part x%_L.

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
...
assert (INR 0 / INR (0 + 1) <= x < 1) by (now simpl; lra).
pose proof Int_part_close_to_1 x 0 H as H1.
now simpl in H1; rewrite Rmult_1_r in H1.
Qed.

Theorem frac_part_small : ∀ x, 0 <= x < 1 → frac_part x = x.
Proof.
intros * Hx.
unfold frac_part.
rewrite Int_part_small; [ lra | easy ].
Qed.

Theorem pow_INR : ∀ n k, INR (n ^ k) = INR n ^ k.
Proof.
intros.
induction k; [ easy | ].
simpl; rewrite mult_INR.
now rewrite IHk.
Qed.

Theorem frac_part_INR : ∀ n, frac_part (INR n) = 0.
Proof.
intros.
unfold frac_part.
rewrite Int_part_INR.
now rewrite <- INR_IZR_INZ, Rminus_diag_eq.
Qed.

Theorem Int_part_IZR : ∀ z, Int_part (IZR z) = z.
Proof.
intros.
destruct (Z_le_dec 0 z) as [Hz| Hz]. {
  apply Z2Nat.id in Hz.
  rewrite <- Hz at 1.
  rewrite <- INR_IZR_INZ.
  now rewrite Int_part_INR.
}
apply Z.nle_gt in Hz.
destruct z as [| p| p]; [ easy | easy | ].
unfold IZR.
replace (- IPR p) with (0 - IPR p) by lra.
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
