(* Banach-Tarski paradox. *)

Require Import Utf8 List Relations NPeano Wf_nat.
Import ListNotations.
Require Import Reals Psatz.

Require Import Misc Words Normalize Reverse.

Notation "'ℝ'" := R.
Notation "'ℤ'" := Z.
Notation "'ℕ'" := nat.

Notation "x '≤' y" := (le x y) : nat_scope.

Notation "'√'" := sqrt.
Notation "x '≤' y" := (Rle x y) : R_scope.
Notation "x '≤' y '<' z" := (Rle x y ∧ Rlt y z)
 (at level 70, y at next level) : R_scope.
Notation "x '≤' y '≤' z" := (Rle x y ∧ Rle y z)
 (at level 70, y at next level) : R_scope.
Notation "x '<' y '≤' z" := (Rlt x y ∧ Rle y z)
 (at level 70, y at next level) : R_scope.

Open Scope R_scope.

Theorem fold_Rminus : ∀ x y, x + - y = x - y.
Proof. intros. now fold (Rminus x y). Qed.

Theorem fold_Rdiv : ∀ x y, x * / y = x / y.
Proof. intros; now fold (Rdiv x y). Qed.

Theorem fold_Rsqr : ∀ x, x * x = x².
Proof. intros; now fold (Rsqr x). Qed.

Theorem Rmult_div : ∀ x y z, x * y / z = x / z * y.
Proof. intros; lra. Qed.

Theorem Rdiv_mult : ∀ x y z, x * (y / z) = x * y / z.
Proof. intros; lra. Qed.

Theorem Rminus_plus_distr : ∀ x y z, x - (y + z) = x - y - z.
Proof. intros; lra. Qed.

Theorem Rminus_opp : ∀ x y, x - - y = x + y.
Proof. intros; lra. Qed.

Theorem Ropp_div_r : ∀ x y, y ≠ 0 → x / - y = - (x / y).
Proof.
intros * Hy.
unfold Rdiv.
rewrite <- Ropp_inv_permute; [ | easy ].
now rewrite <- Ropp_mult_distr_r.
Qed.

Theorem Rmult_div_same : ∀ x y, y ≠ 0 → x / y * y = x.
Proof.
intros * Hy.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l; [ lra | easy ].
Qed.

Theorem Rplus_shuffle0 : ∀ n m p : ℝ, n + m + p = n + p + m.
Proof.
intros.
rewrite Rplus_comm, <- Rplus_assoc.
f_equal; apply Rplus_comm.
Qed.

Theorem Rmult_shuffle0 : ∀ n m p : ℝ, n * m * p = n * p * m.
Proof.
intros.
rewrite Rmult_comm, <- Rmult_assoc.
f_equal; apply Rmult_comm.
Qed.

Theorem Rdiv_mult_simpl_l : ∀ x y z,
  x ≠ 0
  → z ≠ 0
  → (x * y) / (x * z) = y / z.
Proof.
intros * Hx Hz.
unfold Rdiv.
rewrite Rinv_mult_distr; [ | easy | easy ].
rewrite <- Rmult_assoc.
f_equal; rewrite Rmult_shuffle0.
rewrite Rinv_r; [ | easy ].
now rewrite Rmult_1_l.
Qed.

Theorem Rdiv_mult_simpl_r : ∀ x y z,
  y ≠ 0
  → z ≠ 0
  → (x * z) / (y * z) = x / y.
Proof.
intros * Hy Hz.
specialize (Rdiv_mult_simpl_l z x y Hz Hy) as H.
rewrite <- H.
f_equal; lra.
Qed.

Theorem Req_dec : ∀ x y : ℝ, { x = y } + { x ≠ y }.
Proof.
intros x y.
destruct (Rle_dec x y) as [H₁| H₁].
 destruct (Rle_dec y x) as [H₂| H₂].
  left; now apply Rle_antisym.

  right; intros H; subst y; apply H₂, Rle_refl.

 right; intros H; subst y.
 apply H₁, Rle_refl.
Qed.

Theorem Rmult5_sqrt2_sqrt5 : ∀ a b c d, 0 <= b →
  a * √ b * c * d * √ b = a * b * c * d.
Proof.
intros a b c d Hb.
rewrite Rmult_comm, <- Rmult_assoc; f_equal.
rewrite <- Rmult_assoc; f_equal.
rewrite Rmult_comm, Rmult_assoc; f_equal.
now apply sqrt_sqrt.
Qed.

Theorem Rdiv_0_l : ∀ x, 0 / x = 0.
Proof.
intros x; unfold Rdiv; apply Rmult_0_l.
Qed.

Theorem Rdiv_1_r : ∀ x, x / 1 = x.
Proof. intros x; lra. Qed.

Theorem Rdiv_same : ∀ x, x ≠ 0 → x / x = 1.
Proof.
intros.
unfold Rdiv.
now rewrite Rinv_r.
Qed.

Theorem Int_part_close_to_1 : ∀ r n,
  INR n / INR (n + 1) <= r < 1
  → Int_part (r * (INR (n + 1))) = Z.of_nat n.
Proof.
intros * (Hnr, Hr1).
apply Rmult_le_compat_r with (r := INR (n + 1)) in Hnr; [ | apply pos_INR ].
rewrite <- Rmult_div in Hnr.
unfold Rdiv in Hnr.
rewrite Rmult_assoc in Hnr.
rewrite Rinv_r in Hnr; [ | now apply not_0_INR; rewrite Nat.add_comm ].
rewrite Rmult_1_r in Hnr.
apply Rmult_lt_compat_r with (r := INR (n + 1)) in Hr1. 2: {
 rewrite plus_INR; simpl.
 apply Rplus_le_lt_0_compat; [ apply pos_INR | lra ].
}

 rewrite Rmult_1_l in Hr1.
 remember (r * INR (n + 1)) as x eqn:Hx.
 rewrite plus_INR in Hr1; simpl in Hr1.
 rewrite INR_IZR_INZ in Hnr.
 rewrite INR_IZR_INZ in Hr1.
 unfold Int_part.
 apply Z.add_cancel_r with (p := 1%Z).
 rewrite Z.sub_add; symmetry.
 apply tech_up; [ now rewrite plus_IZR | ].
 rewrite plus_IZR; simpl.
 now apply Rplus_le_compat_r.
Qed.

Theorem Int_part_small : ∀ x, 0 <= x < 1 → Int_part x = 0%Z.
Proof.
intros * Hx.
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
destruct (Z_le_dec 0 z) as [Hz| Hz].
 apply Z2Nat.id in Hz.
 rewrite <- Hz at 1.
 rewrite <- INR_IZR_INZ.
 now rewrite Int_part_INR.

 apply Z.nle_gt in Hz.
 destruct z as [| p| p]; [ easy | easy | ].
 unfold IZR.
 replace (- IPR p) with (0 - IPR p) by lra; simpl.
 rewrite Rminus_Int_part1.
  rewrite Int_part_small; [ | lra ].
  rewrite <- INR_IPR.
  rewrite Int_part_INR.
  rewrite positive_nat_Z.
  now unfold Zminus.





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
rewrite Rminus_Int_part1 in H.
 rewrite Int_part_IZR in H.
 now apply -> Z.sub_move_0_r in H.

 rewrite frac_part_IZR.
 apply Rle_ge, frac_part_interv.
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
intros; split.
 intros Hxy.
 unfold Rabs in Hxy.
 destruct (Rcase_abs x); lra.

 intros (Hyx, Hxy).
 unfold Rabs.
 destruct (Rcase_abs x); [ lra | easy ].
Qed.

Theorem Rabs_le : ∀ x y, Rabs x ≤ y ↔ - y ≤ x ≤ y.
Proof.
intros; split.
 intros Hxy.
 unfold Rabs in Hxy.
 destruct (Rcase_abs x); lra.

 intros (Hyx, Hxy).
 unfold Rabs.
 destruct (Rcase_abs x); [ lra | easy ].
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

Theorem Rdiv_div : ∀ x y z, y ≠ 0 → z ≠ 0 → x / y / z = x / (y * z).
Proof.
intros * Hy Hz.
unfold Rdiv.
rewrite Rinv_mult_distr; [ lra | easy | easy ].
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
destruct (Req_dec (x * y) 0) as [Hxyz| Hxyz].
 destruct (Req_dec x 0) as [Hx| Hx]; [ lra | ].
 destruct (Req_dec y 0) as [Hy| Hy]; [ lra | ].
 apply Rmult_integral in Hxyz; lra.

 destruct (Req_dec x 0) as [Hxz| Hxz]; [ rewrite Hxz in Hxyz; lra | ].
 destruct (Req_dec y 0) as [Hyz| Hyz]; [ rewrite Hyz in Hxyz; lra | ].
 destruct (Rle_dec 0 (x * y)) as [Hxy| Hxy].
  destruct (Rle_dec 0 x) as [Hx| Hx].
   destruct (Rle_dec 0 y) as [Hy| Hy]; [ lra | exfalso ].
   apply Hy; clear Hy.
   apply Rmult_le_reg_l with (r := x); [ lra | ].
   now rewrite Rmult_0_r.

   destruct (Rle_dec 0 y) as [Hy| Hy]; [ exfalso | lra ].
   apply Hx; clear Hx.
   apply Rmult_le_reg_r with (r := y); [ lra | ].
   now rewrite Rmult_0_l.

  destruct (Rle_dec 0 x) as [Hx| Hx].
   destruct (Rle_dec 0 y) as [Hy| Hy]; [ exfalso | lra ].
   apply Hxy; clear Hxy.
   now apply Rmult_le_pos.

   destruct (Rle_dec 0 y) as [Hy| Hy]; [ lra | exfalso ].
   apply Hxy; clear Hxy.
   rewrite <- Rmult_opp_opp.
   apply Rmult_le_pos; lra.
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
split.
 apply Rmult_le_reg_r with (r := / y); [ now apply Rinv_0_lt_compat | ].
 rewrite Rmult_0_l, fold_Rdiv, Rdiv_minus_distr, Rmult_div.
 rewrite Rmult_div_same; [ | lra ].
 specialize (base_Int_part (x / y)); lra.

 apply Rmult_lt_reg_r with (r := / y); [ now apply Rinv_0_lt_compat | ].
 rewrite fold_Rdiv, fold_Rdiv, Rdiv_minus_distr, Rmult_div.
 rewrite Rmult_div_same; [ | lra ].
 rewrite Rdiv_same; [ | lra ].
 specialize (base_Int_part (x / y)); lra.
Qed.

Theorem Rmod_from_ediv : ∀ x y, x rmod y = x - IZR (x // y) * y.
Proof.
intros.
unfold Rmod, Rediv, fst, snd.
remember (Rediv_mod x y) as rdm eqn:Hrdm.
symmetry in Hrdm.
destruct rdm as (q, r).
unfold Rediv_mod in Hrdm.
destruct (Rcase_abs y) as [Hy| Hy].
 remember Z.sub as f.
 injection Hrdm; clear Hrdm; intros Hr Hq; subst f.
 now rewrite Hq in Hr.

 remember Z.sub as f.
 injection Hrdm; clear Hrdm; intros Hr Hq; subst f.
 now rewrite Hq in Hr.
Qed.

Theorem Int_part_neg : ∀ x,
  Int_part (- x) =
    (- Int_part x - if Req_dec x (IZR (Int_part x)) then 0 else 1)%Z.
Proof.
intros.
destruct (Req_dec x (IZR (Int_part x))) as [Hx| Hx].
 rewrite Hx at 1.
 now rewrite <- opp_IZR, Int_part_IZR, Z.sub_0_r.

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
destruct (Rcase_abs y) as [Hy| Hy].
 unfold Rdiv.
 rewrite <- Ropp_inv_permute; [ | lra ].
 rewrite <- Ropp_mult_distr_r.
 rewrite Rmult_plus_distr_r.
 rewrite Rinv_r; [ | lra ].
 rewrite Ropp_plus_distr.
 rewrite fold_Rminus.
 rewrite <- Ropp_mult_distr_r.
 ring_simplify.
 rewrite Rminus_Int_part1.
  rewrite Z.opp_sub_distr.
  replace 1 with (IZR 1) by lra.
  now rewrite Int_part_IZR.

  replace 1 with (IZR 1) by lra.
  rewrite frac_part_IZR.
  specialize (frac_part_interv (- (x * / y))) as (Hn, Hp); lra.

 rewrite Rdiv_plus_distr.
 rewrite Rdiv_same; [ | easy ].
 rewrite plus_Int_part2.
  replace 1 with (IZR 1) by lra.
  now rewrite Int_part_IZR.

  replace 1 with (IZR 1) at 1 by lra.
  rewrite frac_part_IZR, Rplus_0_r.
  apply frac_part_interv.
Qed.

Theorem Rediv_opp_r : ∀ x y, y ≠ 0 → x // - y = (- (x // y))%Z.
Proof.
intros * Hyz.
unfold "//", fst, Rediv_mod.
destruct (Rcase_abs (- y)) as [Hy| Hy].
 destruct (Rcase_abs y); [ lra | now rewrite Ropp_involutive ].

 destruct (Rcase_abs y); [ now rewrite Z.opp_involutive | lra ].
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
destruct (Z_le_dec 0 a) as [Ha| Ha].
 apply IZN in Ha.
 destruct Ha as (n, Hn); subst a.
 rewrite <- INR_IZR_INZ.
 now apply Rediv_add_nat.

 remember (- a)%Z as b eqn:Hb.
 assert (a = (- b)%Z) by lia; subst a; clear Hb.
 rename b into a.
 assert (Hb : (0 < a)%Z) by lia; clear Ha; rename Hb into Ha.
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
destruct (Req_dec x 0) as [Hx| Hx].
 rewrite Hx, Rmult_0_r; apply Rmod_0_l.

 specialize (Rmod_add_Z 0 x a Hx) as H.
 rewrite Rplus_0_l in H; rewrite H.
 apply Rmod_0_l.
Qed.

Theorem Rmod_small : ∀ x y, 0 ≤ x < y → x rmod y = x.
Proof.
intros * (Hx, Hxy).
unfold Rmod, snd, Rediv_mod.
destruct (Rcase_abs y) as [Hyn| Hyp]; [ lra | ].
assert (H : 0 ≤ x / y < 1).
 split.
  apply Rmult_le_reg_r with (r := y); [ lra | ].
  rewrite Rmult_0_l, Rmult_div_same; [ easy | lra ].

  apply Rmult_lt_reg_r with (r := y); [ lra | ].
  rewrite Rmult_1_l, Rmult_div_same; [ easy | lra ].

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
rewrite Ropp_div_r; [ | lra ].
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
do 2 rewrite double.
destruct (Rlt_dec (frac_part x) (1 / 2)) as [Hx| Hx].
 rewrite Rminus_0_r; apply plus_frac_part2; lra.

 apply plus_frac_part1; lra.
Qed.

Theorem Int_part_double : ∀ x,
  Int_part (2 * x) =
    (2 * Int_part x + if Rlt_dec (frac_part x) (1 / 2) then 0 else 1)%Z.
Proof.
intros.
rewrite double.
destruct (Rlt_dec (frac_part x) (1 / 2)) as [Hx| Hx].
 rewrite plus_Int_part2; [ lia | lra ].

 rewrite plus_Int_part1; [ lia | lra ].
Qed.

Theorem pow_1_abs_nat_odd : ∀ n, (-1) ^ Z.abs_nat (2 * n + 1) = -1.
Proof.
intros n.
destruct n as [| n| n].
 rewrite Z.mul_0_r, Z.add_0_l.
 simpl (Z.abs_nat _); unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).
 now rewrite pow_1.

 rewrite Zabs2Nat.inj_add; [ | lia | lia ].
 rewrite Zabs2Nat.inj_mul.
 simpl (Z.abs_nat _); unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).
 now rewrite Nat.add_1_r, pow_1_odd.

 replace (Z.neg n) with (- Z.pos n)%Z by apply Pos2Z.opp_pos.
 rewrite <- Zopp_mult_distr_r, <- Z.opp_sub_distr.
 rewrite <- Zabs_N_nat, Zabs2N.inj_opp, Zabs_N_nat.
 rewrite Zabs2Nat.inj_sub; [ | lia ].
 simpl (Z.abs_nat 1); unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).
 rewrite <- Rpow_div_sub; [ | lra | lia ].
 rewrite pow_1, Zabs2Nat.inj_mul.
 simpl (Z.abs_nat 2); unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).



 rewrite pow_1_even; lra.

Qed.

Theorem Rdiv_mod : ∀ x y, y ≠ 0 → x = y * IZR (x // y) + x rmod y.
Proof.
intros x y Hy.
rewrite Rmod_from_ediv.
lra.
Qed.
