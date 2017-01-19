(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List Relations NPeano Wf_nat.
Import ListNotations.
Require Import Reals Psatz.

Require Import Misc Words Normalize Reverse.

Notation "'ℝ'" := R.
Notation "'ℤ'" := Z.
Notation "'ℕ'" := nat.

Notation "'√'" := sqrt.
Notation "x '≤' y" := (Rle x y) : R_scope.
Notation "x '≤' y '<' z" := (Rle x y ∧ Rlt y z)
 (at level 70, y at next level) : R_scope.
Notation "x '≤' y '≤' z" := (Rle x y ∧ Rle y z)
 (at level 70, y at next level) : R_scope.

Theorem fold_Rminus : ∀ x y, (x + - y = x - y)%R.
Proof. intros. now fold (Rminus x y). Qed.

Theorem fold_Rdiv : ∀ x y, (x * / y = x / y)%R.
Proof. intros; now fold (Rdiv x y). Qed.

Theorem fold_Rsqr : ∀ x, (x * x = x²)%R.
Proof. intros; now fold (Rsqr x). Qed.

Theorem Rmult_div : ∀ x y z, (x * y / z = x / z * y)%R.
Proof. intros; lra. Qed.

Theorem Rplus_shuffle0 : ∀ n m p : ℝ, (n + m + p)%R = (n + p + m)%R.
Proof.
intros.
rewrite Rplus_comm, <- Rplus_assoc.
f_equal; apply Rplus_comm.
Qed.

Theorem Rmult_shuffle0 : ∀ n m p : ℝ, (n * m * p)%R = (n * p * m)%R.
Proof.
intros.
rewrite Rmult_comm, <- Rmult_assoc.
f_equal; apply Rmult_comm.
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

Theorem Rmult5_sqrt2_sqrt5 : ∀ a b c d, (0 <= b)%R →
  (a * √ b * c * d * √ b)%R = (a * b * c * d)%R.
Proof.
intros a b c d Hb.
rewrite Rmult_comm, <- Rmult_assoc; f_equal.
rewrite <- Rmult_assoc; f_equal.
rewrite Rmult_comm, Rmult_assoc; f_equal.
now apply sqrt_sqrt.
Qed.

Theorem Rdiv_0_l : ∀ x, (0 / x = 0)%R.
Proof.
intros x; unfold Rdiv; apply Rmult_0_l.
Qed.

Theorem Rdiv_1_r : ∀ x, (x / 1)%R = x.
Proof. intros x; lra. Qed.

Theorem Rdiv_eq_0 : ∀ x y, (y ≠ 0 → x / y = 0 → x = 0)%R.
Proof.
intros * Hy Hxy.
apply Rmult_eq_compat_r with (r := y) in Hxy.
unfold Rdiv in Hxy.
rewrite Rmult_assoc in Hxy.
rewrite Rinv_l in Hxy; lra.
Qed.

Theorem Rdiv_same : ∀ x, x ≠ 0%R → (x / x = 1)%R.
Proof.
intros.
unfold Rdiv.
now rewrite Rinv_r.
Qed.

Theorem up_0 : (up 0 = 1)%Z.
Proof.
pose proof archimed 0 as H.
rewrite Rminus_0_r in H.
remember (up 0) as z eqn:Hz; clear Hz.
destruct H as (H₁, H₂).
assert (H : (0 <= z)%Z).
 apply le_IZR; simpl.
 eapply Rle_trans; [ apply Rlt_le; eassumption | apply Rle_refl ].

 apply IZN in H.
 destruct H as (n, H); subst z.
 rewrite <- INR_IZR_INZ in H₁, H₂.
 destruct n; [ now apply Rlt_irrefl in H₁ | ].
 destruct n; [ easy | exfalso ].
 apply Rle_not_lt in H₂; apply H₂.
 remember (S n) as sn; simpl; subst sn; clear.
 induction n; [ simpl; lra | ].
 remember (S n) as sn; simpl; subst sn.
 eapply Rlt_le_trans; [ eassumption | lra ].
Qed.

Theorem Int_part_le_compat : ∀ x y, (x <= y)%R → (Int_part x <= Int_part y)%Z.
Proof.
intros * Hxy.
destruct (Z_le_gt_dec (Int_part x) (Int_part y)) as [| Hlt]; [ easy | ].
exfalso; apply Z.gt_lt in Hlt.
apply IZR_lt in Hlt.
pose proof base_Int_part x as Hx.
pose proof base_Int_part y as Hy.
destruct Hx as (Hx1, Hx2).
destruct Hy as (Hy1, Hy2).
remember (IZR (Int_part x)) as a eqn:Ha.
remember (IZR (Int_part y)) as b eqn:Hb.
assert (Hab : (0 < a - b < 1)%R).
 split.
  apply Rplus_lt_reg_r with (r := b).
  now rewrite Rplus_0_l, Rplus_comm, Rplus_minus.

  eapply Rle_lt_trans.
   apply Rplus_le_compat; [ eassumption | apply Rle_refl ].

   eapply Rle_lt_trans.
    apply Rplus_le_compat; [ eassumption | apply Rle_refl ].

    apply Rgt_lt, Ropp_lt_contravar in Hy2.
    rewrite Ropp_minus_distr in Hy2.
    now rewrite Ropp_involutive in Hy2.

 rewrite Ha, Hb in Hab.
 rewrite Z_R_minus in Hab.
 replace 0%R with (IZR 0) in Hab by lra.
 replace 1%R with (IZR 1) in Hab by lra.
 destruct Hab as (H1, H2).
 apply lt_IZR in H1.
 apply lt_IZR in H2.
 remember (Int_part x - Int_part y)%Z as z.
 clear -H1 H2.
 rewrite Z.one_succ in H2.
 apply Zlt_succ_le in H2.
 now apply Zle_not_lt in H2.
Qed.

Theorem Int_part_close_to_1 : ∀ r n,
  (INR n / INR (n + 1) <= r < 1)%R
  → Int_part (r * (INR (n + 1))) = Z.of_nat n.
Proof.
intros * (Hnr, Hr1).
apply Rmult_le_compat_r with (r := INR (n + 1)) in Hnr; [ | apply pos_INR ].
rewrite <- Rmult_div in Hnr.
unfold Rdiv in Hnr.
rewrite Rmult_assoc in Hnr.
rewrite Rinv_r in Hnr; [ | now apply not_0_INR; rewrite Nat.add_comm ].
rewrite Rmult_1_r in Hnr.
apply Rmult_lt_compat_r with (r := INR (n + 1)) in Hr1.
 Focus 2.
 rewrite plus_INR; simpl.
 apply Rplus_le_lt_0_compat; [ apply pos_INR | lra ].

 rewrite Rmult_1_l in Hr1.
 remember (r * INR (n + 1))%R as x eqn:Hx.
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

Theorem Int_part_is_0 : ∀ x, (0 <= x < 1)%R → Int_part x = 0%Z.
Proof.
intros * Hx.
assert ((INR 0 / INR (0 + 1) <= x < 1)%R) by (now simpl; lra).
pose proof Int_part_close_to_1 x 0 H as H1.
now simpl in H1; rewrite Rmult_1_r in H1.
Qed.

Theorem frac_part_mult_for_0 : ∀ x y,
  frac_part x = 0%R
  → frac_part y = 0%R
  → frac_part (x * y) = 0%R.
Proof.
intros * Hx Hy.
apply fp_nat in Hy.
destruct Hy as (i, Hy); subst y.
destruct i; simpl; [ rewrite Rmult_0_r; apply fp_R0 | | ].
 remember (Pos.to_nat p) as n eqn:Hn; clear p Hn.
 induction n; simpl; [ rewrite Rmult_0_r; apply fp_R0 | ].
 destruct n; [ now rewrite Rmult_1_r | ].
 rewrite Rmult_plus_distr_l, Rmult_1_r.
 rewrite plus_frac_part2; rewrite Hx, IHn; lra.

 remember (Pos.to_nat p) as n eqn:Hn; clear p Hn.
 induction n; simpl; [ rewrite Ropp_0, Rmult_0_r; apply fp_R0 | ].
 destruct n.
  rewrite <- Ropp_mult_distr_r, Rmult_1_r.
  replace (- x)%R with (0 - x)%R by lra.
  rewrite Rminus_fp1; rewrite Hx; [ | rewrite fp_R0; lra ].
  rewrite Rminus_diag_eq; [ easy | apply fp_R0 ].

  rewrite Ropp_plus_distr, Rmult_plus_distr_l.
  rewrite plus_frac_part2.
   rewrite IHn, Rplus_0_l.
   rewrite <- Ropp_mult_distr_r, Rmult_1_r.
   replace (- x)%R with (0 - x)%R by lra.
   rewrite Rminus_fp1; rewrite Hx; [ | rewrite fp_R0; lra ].
   rewrite Rminus_diag_eq; [ easy | apply fp_R0 ].

   rewrite IHn, Rplus_0_l.
   rewrite <- Ropp_mult_distr_r, Rmult_1_r.
   replace (- x)%R with (0 - x)%R by lra.
   rewrite Rminus_fp1; rewrite Hx; [ | rewrite fp_R0; lra ].
   rewrite fp_R0, Rminus_diag_eq; [ lra | easy ].
Qed.

Theorem pow_INR : ∀ n k, INR (n ^ k) = (INR n ^ k)%R.
Proof.
intros.
induction k; [ easy | ].
simpl; rewrite mult_INR.
now rewrite IHk.
Qed.

Theorem frac_part_INR : ∀ n, frac_part (INR n) = 0%R.
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
 replace (IZR (Z.neg p)) with (0 + IZR (Z.neg p))%R by lra; simpl.
 rewrite fold_Rminus.
 rewrite Rminus_Int_part1.
  rewrite Int_part_is_0; [ | lra ].
  simpl; rewrite Int_part_INR.
  now rewrite positive_nat_Z.

  rewrite fp_R0, frac_part_INR; lra.
Qed.

Theorem frac_part_IZR : ∀ z, (frac_part (IZR z) = 0)%R.
Proof.
intros.
unfold frac_part.
rewrite Int_part_IZR; lra.
Qed.

Theorem fp_R1 : frac_part 1 = 0%R.
Proof.
replace 1%R with (INR 1) by easy.
apply frac_part_INR.
Qed.

Theorem Rpow_div_sub : ∀ x i j, (x ≠ 0)%R → j ≤ i → (x ^ i / x ^ j = x ^ (i - j))%R.
Proof.
intros * Hx Hij.
unfold Rdiv.
replace i with ((i - j) + j)%nat at 1 by now rewrite Nat.sub_add.
now symmetry; apply pow_RN_plus.
Qed.

Theorem frac_part_pow : ∀ x i, frac_part x = 0%R → frac_part (x ^ i) = 0%R.
Proof.
intros * Hx.
induction i; [ apply fp_R1 | simpl ].
now apply frac_part_mult_for_0.
Qed.

Theorem frac_part_self : ∀ x, (0 <= x < 1)%R → frac_part x = x.
Proof.
intros * Hx.
unfold frac_part.
rewrite Int_part_is_0; [ lra | easy ].
Qed.

Theorem frac_part_interv : ∀ x, (0 ≤ frac_part x < 1)%R.
Proof.
intros.
unfold frac_part.
specialize (base_Int_part x); intros Hx; lra.
Qed.

Theorem Int_part_interv : ∀ z x, (IZR z ≤ x < IZR (z + 1))%R → Int_part x = z.
Proof.
intros * (Hzx, Hxz).
rewrite plus_IZR in Hxz; simpl in Hxz.
assert (H : (0 ≤ x - IZR z < 1)%R) by lra.
apply Int_part_is_0 in H.
rewrite Rminus_Int_part1 in H.
 rewrite Int_part_IZR in H.
 now apply -> Z.sub_move_0_r in H.

 rewrite frac_part_IZR.
 apply Rle_ge, frac_part_interv.
Qed.

Theorem Rabs_or : ∀ x y, Rabs x = y → x = y ∨ x = (- y)%R.
Proof.
intros * Hxy; subst y.
unfold Rabs.
destruct (Rcase_abs x) as [H₁| H₁]; [ right | now left ].
symmetry; apply Ropp_involutive.
Qed.

Theorem Rabs_eq_0 : ∀ x, Rabs x = 0%R → x = 0%R.
Proof.
intros * Hx.
unfold Rabs in Hx.
destruct (Rcase_abs x); [ | easy ].
apply Ropp_eq_0_compat in Hx.
now rewrite Ropp_involutive in Hx.
Qed.

Theorem Rabs_eq_Rabs : ∀ x y, Rabs x = Rabs y → x = y ∨ x = (- y)%R.
Proof.
intros * Hxy.
unfold Rabs in Hxy.
destruct (Rcase_abs x) as [Hx| Hx].
 destruct (Rcase_abs y); lra.
 destruct (Rcase_abs y); lra.
Qed.

Theorem sqrt_inv : ∀ x, (0 < x)%R → (√ (/ x) = / √ x)%R.
Proof.
intros * Hx.
replace (/ x)%R with (1 * / x)%R by lra.
rewrite fold_Rdiv.
rewrite sqrt_div; [ | apply Rle_0_1 | easy ].
rewrite sqrt_1; lra.
Qed.

Theorem eq_mul_div_eq : ∀ a b c, b ≠ 0%R → (a = b * c → a / b = c)%R.
Proof.
intros * Hb Hab.
subst a; unfold Rdiv.
rewrite Rmult_comm, <- Rmult_assoc.
rewrite Rinv_l; [ | easy ].
now rewrite Rmult_1_l.
Qed.

Theorem nonneg_plus_4_sqr : ∀ a b c d, (0 ≤ a² + b² + c² + d²)%R.
Proof.
intros.
apply Rplus_le_le_0_compat; [ | apply Rle_0_sqr ].
apply Rplus_le_le_0_compat; [ | apply Rle_0_sqr ].
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.
