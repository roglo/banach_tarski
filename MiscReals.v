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

Theorem Rplus_simpl_r : ∀ x y, x + y - y = x.
Proof. intros; lra. Qed.

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

Theorem Rdiv_eq_0 : ∀ x y, y ≠ 0 → x / y = 0 → x = 0.
Proof.
intros * Hy Hxy.
apply Rmult_eq_compat_r with (r := y) in Hxy.
unfold Rdiv in Hxy.
rewrite Rmult_assoc in Hxy.
rewrite Rinv_l in Hxy; lra.
Qed.

Theorem Rdiv_same : ∀ x, x ≠ 0 → x / x = 1.
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

Theorem Int_part_le_compat : ∀ x y, x <= y → (Int_part x <= Int_part y)%Z.
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
assert (Hab : 0 < a - b < 1).
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
 replace 0 with (IZR 0) in Hab by lra.
 replace 1 with (IZR 1) in Hab by lra.
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
apply Rmult_lt_compat_r with (r := INR (n + 1)) in Hr1.
 Focus 2.
 rewrite plus_INR; simpl.
 apply Rplus_le_lt_0_compat; [ apply pos_INR | lra ].

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

Theorem Int_part_is_0 : ∀ x, 0 <= x < 1 → Int_part x = 0%Z.
Proof.
intros * Hx.
assert (INR 0 / INR (0 + 1) <= x < 1) by (now simpl; lra).
pose proof Int_part_close_to_1 x 0 H as H1.
now simpl in H1; rewrite Rmult_1_r in H1.
Qed.

Theorem frac_part_mult_for_0 : ∀ x y,
  frac_part x = 0
  → frac_part y = 0
  → frac_part (x * y) = 0.
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
  replace (- x) with (0 - x) by lra.
  rewrite Rminus_fp1; rewrite Hx; [ | rewrite fp_R0; lra ].
  rewrite Rminus_diag_eq; [ easy | apply fp_R0 ].

  rewrite Ropp_plus_distr, Rmult_plus_distr_l.
  rewrite plus_frac_part2.
   rewrite IHn, Rplus_0_l.
   rewrite <- Ropp_mult_distr_r, Rmult_1_r.
   replace (- x) with (0 - x) by lra.
   rewrite Rminus_fp1; rewrite Hx; [ | rewrite fp_R0; lra ].
   rewrite Rminus_diag_eq; [ easy | apply fp_R0 ].

   rewrite IHn, Rplus_0_l.
   rewrite <- Ropp_mult_distr_r, Rmult_1_r.
   replace (- x) with (0 - x) by lra.
   rewrite Rminus_fp1; rewrite Hx; [ | rewrite fp_R0; lra ].
   rewrite fp_R0, Rminus_diag_eq; [ lra | easy ].
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
 replace (IZR (Z.neg p)) with (0 + IZR (Z.neg p)) by lra; simpl.
 rewrite fold_Rminus.
 rewrite Rminus_Int_part1.
  rewrite Int_part_is_0; [ | lra ].
  simpl; rewrite Int_part_INR.
  now rewrite positive_nat_Z.

  rewrite fp_R0, frac_part_INR; lra.
Qed.

Theorem frac_part_IZR : ∀ z, frac_part (IZR z) = 0.
Proof.
intros.
unfold frac_part.
rewrite Int_part_IZR; lra.
Qed.

Theorem fp_R1 : frac_part 1 = 0.
Proof.
replace 1 with (INR 1) by easy.
apply frac_part_INR.
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

Theorem frac_part_pow : ∀ x i, frac_part x = 0 → frac_part (x ^ i) = 0.
Proof.
intros * Hx.
induction i; [ apply fp_R1 | simpl ].
now apply frac_part_mult_for_0.
Qed.

Theorem frac_part_self : ∀ x, 0 <= x < 1 → frac_part x = x.
Proof.
intros * Hx.
unfold frac_part.
rewrite Int_part_is_0; [ lra | easy ].
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
apply Int_part_is_0 in H.
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

Theorem Rabs_eq_Rabs : ∀ x y, Rabs x = Rabs y → x = y ∨ x = - y.
Proof.
intros * Hxy.
unfold Rabs in Hxy.
destruct (Rcase_abs x) as [Hx| Hx].
 destruct (Rcase_abs y); lra.
 destruct (Rcase_abs y); lra.
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

Theorem Rabs_div : ∀ x y, y ≠ 0 → Rabs (x / y) = Rabs x / Rabs y.
Proof.
intros * Hy.
unfold Rdiv.
rewrite Rabs_mult; f_equal.
now apply Rabs_Rinv.
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

Theorem sqrt_inv : ∀ x, 0 < x → √ (/ x) = / √ x.
Proof.
intros * Hx.
replace (/ x) with (1 * / x) by lra.
rewrite fold_Rdiv.
rewrite sqrt_div; [ | apply Rle_0_1 | easy ].
rewrite sqrt_1; lra.
Qed.

Theorem eq_mul_div_eq : ∀ a b c, b ≠ 0 → a = b * c → a / b = c.
Proof.
intros * Hb Hab.
subst a; unfold Rdiv.
rewrite Rmult_comm, <- Rmult_assoc.
rewrite Rinv_l; [ | easy ].
now rewrite Rmult_1_l.
Qed.

Theorem nonneg_plus_4_sqr : ∀ a b c d, 0 ≤ a² + b² + c² + d².
Proof.
intros.
apply Rplus_le_le_0_compat; [ | apply Rle_0_sqr ].
apply Rplus_le_le_0_compat; [ | apply Rle_0_sqr ].
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Theorem Rmult_minus_distr_r : ∀ r1 r2 r3,
  (r1 - r2) * r3 = r1 * r3 - r2 * r3.
Proof.
intros.
unfold Rminus.
rewrite Rmult_plus_distr_r; lra.
Qed.

Theorem Rminus_plus: ∀ x y, x - y + y = x.
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

Theorem nonneg_inv : ∀ r, 0 < r → 0 ≤ / r.
Proof.
intros * Hr.
apply Rmult_le_reg_l with (r := r); [ lra | ].
rewrite Rmult_0_r, Rinv_r; lra.
Qed.

Theorem nonneg_plus_sqr : ∀ x y, 0 ≤ x² + y².
Proof.
intros.
apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Definition Rsignp x := if Rle_dec 0 x then 1 else -1.
Definition Rsign x := if Req_dec x 0 then 0 else Rsignp x.

Theorem Rsignp_0 : Rsignp 0 = 1.
Proof.
unfold Rsignp.
destruct (Rle_dec 0 0); [ easy | lra ].
Qed.

Theorem Rsign_0 : Rsign 0 = 0.
Proof.
unfold Rsign.
destruct (Req_dec 0 0); [ easy | lra ].
Qed.

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
destruct (Req_dec x 0); [ lra |  ].
destruct (Rle_dec 0 x); [ easy | lra ].
Qed.

Theorem Rsign_of_neg : ∀ x, x < 0 → Rsign x = -1.
Proof.
intros * Hx.
unfold Rsign, Rsignp.
destruct (Req_dec x 0); [ lra |  ].
destruct (Rle_dec 0 x); [ lra | easy ].
Qed.

Theorem Rsign_neg : ∀ x, Rsign (- x) = - Rsign x.
Proof.
intros.
unfold Rsign, Rsignp.
destruct (Req_dec x 0) as [Hxz| Hxz].
 subst x; rewrite Ropp_0; simpl.
 destruct (Req_dec 0 0); [ easy | lra ].

 destruct (Req_dec (- x) 0) as [| H]; [ lra | clear H ].
 destruct (Rle_dec 0 x) as [Hp| Hn].
  destruct (Rle_dec 0 (- x)); [ lra | easy ].
  destruct (Rle_dec 0 (- x)); lra.
Qed.

Definition atan' x y :=
  if Req_dec y 0 then Rsign x * PI / 2 else atan (x / y).

Definition asin x := atan' x (√ (1 - x²)).
Definition acos x := PI / 2 - asin x.

Definition angle_of_sin_cos s c :=
  if Rlt_dec s 0 then
    if Rlt_dec c 0 then 2 * PI - acos c else asin s + 2 * PI
  else
    if Rlt_dec c 0 then acos c else asin s.

Theorem cos_atan : ∀ x, cos (atan x) = 1 / √ (1 + x²).
Proof.
intros.
assert (Hs : √ (1 + x²) ≠ 0).
 intros H.
 specialize (Rle_0_sqr x) as Hs.
 apply sqrt_eq_0 in H; lra.

 assert (Hca : ∀ x, 0 < cos (atan x)).
  intros y.
  specialize (atan_bound y) as (Hlta, Halt).
  apply cos_gt_0; [ lra | easy ].

  apply Rmult_eq_reg_r with (r := √ (1 + x²)); [ | easy ].
  rewrite <- Rinv_div, Rinv_l; [ | easy ].
  remember (atan x) as y eqn:Hy.
  assert (Hx : x = tan y) by (now subst y; rewrite atan_right_inv).
  subst x.
  specialize (Hca (tan y)); rewrite <- Hy in Hca.
  unfold tan.
  rewrite Rsqr_div; [ | lra ].
  replace (cos y) with (√ (cos y)²) at 1 by (apply sqrt_Rsqr; lra).
  rewrite <- sqrt_mult_alt; [ | apply Rle_0_sqr ].
  rewrite Rmult_plus_distr_l, Rmult_1_r.
  rewrite Rmult_div_r; [ | intros H; apply Rsqr_eq_0 in H; lra ].
  rewrite Rplus_comm, sin2_cos2.
  apply sqrt_1.
Qed.

Theorem sin_atan : ∀ x, sin (atan x) = x / √ (1 + x²).
Proof.
intros.
unfold Rdiv.
rewrite Rinv_div, <- cos_atan.
remember (atan x) as y eqn:Hy.
assert (Hx : x = tan y) by (now subst y; rewrite atan_right_inv).
subst x; unfold tan.
rewrite <- Rmult_div.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_r; [ lra | ].
intros H; rewrite Hy in H.
rewrite cos_atan in H.
unfold Rdiv in H.
apply Rmult_integral in H.
destruct H; [ lra | ].
apply Rinv_neq_0_compat in H; [ easy | ].
clear H; intros H.
apply sqrt_eq_0 in H.
 enough (Ht : 0 ≤ (tan y)²) by lra.
 apply Rle_0_sqr.

 replace 1 with (1 ^ 2) by lra.
 rewrite <- Rsqr_pow2.
 apply nonneg_plus_sqr.
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

Theorem sin_cos_asin : ∀ x,
  -1 ≤ x ≤ 1
  → sin (asin x) = x ∧ cos (asin x) = √ (1 - x²).
intros * Hx.
unfold asin.
unfold atan'.
destruct (Req_dec (√ (1 - x²)) 0) as [Hsx| Hsx].
 rewrite Hsx.
 unfold Rsign, Rsignp.
 destruct (Req_dec x 0) as [Hxz| Hxz].
  rewrite Hxz in Hsx.
  rewrite Rsqr_0, Rminus_0_r, sqrt_1 in Hsx; lra.

  destruct (Rle_dec 0 x) as [Hxp| Hxn].
   rewrite Rmult_1_l.
   rewrite sin_PI2, cos_PI2.
   split; [ | easy ].
   symmetry.
   apply sqrt_diff_sqr_eq_0; [ lra | now rewrite Rsqr_1 ].

   rewrite <- Ropp_mult_distr_l, Rmult_1_l, Ropp_div.
   rewrite sin_neg, cos_neg.
   rewrite sin_PI2, cos_PI2.
   split; [ | easy ].
   rewrite <- Ropp_involutive.
   f_equal; symmetry.
   apply sqrt_diff_sqr_eq_0; [ lra | ].
   now rewrite Rsqr_1, <- Rsqr_neg.

 assert (Hx' : -1 < x < 1).
  apply Rabs_lt, Rnot_le_lt.
  intros Ha; apply Hsx; clear Hsx.
  apply Rsqr_inj; [ apply sqrt_pos | lra | ].
  rewrite Rsqr_0; unfold Rabs in Ha.
  destruct (Rcase_abs x) as [Hc| Hc].
   assert (x = -1) by lra; subst x.
   rewrite <- Rsqr_neg, Rsqr_1, Rminus_diag_eq; [ | easy ].
   now rewrite sqrt_0, Rsqr_0.

   assert (x = 1) by lra; subst x.
   rewrite Rsqr_1, Rminus_diag_eq; [ | easy ].
   now rewrite sqrt_0, Rsqr_0.

  clear Hx; rename Hx' into Hx; move Hx before x.
  remember (x / √ (1 - x²)) as y eqn:Hy.
  rewrite sin_atan, cos_atan.
  destruct (Req_dec x 0) as [Hxz| Hxz].
   subst x; rewrite Rdiv_0_l in Hy; subst y.
   split; [ now rewrite Rdiv_0_l | ].
   now rewrite Rsqr_0, Rplus_0_r, Rminus_0_r, sqrt_1, Rdiv_1_r.

   assert (H1x : 0 < 1 - x²).
    replace 1 with 1² by apply Rsqr_1.
    rewrite <- Rsqr_plus_minus.
    apply Rmult_lt_0_compat; lra.

    assert (Hsp : 0 < √ (1 - x²)).
     apply Rsqr_incrst_0; [ | lra | apply sqrt_pos ].
     rewrite Rsqr_sqrt; [ now rewrite Rsqr_0 | lra ].

     assert (Hyz : y ≠ 0).
      intros H; apply Hxz; subst y.
      apply Rmult_eq_compat_r with (r := √ (1 - x²)) in H.
      unfold Rdiv in H; rewrite Rmult_assoc, Rmult_0_l in H.
      rewrite Rinv_l in H; lra.

      assert (Hxy : 0 ≤ x * y).
       subst y; unfold Rdiv; rewrite <- Rmult_assoc.
       rewrite fold_Rsqr.
       apply Rmult_le_pos; [ apply Rle_0_sqr | ].
       apply Rmult_le_reg_r with (r := √ (1 - x²)); [ lra | ].
       rewrite Rmult_0_l, Rinv_l; lra.

       apply (f_equal Rsqr) in Hy.
       rewrite Rsqr_div in Hy; [ | lra ].
       rewrite Rsqr_sqrt in Hy; [ | lra ].
       apply Rmult_eq_compat_r with (r := 1 - x²) in Hy.
       unfold Rdiv in Hy; rewrite Rmult_assoc in Hy.
       rewrite Rinv_l in Hy; [ rewrite Rmult_1_r in Hy | lra ].
       rewrite Rmult_minus_distr_l, Rmult_1_r in Hy.
       assert (H : y² = x² * (1 + y²)) by lra.
       apply Rmult_eq_compat_r with (r := / (1 + y²)) in H.
       rewrite Rmult_assoc in H.
       assert (H1y : 0 < 1 + y²).
        apply Rplus_lt_le_0_compat; [ lra | apply Rle_0_sqr ].

        assert (Hsy : 0 < √ (1 + y²)).
         apply Rsqr_incrst_0; [ | lra | apply sqrt_pos ].
         rewrite Rsqr_sqrt; [ now rewrite Rsqr_0 | lra ].

         rewrite Rinv_r in H; [ | lra ].
         replace (/ (1 + y²)) with (/ √ (1 + y²))² in H.
          rewrite <- Rsqr_mult in H.
          rewrite Rmult_1_r in H.
          apply Rsqr_eq in H.
          split.
           destruct H as [H| H]; [ easy | exfalso ].
           apply Ropp_eq_compat in H.
           rewrite Ropp_involutive in H.
           rewrite <- H in Hxy.
           rewrite <- Ropp_mult_distr_l in Hxy.
           rewrite Rmult_comm, <- Rmult_assoc, fold_Rsqr in Hxy.
           replace 0 with (-0) in Hxy by apply Ropp_0.
           apply Ropp_le_cancel in Hxy.
           apply Rmult_le_compat_r with (r := √ (1 + y²)) in Hxy; [ | lra ].
           rewrite Rmult_assoc, Rmult_0_l in Hxy.
           rewrite Rinv_l in Hxy; [ | lra ].
           rewrite Rmult_1_r in Hxy.
           apply Rle_not_lt in Hxy; apply Hxy.
           now apply Rlt_0_sqr.

           apply Rmult_eq_reg_r with (r := √ (1 + y²)); [ | lra ].
           rewrite <- Rinv_div.
           rewrite Rinv_l; [ | lra ].
           symmetry.
           rewrite <- sqrt_mult; [ | lra | lra ].
           rewrite Rmult_plus_distr_l, Rmult_1_r.
           rewrite Rmult_minus_distr_r, Rmult_1_l.
           rewrite Rmult_comm, Hy.
           now rewrite Rminus_plus, sqrt_1.

          rewrite Rsqr_inv; [ | lra ].
          rewrite Rsqr_sqrt; [ easy | lra ].
Qed.

Theorem sin_asin : ∀ x, -1 ≤ x ≤ 1 → sin (asin x) = x.
Proof.
intros * Hx.
now apply sin_cos_asin.
Qed.

Theorem cos_asin : ∀ x, -1 ≤ x ≤ 1 → cos (asin x) = √ (1 - x²).
Proof.
intros * Hx.
now apply sin_cos_asin.
Qed.

Theorem cos_acos : ∀ x, -1 ≤ x ≤ 1 → cos (acos x) = x.
Proof.
intros * Hx.
unfold acos; rewrite cos_shift.
now apply sin_asin.
Qed.

Theorem sin_Zperiod : ∀ x k, sin (x + 2 * IZR k * PI) = sin x.
Proof.
intros.
destruct k as [| k| k].
 now rewrite Rmult_0_r, Rmult_0_l, Rplus_0_r.

 now simpl; rewrite sin_period.

 simpl; rewrite <- Ropp_mult_distr_r, <- Ropp_mult_distr_l, fold_Rminus.
 rewrite <- sin_period with (k := Pos.to_nat k).
 now rewrite Rminus_plus.
Qed.

Theorem cos_Zperiod : ∀ x k, cos (x + 2 * IZR k * PI) = cos x.
Proof.
intros.
destruct k as [| k| k].
 now rewrite Rmult_0_r, Rmult_0_l, Rplus_0_r.

 now simpl; rewrite cos_period.

 simpl; rewrite <- Ropp_mult_distr_r, <- Ropp_mult_distr_l, fold_Rminus.
 rewrite <- cos_period with (k := Pos.to_nat k).
 now rewrite Rminus_plus.
Qed.

Theorem sin_nPI : ∀ n, sin (INR n * PI) = 0.
Proof.
intros.
induction n; [ rewrite Rmult_0_l; apply sin_0 | ].
rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, neg_sin; lra.
Qed.

Theorem cos_nPI : ∀ n, cos (INR n * PI) = (-1) ^ n.
Proof.
intros.
induction n; [ now rewrite Rmult_0_l, cos_0 | ].
rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, neg_cos, IHn.
simpl; lra.
Qed.

Theorem sin_ZPI : ∀ z, sin (IZR z * PI) = 0.
Proof.
intros.
destruct z as [| z| z]; simpl; [ now rewrite Rmult_0_l, sin_0 | | ].
 now rewrite sin_nPI.

 rewrite <- Ropp_mult_distr_l.
 rewrite sin_neg, sin_nPI; lra.
Qed.

Theorem cos_ZPI : ∀ z, cos (IZR z * PI) = (-1) ^ Z.abs_nat z.
Proof.
intros.
destruct z as [| z| z]; simpl; [ now rewrite Rmult_0_l, cos_0 | | ].
 now rewrite cos_nPI.

 rewrite <- Ropp_mult_distr_l.
 now rewrite cos_neg, cos_nPI.
Qed.

Theorem tan_period : ∀ x k, cos x ≠ 0 → tan (x + INR k * PI) = tan x.
Proof.
intros * Hcz.
destruct (eq_nat_dec (k mod 2) 0) as [Hk| Hk].
 apply Nat.mod_divides in Hk; [ | easy ].
 destruct Hk as (c, Hc); subst k.
 rewrite mult_INR; simpl.
 unfold tan.
 now rewrite sin_period, cos_period.

 destruct k; [ easy | ].
 rewrite S_INR.
 rewrite Rmult_plus_distr_r.
 rewrite Rmult_1_l, <- Rplus_assoc.
 unfold tan.
 rewrite neg_sin, neg_cos.
 rewrite sin_plus, cos_plus.
 rewrite sin_nPI, cos_nPI.
 do 2 rewrite Rmult_0_r.
 rewrite Rplus_0_r, Rminus_0_r.
 do 2 rewrite Ropp_mult_distr_r.
 rewrite Rdiv_mult_simpl_r; [ easy | easy | ].
 clear; induction k; simpl; lra.
Qed.

Theorem tan_Zperiod : ∀ x k, cos x ≠ 0 → tan (x + IZR k * PI) = tan x.
Proof.
intros * Hcz.
destruct (Z_eq_dec (k mod 2) 0) as [Hk| Hk].
 apply Zdiv.Zmod_divides in Hk; [ | easy ].
 destruct Hk as (c, Hc); subst k.
 rewrite mult_IZR; simpl.
 unfold tan.
 now rewrite sin_Zperiod, cos_Zperiod.

 destruct k as [| k| k]; [ easy | now apply tan_period | ].
 simpl; rewrite <- Ropp_mult_distr_l, fold_Rminus.
 rewrite <- tan_period with (k := Pos.to_nat k).
  now rewrite Rminus_plus.

  rewrite cos_minus.
  rewrite cos_nPI, sin_nPI, Rmult_0_r, Rplus_0_r.
  intros H.
  apply Rmult_integral in H.
  destruct H as [H| H]; [ easy | ].
  apply pow_nonzero in H; [ easy | lra ].
Qed.

Theorem tan_ZPI : ∀ k, tan (IZR k * PI) = 0.
Proof.
intros.
assert (Hc : cos 0 ≠ 0) by (rewrite cos_0; lra).
specialize (tan_Zperiod 0 k Hc) as H.
now rewrite Rplus_0_l, tan_0 in H.
Qed.

Print Int_part.

Definition Rdiv_mod x y :=
  let k :=
    match Rcase_abs y with
    | left _ => (- Int_part (x / - y))%Z
    | right _ => Int_part (x / y)
    end
  in
  (k, x - IZR k * y).

Definition Rediv x y := fst (Rdiv_mod x y).
Definition Rmod x y := snd (Rdiv_mod x y).

Notation "x 'ediv' y" := (Rediv x y) (at level 40).
Notation "x 'rmod' y" := (Rmod x y) (at level 40).

Theorem Rmod_interv : ∀ x y, 0 < y → 0 ≤ Rmod x y < y.
Proof.
intros * Hy.
unfold Rmod, Rdiv_mod, snd.
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

Theorem Rmod_from_ediv : ∀ x y, Rmod x y = x - IZR (Rediv x y) * y.
Proof.
intros.
unfold Rmod, Rediv, fst, snd.
remember (Rdiv_mod x y) as rdm eqn:Hrdm.
symmetry in Hrdm.
destruct rdm as (q, r).
unfold Rdiv_mod in Hrdm.
destruct (Rcase_abs y) as [Hy| Hy].
 remember Z.sub as f.
 injection Hrdm; clear Hrdm; intros Hr Hq; subst f.
 now rewrite Hq in Hr.

 remember Z.sub as f.
 injection Hrdm; clear Hrdm; intros Hr Hq; subst f.
 now rewrite Hq in Hr.
Qed.

Theorem up_Int_part : ∀ x, up x = (Int_part x + 1)%Z.
Proof. intros; unfold Int_part; lia. Qed.

Theorem Rediv_add : ∀ x y, y ≠ 0 → Rediv (x + y) y = (Rediv x y + 1)%Z.
Proof.
intros * Hyz.
unfold Rediv, Rdiv_mod, fst.
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

Theorem neg_cos_atan_tan : ∀ x,
  cos x < 0
  → atan (tan x) = x - IZR (Rediv (x + PI / 2) PI) * PI.
Proof.
intros * Hc.
unfold atan.
destruct (pre_atan (tan x)) as (y & Hy & Hyx).
remember (Rmod (x + PI / 2) PI - PI / 2) as z eqn:Hz.
assert (Htz : tan z = tan x).
 subst z.
 unfold Rmod, Rdiv_mod, snd.
 destruct (Rcase_abs PI) as [HP| HP]; [ lra | ].
 remember (IZR (Int_part ((x + PI / 2) / PI)) * PI) as t eqn:Ht.
 replace (x + PI / 2 - t - PI / 2) with (x - t) by lra.
 rewrite tan_minus; [ | lra | | | ].
  subst t; rewrite tan_ZPI.
  now rewrite Rminus_0_r, Rmult_0_r, Rplus_0_r, Rdiv_1_r.

  subst t.
  rewrite cos_ZPI.
  apply pow_nonzero; lra.

  subst t.
  rewrite cos_minus.
  rewrite cos_ZPI, sin_ZPI.
  rewrite Rmult_0_r, Rplus_0_r.
  intros H.
  apply Rmult_integral in H.
  destruct H as [H| H]; [ lra | ].
  apply pow_nonzero in H; lra.

  subst t.
  rewrite tan_ZPI, Rmult_0_r, Rplus_0_r; lra.

 assert (Hzi : - PI / 2 < z < PI / 2).
  rewrite Hz.
  assert (HPP : 0 < PI) by lra.
  specialize (Rmod_interv (x + PI / 2) PI HPP) as H.
  split; [ | lra ].
  enough (Rmod (x + PI / 2) PI ≠ 0) by lra.
  intros Hm.
  unfold Rmod, Rdiv_mod, snd in Hm.
  destruct (Rcase_abs PI) as [HPQ| HPQ]; [ lra | ].
  fold (Int_part ((x + PI / 2) / PI)) in Hm.
  apply Rminus_diag_uniq in Hm.
  remember (Int_part ((x + PI / 2) / PI)) as k.
  assert (x = IZR k * PI - PI / 2) by lra.
  rewrite H0 in Hc.
  rewrite cos_minus in Hc.
  rewrite cos_ZPI, sin_ZPI in Hc.
  rewrite Rmult_0_l, Rplus_0_r in Hc.
  rewrite cos_PI2, Rmult_0_r in Hc; lra.

  rewrite <- Htz in Hyx.
  specialize (tan_is_inj y z Hy Hzi Hyx) as H.
  move H at top; subst z.
  rewrite Rmod_from_ediv in Hz; lra.
Qed.

Theorem pos_cos_atan_tan : ∀ x,
  0 < cos x
  → atan (tan x) = x - IZR (Rediv (x + PI / 2) PI) * PI.
Proof.
intros * Hc.
assert (Hcp : cos (x + PI) < 0) by (rewrite neg_cos; lra).
specialize (neg_cos_atan_tan (x + PI) Hcp) as H.
assert (Hcz : cos x ≠ 0) by lra.
specialize (tan_period x 1 Hcz) as Ht.
simpl (INR _) in Ht.
rewrite Rmult_1_l in Ht.
rewrite Rplus_shuffle0 in H.
rewrite Rediv_add in H; [ | apply PI_neq0 ].
rewrite plus_IZR in H.
simpl (IZR _) in H.
rewrite Ht in H; lra.
Qed.

Theorem atan_tan : ∀ x,
  cos x ≠ 0
  → atan (tan x) = x - IZR (Rediv (x + PI / 2) PI) * PI.
Proof.
intros * Hxz.
destruct (Rlt_dec (cos x) 0) as [Hx| Hx].
 now apply neg_cos_atan_tan.

 apply pos_cos_atan_tan; lra.
Qed.

Theorem asin_sin : ∀ x,
  asin (sin x) = Rsignp (cos x) * atan' (sin x) (cos x).
Proof.
intros.
unfold asin, atan'.
rewrite <- cos2.
rewrite sqrt_Rsqr_abs.
destruct (Req_dec (cos x) 0) as [Haz| Haz].
 rewrite Haz, Rabs_R0.
 rewrite Rsignp_of_pos; [ | lra ].
 destruct (Req_dec 0 0); lra.

 destruct (Req_dec (Rabs (cos x))) as [Hab| Hab].
  now apply Rabs_eq_0 in Hab.

  unfold Rabs.
  destruct (Rcase_abs (cos x)) as [Ha| Ha].
   unfold Rdiv.
   rewrite Rsignp_of_neg; [ | easy ].
   destruct (Rle_dec 0 (cos x)); [ lra | ].
   rewrite <- Ropp_inv_permute; [ | lra ].
   rewrite <- Ropp_mult_distr_r.
   rewrite fold_Rdiv.
   fold (tan x); rewrite atan_opp; lra.

   rewrite Rsignp_of_pos; lra.
Qed.

Theorem cos_plus_PI2 : ∀ x, cos (x + PI / 2) = - sin x.
Proof.
intros.
rewrite cos_plus, cos_PI2, sin_PI2; lra.
Qed.

Theorem asin_cos : ∀ x,
  asin (cos x) =
   if Req_dec (sin x) 0 then Rsign (cos x) * PI / 2
   else - Rsign (sin x) * atan (tan (x + PI / 2)).
Proof.
intros.
rewrite cos_sin, asin_sin.
rewrite Rplus_comm.
unfold atan'.
fold (tan (x + PI / 2)).
rewrite cos_plus_PI2.
unfold Rsignp.
destruct (Req_dec (- sin x) 0) as [H1| H1].
 rewrite H1.
 apply (f_equal Ropp) in H1.
 rewrite Ropp_involutive, Ropp_0 in H1.
 rewrite H1.
 destruct (Rle_dec 0 0) as [H| H]; [ clear H | lra ].
 destruct (Req_dec 0 0); lra.

 destruct (Req_dec (sin x) 0) as [Hs| Hs]; [ lra | clear H1 ].
 destruct (Rle_dec 0 (- sin x)) as [H1| H1].
  rewrite Rsign_of_neg; lra.
  rewrite Rsign_of_pos; lra.
Qed.

Theorem acos_cos : ∀ x, acos (cos x) = PI / 2 - asin (cos x).
Proof. easy. Qed.

Theorem asin_0 : asin 0 = 0.
Proof.
unfold asin, atan'.
rewrite Rsqr_0, Rminus_0_r, sqrt_1, Rdiv_1_r, atan_0.
destruct (Req_dec 1 0); [ lra | easy ].
Qed.

(*
Theorem asin_increasing : ∀ x y,
  -1 ≤ x ≤ 1
  → -1 ≤ y ≤ 1
  → x < y
  → asin x < asin y.
Proof.
bbb.
*)

Theorem pos_sin_interv : ∀ x, 0 < sin x → x rmod (2 * PI) < PI.
Proof.
intros * Hs.
apply Rnot_le_lt; intros Hx.
apply Rlt_not_le in Hs; apply Hs; clear Hs.
enough (H : sin (x rmod (2 * PI)) ≤ 0).
 rewrite Rmod_from_ediv in H.
 unfold Rminus in H.
 rewrite Ropp_mult_distr_l in H.
 rewrite <- opp_IZR in H.
 rewrite Rmult_comm, Rmult_shuffle0 in H.
 now rewrite sin_Zperiod in H.

 apply sin_le_0; [ easy | ].
 assert (HP : 0 < 2 * PI) by (specialize PI_RGT_0; lra).
 specialize (Rmod_interv x (2 * PI) HP) as H; lra.
Qed.

(*
Theorem pos_sin_interv2 : ∀ x k,
  0 < sin x
  → k = x ediv (2 * PI)
  →  2 * IZR k * PI < x < PI + 2 * IZR k * PI.
Proof.
intros * Hs Hk.
specialize (pos_sin_interv x Hs) as H.
rewrite Rmod_from_ediv in H.
rewrite <- Hk in H; lra.
Qed.

Theorem neg_sin_interv : ∀ x k,
  sin x < 0
  → k = (x - PI) ediv (2 * PI)
  → PI + 2 * IZR k * PI < x < 2 * PI + 2 * IZR k * PI.
Proof.
intros * Hs Hk.
apply Ropp_lt_contravar in Hs.
rewrite <- neg_sin, Ropp_0 in Hs.
rewrite <- sin_Zperiod with (k := (-1)%Z) in Hs; simpl in Hs.
replace (x + PI + 2 * -1 * PI) with (x - PI) in Hs by lra.
remember (x - PI) as y eqn:Hy.
replace (2 * PI) with (PI + PI) by lra.
assert (x = y + PI) by lra.
subst x; clear Hy.
enough (2 * IZR k * PI < y < PI + 2 * IZR k * PI) by lra.
bbb.
*)

Theorem Rediv_div : ∀ x y z,
  y ≠ 0
  → 0 < z
  → IZR (x ediv y) ediv z = x ediv (y * z).
Proof.
intros * Hy Hz.
unfold Rediv, fst, Rdiv_mod.
destruct (Rcase_abs z) as [Haz| Haz]; [ lra | clear Haz ].
destruct (Rcase_abs y) as [Hay| Hay].
 destruct (Rcase_abs (y * z)) as [Hayz| Hayz].
  rewrite opp_IZR.
  remember (- y) as y' eqn:Hy'.
  assert (H : 0 < y') by lra; clear Hay; rename H into Hay.
  rewrite Ropp_mult_distr_l, <- Hy'.
  clear y Hy Hy' Hayz; rename y' into y; move y before x.
Theorem glop : ∀ x,
  0 < x
  → IZR (Int_part (- x)) =
      - IZR (Int_part x)
      - if Req_dec x (IZR (Int_part x)) then 0 else 1.
Proof.
Admitted. Show.

rewrite glop.
Search (Int_part (- _)).
Check Int_part.
bbb.

Theorem angle_of_sin_cos_inv : ∀ x,
  angle_of_sin_cos (sin x) (cos x) = Rmod x (2 * PI).
Proof.
intros.
unfold angle_of_sin_cos.
destruct (Rlt_dec (sin x) 0) as [Hs| Hs].
 destruct (Rlt_dec (cos x) 0) as [Hc| Hc].
  rewrite acos_cos.
   rewrite asin_cos.
   destruct (Req_dec (sin x) 0) as [| H]; [ lra | clear H ].
   rewrite <- Ropp_mult_distr_l, Rminus_opp.
   rewrite Rsign_of_neg; [ | easy ].
   rewrite <- Ropp_mult_distr_l, Rmult_1_l.
   rewrite fold_Rminus.
   rewrite atan_tan.
    replace (x + PI / 2 + PI / 2) with (x + PI) by lra.
    rewrite Rediv_add; [ | apply PI_neq0 ].
    rewrite Rmod_from_ediv.
    rewrite plus_IZR; simpl (IZR 1).
Search (_ ediv (_ * _)).
replace (2 * PI) with (PI * 2) by lra.
rewrite <- Rediv_div.

bbb.
  rewrite acos_cos; [ | lra ].
  rewrite Rsign_of_neg; [ | easy ].
  rewrite <- Ropp_mult_distr_l, Rmult_1_l.
  rewrite Rminus_plus_distr.
  rewrite Rminus_opp.
  rewrite Rplus_comm.
  rewrite atan_tan.
   rewrite Rplus_assoc.
   replace (PI / 2 + PI / 2) with PI by lra.
   rewrite Rediv_add; [ | apply PI_neq0 ].
   rewrite plus_IZR; simpl (IZR 1).
   rewrite Rmult_plus_distr_r.
   rewrite Rmult_1_l.
   rewrite Rmod_from_ediv.
   remember (IZR (x ediv PI) * PI) as t eqn:Ht.
   replace (x + PI / 2 - (t + PI) + 2 * PI - PI / 2)
   with (x - (t - PI)) by lra.
   subst t; f_equal.
   unfold Rediv, fst, Rdiv_mod.
   specialize PI_RGT_0 as HPI.
   destruct (Rcase_abs PI) as [HP| HP]; [ lra | clear HP ].
   destruct (Rcase_abs (2 * PI)) as [HP| HP]; [ lra | clear HP ].
   enough (∃ k, PI + 2 * IZR k * PI < x < 2 * PI + 2 * IZR k * PI) as (k, Hk).
    assert (H1 : IZR (2 * k + 1) ≤ x / PI < IZR (2 * k + 1 + 1)).
     do 3 rewrite plus_IZR; simpl (IZR 1).
     split.
      apply Rmult_le_reg_r with (r := PI); [ lra | ].
      rewrite mult_IZR; simpl (IZR 2).
      rewrite Rmult_div_same; lra.

      apply Rmult_lt_reg_r with (r := PI); [ lra | ].
      rewrite mult_IZR; simpl (IZR 2).
      rewrite Rmult_div_same; lra.

     erewrite Int_part_interv; [ | eassumption ].
     assert (H2 : IZR k ≤ x / (2 * PI) < IZR (k + 1)).
      rewrite plus_IZR; simpl (IZR 1).
      split.
       apply Rmult_le_reg_r with (r := 2 * PI); [ lra | ].
       rewrite Rmult_div_same; lra.

       apply Rmult_lt_reg_r with (r := 2 * PI); [ lra | ].
       rewrite Rmult_div_same; lra.

      erewrite Int_part_interv; [ | eassumption ].
      rewrite plus_IZR; simpl (IZR 1).
      rewrite mult_IZR; simpl (IZR 2).
      rewrite Rmult_plus_distr_r, Rmult_1_l.
      rewrite Rplus_simpl_r; lra.

    idtac.
Check neg_sin_interv.

bbb.
Search (sin _ < _ → _).
unfold sin in Hs.
unfold exist_sin in Hs.
unfold Alembert_C3 in Hs.
destruct (total_order_T x² 0) as [[Hx| Hx]| Hx].
 exfalso; clear - Hx; apply Rlt_not_le in Hx; apply Hx.
 apply Rle_0_sqr.

 specialize (Rsqr_eq_0 _ Hx) as Hx2; subst x; simpl in Hs.
 destruct (AlembertC3_step2 sin_n 0² Hx); lra.

 simpl in Hs.

bbb.

Theorem cos_angle_of_sin_cos : ∀ x,
  cos x = cos (angle_of_sin_cos (sin x) (cos x)).
Proof.
(*
intros.
rewrite angle_of_sin_cos_inv.
rewrite Rmod_from_ediv.
rewrite cos_minus.
rewrite <- Rmult_assoc.
replace 2 with (IZR 2) by lra.
rewrite <- mult_IZR.
rewrite cos_ZPI, sin_ZPI, Rmult_0_r, Rplus_0_r.
rewrite Zabs2Nat.inj_mul; simpl (Z.abs_nat 2).
unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).
now rewrite Nat.mul_comm, pow_1_even, Rmult_1_r.
bbb.
*)
intros.
unfold angle_of_sin_cos.
destruct (Rlt_dec (sin x) 0) as [Hs| Hs].
 destruct (Rlt_dec (cos x) 0) as [Hc| Hc].
  rewrite cos_minus.
  rewrite cos_2PI, sin_2PI, Rmult_1_l, Rmult_0_l, Rplus_0_r.
  rewrite cos_acos; [ easy | ].
  split; [ | lra ].
  specialize (COS_bound x) as (H, _).
  destruct (Req_dec (cos x) (-1)) as [H1| H1]; [ exfalso | lra ].
  clear H Hc.
  assert (Hs2 : 0 < (sin x)²) by (apply Rlt_0_sqr; lra).
  specialize (sin2_cos2 x) as Hsc.
  rewrite H1, <- Rsqr_neg, Rsqr_1 in Hsc; lra.

  apply Rnot_lt_le in Hc.
  rewrite cos_plus, cos_2PI, sin_2PI, Rmult_1_r, Rmult_0_r, Rminus_0_r.
  destruct (Req_dec (sin x) (-1)) as [Hs1| Hs1].
   rewrite Hs1.
   unfold asin, atan'.
   rewrite <- Rsqr_neg, Rsqr_1, Rminus_diag_eq; [ | easy ].
   rewrite sqrt_0.
   destruct (Req_dec 0 0) as [Hz| Hz]; [ clear Hz | lra ].
   rewrite Rsign_of_neg; [ | lra ].
   rewrite <- Ropp_mult_distr_l, Rmult_1_l.
   rewrite Ropp_div, cos_neg, cos_PI2.
   specialize (sin2_cos2 x) as H.
   rewrite Hs1, <- Rsqr_neg, Rsqr_1 in H.
   assert (Hz : (cos x)² = 0) by lra.
   now apply Rsqr_eq_0 in Hz.

   rewrite cos_asin; [ | apply SIN_bound ].
   specialize (sin2_cos2 x) as Hsc.
   apply Rsqr_inj; [ easy | apply sqrt_pos | ].
   rewrite Rsqr_sqrt; [ lra | ].
   enough ((sin x)² ≤ 1) by lra.
   replace 1 with 1² by apply Rsqr_1.
   apply neg_pos_Rsqr_le; [ | lra ].
   apply SIN_bound.

 destruct (Rlt_dec (cos x) 0) as [Hc| Hc].
  rewrite cos_acos; [ easy | apply COS_bound ].

  rewrite cos_asin; [ | apply SIN_bound ].
  apply Rnot_lt_le in Hc.
  specialize (sin2_cos2 x) as Hsc.
  apply Rsqr_inj; [ easy | apply sqrt_pos | ].
  rewrite Rsqr_sqrt; [ lra | ].
  enough ((sin x)² ≤ 1) by lra.
  replace 1 with 1² by apply Rsqr_1.
  apply Rsqr_incr_1; [ | lra | lra ].
  apply SIN_bound.
Qed.

Theorem Rneq_le_lt : ∀ x y, x ≠ y → x ≤ y → x < y.
Proof.
intros * Hnxy Hxy.
apply Rnot_le_lt; intros H.
now apply Rle_antisym in H.
Qed.
