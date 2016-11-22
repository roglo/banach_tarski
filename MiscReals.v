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

Theorem fold_Rsqr : ∀ a, (a * a = a²)%R.
Proof. easy. Qed.

Theorem Rmul_div : ∀ x y z, (x * y / z = x / z * y)%R.
Proof. intros; lra. Qed.

Theorem Rmult_shuffle0 : ∀ n m p : ℝ, (n * m * p)%R = (n * p * m)%R.
Proof.
intros.
rewrite Rmult_comm, <- Rmult_assoc.
f_equal; apply Rmult_comm.
Qed.

Theorem Req_dec : ∀ x y : ℝ, { (x = y)%R } + { (x ≠ y)%R }.
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

Theorem fold_Rdiv : ∀ x y, (x * / y = x / y)%R.
Proof. easy. Qed.

Theorem Rdiv_1_r : ∀ x, (x / 1)%R = x.
Proof. intros x; lra. Qed.

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
rewrite <- Rmul_div in Hnr.
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

Theorem fp_R1 : frac_part 1 = 0%R.
Proof.
replace 1%R with (INR 1) by easy.
apply frac_part_INR.
Qed.


(* useless since there is theorem 'base_fp' in Coq library
Theorem frac_part_in_0_1 : ∀ x, (0 <= frac_part x)%R ∧ (frac_part x < 1)%R.
Proof.
intros x.
pose proof base_fp x as H.
destruct H as (H1, H2).
now apply Rge_le in H1.
Qed.
*)
