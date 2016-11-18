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

Theorem Int_part_close_to_1 : ∀ r n,
  (INR n / INR (n + 1) <= r < 1)%R
  → Int_part (r * (INR n + 1)) = Z.of_nat n.
Proof.
intros * Hn.
revert r Hn.
induction n; intros.
Focus 2.

bbb.

Theorem Int_part_is_0 : ∀ x, (0 <= x < 1)%R → Int_part x = 0%Z.
Proof.
intros * Hx.
assert ((INR 0 / INR (0 + 1) <= x < 1)%R) by (now simpl; lra).
pose proof Int_part_close_to_1 x 0 H as H1.
simpl in H1.
now rewrite Rplus_0_l, Rmult_1_r in H1.
bbb.

intros * Hx.
unfold Int_part.
pose proof archimed x as H.
destruct H as (Hgt, Hle).
destruct Hx as (Hx1, Hx2).
apply Z.sub_move_r; simpl.
apply Rplus_le_compat_r with (r := x) in Hle.
unfold Rminus in Hle.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r in Hle.
remember (up x) as z eqn:Hz; symmetry in Hz.
assert (Hzp : (0 <= z)%Z).
 subst z; apply le_IZR; simpl.
 eapply Rle_trans; [ eassumption | now apply Rlt_le ].

 apply IZN in Hzp.
 destruct Hzp as (n, Hn).
 move Hn at top; subst z.
 destruct n; [ simpl in Hgt; lra | ].
 destruct n; [ easy | exfalso ].
 apply Rle_not_lt in Hle; apply Hle.
 apply Rlt_le_trans with (r2 := (1 + 1)%R); [ lra | ].
 rewrite <- INR_IZR_INZ; simpl.
 destruct n; [ lra | ].
 rewrite Rplus_assoc.
 replace 2%R with (0 + 2)%R at 1 by lra.
 apply Rplus_le_compat_r, pos_INR.
Qed.

(* useless since there is theorem 'base_fp' in Coq library *)
Theorem frac_part_in_0_1 : ∀ x, (0 <= frac_part x)%R ∧ (frac_part x < 1)%R.
Proof.
intros x.
pose proof base_fp x as H.
destruct H as (H1, H2).
now apply Rge_le in H1.
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
