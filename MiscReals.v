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

Theorem Int_part_is_0 : ∀ x, (0 <= x < 1)%R → Int_part x = 0%Z.
Proof.
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
