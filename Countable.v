(* Banach-Tarski paradox. *)

From Stdlib Require Import Utf8 Bool Compare_dec ZArith Psatz.
Require Import Misc.

Definition prod_nat_of_nat n :=
  let s := Nat.sqrt n in
  (s - (n - s ^ 2), n - s ^ 2)%nat.

Definition prod_nat_to_nat '(i, j) :=
  ((i + j) ^ 2 + j)%nat.

Theorem nat_sqrt_add : ∀ n p, (p ≤ 2 * n)%nat → Nat.sqrt (n * n + p) = n.
Proof.
intros * Hp.
apply Nat.sqrt_unique.
split; [ apply Nat.le_add_r | simpl ].
setoid_rewrite Nat.mul_comm; simpl.
rewrite Nat.add_comm, Nat.add_assoc.
eapply Nat.le_lt_trans; [ apply Nat.add_le_mono_r, Hp | ].
simpl; rewrite Nat.add_0_r.
apply Nat.lt_succ_diag_r.
Qed.

Theorem prod_nat_to_nat_id : ∀ i j,
  prod_nat_of_nat (prod_nat_to_nat (i, j)) = (i, j).
Proof.
intros; simpl.
unfold prod_nat_of_nat.
rewrite Nat.mul_1_r.
remember ((i + j) * (i + j) + j)%nat as n eqn:Hn.
remember (Nat.sqrt n) as s eqn:Hs.
rewrite Hn in Hs.
rewrite nat_sqrt_add in Hs. {
  rewrite Nat.add_comm in Hn.
  subst; rewrite Nat.pow_2_r.
  rewrite Nat.add_sub.
  now rewrite Nat.add_sub.
}
simpl.
rewrite Nat.add_0_r, Nat.add_assoc, Nat.add_comm.
apply Nat.le_add_r.
Qed.

Definition Z_of_nat_surj n :=
  if zerop (n mod 2) then Z.of_nat (n / 2)
  else (- Z.of_nat (S n / 2))%Z.

Definition Z_to_nat_inj z :=
  if Z_lt_dec z 0 then Z.to_nat (- z * 2 - 1) else Z.to_nat (z * 2).

Theorem Z2Nat_bij_id : ∀ k, Z_of_nat_surj (Z_to_nat_inj k) = k.
Proof.
intros.
unfold Z_of_nat_surj, Z_to_nat_inj.
destruct (Z_lt_dec k 0) as [Hk | Hk]. {
  rewrite Z2Nat.inj_sub; [ simpl | easy ].
  unfold Pos.to_nat; simpl.
  rewrite <- nat_mod_add_once.
  rewrite <- Nat.add_sub_swap. {
    rewrite <- Nat.add_sub_assoc; [ simpl | lia ].
    rewrite Z2Nat.inj_mul; [ simpl | lia | easy ].
    unfold Pos.to_nat; simpl.
    rewrite Nat.add_comm.
    rewrite Nat.Div0.mod_add.
    rewrite <- Nat.sub_succ_l. {
      rewrite Nat.sub_succ, Nat.sub_0_r.
      rewrite Nat.div_mul; [ | easy ].
      rewrite Z2Nat.id; [ | lia ].
      now rewrite Z.opp_involutive.
    }
    remember (Z.to_nat (- k)) as n eqn:Hn.
    destruct n; [ | lia ].
    apply (f_equal Z.of_nat) in Hn.
    rewrite Z2Nat.id in Hn; lia.
  }
  rewrite Z2Nat.inj_mul; [ simpl | lia | easy ].
  unfold Pos.to_nat; simpl.
  remember (- k)%Z as l eqn:Hl.
  apply (f_equal Z.opp) in Hl.
  rewrite Z.opp_involutive in Hl.
  subst k; rename l into k; f_equal.
  assert (H : (0 < k)%Z) by lia.
  clear Hk; rename H into Hk.
  remember (Z.to_nat k) as n eqn:Hn.
  destruct n; [ | lia ].
  apply (f_equal Z.of_nat) in Hn.
  rewrite Z2Nat.id in Hn; lia.
}
apply Z.le_ngt in Hk.
rewrite Z2Nat.inj_mul; [ simpl | easy | easy ].
unfold Pos.to_nat; simpl.
rewrite Nat.Div0.mod_mul.
rewrite Nat.div_mul; [ | easy ].
now rewrite Z2Nat.id.
Qed.

(* Rémi Nollet's code, modified *)

Theorem Cantor : ∀ E (F : E → (E → bool)), ∃ f : E → bool, ∀ x, f x ≠ F x x.
Proof.
intros E F; exists (fun e => negb (F e e)); intros x H.
exact (no_fixpoint_negb _ H).
Qed.

Lemma Cantor_gen : ∀ E X Y (Yss : Y → Prop),
  ∀ (sX : E → X) (sY : Y → (E → bool)),
  ∀ (sX_surj : ∀ e, ∃ x, sX x = e),
  ∀ (sY_surj : ∀ f, ∃ y, Yss y ∧ ∀ x, sY y x = f x),
  ∀ f : X → Y, ∃ y, ∀ x, Yss y ∧ y ≠ f x.
Proof.
intros * sX_surj sY_surj F.
destruct Cantor with E (fun e => sY (F (sX e))) as [f H].
destruct sY_surj with f as [y Hy]; subst.
destruct Hy as (Hy, Hyf).
exists y; intros x; split; [ easy | ]; subst.
destruct sX_surj with x as [e]; subst.
specialize (H e).
now intros H2; apply H; subst.
Qed.

(* End Rémi Nollet's code *)
