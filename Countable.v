(* Banach-Tarski paradox. *)
(* Coq V8.6 *)

Require Import Utf8 NPeano Bool Compare_dec.
Require Import Misc.

Definition is_countable A := ∃ f : nat → A, FinFun.Surjective f.

Definition prod_nat_of_nat n :=
  let s := Nat.sqrt n in
  (s - (n - s ^ 2), n - s ^ 2)%nat.

Definition nat_of_prod_nat '(i, j) :=
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

Theorem prod_nat_of_nat_inv : ∀ i j,
  prod_nat_of_nat (nat_of_prod_nat (i, j)) = (i, j).
Proof.
intros; simpl.
unfold prod_nat_of_nat.
rewrite Nat.mul_1_r.
remember ((i + j) * (i + j) + j)%nat as n eqn:Hn.
remember (Nat.sqrt n) as s eqn:Hs.
rewrite Hn in Hs.
rewrite nat_sqrt_add in Hs.
 rewrite Nat.add_comm in Hn.
 subst; rewrite Nat.pow_2_r.
 rewrite Nat.add_sub.
 now rewrite Nat.add_sub.

 simpl.
 rewrite Nat.add_0_r, Nat.add_assoc, Nat.add_comm.
 apply Nat.le_add_r.
Qed.

Theorem countable_product_types : ∀ A B,
  is_countable A
  → is_countable B
  → is_countable (A * B).
Proof.
intros * (fa, HA) (fb, HB).
unfold is_countable.
exists (λ n, let (i, j) := prod_nat_of_nat n in (fa i, fb j)).
intros (a, b).
specialize (HA a) as (na, Hna).
specialize (HB b) as (nb, Hnb).
subst a b.
exists (nat_of_prod_nat (na, nb)).
remember (prod_nat_of_nat (nat_of_prod_nat (na, nb))) as ij eqn:Hij.
symmetry in Hij.
destruct ij as (i, j).
rewrite prod_nat_of_nat_inv in Hij.
now injection Hij; intros; subst.
Qed.

Theorem countable_sum_types : ∀ A B,
  is_countable A
  → is_countable B
  → is_countable (A + B).
Proof.
intros * (fa, Ha) (fb, Hb).
unfold is_countable.
exists (λ n, if zerop (n mod 2) then inl (fa (n / 2)) else inr (fb (n / 2))).
intros [a| b].
 specialize (Ha a) as (n, Ha).
 exists (n * 2)%nat; subst a.
 rewrite Nat.mod_mul; [ simpl | easy ].
 now rewrite Nat.div_mul.

 specialize (Hb b) as (n, Hb).
 exists (n * 2 + 1)%nat; subst b.
 rewrite Nat.add_comm, Nat.mod_add; [ simpl | easy ].
 now rewrite <- Nat.add_1_l, Nat.div_add.
Qed.

Theorem countable_surjection : ∀ A B (f : A → B),
  is_countable A
  → FinFun.Surjective f
  → is_countable B.
Proof.
intros * (fa, HA) Hf.
unfold FinFun.Surjective in Hf.
exists (λ n, f (fa n)).
intros b.
specialize (Hf b) as (a, Hf).
specialize (HA a) as (n, HA).
now subst; exists n.
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
