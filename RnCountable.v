(* Banach-Tarski paradox. *)
(* Coq v8.6 *)

Require Import Utf8.
Require Import Reals Psatz.

Require Import MiscReals Countable.

Notation "'ℝ'" := R.
Notation "x '≤' y" := (Rle x y) : R_scope.

Definition ter_bin_of_frac_part x n :=
  if Rlt_dec (frac_part (x * 3 ^ n)) (1 / 3) then false else true.

Fixpoint partial_sum3_aux k (u : nat → bool) pow i :=
  match k with
  | 0 => 0%R
  | S k' =>
      if u i then (pow / 3 + partial_sum3_aux k' u (pow / 3) (S i))%R
      else partial_sum3_aux k' u (pow / 3)%R (S i)
  end.

Definition partial_sum3 u k := partial_sum3_aux k u 1%R 0.

(* Σ (i=0,c-1) 3^(c-1-i)ui *)
Fixpoint n_partial_sum3 (u : ℕ → bool) c :=
  match c with
  | O => O
  | S c' => (3 * n_partial_sum3 u c' + Nat.b2n (u c'))%nat
  end.

Definition b2r b := INR (Nat.b2n b).

Theorem partial_sum3_aux_le_half_pow : ∀ u k pow pow2 i,
  (0 ≤ pow)%R
  → pow2 = (pow / 2)%R
  → (partial_sum3_aux k u pow i ≤ pow2)%R.
Proof.
intros * Hpow Hpow2; subst pow2.
revert pow i Hpow.
induction k; intros; simpl; [ lra | ].
destruct (u i).
 apply Rplus_le_reg_l with (r := (- (pow / 3))%R).
 rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
 eapply Rle_trans; [ apply IHk; lra | lra ].

 eapply Rle_trans; [ apply IHk; lra | lra ].
Qed.

Theorem partial_sum3_aux_succ : ∀ u n pow i,
  partial_sum3_aux (S n) u pow i =
  (partial_sum3_aux n u pow i +
   INR (Nat.b2n (u (i + n)%nat)) * pow / 3 ^ S n)%R.
Proof.
intros.
revert pow i.
induction n; intros.
 simpl; rewrite Rplus_0_r, Rplus_0_l, Rmult_1_r, Nat.add_0_r.
 destruct (u i); simpl; lra.

 remember (S n) as sn; simpl; subst sn.
 remember (u i) as bi eqn:Hbi; symmetry in Hbi.
 destruct bi.
  remember (3 ^ S n)%R as sn3 eqn:Hsn3.
  rewrite IHn; simpl; rewrite Hbi.
  rewrite Rplus_assoc.
  do 2 apply Rplus_eq_compat_l.
  rewrite <- Nat.add_succ_comm.
  unfold Rdiv; subst sn3.
  rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
  now do 3 rewrite Rmult_assoc.

  remember (3 ^ S n)%R as sn3 eqn:Hsn3.
  rewrite IHn; simpl; rewrite Hbi.
  rewrite <- Nat.add_succ_comm.
  apply Rplus_eq_compat_l.
  unfold Rdiv; subst sn3.
  rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
  now do 3 rewrite Rmult_assoc.
Qed.

Theorem partial_sum3_succ : ∀ u n,
  (partial_sum3 u (S n) =
   partial_sum3 u n + INR (Nat.b2n (u n)) / 3 ^ S n)%R.
Proof.
intros.
unfold partial_sum3.
rewrite partial_sum3_aux_succ.
now rewrite Rmult_1_r.
Qed.

Theorem partial_sum3_aux_add : ∀ u k₁ k₂ pow i,
  partial_sum3_aux (k₁ + k₂) u pow i =
  (partial_sum3_aux k₁ u pow i +
   partial_sum3_aux k₂ u (pow / 3 ^ k₁) (i + k₁))%R.
Proof.
intros.
revert k₂ pow i.
induction k₁; intros.
 now simpl; rewrite Rplus_0_l, Nat.add_0_r, Rdiv_1_r.

 simpl.
 remember (u i) as bi eqn:Hbi; symmetry in Hbi.
 rewrite <- Nat.add_succ_comm.
 unfold Rdiv at 7.
 rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
 rewrite <- Rmult_assoc; do 2 rewrite fold_Rdiv.
 destruct bi; [ | apply IHk₁; lra ].
 rewrite Rplus_assoc.
 apply Rplus_eq_compat_l, IHk₁; lra.
Qed.

Theorem partial_sum3_aux_nonneg : ∀ u k pos i,
  (0 ≤ pos)%R
  → (0 ≤ partial_sum3_aux k u pos i)%R.
Proof.
intros * Hpos.
revert pos i Hpos.
induction k; intros; simpl; [ lra | ].
destruct (u i); [ | apply IHk; lra ].
apply Rplus_le_le_0_compat; [ lra | apply IHk; lra ].
Qed.

Theorem partial_sum3_upper_bound : ∀ u n k,
  (partial_sum3 u k ≤ partial_sum3 u n + / (2 * 3 ^ n))%R.
Proof.
intros.
unfold partial_sum3.
destruct (le_dec k n) as [ Hkn | Hkn ].
 remember (n - k)%nat as nk eqn:Hnk.
 assert (Hn : (n = k + nk)%nat).
  now subst nk; rewrite Nat.add_comm, Nat.sub_add.

  subst n.
  rewrite partial_sum3_aux_add, Nat.add_0_l, Rplus_assoc.
  eapply Rplus_le_reg_l; rewrite Rplus_opp_l.
  rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
  apply Rplus_le_le_0_compat.
   apply partial_sum3_aux_nonneg.
   unfold Rdiv; rewrite Rmult_1_l.
   eapply Rmult_le_reg_l; [ | rewrite Rmult_0_r, Rinv_r; try lra ].
    apply pow_lt; lra.
    apply pow_nonzero; lra.

   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   apply Rmult_le_pos; [ lra | ].
   eapply Rmult_le_reg_l; [ | rewrite Rmult_0_r, Rinv_r; try lra ].
    apply pow_lt; lra.
    apply pow_nonzero; lra.

 apply Nat.nle_gt in Hkn.
 remember (k - n)%nat as nk eqn:Hnk.
 assert (Hn : (k = n + nk)%nat).
  subst nk; rewrite Nat.add_comm, Nat.sub_add; [ easy | ].
  now apply Nat.lt_le_incl.

  subst k; clear Hnk Hkn; rename nk into k.
  rewrite partial_sum3_aux_add, Nat.add_0_l.
  apply Rplus_le_compat_l.
  revert n.
  induction k; intros; simpl.
   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   apply Rmult_le_pos; [ lra | ].
   eapply Rmult_le_reg_l; [ | rewrite Rmult_0_r, Rinv_r; try lra ].
    apply pow_lt; lra.
    apply pow_nonzero; lra.

   remember (u n) as b eqn:Hb; symmetry in Hb.
   destruct b.
    apply Rplus_le_reg_l with (r := (- (1 / 3 ^ n / 3))%R).
    rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
    field_simplify; [ | apply pow_nonzero; lra ].
    rewrite Rdiv_1_r.
    apply partial_sum3_aux_le_half_pow.
     unfold Rdiv; rewrite Rmult_1_l.
     apply Rmult_le_pos; [ | lra ].
     eapply Rmult_le_reg_l; [ | rewrite Rmult_0_r, Rinv_r; try lra ].
      apply pow_lt; lra.
      apply pow_nonzero; lra.

     unfold Rdiv.
     rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
     replace (1 / 3 ^ n / 3)%R with (1 / (3 ^ S n))%R.
      eapply Rle_trans; [ apply IHk | ].
      apply Rle_Rinv.
       apply Rmult_lt_0_compat; [ lra | apply pow_lt; lra ].

       apply Rmult_lt_0_compat; [ lra | apply pow_lt; lra ].

       apply Rmult_le_compat_l; [ lra | ].
       apply Rle_pow; [ lra | apply Nat.le_succ_diag_r ].

      simpl; unfold Rdiv.
      rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
Qed.

Theorem partial_sum3_aux_shift_seq : ∀ u k pow i,
  partial_sum3_aux (S k) u pow i =
  ((pow * b2r (u i) + partial_sum3_aux k (λ n, u (S n)) pow i) / 3)%R.
Proof.
intros.
set (v := λ n, u (S n)).
revert pow i.
induction k; intros; [ simpl; destruct (u i); unfold b2r; simpl; lra | ].
rewrite partial_sum3_aux_succ.
rewrite IHk.
rewrite partial_sum3_aux_succ.
set (x := partial_sum3_aux k v pow i).
unfold v; rewrite <- Nat.add_succ_comm; simpl.
set (y := INR (Nat.b2n (u (S (i + k))))).
field_simplify; [ easy | | ]; apply pow_nonzero; lra.
Qed.

Theorem n_partial_sum3_succ2 : ∀ u n,
  n_partial_sum3 u (S n) =
  (3 ^ n * Nat.b2n (u O) + n_partial_sum3 (λ n, u (S n)) n)%nat.
Proof.
intros.
set (v n := u (S n)).
induction n; [ now simpl; do 2 rewrite Nat.add_0_r | ].
remember (S n) as sn; simpl; subst sn.
rewrite IHn; simpl.
set (m := n_partial_sum3 v n).
subst v.
do 3 rewrite Nat.add_0_r.
ring.
Qed.

Theorem n_partial_sum3_succ : ∀ u n,
  n_partial_sum3 u (S n) = (3 * n_partial_sum3 u n + Nat.b2n (u n))%nat.
Proof. easy. Qed.

Theorem partial_sum3_n_partial_sum3 : ∀ u n,
  (3 ^ n * partial_sum3 u n = INR (n_partial_sum3 u n))%R.
Proof.
intros.
unfold partial_sum3.
induction n; [ simpl; lra | ].
rewrite partial_sum3_aux_succ, n_partial_sum3_succ.
rewrite plus_INR, mult_INR; simpl.
replace (2 + 1)%R with 3%R by lra.
rewrite Rmult_plus_distr_l.
rewrite Rmult_assoc.
rewrite IHn.
apply Rplus_eq_compat_l.
rewrite Rmult_comm.
unfold Rdiv.
rewrite Rmult_1_r.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [ easy | ].
apply Rmult_integral_contrapositive.
split; [ lra | ].
apply pow_nonzero; lra.
Qed.

Theorem le_partial_sum3_lt_n_partial_sum3 : ∀ u r n,
  (r ≤ partial_sum3 u (S n) + / (2 * 3 ^ S n))%R
  → (r * 3 ^ n < INR (n_partial_sum3 u n) + 1)%R.
Proof.
intros * Hr2.
apply Rmult_le_compat_r with (r := (3 ^ n)%R) in Hr2; [ | apply pow_le; lra ].
rewrite Rmult_plus_distr_r in Hr2.
rewrite Rinv_mult_distr in Hr2; [ | lra | apply pow_nonzero; lra ].
simpl in Hr2.
rewrite Rinv_mult_distr in Hr2; [ | lra | apply pow_nonzero; lra ].
rewrite <- Rmult_assoc in Hr2.
rewrite Rmult_assoc in Hr2.
rewrite Rinv_l in Hr2; [ | apply pow_nonzero; lra ].
rewrite Rmult_1_r in Hr2.
rewrite <- Rinv_mult_distr in Hr2; [ | lra | lra ].
setoid_rewrite Rmult_comm in Hr2 at 2.
rewrite partial_sum3_succ in Hr2.
rewrite Rmult_plus_distr_l in Hr2.
unfold Rdiv in Hr2; simpl in Hr2.
rewrite Rinv_mult_distr in Hr2; [ | lra | apply pow_nonzero; lra ].
rewrite <- Rmult_assoc, Rmult_shuffle0 in Hr2.
rewrite <- Rmult_assoc in Hr2.
rewrite Rmult_assoc, Rmult_shuffle0 in Hr2.
rewrite <- Rmult_assoc in Hr2.
rewrite Rinv_r in Hr2; [ | apply pow_nonzero; lra ].
rewrite Rmult_1_l in Hr2.
rewrite  partial_sum3_n_partial_sum3 in Hr2.
destruct (u n); simpl in Hr2; lra.
Qed.

Theorem Int_part_n_partial_sum3 : ∀ u r n,
  (∀ k, (partial_sum3 u k ≤ r)%R)
  → (∀ b, (∀ k, (partial_sum3 u k ≤ b)%R) → (r ≤ b)%R)
  → Int_part (r * 3 ^ n) = Z.of_nat (n_partial_sum3 u n).
Proof.
intros * Hr1 Hr2.
specialize (Hr1 (S n)).
assert (H : (r ≤ partial_sum3 u (S n) + / (2 * 3 ^ S n))%R).
 apply Hr2, partial_sum3_upper_bound.

 clear Hr2; rename H into Hr2.
 rewrite (Int_part_interv (Z.of_nat (n_partial_sum3 u n))); [ easy | ].
 rewrite plus_IZR, <- INR_IZR_INZ; simpl.
 split.
  revert u r Hr1 Hr2.
  induction n; intros.
   unfold partial_sum3 in Hr1, Hr2; simpl in Hr1, Hr2; simpl.
   destruct (u O); simpl; lra.

   unfold partial_sum3 in Hr1, Hr2.
   rewrite partial_sum3_aux_shift_seq in Hr1, Hr2.
   rewrite Rmult_1_l in Hr1, Hr2.
   rewrite n_partial_sum3_succ2.
   remember (u O) as b eqn:Hb; symmetry in Hb.
   unfold b2r in Hr1, Hr2.
   destruct b.
    remember (S n) as sn; simpl in Hr1, Hr2; subst sn.
    simpl; rewrite Nat.mul_1_r.
    set (v n := u (S n)) in *.
    rewrite plus_INR.
    apply Rplus_le_reg_l with (r := (- INR (3 ^ n))%R).
    rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
    rewrite Rplus_comm.
    rewrite pow_INR; simpl.
    replace (2 + 1)%R with 3%R by lra.
    replace (- 3 ^ n)%R with ((- 1) * 3 ^ n)%R by lra.
    rewrite <- Rmult_assoc, <- Rmult_plus_distr_r.
    fold (Rminus (r * 3) 1).
    apply IHn; [ unfold partial_sum3; lra | ].
    unfold partial_sum3.
    set (x := partial_sum3_aux (S n) v 1 0) in *.
    apply Rplus_le_reg_r with (r := 1%R).
    replace (r * 3 - 1 + 1)%R with (r * 3)%R by lra.
    remember 3%R as three.
    rewrite Rplus_comm, <- Rplus_assoc; subst three.
    apply Rmult_le_reg_r with (r := (/ 3)%R); [ lra | ].
    rewrite Rmult_assoc, Rinv_r; [ | lra ].
    rewrite Rmult_1_r.
    rewrite Rmult_plus_distr_r.
    rewrite fold_Rdiv.
    rewrite <- Rinv_mult_distr; [ | | lra ].
     now rewrite <- Rmult_assoc in Hr2; rewrite Rmult_shuffle0.

     apply Rmult_integral_contrapositive.
     split; [ lra | apply pow_nonzero; lra ].

    remember (S n) as sn; simpl in Hr1, Hr2; subst sn.
    simpl; rewrite Nat.mul_0_r, Nat.add_0_l.
    rewrite Rplus_0_l in Hr1, Hr2.
    set (v n := u (S n)) in *.
    rewrite <- Rmult_assoc.
    apply IHn; [ unfold partial_sum3; lra | ].
    unfold partial_sum3.
    set (x := partial_sum3_aux (S n) v 1 0) in *.
    apply Rmult_le_reg_r with (r := (/ 3)%R); [ lra | ].
    rewrite Rmult_assoc, Rinv_r; [ | lra ].
    rewrite Rmult_1_r.
    rewrite Rmult_plus_distr_r.
    rewrite fold_Rdiv.
    rewrite <- Rinv_mult_distr; [ | | lra ].
     now rewrite <- Rmult_assoc in Hr2; rewrite Rmult_shuffle0.

     apply Rmult_integral_contrapositive.
     split; [ lra | apply pow_nonzero; lra ].
     now apply le_partial_sum3_lt_n_partial_sum3.
Qed.

Theorem IZR_Int_part_mult_pow_succ : ∀ u r n,
  (∀ k, (partial_sum3 u k ≤ r)%R)
  → (∀ b, (∀ k, (partial_sum3 u k ≤ b)%R) → (r ≤ b)%R)
  → IZR (Int_part (r * 3 ^ S n)) =
    (3 * IZR (Int_part (r * 3 ^ n)) + INR (Nat.b2n (u n)))%R.
Proof.
intros * Hr1 Hr2.
rewrite Int_part_n_partial_sum3 with (u := u); [ | easy | easy ].
rewrite Int_part_n_partial_sum3 with (u := u); [ | easy | easy ].
do 2 rewrite <- INR_IZR_INZ.
rewrite n_partial_sum3_succ.
rewrite plus_INR, mult_INR.
now replace (INR 3) with 3%R by (simpl; lra).
Qed.

Theorem Int_part_eq_partial_sum3 : ∀ u r n,
  (∀ k : nat, (partial_sum3 u k ≤ r)%R)
  → (∀ b : R, (∀ k : nat, (partial_sum3 u k ≤ b)%R) → (r ≤ b)%R)
  → IZR (Int_part (r * 3 ^ n)) = (partial_sum3 u n * 3 ^ n)%R.
Proof.
intros * Hk1 Hk2.
induction n.
 unfold partial_sum3; simpl.
 do 2 rewrite Rmult_1_r.
 specialize (Hk1 O); simpl in Hk1.
 unfold partial_sum3 in Hk1; simpl in Hk1.
 assert (H : ∀ k, (partial_sum3 u k ≤ 1 / 2)%R).
  intros k; apply partial_sum3_aux_le_half_pow; lra.

  specialize (Hk2 (1 / 2)%R H).
  replace 0%R with (IZR 0) by easy.
  apply IZR_eq, Int_part_interv; simpl; lra.

 rewrite partial_sum3_succ.
 rewrite Rmult_plus_distr_r.
 unfold Rdiv; rewrite Rmult_assoc.
 rewrite Rinv_l; [ | apply pow_nonzero; lra ].
 rewrite Rmult_1_r.
 remember (r * 3 ^ S n)%R as x; simpl; subst x.
 rewrite <- Rmult_assoc, Rmult_shuffle0, <- IHn.
 setoid_rewrite Rmult_comm at 3.
 now apply IZR_Int_part_mult_pow_succ.
Qed.

Theorem ter_bin_of_frac_part_surj : ∀ u : nat → bool,
  ∃ r : R, (0 ≤ r < 1)%R ∧ (∀ n, ter_bin_of_frac_part r n = u n).
Proof.
intros.
set (E x := ∃ k, partial_sum3 u k = x).
assert (Hb : bound E).
 exists (1 / 2)%R; subst E; simpl.
 intros r (k & H); subst r.
 apply partial_sum3_aux_le_half_pow; lra.

 assert (He : ∃ r, E r).
  exists 0%R; subst E; simpl.
  now exists O; unfold partial_sum3.

  destruct (completeness E Hb He) as (r & Hr1 & Hr2).
  assert (Hr3 : (∀ k, partial_sum3 u k ≤ r)%R).
   unfold is_upper_bound, E in Hr1; simpl in Hr1.
   now intros k; apply Hr1; exists k.

   assert (Hr4 : (∀ b, (∀ k, partial_sum3 u k ≤ b) → (r ≤ b))%R).
    unfold is_upper_bound, E in Hr2; simpl in Hr2.
    intros b H; apply Hr2; intros x (k, Hx); subst x.
    apply H.

    assert (Hh : (r ≤ 1 / 2)%R).
     apply Hr2; unfold E; simpl.
     intros x (k & H); subst x.
     apply partial_sum3_aux_le_half_pow; lra.

     exists r; clear Hb He; simpl.
     split.
      split; [ | lra ].
      apply Hr1; unfold E; simpl.
      now exists O; unfold partial_sum3.

      intros n.
      clear E Hr1 Hr2.
      unfold ter_bin_of_frac_part; symmetry.
      destruct (Rlt_dec (frac_part (r * 3 ^ n)) (1 / 3)) as [H1| H1].
       unfold frac_part in H1.
       rewrite (Int_part_eq_partial_sum3 u) in H1; [ | easy | easy ].
       unfold Rminus in H1.
       rewrite Ropp_mult_distr_l in H1.
       rewrite <- Rmult_plus_distr_r in H1.
       rewrite fold_Rminus in H1.
       apply Rmult_lt_compat_r with (r := (/ 3 ^ n)%R) in H1.
        rewrite Rmult_assoc in H1.
        rewrite Rinv_r in H1; [ | apply pow_nonzero; lra ].
        rewrite Rmult_1_r in H1.
        unfold Rdiv in H1.
        rewrite Rmult_assoc in H1.
        rewrite <- Rinv_mult_distr in H1; [ | lra | apply pow_nonzero; lra ].
        replace (3 * 3 ^ n)%R with (3 ^ S n)%R in H1 by easy.
        fold (Rdiv 1 (3 ^ S n)) in H1.
        specialize (Hr3 (S n)).
        rewrite partial_sum3_succ in Hr3.
        destruct (u n); [ exfalso | easy ].
        simpl in Hr3, H1; lra.

        apply Rinv_0_lt_compat, pow_lt; lra.

       apply Rnot_lt_le in H1.
       unfold frac_part in H1.
       rewrite (Int_part_eq_partial_sum3 u) in H1; [ | easy | easy ].
       unfold Rminus in H1.
       rewrite Ropp_mult_distr_l in H1.
       rewrite <- Rmult_plus_distr_r in H1.
       rewrite fold_Rminus in H1.
       apply Rmult_le_compat_r with (r := (/ 3 ^ n)%R) in H1.
        rewrite Rmult_assoc in H1.
        rewrite Rinv_r in H1; [ | apply pow_nonzero; lra ].
        rewrite Rmult_1_r in H1.
        unfold Rdiv in H1; rewrite Rmult_1_l in H1.
        rewrite <- Rinv_mult_distr in H1; [ | lra | apply pow_nonzero; lra ].
        replace (3 * 3 ^ n)%R with (3 ^ S n)%R in H1 by easy.
        specialize (partial_sum3_upper_bound u (S n)); intros H.
        apply Hr4 in H.
        rewrite partial_sum3_succ in H.
        destruct (u n); [ easy | exfalso ].
        simpl in H1, H.
        unfold Rdiv in H.
        rewrite Rmult_0_l, Rplus_0_r in H.
        rewrite Rinv_mult_distr in H; [ | lra | ].
         set (s := partial_sum3 u n) in H1, H.
         set (t := (/ (3 * 3 ^ n))%R) in H1, H.
         enough (0 < t)%R by lra; subst t.
         apply Rinv_0_lt_compat.
         apply Rmult_lt_0_compat; [ lra | apply pow_lt; lra ].

         apply Rmult_integral_contrapositive.
         split; [ lra | apply pow_nonzero; lra ].

        apply Rlt_le.
        apply Rinv_0_lt_compat.
        apply pow_lt; lra.
Qed.

Definition id {A} (a : A) := a.

Theorem id_nat : ∀ e : ℕ, ∃ x : ℕ, id x = e.
Proof. now intros; exists e. Qed.

Theorem Cantor_ℕ_ℝ : ∀ f : nat → R, ∃ x : R, ∀ n : nat, x ≠ f n.
Proof.
specialize
  (Cantor_gen ℕ ℕ ℝ (λ x, (0 ≤ x < 1)%R) id ter_bin_of_frac_part id_nat
     ter_bin_of_frac_part_surj).
intros H f.
specialize (H f).
destruct H as (x, H); exists x.
intros n; apply H.
Qed.
