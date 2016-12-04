(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List Relations NPeano Wf_nat.
Import ListNotations.
Require Import Reals Psatz Nsatz.

Require Import Misc Words Normalize Reverse MiscReals Matrix Pset Orbit.
Require Import Partition OrbitRepr GroupTransf Equidecomp Cantor RnCountable.

Theorem Rno_intersect_spheres_x3_x6 : ∀ x y z,
  ((x - 3)² + y² + z² <= 1)%R
  → ((x - 6)² + y² + z² <= 1)%R
  → False.
Proof.
intros x y z H3 H6.
apply Rplus_le_reg_pos_r in H3; [ | apply Rle_0_sqr ].
apply Rplus_le_reg_pos_r in H3; [ | apply Rle_0_sqr ].
apply Rplus_le_reg_pos_r in H6; [ | apply Rle_0_sqr ].
apply Rplus_le_reg_pos_r in H6; [ | apply Rle_0_sqr ].
clear - H3 H6.
rewrite <- Rsqr_1 in H3 at 4.
rewrite <- Rsqr_1 in H6 at 6.
apply Rsqr_le_abs_0 in H3.
apply Rsqr_le_abs_0 in H6.
rewrite Rabs_R1 in H3, H6.
unfold Rabs in H3, H6.
destruct (Rcase_abs (x - 3)), (Rcase_abs (x - 6)); lra.
Qed.

Theorem Banach_Tarski_paradox_but_fixpoints :
  equidecomposable sphere_but_fixpoints
    (xtransl 3 sphere_but_fixpoints ∪ xtransl 6 sphere_but_fixpoints)%S.
Proof.
pose proof TTCA _ same_orbit equiv_same_orbit as H.
destruct H as (f & Hu & Hm).
remember (mkcf _ _ f Hm Hu) as Hosf.
remember (mkos _ f) as os eqn:Hos.
clear HeqHosf.
set (A₁ := (M ∪ SS ạ ∪ B)%S).
set (A₂ := (SS ạ⁻¹ ∖ B)%S).
set (A₃ := SS ḅ).
set (A₄ := SS ḅ⁻¹).
exists [A₁; A₂; A₃; A₄].
exists
  (map (xtransl 3) [A₁; rot ạ A₂] ++
   map (xtransl 6) [A₃; rot ḅ A₄]); simpl.
split.
 subst A₁ A₂ A₃ A₄.
 eapply r_decomposed_4; now try eassumption.

 split.
  pose proof r_decomposed_2_a f Hosf os Hos as Ha.
  pose proof r_decomposed_2_b f Hosf os Hos as Hb.
  eapply partition_group_map with (g := Xtransl 3) in Ha; try eassumption.
  eapply partition_group_map with (g := Xtransl 6) in Hb; try eassumption.
  eapply partition_union in Hb; [ | | apply Ha ].
   apply Hb.

   unfold intersection, set_eq; intros (x, y, z).
   split; [ intros (H₁, H₂) | easy ].
   simpl in H₁, H₂.
   unfold empty_set; simpl.
   destruct H₁ as (H₁, H₃).
   destruct H₂ as (H₂, H₄).
   unfold sphere in H₁, H₂.
   now apply (Rno_intersect_spheres_x3_x6 x y z).

  constructor; [ now exists (Xtransl 3) | ].
  constructor; [ now exists (Comb (Xtransl 3) (Rot ạ)) | ].
  constructor; [ now exists (Xtransl 6) | ].
  constructor; [ now exists (Comb (Xtransl 6) (Rot ḅ)) | ].
  constructor.
Qed.

Check Banach_Tarski_paradox_but_fixpoints.

Theorem equidec_union : ∀ E₁ E₂ F₁ F₂,
  (E₁ ∩ F₁ = ∅)%S
  → (E₂ ∩ F₂ = ∅)%S
  → equidecomposable E₁ E₂
  → equidecomposable F₁ F₂
  → equidecomposable (E₁ ∪ F₁) (E₂ ∪ F₂).
Proof.
intros * HEF₁ HEF₂ HE HF.
destruct HE as (PE₁ & PE₂ & HE₁ & HE₂ & HE).
destruct HF as (PF₁ & PF₂ & HF₁ & HF₂ & HF).
unfold equidecomposable.
exists (PE₁ ++ PF₁), (PE₂ ++ PF₂).
split; [ now apply partition_union | ].
split; [ now apply partition_union | ].
now apply Forall2_app.
Qed.

Theorem equidec_transl : ∀ dx E F,
  equidecomposable E F
  → equidecomposable (xtransl dx E) (xtransl dx F).
Proof.
intros * HEF.
destruct HEF as (PE & PF & HPE & HPF & HEF).
unfold equidecomposable.
exists (map (xtransl dx) PE), (map (xtransl dx) PF).
split; [ apply (partition_group_map E PE (Xtransl dx) HPE) | ].
split; [ apply (partition_group_map F PF (Xtransl dx) HPF) | ].
apply Forall2_Forall_combine in HEF.
destruct HEF as (HEF, Hlen).
apply Forall2_Forall_combine.
do 2 rewrite map_length.
split; [ | easy ].
rewrite Forall_forall in HEF.
apply Forall_forall; intros (E₁, F₁) HEF₁.
rewrite combine_map in HEF₁.
apply in_map_iff in HEF₁.
destruct HEF₁ as ((E₂ & F₂) & Hp & HEF₁).
injection Hp; clear Hp; intros; subst E₁ F₁.
apply HEF in HEF₁.
destruct HEF₁ as (g, HEF₁).
exists (Comb (Xtransl dx) (Comb g (Xtransl (-dx)))); simpl.
rewrite xtransl_xtransl, Rplus_opp_l.
now rewrite xtransl_0, HEF₁.
Qed.

Theorem separated_spheres_without_fixpoints :
  (xtransl 3 sphere_but_fixpoints ∩ xtransl 6 sphere_but_fixpoints = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6); simpl | easy ].
unfold sphere_but_fixpoints in H3, H6.
simpl in H3, H6.
destruct H3 as (H3, _).
destruct H6 as (H6, _).
now apply (Rno_intersect_spheres_x3_x6 x y z).
Qed.

Theorem separated_spheres :
  (xtransl 3 sphere ∩ xtransl 6 sphere = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6) | easy ].
unfold sphere in H3, H6.
simpl in H3, H6.
now apply (Rno_intersect_spheres_x3_x6 x y z).
Qed.

Definition nat_of_free_elem e : nat :=
  match e with
  | ạ => 0
  | ạ⁻¹ => 1
  | ḅ => 2
  | ḅ⁻¹ => 3
  end.

Definition free_elem_of_nat n :=
  match n with
  | 0 => ạ
  | 1 => ạ⁻¹
  | 2 => ḅ
  | _ => ḅ⁻¹
  end.

Fixpoint path_of_nat_aux it (n : nat) :=
  match it with
  | O => []
  | S it' =>
      free_elem_of_nat (n mod 4) ::
      match (n / 4)%nat with
      | O => []
      | S n' => path_of_nat_aux it' n'
      end
  end.

Definition path_of_nat n :=
  match n with
  | O => []
  | S n' => path_of_nat_aux n n'
  end.

Theorem free_elem_of_nat_nat_of_free_elem_mod_4 : ∀ e,
  free_elem_of_nat (nat_of_free_elem e mod 4) = e.
Proof. intros (t, d); now destruct t, d. Qed.

Theorem nat_of_free_elem_div_4 : ∀ e, (nat_of_free_elem e / 4 = 0)%nat.
Proof. intros (t, d); now destruct t, d. Qed.

Theorem path_of_nat_aux_enough_iter : ∀ m n p,
  m < n
 → m < p
  → path_of_nat_aux n m = path_of_nat_aux p m.
Proof.
intros * Hmn Hmp.
revert m p Hmn Hmp.
induction n; intros; [ easy | ].
destruct p; [ easy | ].
simpl; f_equal.
remember (m / 4) as q eqn:Hq; symmetry in Hq.
destruct q; [ easy | ].
destruct m; [ easy | ].
apply Nat.succ_lt_mono in Hmn.
apply Nat.succ_lt_mono in Hmp.
destruct (lt_dec q n) as [Hqn| Hqn].
 destruct (lt_dec q p) as [Hqp| Hqp]; [ apply IHn; easy | ].
 apply Nat.nlt_ge in Hqp.
 apply Nat.succ_le_mono in Hqp.
 rewrite <- Hq in Hqp.
 apply Nat.succ_lt_mono in Hmp.
 assert (H : S m < S m / 4) by (eapply Nat.lt_le_trans; eassumption).
 apply Nat.nle_gt in H.
 exfalso; apply H; clear.
 remember (S m) as n; clear m Heqn.
 apply Nat.div_le_upper_bound; [ easy | ].
 induction n; [ easy | ].
 rewrite Nat.mul_comm; simpl.
 apply -> Nat.succ_le_mono.
 eapply Nat.le_trans; [ eassumption | ].
 rewrite Nat.mul_comm.
 eapply Nat.le_trans; [ | eapply Nat.le_succ_diag_r ].
 eapply Nat.le_trans; eapply Nat.le_succ_diag_r.

 apply Nat.nlt_ge in Hqn.
 apply Nat.succ_le_mono in Hqn.
 rewrite <- Hq in Hqn.
 assert (H : m < S m / 4).
  eapply lt_trans; [ eapply Hmn | assumption ].

  exfalso; clear - H.
  apply Nat.nle_gt in H.
  exfalso; apply H; clear.
  destruct m; [ easy | ].
  apply Nat.div_le_upper_bound; [ easy | simpl ].
  rewrite <- Nat.add_succ_comm; simpl.
  do 2 apply -> Nat.succ_le_mono.
  apply Nat.le_add_r.
Qed.

Theorem path_of_nat_aux_cons : ∀ e p q, (q < p)%nat →
  ∃ m n : ℕ, n < m ∧ path_of_nat_aux m n = e :: path_of_nat_aux p q.
Proof.
intros * Hqp.
remember (nat_of_free_elem e) as r eqn:Hr.
exists (S (r + S q * 4)), (r + S q * 4)%nat.
split; [ apply Nat.lt_succ_diag_r | ].
remember (S q) as sq; simpl; subst sq.
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.div_add; [ | easy ].
rewrite <- Nat.add_succ_comm.
remember (S q * 4)%nat as qq; simpl; subst qq.
rewrite Hr, free_elem_of_nat_nat_of_free_elem_mod_4.
f_equal.
rewrite nat_of_free_elem_div_4, Nat.add_0_l.
apply path_of_nat_aux_enough_iter; [ | easy ].
eapply Nat.lt_trans; [ apply Nat.lt_succ_diag_r | ].
rewrite Nat.mul_comm, Nat.add_comm; simpl.
do 4 rewrite <- Nat.add_succ_l.
rewrite <- Nat.add_assoc.
apply Nat.lt_add_pos_r, Nat.lt_0_succ.
Qed.

Theorem path_of_nat_aux_is_cons : ∀ e el,
  ∃ m n, (n < m)%nat ∧ path_of_nat_aux m n = e :: el.
Proof.
intros.
revert e.
induction el as [| e₁]; intros.
 remember (nat_of_free_elem e) as m eqn:Hm.
 exists (S m), m.
 split; [ now apply Nat.lt_succ_r | ].
 now subst m; destruct e as (t, d); destruct t, d.

 pose proof IHel e₁ as He₁.
 destruct He₁ as (p & q & Hpq & He₁).
 rewrite <- He₁.
 clear - Hpq.
 now apply path_of_nat_aux_cons.
Qed.

Theorem paths_are_countable : is_countable (list free_elem).
Proof.
unfold is_countable; simpl.
exists path_of_nat.
intros el.
destruct el as [| e el]; [ now exists O | ].
enough (Hn : ∃ n, path_of_nat (S n) = e :: el).
 destruct Hn as (n, Hn).
 now exists (S n).

 pose proof path_of_nat_aux_is_cons e el.
 destruct H as (m & n & Hmn & H).
 exists n; unfold path_of_nat.
 rewrite path_of_nat_aux_enough_iter with (p := m); try easy.
 apply Nat.lt_succ_diag_r.
Qed.

Definition unit_interv := mkset (λ x, (0 <= x < 1)%R).

Definition ter_bin_of_point '(P x y z) := ter_bin_of_frac_part x.

Theorem ter_bin_of_sphere_surj : ∀ u : ℕ → bool,
  ∃ p : point, p ∈ sphere ∧ (∀ n, ter_bin_of_point p n = u n).
Proof.
intros.
specialize (ter_bin_of_frac_part_surj u); intros (r & Hr & Hn).
exists (P r 0 0); simpl in Hr; simpl.
split; [ | easy ].
do 2 rewrite Rsqr_pow2.
rewrite pow_i; [ | apply Nat.lt_0_succ ].
do 2 rewrite Rplus_0_r.
replace 1%R with (1 ^ 2)%R by lra.
apply pow_incr; lra.
Qed.

Theorem sphere_not_countable : ¬ (is_countable {p : point | p ∈ sphere}).
Proof.
intros H.
unfold is_countable in H.
destruct H as (f, Hf).
enough (Hcontr : ∃ a, a ∈ sphere ∧ ∀ n, proj1_sig (f n) ≠ a).
 destruct Hcontr as (a & Ha & Hnn).
 specialize (Hf (exist _ a Ha)).
 destruct Hf as (n, Hn).
 specialize (Hnn n).
 now rewrite Hn in Hnn; apply Hnn.

 specialize
  (Cantor_gen ℕ ℕ point (setp sphere) id ter_bin_of_point id_nat
     ter_bin_of_sphere_surj).
 intros H.
 specialize (H (λ n, proj1_sig (f n))) as (p, H).
 exists p.
 split; [ apply (H O) | ].
 intros n Hn.
 specialize (H n).
 destruct H.
 now symmetry in Hn.
Qed.

Definition prod_nat_of_nat n :=
  let s := Nat.sqrt n in
  (s - (n - s ^ 2), n - s ^ 2)%nat.

Definition nat_of_prod_nat '(i, j) :=
  ((i + j) ^ 2 + j)%nat.

Theorem prod_nat_of_nat_inv : ∀ i j,
  prod_nat_of_nat (nat_of_prod_nat (i, j)) = (i, j).
Proof.
intros; simpl.
unfold prod_nat_of_nat.
rewrite Nat.mul_1_r.
remember ((i + j) * (i + j) + j)%nat as n eqn:Hn.
remember (Nat.sqrt n) as s eqn:Hs.
revert j n s Hn Hs.
induction i; intros.
 simpl; rewrite Nat.mul_1_r.
 simpl in Hn.
 revert n s Hn Hs.
 induction j; intros; [ now subst n s | ].

Theorem glop : ∀ n p, (p ≤ 2 * n)%nat → Nat.sqrt (n * n + p) = n.
Proof.
intros * Hp.
revert p Hp.
induction n; intros; [ now apply Nat.le_0_r in Hp; subst p | ].
simpl.

bbb.
revert i.
induction j; intros.
 simpl; rewrite Nat.mul_1_r.
 do 2 rewrite Nat.add_0_r.
 unfold prod_nat_of_nat.
 rewrite Nat.sqrt_square, Nat.pow_2_r.
 now rewrite Nat.sub_diag, Nat.sub_0_r.

 remember (nat_of_prod_nat (i, S j)) as n eqn:Hn.
 unfold prod_nat_of_nat.
 unfold nat_of_prod_nat in Hn.
bbb.

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
bbb.

Fixpoint prod_nat_of_nat n :=
  match n with
  | O => (O, O)
  | S n' =>
      let (i, j) := prod_nat_of_nat n' in
      match i with
      | O => (S j, O)
      | S i' => (i', S j)
      end
  end.

Fixpoint nat_of_nat_nat_aux k i j : nat :=
  match k with
  | O => O
  | S k' =>
      match j with
      | O =>
          match i with
          | O => O
          | S i' => S (nat_of_nat_nat_aux k' O i')
          end
      | S j' => S (nat_of_nat_nat_aux k' (S i) j')
      end
  end.

Definition nat_of_nat_nat2 i j := nat_of_nat_nat_aux (i + j) i j.

Fixpoint nat_of_prod_nat_O_r i : nat :=
  match i with
  | O => O
  | S i' => S (nat_of_prod_nat_O_r i' + i')
  end.

Fixpoint nat_of_nat_nat i j : nat :=
  match j with
  | O => nat_of_prod_nat_O_r i
  | S j' => S (nat_of_nat_nat (S i) j')
  end.

Definition nat_of_prod_nat '(i, j) := nat_of_nat_nat i j.

Definition nat_of_prod_nat_f '(i, j) := ((i + j) * S (i + j) / 2 + j)%nat.

Theorem succ_succ_div_2 : ∀ n, (S (S n) / 2 = S (n / 2))%nat.
Proof.
intros n.
do 2 rewrite <- Nat.add_1_r.
rewrite <- Nat.add_assoc; simpl.
replace 2%nat with (1 * 2)%nat by easy.
rewrite Nat.div_add; [ | easy ].
now rewrite Nat.add_1_r.
Qed.

Theorem nat_of_prod_nat_O_r_sum : ∀ i,
  nat_of_prod_nat_O_r i = ((i * S i) / 2)%nat.
Proof.
intros.
induction i; [ easy | ].
simpl; rewrite IHi; rewrite succ_succ_div_2; f_equal.
setoid_rewrite Nat.mul_comm; simpl.
rewrite Nat.add_assoc.
replace (i + i)%nat with (i * 2)%nat by ring.
rewrite Nat.div_add_l; [ | easy ].
apply Nat.add_comm.
Qed.

Theorem nat_of_prod_nat_form : ∀ ij,
  nat_of_prod_nat ij = nat_of_prod_nat_f ij.
Proof.
intros (i, j); simpl.
revert i.
induction j; intros.
 simpl; do 2 rewrite Nat.add_0_r.
 apply nat_of_prod_nat_O_r_sum.

 simpl; rewrite Nat.add_succ_r; f_equal.
 rewrite <- Nat.add_succ_comm.
 apply IHj.
Qed.

Theorem nat_of_nat_nat_succ_l : ∀ i j,
  nat_of_nat_nat (S i) j = S (nat_of_nat_nat i j + i + j).
Proof.
intros.
revert i.
induction j; intros; [ now rewrite Nat.add_0_r | ].
simpl; rewrite IHj.
do 2 rewrite <- Nat.add_assoc.
now rewrite <- Nat.add_succ_comm.
Qed.

Theorem nat_of_prod_nat_inv : ∀ n,
  nat_of_prod_nat (prod_nat_of_nat n) = n.
Proof.
intros.
induction n; [ easy | simpl ].
remember (prod_nat_of_nat n) as ij eqn:Hij.
symmetry in Hij.
destruct ij as (i, j); simpl in IHn.
destruct i.
 simpl; f_equal; subst n.
 clear Hij.
 induction j; [ easy | ].
 simpl; rewrite IHj; f_equal.
 now rewrite nat_of_nat_nat_succ_l, Nat.add_0_r, <- Nat.add_succ_comm, <- IHj.

 now simpl; rewrite IHn.
Qed.

Theorem nat_of_prod_nat_O_r_succ : ∀ i,
  nat_of_prod_nat_O_r (S i) = S (nat_of_nat_nat 0 i).
Proof.
intros i; simpl.
induction i; [ easy | simpl ].
f_equal; f_equal.
apply Nat.succ_inj in IHi.
rewrite IHi; clear IHi.
rewrite nat_of_nat_nat_succ_l, Nat.add_0_r.
now rewrite <- Nat.add_succ_comm.
Qed.

Theorem glop : ∀ i n,
  nat_of_prod_nat_O_r (i + S n) =
  S (nat_of_prod_nat_O_r i + i * S n + n * (S n) / 2)%nat.
Proof.
intros.
revert i.
induction n; intros.
 simpl.
 rewrite Nat.div_small; [ | apply Nat.lt_0_succ ].
 rewrite Nat.mul_1_r.
 rewrite Nat.add_0_r.
 now rewrite Nat.add_comm.

 rewrite <- Nat.add_succ_comm, IHn; simpl.
 f_equal; rewrite <- Nat.add_succ_r.
 ring_simplify.
 do 2 rewrite <- Nat.add_assoc; f_equal.
 symmetry.
 replace 2%nat with (1 * 2)%nat at 1 by easy.
 rewrite Nat.div_add_l; [ | easy ].
 simpl; symmetry.
 rewrite Nat.add_assoc, Nat.add_comm; simpl; f_equal.
 rewrite Nat.mul_comm; simpl.
 symmetry; rewrite Nat.mul_comm; simpl.
(* merde, c'est faux *)
Abort.

Fixpoint greatest_triangular_aux k n :=
  match k with
  | O => O
  | S k' =>
      let m := (k * (k + 1) / 2)%nat in
      if le_dec m n then k else greatest_triangular_aux k' n
  end.

Definition greatest_triangular_index n := greatest_triangular_aux n n.

Fixpoint sum_up_to k :=
  match k with
  | O => O
  | S k' => (k + sum_up_to k')%nat
  end.

Theorem caca : ∀ i j, prod_nat_of_nat (sum_up_to (i + j) + j) = (i, j).
Proof.
intros.
remember (i + j)%nat as k eqn:Hk.
symmetry in Hk.
revert i j Hk.
induction k; intros.
 apply Nat.eq_add_0 in Hk.
 now destruct Hk; subst.

 remember prod_nat_of_nat as f; simpl; subst f.
 rewrite <- Nat.add_succ_r.
Abort.

Theorem essai : ∀ k, prod_nat_of_nat (sum_up_to k) = (k, O).
Proof.
intros k.
induction k as (k, Hk) using lt_wf_rec.
destruct k; [ easy | simpl ].
remember (prod_nat_of_nat (k + sum_up_to k)) as ij eqn:Hij.
symmetry in Hij.
destruct ij as (i, j).
destruct i.
 f_equal; f_equal.
 remember (prod_nat_of_nat (S k + sum_up_to k)) as ij eqn:Hij₁.
 symmetry in Hij₁.
 destruct ij as (i₁, j₁).
 generalize Hij₁; intros H.
 simpl in H; rewrite Hij in H.
 injection H; clear H; intros; subst i₁ j₁.
Abort.
(*
intros k.
induction k; [ easy | simpl ].
remember (prod_nat_of_nat (k + sum_up_to k)) as ij eqn:Hij.
symmetry in Hij.
destruct ij as (i, j).
destruct i.
 f_equal; f_equal.
 remember (prod_nat_of_nat (S k + sum_up_to k)) as ij eqn:Hij₁.
 symmetry in Hij₁.
 destruct ij as (i₁, j₁).
 generalize Hij₁; intros H.
 simpl in H; rewrite Hij in H.
 injection H; clear H; intros; subst i₁ j₁.
SearchAbout (_ → (∀ _ : nat, _ _)).
bbb.
*)

Theorem prod_nat_of_nat_inv_O_r : ∀ i,
  prod_nat_of_nat (nat_of_prod_nat_O_r i) = (i, O).
Proof.
intros i.
induction i; [ easy | simpl ].
remember (prod_nat_of_nat (nat_of_prod_nat_O_r i + i)) as ij eqn:Hij.
symmetry in Hij.
destruct ij as (i₁, j).
destruct i₁.
 f_equal; f_equal.
 destruct i; [ now simpl in Hij; injection Hij; intros; subst j | ].
 simpl in IHi, Hij.
 remember (prod_nat_of_nat (nat_of_prod_nat_O_r i + i)) as ij eqn:Hij₂.
 symmetry in Hij₂.
 destruct ij as (i₂, j₂).
 destruct i₂.
  injection IHi; clear IHi; intros; subst j₂.
  remember (prod_nat_of_nat (nat_of_prod_nat_O_r i + i + S i)) as ij eqn:Hij₃.
  symmetry in Hij₃.
  destruct ij as (i₃, j₃).
  destruct i₃; [ easy | ].
  injection Hij; clear Hij; intros; subst i₃ j.
  f_equal; rename j₃ into j.
  destruct i; [ now simpl in Hij₃; injection Hij₃; intros; subst j | ].
  simpl in Hij₂, Hij₃.
Abort.

Theorem prod_nat_of_nat_inv : ∀ ij,
  prod_nat_of_nat (nat_of_prod_nat ij) = ij.
Proof.
intros (i, j).
rewrite nat_of_prod_nat_form; simpl.
bbb.

revert i.
induction j; intros.
 simpl.
 induction i; [ easy | ].
 do 2 rewrite Nat.add_0_r in IHi.
 do 2 rewrite Nat.add_0_r.

Theorem glop : ∀ k, prod_nat_of_nat (k * S k / 2) = (k, O).
Proof.
Admitted.

(*
Theorem glop : ∀ i k,
  i = (k * S k / 2)%nat
  → prod_nat_of_nat i = (k, O).
Proof.
intros * Hk.
revert i Hk.
induction k; intros; [ now subst i | ].
subst i; simpl.
rewrite succ_succ_div_2; simpl.

bbb.
intros * Hk.
revert k Hk.
induction i; intros.
 destruct k; [ easy | simpl in Hk ].
 now rewrite succ_succ_div_2 in Hk.

 simpl.
 remember (prod_nat_of_nat i) as ij eqn:Hij₁.
 symmetry in Hij₁.
 destruct ij as (i₁, j₁).
 destruct i₁.
  f_equal.
  destruct k; [ easy | ].
  f_equal; simpl in Hk.
  rewrite succ_succ_div_2 in Hk.
  apply Nat.succ_inj in Hk.
  rewrite Hk in Hij₁.
  rewrite Nat.mul_comm in Hij₁.
  simpl in Hij₁.

bbb.
*)
Show.
Check glop.
apply glop.
setoid_rewrite <- Nat.add_succ_comm at 2 3.

bbb.
Restart.

intros (i, j).
rewrite nat_of_prod_nat_form; simpl.
revert j.
induction i; intros.
 simpl.
 induction j; [ easy | simpl ].
 rewrite succ_succ_div_2.
 simpl.
bbb.

 induction i; [ easy | simpl ].
 rewrite succ_succ_div_2.
 simpl.
 rewrite Nat.mul_comm; simpl.
 rewrite <- Nat.div2_div.
bbb.

 destruct i; [ easy | ].
 destruct i; [ easy | ].
 destruct i; [ easy | ].
 destruct i; [ easy | ].
 destruct i; [ easy | ].
 destruct i; [ easy | ].
 destruct i; [ easy | ].
 destruct i; [ easy | ].
bbb.

 destruct i; [ easy | ].
 rewrite nat_of_prod_nat_O_r_succ; simpl.
induction i; [ easy | ].
simpl.
rewrite nat_of_nat_nat_succ_l, Nat.add_0_r.
simpl.
Print prod_nat_of_nat.

bbb.

rewrite nat_of_nat_nat_succ_l.
rewrite Nat.add_0_r.
simpl.

bbb.

 destruct i; [ easy | ].
Check nat_of_prod_nat_O_r_succ.

simpl in IHi; simpl.
assert (nat_of_prod_nat_O_r i + i = nat_of_prod_nat_O_r (S i) - 1)%nat.
 now simpl; rewrite Nat.sub_0_r.
rewrite H in IHi.
bbb.
Print prod_nat_of_nat.
assert (∀ i, prod_nat_of_nat (i - 1) =

 destruct i; [ easy | ].
 destruct i; [ easy | ].
simpl.

bbb.
intros (i, j); simpl.
remember (i + j)%nat as s eqn:Hs.
symmetry in Hs.
revert i j Hs.
induction s; intros.
 apply Nat.eq_add_0 in Hs.
 now destruct Hs; subst i j.

 revert i Hs.
 induction j; intros.
  rewrite Nat.add_0_r in Hs; subst i.
  rewrite nat_of_nat_nat_succ_l, Nat.add_0_r.
  rewrite <- Nat.add_succ_r; simpl.
bbb.

intros (i, j); simpl.
destruct j.
 simpl.
 destruct i; [ easy | simpl ].
 remember (prod_nat_of_nat (nat_of_prod_nat_O_r i + i)) as ij eqn:Hij.
 symmetry in Hij.
 destruct ij as (i', j').
 destruct i'.
  destruct i; [ now simpl in Hij; injection Hij; intros; subst | ].
  rewrite nat_of_prod_nat_O_r_succ in Hij.
  simpl in Hij.
  remember (prod_nat_of_nat (nat_of_nat_nat 0 i + S i)) as ij eqn:Hij2.
  symmetry in Hij2.
  destruct ij as (i'', j'').
  destruct i''; [ easy | ].
  injection Hij; clear Hij; intros; subst i'' j'.
  rewrite <- Nat.add_succ_comm in Hij2; simpl in Hij2.
  remember (prod_nat_of_nat (nat_of_nat_nat 0 i + i)) as ij eqn:Hij3.
  symmetry in Hij3.
  destruct ij as (i''', j''').
  destruct i'''.
   injection Hij2; clear Hij2; intros; subst j'' j'''.
bbb.
SearchAbout nat_of_nat_nat.
Print nat_of_nat_nat.

  rewrite nat_of_prod_nat_O_r_succ, <- Nat.add_succ_comm in Hij.
  simpl in Hij.
  re
SearchAbout nat_of_prod_nat_O_r.

remember (i + j)%nat as s eqn:Hs.
symmetry in Hs.



intros (i, j); simpl.
remember (nat_of_nat_nat i j) as n eqn:Hn.
symmetry in Hn.
revert i j Hn.
induction n; intros.
 destruct j; intros; [ now destruct i | easy ].

 destruct j.
  destruct i; [ easy | ].
  simpl in Hn; simpl.
  apply Nat.succ_inj in Hn.
  remember (prod_nat_of_nat n) as ij eqn:Hij.
  symmetry in Hij.
  destruct ij as (i', j').
  destruct i'.
   subst n.

Theorem glop : ∀ m n,
  prod_nat_of_nat (m + n) = ...

bbb.
intros (i, j); simpl.
revert i.
induction j; intros; simpl.
 induction i; [ easy | ].
 rewrite nat_of_prod_nat_O_r_succ; simpl.
 remember (prod_nat_of_nat (nat_of_nat_nat 0 i)) as ij eqn:Hij.
 symmetry in Hij.
 destruct ij as (i', j').
 destruct i'.
  revert i IHi Hij.
  induction j'; intros.
   destruct i; [ easy | ].
   simpl in Hij.
   remember (prod_nat_of_nat (nat_of_nat_nat 1 i)) as ij eqn:Hij'.
   destruct ij as (i'', j'').
   now destruct i''.

   destruct i; [ easy | ].
   simpl in Hij.
   simpl in IHi.

bbb.

assert (∀ i, nat_of_prod_nat (S i, O) = S (nat_of_prod_nat (O, i))).
 clear; intros.
 simpl.
Focus 2.
 simpl in H.
 specialize (H i).
 apply Nat.succ_inj in H.
 rewrite H.
remember (prod_nat_of_nat (nat_of_nat_nat 0 i)) as ij eqn:Hij.
symmetry in Hij.
destruct ij as (i', j).
destruct i'.

Inspect 2.
Print nat_of_prod_nat_O_r.
bbb.

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

bbb.

enough (∀ i, (nat_of_prod_nat_O_r i = (i * S i) / 2)%nat).
 rewrite H.
 induction i; [ easy | ].
 simpl.
bbb.

 destruct i; [ easy | ].
(*
 destruct i; [ easy | ].
 destruct i; [ easy | ].
 destruct i; [ easy | ].
 destruct i; [ easy | ].
bbb.

Compute (nat_of_prod_nat_O_r 4).
*)
enough (∀ i, nat_of_prod_nat_O_r (S i) = S (nat_of_prod_nat_O_r i + i)).
 rewrite H.
 simpl.
 rename i into i₁.


 remember (prod_nat_of_nat (nat_of_prod_nat_O_r i + i)) as ij eqn:Hij.
 symmetry in Hij.
 destruct ij as (i', j').
 destruct i'.
enough (nat_of_prod_nat_O_r i + i = nat_of_nat_nat 0 i)%nat.
rewrite H in Hij.

Focus 2.
Compute (nat_of_prod_nat_O_r 4).
apply (f_equal nat_of_prod_nat) in Hij.
simpl in Hij.

bbb.
 destruct i; [ easy | ].
 destruct i; [ easy | ].
bbb.

 rewrite <- Nat.add_succ_comm; simpl.
 remember (prod_nat_of_nat (nat_of_prod_nat_O i + i)) as ij' eqn:Hij'.
 symmetry in Hij'.
 destruct ij' as (i', j').
 destruct i'.

bbb.

rewrite prod_nat_of_nat_inv in Hij.
injection Hij; intros; subst; easy.
Qed.

revert na Hij.
induction nb; intros.
 simpl in Hij.
 revert i j Hij.
 induction na; intros; [ simpl in Hij; now injection Hij; intros; subst | ].
 simpl in Hij.
 rewrite <- Nat.add_succ_comm in Hij; simpl in Hij.
 remember (prod_nat_of_nat (nat_of_prod_nat_O na + na)) as ij' eqn:Hij'.
 symmetry in Hij'.
 destruct ij' as (i', j').
 destruct i'.
  injection Hij; clear Hij; intros; subst i j.

bbb.

Definition rotation_fixpoint (m : matrix) k :=
  let x := (a₃₂ m - a₂₃ m)%R in
  let y := (a₁₃ m - a₃₁ m)%R in
  let z := (a₂₁ m - a₁₂ m)%R in
  let r := √ (x² + y² + z²) in
  P (k * x / r) (k * y / r) (k * z / r).

Definition mat_of_path el :=
  List.fold_right mat_mul mat_id (map mat_of_elem el).

Definition fixpoint_of_path el :=
  rotation_fixpoint (mat_of_path el) 1.

Definition map_empty_path_to_single el :=
  match el with
  | [] => ạ :: []
  | _ => el
  end.

Definition fixpoint_of_nat n :=
  fixpoint_of_path (map_empty_path_to_single (norm_list (path_of_nat n))).

Theorem D_is_countable : is_countable {p : point | p ∈ D}.
Proof.
unfold is_countable, D; simpl.
bbb.
exists fixpoint_of_nat.
intros p Hp.
unfold D in Hp; simpl in Hp.
destruct Hp as (el & p₁ & Hs & Hn & Hr).
bbb.
SearchAbout FinFun.Surjective.

(* using Cantor_gen, we could prove that ℝ ∖ a countable set contains at
   least one element; if D is countable, ℝ ∖ D countains at least one
   element *)

Theorem equidec_sphere_with_and_without_fixpoints :
  equidecomposable sphere sphere_but_fixpoints.
Proof.
intros.
assert (∃ p₁, p₁ ∈ sphere ∖ D).
 unfold "∈", "∖".
 SearchAbout D.
bbb.

assert (∃ p₁, p₁ ∉ D).
bbb.
assert (∀ p₁, (∀ el p, ¬ (same_orbit p₁ p ∧ norm_list el ≠ [] ∧ fold_right rotate p el = p)) → p₁ ∉ D).
intros p₁ Hf.
apply Classical_Pred_Type.all_not_not_ex; intros el (p, Hp).
revert Hp; apply Hf.
simpl.

bbb.

assert (∃ p₁ θ, ∀ p n, p ∈ D → p ∉ rotate_set p₁ (INR n * θ) D).
bbb.

Theorem Banach_Tarski_paradox :
  equidecomposable sphere (xtransl 3 sphere ∪ xtransl 6 sphere)%S.
Proof.
transitivity sphere_but_fixpoints.
 apply equidec_sphere_with_and_without_fixpoints.

 etransitivity.
  apply Banach_Tarski_paradox_but_fixpoints.

  apply equidec_union.
   apply separated_spheres_without_fixpoints.

   apply separated_spheres.

   apply equidec_transl; symmetry.
   apply equidec_sphere_with_and_without_fixpoints.

   apply equidec_transl; symmetry.
   apply equidec_sphere_with_and_without_fixpoints.
Qed.

Check Banach_Tarski_paradox.
