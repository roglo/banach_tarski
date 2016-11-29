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
Require Import Partition OrbitRepr GroupTransf Equidecomp.

Notation "x '≤' y" := (Rle x y) : R_scope.
Notation "x '≤' y '<' z" := (Rle x y ∧ Rlt y z)
 (at level 70, y at next level) : R_scope.
Notation "x '≤' y '≤' z" := (Rle x y ∧ Rle y z)
 (at level 70, y at next level) : R_scope.

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
  equidecomposable set_equiv sphere_but_fixpoints
    (xtransl 3 sphere_but_fixpoints ∪ xtransl 6 sphere_but_fixpoints)%S.
Proof.
set (s := set_equiv).
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
  subst s; remember set_equiv as s eqn:Hs.
  pose proof r_decomposed_2_a f Hosf os Hos as Ha.
  pose proof r_decomposed_2_b f Hosf os Hos as Hb.
  subst s; set (s := set_equiv).
  eapply partition_group_map with (g := Xtransl 3) in Ha; try eassumption.
  eapply partition_group_map with (g := Xtransl 6) in Hb; try eassumption.
  eapply partition_union in Hb; [ | | apply Ha ].
   apply Hb.

   unfold intersection, set_eq; subst s; intros (x, y, z).
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

Theorem equidec_union : ∀ (s := set_equiv) E₁ E₂ F₁ F₂,
  (E₁ ∩ F₁ = ∅)%S
  → (E₂ ∩ F₂ = ∅)%S
  → equidecomposable set_equiv E₁ E₂
  → equidecomposable set_equiv F₁ F₂
  → equidecomposable set_equiv (E₁ ∪ F₁) (E₂ ∪ F₂).
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
  equidecomposable set_equiv E F
  → equidecomposable set_equiv (xtransl dx E) (xtransl dx F).
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

Theorem separated_spheres_without_fixpoints : ∀ (s := set_equiv),
  (xtransl 3 sphere_but_fixpoints ∩ xtransl 6 sphere_but_fixpoints = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6); simpl | easy ].
unfold sphere_but_fixpoints in H3, H6.
simpl in H3, H6.
destruct H3 as (H3, _).
destruct H6 as (H6, _).
now apply (Rno_intersect_spheres_x3_x6 x y z).
Qed.

Theorem separated_spheres : ∀ (s := set_equiv),
  (xtransl 3 sphere ∩ xtransl 6 sphere = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6) | easy ].
unfold sphere in H3, H6.
simpl in H3, H6.
now apply (Rno_intersect_spheres_x3_x6 x y z).
Qed.

Definition rotate_set axis ang E :=
  mkset (λ p, mat_vec_mul (rot_mat_of_axis_cos axis (-cos ang)) p ∈ E).

Definition nat_of_free_elem e : nat :=
  match e with
  | ạ => 0
  | ạ⁻¹ => 1
  | ḅ => 2
  | ḅ⁻¹ => 3
  end.

Fixpoint nat_of_path el :=
  match el with
  | e :: el' => (nat_of_path el' * 4 + nat_of_free_elem e)%nat
  | [] => 1%nat
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

Theorem nat_of_path_ne_0 : ∀ el, nat_of_path el ≠ 0%nat.
Proof.
intros * H.
induction el as [| e el]; [ easy | ].
simpl in H; apply Nat.eq_add_0 in H.
destruct H as (H, _).
now apply Nat.eq_mul_0_l in H.
Qed.

Theorem nat_of_free_elem_injective : FinFun.Injective nat_of_free_elem.
Proof.
intros (t₁, d₁) (t₂, d₂) He; simpl in He.
now destruct t₁, d₁, t₂, d₂.
Qed.

Theorem nat_of_free_elem_sub_le : ∀ e₁ e₂,
  nat_of_free_elem e₁ - nat_of_free_elem e₂ < 4.
Proof.
intros (t₁, d₁) (t₂, d₂).
destruct t₁, d₁, t₂, d₂; simpl; try apply Nat.lt_0_succ.
 apply -> Nat.succ_lt_mono; apply Nat.lt_0_succ.
 do 2 apply -> Nat.succ_lt_mono; apply Nat.lt_0_succ.
 apply Nat.lt_succ_diag_r.
 apply -> Nat.succ_lt_mono; apply Nat.lt_0_succ.
 apply -> Nat.succ_lt_mono; apply Nat.lt_0_succ.
 do 2 apply -> Nat.succ_lt_mono; apply Nat.lt_0_succ.
Qed.

Theorem nat_of_path_injective : FinFun.Injective nat_of_path.
Proof.
intros el₁ el₂ Hf.
revert el₂ Hf.
induction el₁ as [| e₁ el₁]; intros.
 destruct el₂ as [| e₂ el₂]; [ easy | exfalso; simpl in Hf ].
 remember (nat_of_path el₂) as n eqn:Hn; symmetry in Hn.
 destruct n; [ revert Hn; apply nat_of_path_ne_0 | easy ].

 destruct el₂ as [| e₂ el₂]; [ exfalso; simpl in Hf | ].
  remember (nat_of_path el₁) as n eqn:Hn; symmetry in Hn.
  destruct n; [ revert Hn; apply nat_of_path_ne_0 | easy ].

  simpl in Hf.
  set (np₁ := nat_of_path el₁) in Hf.
  set (np₂ := nat_of_path el₂) in Hf.
  set (n₁ := nat_of_free_elem e₁) in Hf.
  set (n₂ := nat_of_free_elem e₂) in Hf.
  destruct (lt_eq_lt_dec np₁ np₂) as [[H₁| H₁]| H₁].
   apply Nat.add_sub_eq_l in Hf.
   rewrite Nat.add_sub_swap in Hf.
    rewrite <- Nat.mul_sub_distr_r in Hf.
    apply Nat.add_sub_eq_r in Hf.
    remember (np₂ - np₁)%nat as n eqn:Hn.
    symmetry in Hn.
    destruct n.
     apply Nat.sub_0_le in Hn.
     now apply Nat.nlt_ge in Hn.

     pose proof (nat_of_free_elem_sub_le e₁ e₂) as H.
     fold n₁ n₂ in H; rewrite Hf in H.
     rewrite Nat.mul_succ_l in H.
     apply Nat.lt_add_lt_sub_r in H.
     rewrite Nat.sub_diag in H.
     now apply Nat.nlt_0_r in H.

    apply Nat.mul_le_mono_nonneg_r; [ apply Nat.le_0_l | ].
    now apply Nat.lt_le_incl.

   rewrite H₁ in Hf.
   apply Nat.add_cancel_l in Hf.
   subst n₁ n₂ np₁ np₂.
   apply nat_of_free_elem_injective in Hf.
   f_equal; [ easy | now apply IHel₁ ].

   symmetry in Hf.
   apply Nat.add_sub_eq_l in Hf.
   rewrite Nat.add_sub_swap in Hf.
    rewrite <- Nat.mul_sub_distr_r in Hf.
    apply Nat.add_sub_eq_r in Hf.
    remember (np₁ - np₂)%nat as n eqn:Hn.
    symmetry in Hn.
    destruct n.
     apply Nat.sub_0_le in Hn.
     now apply Nat.nlt_ge in Hn.

     pose proof (nat_of_free_elem_sub_le e₂ e₁) as H.
     fold n₁ n₂ in H; rewrite Hf in H.
     rewrite Nat.mul_succ_l in H.
     apply Nat.lt_add_lt_sub_r in H.
     rewrite Nat.sub_diag in H.
     now apply Nat.nlt_0_r in H.

    apply Nat.mul_le_mono_nonneg_r; [ apply Nat.le_0_l | ].
    now apply Nat.lt_le_incl.
Qed.

Definition is_countable U (eqU : relation U) A :=
  ∃ f : ℕ → U, ∀ a, a ∈ A → ∃ n, eqU (f n) a.

Theorem paths_are_countable : is_countable (list free_elem) eq full_set.
Proof.
unfold is_countable; simpl.
exists path_of_nat.
intros el _.
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

Theorem classic : ∀ (P : Prop), ¬¬P → P.
Proof.
intros * HnP.
now destruct (EM P).
Qed.

Add Parametric Morphism {U} : (@is_countable U)
 with signature eq ==> (@set_eq _ set_equiv) ==> iff
 as is_countable_morph.
Proof.
intros eqU E F HEF.
split; intros H; destruct H as (f, H); exists f; intros x Hx; now apply H, HEF.
Qed.

Theorem uncountable_sub_countable_not_empty : ∀ {U} (A B : set U) eqU,
  not (is_countable _ eqU A)
  → is_countable _ eqU B
  → B ⊂ A
  → ∃ x, x ∈ A ∖ B.
Proof.
intros * HA HB HBA.
apply classic.
intros HnE.
assert (HnA : ∀ x, x ∉ A ∖ B) by (now intros x Hx; apply HnE; exists x).
clear HnE.
set (s := @set_equiv U).
enough (HAB : (A = B)%S) by (now rewrite HAB in HA).
intros x.
split; [ intros Ha | now intros Hb; apply HBA ].
pose proof HnA x as H; simpl in H.
apply classic.
now intros Hb; apply H.
Qed.

Definition unit_interv := mkset (λ x, (0 <= x < 1)%R).

(* equivalence between ℝ and a representation with integer and fractional
   part, the fractional part being a boolean sequence (false for 0, true
   for 1 *)

Record int_frac := mkraif { Rint : ℤ; Rfrac : ℕ → bool }.

Definition bin_of_frac_part x n :=
  if Rlt_dec (frac_part (x * 2 ^ n)) (1 / 2) then false else true.

Definition int_frac_of_R x :=
  mkraif (Int_part x) (bin_of_frac_part (frac_part x)).

Fixpoint partial_sum_aux k (u : ℕ → bool) pow i :=
  match k with
  | 0 => 0%R
  | S k' =>
      if u i then (pow / 2 + partial_sum_aux k' u (pow / 2) (S i))%R
      else partial_sum_aux k' u (pow / 2)%R (S i)
  end.

Definition partial_sum u k := partial_sum_aux k u 1%R 0.

Theorem bin_of_frac_part_succ : ∀ x i,
  bin_of_frac_part x (S i) = bin_of_frac_part (x * 2) i.
Proof.
intros.
unfold bin_of_frac_part; simpl.
now rewrite Rmult_assoc.
Qed.

Theorem partial_sum_aux_le_2_pow : ∀ u k pow i,
  (0 < pow)%R
  → (partial_sum_aux k u pow i <= 2 * pow)%R.
Proof.
intros * Hpow.
revert pow i Hpow.
induction k; intros; simpl; [ lra | ].
remember (u i) as b eqn:Hb; symmetry in Hb.
destruct b.
 replace (2 * pow)%R with (pow + pow)%R by lra.
 apply Rplus_le_compat; [ lra | ].
 replace pow with (2 * (pow / 2))%R at 2 by lra.
 apply IHk; lra.

 apply Rle_trans with (r2 := pow); [ | lra ].
 replace pow with (2 * (pow / 2))%R at 2 by lra.
 apply IHk; lra.
Qed.

Theorem partial_sum_aux_le_pow : ∀ u k pow i,
  (0 <= pow)%R
  → (partial_sum_aux k u pow i <= pow)%R.
Proof.
intros * Hpow.
revert pow i Hpow.
induction k; intros; simpl; [ lra | ].
destruct (u i).
 apply Rplus_le_reg_l with (r := (- (pow / 2))%R).
 rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
 eapply Rle_trans; [ apply IHk; lra | lra ].

 eapply Rle_trans; [ apply IHk; lra | lra ].
Qed.

Theorem partial_sum_le_1 : ∀ u k, (partial_sum u k <= 1)%R.
Proof.
intros.
apply partial_sum_aux_le_pow; lra.
Qed.

Definition Rset_of_bin_seq u := mkset (λ x, ∃ k, partial_sum u k = x).

Theorem Rset_of_bin_seq_bound : ∀ u, bound (setp (Rset_of_bin_seq u)).
Proof.
intros.
unfold bound.
exists 1.
unfold is_upper_bound.
intros x HE; unfold Rset_of_bin_seq in HE.
destruct HE as (k, HE); subst x.
apply partial_sum_le_1.
Qed.

Theorem Rset_of_bin_seq_non_empty : ∀ u, ∃ x, x ∈ Rset_of_bin_seq u.
Proof.
intros.
unfold Rset_of_bin_seq; simpl.
now exists (partial_sum u 0), 0%nat.
Qed.

Definition R_of_bin_seq u :=
  completeness (setp (Rset_of_bin_seq u)) (Rset_of_bin_seq_bound u)
    (Rset_of_bin_seq_non_empty u).

Definition R_of_int_frac rif :=
  (IZR (Rint rif) + proj1_sig (R_of_bin_seq (Rfrac rif)))%R.

Definition trunc_bool_seq u n i := if lt_dec i n then u i else false.

(* Begin code Rémi Nollet, modified *)

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

(* End code Rémi Nollet *)

Definition id {A} (a : A) := a.
Theorem id_nat : ∀ e : ℕ, ∃ x : ℕ, id x = e.
Proof. now intros; exists e. Qed.

Definition ter_bin_of_frac_part x n :=
  if Rlt_dec (frac_part (x * 3 ^ n)) (1 / 3) then false else true.

Fixpoint partial_sum3_aux k (u : ℕ → bool) pow i :=
  match k with
  | 0 => 0%R
  | S k' =>
      if u i then (pow / 3 + partial_sum3_aux k' u (pow / 3) (S i))%R
      else partial_sum3_aux k' u (pow / 3)%R (S i)
  end.

Definition partial_sum3 u k := partial_sum3_aux k u 1%R 0.

Theorem partial_sum3_aux_le_pow : ∀ u k pow pow2 i,
  (0 <= pow)%R
  → pow2 = (pow / 2)%R
  → (partial_sum3_aux k u pow i <= pow2)%R.
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

Theorem partial_sum3_le_half : ∀ u k, (partial_sum3 u k ≤ 1 / 2)%R.
Proof.
intros.
apply partial_sum3_aux_le_pow; lra.
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
    apply partial_sum3_aux_le_pow.
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

Definition b2r b := INR (Nat.b2n b).

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

(* Σ (i=0,c-1) 3^(c-1-i)ui *)
Fixpoint n_partial_sum3 (u : ℕ → bool) c :=
  match c with
  | O => O
  | S c' => (3 * n_partial_sum3 u c' + Nat.b2n (u c'))%nat
  end.

Theorem n_partial_sum3_succ : ∀ u n,
  n_partial_sum3 u (S n) = (3 * n_partial_sum3 u n + Nat.b2n (u n))%nat.
Proof. easy. Qed.

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
    rewrite <- Rmult_assoc, <- Rmult_plus_distr_r, fold_Rminus.
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
  (∀ k : ℕ, (partial_sum3 u k ≤ r)%R)
  → (∀ b : ℝ, (∀ k : ℕ, (partial_sum3 u k ≤ b)%R) → (r ≤ b)%R)
  → IZR (Int_part (r * 3 ^ n)) = (partial_sum3 u n * 3 ^ n)%R.
Proof.
intros * Hk1 Hk2.
induction n.
 unfold partial_sum3; simpl.
 do 2 rewrite Rmult_1_r.
 specialize (Hk1 O); simpl in Hk1.
 unfold partial_sum3 in Hk1; simpl in Hk1.
 specialize (Hk2 (1 / 2)%R (partial_sum3_le_half u)).
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

Theorem ter_bin_of_frac_part_surj : ∀ u : ℕ → bool,
  ∃ r : ℝ, r ∈ unit_interv ∧ (∀ n, ter_bin_of_frac_part r n = u n).
Proof.
intros.
set (E x := ∃ k, partial_sum3 u k = x).
assert (Hb : bound E).
 exists (1 / 2)%R; subst E; simpl.
 intros r (k & H); subst r.
 apply partial_sum3_le_half.

 assert (He : ∃ r, E r).
  exists 0; subst E; simpl.
  now exists O; unfold partial_sum3.

  destruct (completeness E Hb He) as (r & Hr1 & Hr2).
  assert (Hr3 : (∀ k, partial_sum3 u k <= r)%R).
   unfold is_upper_bound, E in Hr1; simpl in Hr1.
   now intros k; apply Hr1; exists k.

   assert (Hr4 : (∀ b, (∀ k, partial_sum3 u k <= b) → (r <= b))%R).
    unfold is_upper_bound, E in Hr2; simpl in Hr2.
    intros b H; apply Hr2; intros x (k, Hx); subst x.
    apply H.

    assert (Hh : (r ≤ 1 / 2)%R).
     apply Hr2; unfold E; simpl.
     intros x (k & H); subst x.
     apply partial_sum3_le_half.

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
        rewrite fold_Rdiv in H1.
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

Theorem Cantor_ℕ_ℝ : ∀ f : ℕ → ℝ, ∃ x : ℝ, ∀ n : ℕ, x ≠ f n.
Proof.
specialize
  (Cantor_gen ℕ ℕ ℝ (setp unit_interv) id ter_bin_of_frac_part id_nat
     ter_bin_of_frac_part_surj).
intros H f.
specialize (H f).
destruct H as (x, H); exists x.
intros n; apply H.
Qed.

Theorem R_not_countable : ¬ (is_countable ℝ eq full_set).
Proof.
intros H.
unfold is_countable in H.
destruct H as (f, Hf).
assert (Hcontr : ∃ a, a ∈ full_set ∧ ∀ n, f n ≠ a).
 clear; simpl.
 specialize (Cantor_ℕ_ℝ f); intros (x & Hf).
 exists x; split; [ easy | ].
 intros n; specialize (Hf n).
 now intros H; apply Hf.

 destruct Hcontr as (a & Ha & Hnn).
 apply Hf in Ha.
 destruct Ha as (n, Hn).
 now apply (Hnn n).
Qed.

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

Theorem sphere_not_countable : ¬ (is_countable _ eq sphere).
Proof.
intros H.
unfold is_countable in H.
destruct H as (f, Hf).
enough (Hcontr : ∃ a, a ∈ sphere ∧ ∀ n, f n ≠ a).
 destruct Hcontr as (a & Ha & Hnn).
 apply Hf in Ha.
 destruct Ha as (n, Hn).
 eapply Hnn; eassumption.

 specialize
  (Cantor_gen ℕ ℕ point (setp sphere) id ter_bin_of_point id_nat
     ter_bin_of_sphere_surj).
 intros H.
 specialize (H f).
 destruct H as (p, H).
 exists p.
 split; [ apply (H O) | ].
 intros n Hn.
 specialize (H n).
 destruct H.
 now symmetry in Hn.
Qed.

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

Theorem D_is_countable : is_countable _ eq D.
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

Theorem equidec_sphere_with_and_without_fixpoints : ∀ (s := set_equiv),
  equidecomposable _ sphere sphere_but_fixpoints.
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

Theorem Banach_Tarski_paradox : ∀ (s := set_equiv),
  equidecomposable _ sphere (xtransl 3 sphere ∪ xtransl 6 sphere)%S.
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
