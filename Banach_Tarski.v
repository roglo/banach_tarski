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

Theorem paths_are_countable : is_countable _ eq (whole_set (list free_elem)).
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

Theorem partial_sum3_le_1_6 : ∀ u k,
  u O = false
  → (partial_sum3 u k ≤ 1 / 6)%R.
Proof.
intros * Hb.
unfold partial_sum3.
destruct k; simpl; [ lra | rewrite Hb ].
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

Definition b2r b := INR (Nat.b2n b).

Check (Cantor_gen ℕ ℕ ℝ (setp unit_interv) id ter_bin_of_frac_part id_nat).

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
Theorem toto : ∀ u r n,
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

Theorem titi : ∀ u r n,
  (∀ k, (partial_sum3 u k ≤ r)%R)
  → (∀ b, (∀ k, (partial_sum3 u k ≤ b)%R) → (r ≤ b)%R)
  → IZR (Int_part (r * 3 ^ S n)) =
    (3 * IZR (Int_part (r * 3 ^ n)) + INR (Nat.b2n (u n)))%R.
Proof.
intros * Hr1 Hr2.
assert (Hrp : (r ≤ partial_sum3 u n + / (2 * 3 ^ n))%R).
 apply Hr2; intros k; unfold partial_sum3.
bbb.

Theorem tutu : ∀ u r n pow i ,
  (0 ≤ pow)%R
  → (∀ k : ℕ, (partial_sum3 u k ≤ r)%R)
  → (∀ b : ℝ, (∀ k : ℕ, (partial_sum3 u k ≤ b)%R) → (r ≤ b)%R)
  → (partial_sum3_aux n u pow i ≤ pow / (2 * 3 ^ i))%R.
Proof.
intros * Hpow Hr1 Hr2.
revert pow i Hpow.
induction n; intros; simpl.
 unfold Rdiv; apply Rmult_le_pos; [ easy | ].
 rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
 apply Rmult_le_pos; [ lra | ].
 rewrite Rinv_pow; [ apply pow_le; lra| lra ].

 remember (u i) as b eqn:Hb; symmetry in Hb.
 destruct b.
  apply Rplus_le_reg_l with (r := (- (pow / 3))%R).
  rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
  destruct n.
   simpl.

bbb.
  eapply Rle_trans; [ apply IHn; lra | ].
bbb.
  apply partial_sum3_aux_le_pow; [ lra | ].

 Focus 2.
bbb.

 apply partial_sum3_aux_le_pow; [ lra | ].
bbb.
*)
intros * Hpow Hr1 Hr2.
revert u r Hr1 Hr2.
induction n; intros.
 unfold partial_sum3 in Hr1.
 simpl; rewrite Rmult_1_r.
 pose proof (Hr1 1%nat) as H1; simpl in H1.
 remember (u O) as b eqn:Hb; symmetry in Hb.
 assert (H : (r ≤ partial_sum3 u 1 + / (2 * 3 ^ 1))%R).
  apply Hr2; intros k; unfold partial_sum3, b2r.
  simpl; rewrite Hb.
  destruct k; simpl; [ destruct b; simpl; lra | rewrite Hb ].
  destruct b; simpl.
   apply Rplus_le_reg_l with (r := (- (1 / 3))%R).
   rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
   apply partial_sum3_aux_le_pow; lra.

   apply partial_sum3_aux_le_pow; lra.

 unfold partial_sum3 in H; simpl in H.
 rewrite Hb in H.
 rewrite (Int_part_interv (Z.b2z b)).
  rewrite (Int_part_interv 0).
   destruct b; simpl in H; simpl; lra.
   destruct b; simpl in H; simpl; lra.

  destruct b; simpl in H; simpl; lra.

 clear IHn.
 destruct n.
  unfold partial_sum3 in Hr1.
  simpl; rewrite Rmult_1_r.
  pose proof (Hr1 2%nat) as H2; simpl in H2.
  remember (u O) as b eqn:Hb; symmetry in Hb.
  remember (u 1%nat) as b1 eqn:Hb1; symmetry in Hb1.
  assert (H : (r ≤ partial_sum3 u 2 + / (2 * 3 ^ 2))%R).
   apply Hr2; intros k; unfold partial_sum3, b2r.
   simpl; rewrite Hb, Hb1.
   destruct k; simpl; [ destruct b, b1; simpl; lra | rewrite Hb ].
   destruct k; simpl; [ destruct b, b1; simpl; lra | rewrite Hb1 ].
   destruct b; simpl.
    apply Rplus_le_reg_l with (r := (- (1 / 3))%R).
    rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
    destruct b1; simpl.
     apply Rplus_le_reg_l with (r := (- (1 / 3 / 3))%R).
     rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
     apply partial_sum3_aux_le_pow; lra.

     apply partial_sum3_aux_le_pow; lra.

    destruct b1; simpl.
     apply Rplus_le_reg_l with (r := (- (1 / 3 / 3))%R).
     rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
     apply partial_sum3_aux_le_pow; lra.

     apply partial_sum3_aux_le_pow; lra.

  unfold partial_sum3 in H; simpl in H.
  rewrite Hb, Hb1 in H.
  rewrite (Int_part_interv (3 * Z.b2z b + Z.b2z b1)).
   rewrite (Int_part_interv (Z.b2z b )).
    destruct b, b1; simpl in H; simpl; lra.
    destruct b, b1; simpl in H; simpl; lra.

   destruct b, b1; simpl in H; simpl; lra.

  destruct n.
   unfold partial_sum3 in Hr1.
   simpl; rewrite Rmult_1_r.
   pose proof (Hr1 3%nat) as H3; simpl in H3.
   assert (H : (r ≤ partial_sum3 u 3 + / (2 * 3 ^ 3))%R).
    apply Hr2; intros k; unfold partial_sum3, b2r; simpl.
    remember (u O) as b eqn:Hb; symmetry in Hb.
    remember (u 1%nat) as b1 eqn:Hb1; symmetry in Hb1.
    remember (u 2%nat) as b2 eqn:Hb2; symmetry in Hb2.
    destruct k; simpl; [ destruct b, b1, b2; simpl; lra | rewrite Hb ].
    destruct k; simpl; [ destruct b, b1, b2; simpl; lra | rewrite Hb1 ].
    destruct k; simpl; [ destruct b, b1, b2; simpl; lra | rewrite Hb2 ].
    destruct b; simpl.
     apply Rplus_le_reg_l with (r := (- (1 / 3))%R).
     rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
     destruct b1; simpl.
      apply Rplus_le_reg_l with (r := (- (1 / 3 / 3))%R).
      rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
      destruct b2; simpl.
       apply Rplus_le_reg_l with (r := (- (1 / 3 / 3 / 3))%R).
       rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
       apply partial_sum3_aux_le_pow; lra.

       apply partial_sum3_aux_le_pow; lra.

      destruct b2; simpl.
       apply Rplus_le_reg_l with (r := (- (1 / 3 / 3 / 3))%R).
       rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
       apply partial_sum3_aux_le_pow; lra.

       apply partial_sum3_aux_le_pow; lra.

     destruct b1; simpl.
      apply Rplus_le_reg_l with (r := (- (1 / 3 / 3))%R).
      rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
      destruct b2; simpl.
       apply Rplus_le_reg_l with (r := (- (1 / 3 / 3 / 3))%R).
       rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
       apply partial_sum3_aux_le_pow; lra.

       apply partial_sum3_aux_le_pow; lra.

      destruct b2; simpl.
       apply Rplus_le_reg_l with (r := (- (1 / 3 / 3 / 3))%R).
       rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
       apply partial_sum3_aux_le_pow; lra.

       apply partial_sum3_aux_le_pow; lra.

   unfold partial_sum3 in H; simpl in H.
   remember (u O) as b eqn:Hb; symmetry in Hb.
   remember (u 1%nat) as b1 eqn:Hb1; symmetry in Hb1.
   remember (u 2%nat) as b2 eqn:Hb2; symmetry in Hb2.
   rewrite (Int_part_interv (9 * Z.b2z b + 3 * Z.b2z b1 + Z.b2z b2)).
    rewrite (Int_part_interv (3 * Z.b2z b + Z.b2z b1)).
     destruct b, b1, b2; simpl in H; simpl; lra.
     destruct b, b1, b2; simpl in H; simpl; lra.

    destruct b, b1, b2; simpl in H; simpl; lra.
bbb.
 (* general case of titi that does not work *)
 assert (HrO : (0 ≤ r)%R) by now specialize (Hr1 O).
 assert (Hr12 : (r ≤ 1 / 2)%R) by apply Hr2, partial_sum3_le_half.
 remember (S (S n)) as ssn; simpl; subst ssn.
 remember (S n) as sn; simpl; subst sn.
 do 2 rewrite <- Rmult_assoc.
 set (v n := u (S n)); fold (v n).
 apply IHn.
  intros k.
  subst v; clear -Hr1 Hr12.
bbb.

(* end of titi; return to toto *)
setoid_rewrite Rmult_comm at 3.
apply titi; easy.

bbb.

(* end of toto; return to ter_bin_of_frac_part_surj *)
unfold frac_part in H1.
rewrite (toto u) in H1; [ | easy | easy ].
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

bbb.
      destruct (Rlt_dec (frac_part (r * 3 ^ n)) (1 / 3)) as [H1| H1].
       unfold frac_part in H1.
revert r Hh Hr3 Hr4 H1.
       induction n; intros.
        simpl in H1; rewrite Rmult_1_r in H1.
        assert (HrO : (0 ≤ r)%R) by now specialize (Hr3 O).
        rewrite Int_part_is_0 in H1; [ | lra ].
        simpl in H1; rewrite Rminus_0_r in H1.
        specialize (Hr3 1%nat).
        unfold partial_sum3 in Hr3; simpl in Hr3.
        destruct (u O); [ lra | easy ].

        simpl in H1.
bbb.


  unfold partial_sum3.
  induction k; simpl; [ lra | ].
  remember (v O) as b eqn:Hb; symmetry in Hb.
  destruct b.
bbb.

 assert
   (Hp :
    ∀ k, partial_sum3 v k = (3 * partial_sum3 u k - INR (Nat.b2n (u O)))%R).
  intros.
  subst v; clear.
  unfold partial_sum3.
  induction k.
   simpl.


 apply IHn.
  intros k.
bbb.

  apply Rmult_le_reg_r with (r := (/ 3)%R); [ lra | ].
  rewrite Rmult_assoc, Rinv_r; [ | lra ].
  rewrite Rmult_1_r.
  rewrite fold_Rdiv.
  apply Rle_trans with (r2 := partial_sum3 u (S k)); [ | apply Hr1 ].
  unfold v; simpl.
  unfold partial_sum3; simpl.
bbb.
*)

Theorem toto : ∀ u r n,
  (∀ k, (partial_sum3 u k ≤ r)%R)
  → (∀ b, (∀ k, (partial_sum3 u k ≤ b)%R) → (r ≤ b)%R)
  → IZR (Int_part (r * 3 ^ n)) = (3 ^ n * partial_sum3 u n)%R.
Proof.
intros * Hr1 Hr2.
assert (HrO : (0 ≤ r)%R) by now specialize (Hr1 O).
assert (Hk : ∀ k, (partial_sum3 u k ≤ 1 / 2)%R).
 apply partial_sum3_le_half.

(*
unfold partial_sum3.
Print partial_sum3_aux.
Check partial_sum3_aux_succ.
bbb.
*)

 induction n.
  simpl; rewrite Rmult_1_l, Rmult_1_r.
  unfold partial_sum3; simpl.
  apply Hr2 in Hk.
  rewrite Int_part_is_0; [ easy | lra ].

  rewrite partial_sum3_succ.
  rewrite Rmult_plus_distr_l.
  setoid_rewrite Rmult_comm at 5.
  unfold Rdiv; rewrite Rmult_assoc.
  rewrite Rinv_l; [ | apply pow_nonzero; lra ].
  rewrite Rmult_1_r.
  remember (r * 3 ^ S n)%R as x; simpl; subst x.
  rewrite Rmult_assoc, <- IHn.
  apply titi.

bbb.

Check tutu.
rewrite tutu.
remember (3 ^ S n)%R as s3 eqn:Hs3; simpl.
rewrite Rmult_plus_distr_l, Rmult_1_l.
rewrite Hs3 at 2; simpl.
rewrite Rmult_assoc.
rewrite <- IHn.
setoid_rewrite Rmult_comm at 4.
rewrite <- Rmult_div.
unfold Rdiv.
rewrite Rmult_assoc; subst s3.
rewrite Rinv_r; [ | apply pow_nonzero; lra ].
rewrite Rmult_1_r.
apply titi.

bbb.

  rewrite partial_sum3_succ.
  rewrite Rmult_plus_distr_l.
  remember (S n) as sn eqn:Hsn.
  rewrite Hsn at 2; simpl; subst sn.
  rewrite Rmult_assoc, <- IHn.
  setoid_rewrite Rmult_comm.
  rewrite <- Rmult_div.
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_r; [ | apply pow_nonzero; lra ].
  rewrite Rmult_1_r.
  rewrite Rmult_comm at 1.
  apply titi.
bbb.
      induction n.
       rewrite pow_O, Rmult_1_r.
       pose proof (Hr3 1%nat) as Hr1.
       unfold partial_sum3 in Hr1; simpl in Hr1.
       rewrite Rplus_0_r in Hr1.
       remember (u O) as b eqn:Hb; symmetry in Hb.
       destruct (Rlt_dec (frac_part r) (1 / 3)) as [Hr | Hr].
        destruct b; [ exfalso | easy ].
        unfold frac_part in Hr.
        rewrite Int_part_is_0 in Hr; lra.

        destruct b; [ easy | exfalso ].
        apply Hr.
        unfold frac_part.
        rewrite Int_part_is_0; [ | lra ].
        rewrite Rminus_0_r.
        apply Rle_lt_trans with (r2 := (1 / 6)%R); [ | lra ].
        apply Hr4; intros k.
        now apply partial_sum3_le_1_6.

       idtac.
       simpl.
destruct n.
 simpl; rewrite Rmult_1_r.
 simpl in IHn; rewrite Rmult_1_r in IHn.
 destruct (Rlt_dec (frac_part (r * 3)) (1 / 3)) as [Hr| Hr].
  specialize (Hr3 2%nat) as Hr2.
  unfold partial_sum3 in Hr2; simpl in Hr2.
  rewrite IHn in Hr2.
  destruct (Rlt_dec (frac_part r) (1 / 3)) as [Hr1| Hr1].
   unfold frac_part in Hr1.
   pose proof Hr3 O as HrO.
   unfold partial_sum3 in HrO; simpl in HrO.
   rewrite Int_part_is_0 in Hr1; [ | lra ].
   rewrite Rminus_0_r in Hr1.
   remember (u 1%nat) as b1 eqn:Hb1; symmetry in Hb1.
   rewrite Rplus_0_r in Hr2.
   destruct b1; [ exfalso | easy ].
   unfold frac_part in Hr.
   rewrite Int_part_is_0 in Hr; [ | lra ].
   rewrite Rminus_0_r in Hr; lra.

   apply Rnot_lt_ge in Hr1.
   rewrite Rplus_0_r in Hr2.

bbb.
  destruct b.
   field_simplify in Hr2.
   rewrite Rdiv_1_r in Hr2.

bbb.

assert (∀ k, (partial_sum u k ≤ 1 / 3)%R).
 intros k; unfold partial_sum.
 induction k; simpl; [ lra | rewrite Hb ].

bbb.

specialize (Hr3 2%nat).
unfold partial_sum3 in Hr3; simpl in Hr3.
rewrite Hb, Rplus_0_r in Hr3.
remember (u 1%nat) as b1 eqn:Hb1; symmetry in Hb1.
destruct b1.

bbb.
destruct (Req_dec y 1) as [H1| H1].
subst y.
unfold ter_bin_of_frac_part.
rewrite Rmult_1_l.
destruct n.
rewrite pow_O.
rewrite fp_R1.
destruct (Rlt_dec 0 (1 / 3)) as [H| ]; [ clear H | lra ].
bbb.

assert (H : ∀ k, (partial_sum3 u k <= 1)%R) by apply partial_sum3_le_1.
specialize (Hr4 1%R H); clear H.
bbb.

specialize (Hy3 1%nat).
unfold partial_sum3 in Hy3; simpl in Hy3.
remember (u O) as b eqn:Hb; symmetry in Hb.
destruct b; [ exfalso | easy ].

bbb.
   intros n.
   unfold ter_bin_of_frac_part; symmetry.
   set (x := (y * 3 ^ n)%R).
   destruct (Rlt_dec (frac_part x) (1 / 3)) as [Hx| Hx].
    subst x E.
    unfold is_upper_bound in Hy1.
    destruct n.
     simpl in Hx.
     rewrite Rmult_1_r in Hx.
     clear Hy1 Hy2.
     specialize (Hy3 1%nat).
     unfold partial_sum3 in Hy3; simpl in Hy3.
     remember (u O) as b eqn:Hb; symmetry in Hb.
     destruct b; [ exfalso | easy ].
     rewrite Rplus_0_r in Hy3.
     unfold partial_sum3 in Hy4; simpl in Hy4.
     assert (H : ∀ k, (partial_sum3 u k <= 1)%R) by apply partial_sum3_le_1.
     specialize (Hy4 1%R H); clear H.
bbb.

Theorem toto : ∀ u y,
  (∀ k, (partial_sum3 u k <= y)%R)
  → (∀ b, (∀ k : ℕ, (partial_sum3 u k <= b)%R) → (y <= b)%R)
  → (frac_part y < 1 / 3)%R
  → IZR (Int_part (y * 3)) = 0%R.
Proof.
intros * Hk1 Hk2 Hy.
specialize (Hk1 O).
unfold partial_sum3 in Hk1; simpl in Hk1.
unfold partial_sum3; simpl.
assert (H : ∀ k, (partial_sum3 u k <= 1)%R) by apply partial_sum3_le_1.
specialize (Hk2 1%R H); clear H.
unfold frac_part in Hy.
Admitted. Show.

eapply toto in Hx; try eassumption.

bbb.

Theorem toto : ∀ u y n,
  (∀ k, (partial_sum3 u k <= y)%R)
  → (∀ b, (∀ k : ℕ, (partial_sum3 u k <= b)%R) → (y <= b)%R)
  → IZR (Int_part (y * 3 ^ S n)) = (3 ^ S n * partial_sum3 u n)%R.
Proof.
intros * Hk1 Hk2.
induction n.
 simpl; rewrite Rmult_1_r.
 specialize (Hk1 O).
 unfold partial_sum3 in Hk1; simpl in Hk1.
 unfold partial_sum3; simpl.
 rewrite Rmult_0_r.
 specialize (Hk2 1).

bbb.
 assert (∀ ε, (ε > 0)%R → (y <= 1 - ε)%R).
  intros ε Hε.
  apply Hk2; intros k.
 

 specialize (Hk2 1).
bbb.

bbb.
Check Rseries_CV_comp.
bbb.

Check
  (Cantor_gen ℕ ℕ ℝ (setp unit_interv) id ter_bin_of_frac_part id_nat
     ter_bin_of_frac_part_surj).

Print unit_interv.
Print set.

bbb.

Definition Canonical_seq := mkset (λ u, ∀ i, ∃ j, i ≤ j ∧ u j = false).

Theorem partial_sum_aux_succ_all_true : ∀ r k pow i,
  (∀ k : ℕ, bin_of_frac_part r k = true)
  → partial_sum_aux (S k) (bin_of_frac_part r) pow i =
    (partial_sum_aux k (bin_of_frac_part r) pow i + pow / 2 ^ S k)%R.
Proof.
intros * Hb.
revert pow i.
induction k; intros; [ simpl; rewrite Hb; lra | ].
simpl in IHk; simpl.
do 2 rewrite Hb.
specialize (IHk (pow / 2)%R (S i)).
rewrite Hb in IHk; rewrite IHk.
rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
apply Rplus_eq_compat_l.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
rewrite <- Rmult_assoc.
rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
Qed.

Theorem partial_sum_aux_mult_distr_r : ∀ k u pow i x,
  (partial_sum_aux k u pow i * x)%R = partial_sum_aux k u (pow * x) i.
Proof.
intros.
revert pow i.
induction k; intros; [ now rewrite Rmult_0_l | simpl ].
destruct (u i).
 rewrite Rmult_plus_distr_r, Rmult_div.
 apply Rplus_eq_compat_l.
 now rewrite IHk; unfold Rdiv; rewrite Rmult_shuffle0.

 now rewrite IHk; unfold Rdiv; rewrite Rmult_shuffle0.
Qed.

Theorem frac_part_partial_sum_0 : ∀ k u pow i,
  (∀ j, j ≤ k → frac_part (pow / 2 ^ j) = 0)
  → frac_part (partial_sum_aux k u pow i) = 0%R.
Proof.
intros * Hj.
revert pow i Hj.
induction k; intros; [ apply fp_R0 | simpl ].
destruct (u i).
 assert (H : 1%nat ≤ S k) by (apply -> Nat.succ_le_mono; apply Nat.le_0_l).
 apply Hj in H; rewrite pow_1 in H.
 rewrite plus_frac_part2; rewrite H, Rplus_0_l.
  rewrite IHk; [ lra | intros j Hjk ].
  apply Nat.succ_le_mono in Hjk.
  apply Hj in Hjk; simpl in Hjk.
  unfold Rdiv in Hjk.
  rewrite Rinv_mult_distr in Hjk; [ | lra | apply pow_nonzero; lra ].
  rewrite <- Rmult_assoc in Hjk.
  now do 2 rewrite fold_Rdiv in Hjk.

  rewrite IHk; [ lra | intros j Hjk ].
  apply Nat.succ_le_mono in Hjk.
  apply Hj in Hjk; simpl in Hjk.
  unfold Rdiv in Hjk.
  rewrite Rinv_mult_distr in Hjk; [ | lra | apply pow_nonzero; lra ].
  rewrite <- Rmult_assoc in Hjk.
  now do 2 rewrite fold_Rdiv in Hjk.

 rewrite IHk; [ lra | intros j Hjk ].
 apply Nat.succ_le_mono in Hjk.
 apply Hj in Hjk; simpl in Hjk.
 unfold Rdiv in Hjk.
 rewrite Rinv_mult_distr in Hjk; [ | lra | apply pow_nonzero; lra ].
 rewrite <- Rmult_assoc in Hjk.
 now do 2 rewrite fold_Rdiv in Hjk.
Qed.

Theorem bin_of_frac_part_first_true : ∀ r i,
  (0 <= r <= 1)%R
  → (∀ j : ℕ, i ≤ j → bin_of_frac_part r j = true)
  → ∃ k,
    bin_of_frac_part (r / 2) k = false ∧
    ∀ j, k < j → bin_of_frac_part (r / 2) j = true.
Proof.
intros * Hr Hj.
destruct (Req_dec r 1) as [Hr1| Hr1].
 subst r; specialize (Hj i (le_refl i)).
 unfold bin_of_frac_part in Hj.
 rewrite Rmult_1_l in Hj.
 rewrite frac_part_pow in Hj.
  destruct (Rlt_dec 0 (1 / 2)); [ easy | lra ].

  replace 2%R with (INR 2) by easy.
  apply frac_part_INR.

 induction i.
  exists O.
  split.
   unfold bin_of_frac_part; simpl.
   rewrite Rmult_1_r.
   destruct (Rlt_dec (frac_part (r / 2)) (1 / 2)) as [ | H]; [ easy | ].
   exfalso; apply H; clear H.
   rewrite frac_part_self; lra.

   intros j Hj0.
   destruct j; [ easy | clear Hj0 ].
   unfold bin_of_frac_part.
   set (x := (r / 2 * 2 ^ S j)%R).
   destruct (Rlt_dec (frac_part x) (1 / 2)) as [H| ]; [ exfalso | easy ].
   subst x; simpl in H.
   unfold Rdiv at 1 in H.
   rewrite Rmult_assoc, Rmult_comm, <- Rmult_assoc in H.
   rewrite Rinv_l, Rmult_1_l in H; [ | lra ].
   specialize (Hj j (Nat.le_0_l j)).
   unfold bin_of_frac_part in Hj; simpl in Hj.
   rewrite Rmult_comm in H.
   set (x := (r * 2 ^ j)%R) in Hj, H.
   now destruct (Rlt_dec (frac_part x) (1 / 2)).

  destruct (Bool.bool_dec (bin_of_frac_part r i) true) as [Hb| Hb].
   apply IHi; intros j Hij.
   destruct (le_dec (S i) j) as [Hsij| Hsij]; [ now apply Hj | ].
   apply Nat.nle_gt, Nat.succ_le_mono in Hsij.
   apply Nat.le_antisymm in Hsij; [ now subst j | easy ].

   apply Bool.not_true_iff_false in Hb.
   exists (S i).
    split.
     unfold bin_of_frac_part.
     set (x := (r / 2 * 2 ^ S i)%R).
     destruct (Rlt_dec (frac_part x) (1 / 2)) as [| H]; [ easy | ].
     exfalso; apply H; clear H; subst x.
     unfold Rdiv at 1; simpl.
     rewrite Rmult_assoc, Rmult_comm, <- Rmult_assoc.
     rewrite Rinv_l, Rmult_1_l; [ | lra ].
     unfold bin_of_frac_part in Hb; rewrite Rmult_comm in Hb.
     set (x := (2 ^ i * r)%R) in Hb |-*.
     now destruct (Rlt_dec (frac_part x) (1 / 2)).

     intros j Hij.
     destruct j; [ easy | ].
     apply Nat.succ_lt_mono in Hij.
     apply Hj in Hij.
     unfold bin_of_frac_part in Hij |-*.
     set (x := (r * 2 ^ j)%R) in Hij.
     destruct (Rlt_dec (frac_part x) (1 / 2)) as [| H]; [ easy | ].
     subst x; set (x := (r / 2 * 2 ^ S j)%R).
     destruct (Rlt_dec (frac_part x) (1 / 2)) as [H'| ]; [ | easy ].
     subst x; simpl in H'.
     unfold Rdiv at 1 in H'; simpl in H'.
     rewrite Rmult_assoc, Rmult_comm, <- Rmult_assoc in H'.
     rewrite Rinv_l, Rmult_1_l in H'; [ | lra ].
     now rewrite Rmult_comm in H'.
Qed.

(*
Theorem converted_real_is_canonical : ∀ r,
  (0 <= r <= 1)%R
  → bin_of_frac_part r ∈ Canonical_seq.
Proof.
intros r Hr i.
enough (H : ¬ (∀ j, i ≤ j → bin_of_frac_part r j = true)).
 apply classic.
 intros Hj; apply H; clear H; intros j Hij.
 apply classic.
 intros H; apply Hj; clear Hj.
 exists j; split; [ easy | ].
 now apply not_true_iff_false in H.

 intros Hj.
 specialize (bin_of_frac_part_first_true r i Hr Hj); intros Hk.
 destruct Hk as (k & Hk1 & Hk2); clear i Hj.
 assert (H : (0 <= r / 2 <= 1 / 2)%R) by lra.
 clear Hr; rename H into Hr.
 remember (r / 2)%R as r'; clear r Heqr'.
 rename r' into r; move Hr before r.
 enough (H : r = ((2 * IZR (Int_part (r * 2 ^ k)) + 1) / 2 ^ S k)%R).
  unfold bin_of_frac_part in Hk1.
  destruct (Rlt_dec (frac_part (r * 2 ^ k)) (1 / 2)) as [H1| ]; [ | easy ].
  clear Hk1; rewrite H in H1.
  set (x := (2 ^ S k)%R) in H1; simpl in x; subst x.
  unfold Rdiv in H1 at 1.
  rewrite Rinv_mult_distr in H1; [ | lra | apply pow_nonzero; lra ].
  do 2 rewrite Rmult_assoc in H1.
  rewrite Rinv_l in H1; [ | apply pow_nonzero; lra ].
  rewrite Rmult_1_r in H1.
  rewrite Rmult_plus_distr_r in H1.
  rewrite Rmult_assoc, Rmult_comm, Rmult_assoc in H1.
  rewrite Rinv_l in H1; [ | lra ].
  rewrite Rmult_1_r, fold_Rdiv in H1.
  rewrite plus_frac_part2 in H1.
SearchAbout (frac_part _ = 0%R).

Theorem frac_part_IZR : ∀ z, frac_part (IZR z) = 0%R.
Proof.
intros z.
destruct (Z_le_dec 0 z) as [Hz| Hz].
 rewrite <- Z2Nat.id with (n := z); [ | easy ].
 rewrite <- INR_IZR_INZ.
 apply frac_part_INR.

 apply Z.nle_gt in Hz.
 destruct z as [| p| p]; [ easy | easy | clear Hz; simpl ].
 remember (Pos.to_nat p) as n; clear p Heqn.
 induction n; [ simpl; rewrite Ropp_0; apply fp_R0 | simpl ].
 destruct n.

bbb.

 assert
   (Hk : ∃ k,
    match k with
    | O => True
    | S k' => bin_of_frac_part r k' = false
    end ∧
    ∀ j, k ≤ j → bin_of_frac_part r j = true).
   induction i; [ now exists O | ].
   destruct (Bool.bool_dec (bin_of_frac_part r i) false) as [Hi'| Hi'].
    now exists (S i).

    apply IHi.
    intros j Hij.
    destruct (lt_dec i j) as [H| H]; [ now apply Hj | ].
    apply Nat.nlt_ge in H.
    apply Nat.le_antisymm in H; [ | easy ].
    now apply not_false_iff_true in Hi'; subst j.

  clear i Hj.
  destruct Hk as (k & Hkk & Hk).
bbb.

  destruct k.
   enough (H : r = 1%R).
    subst r.
    specialize (Hk O (Nat.le_refl _)).
    unfold bin_of_frac_part in Hk; simpl in Hk.
    rewrite Rmult_1_r in Hk.
    rewrite fp_R1 in Hk.
    destruct (Rlt_dec 0 (1 / 2)) as [| H]; [ easy | lra ].

bbb.
  set (u := bin_of_frac_part r).
  set
    (v i :=
       match k with
       | O => false
       | S k' =>
           if lt_dec i k' then u i
           else if eq_nat_dec i k' then true
           else false
       end).
  enough (r = partial_sum v k).
   subst u v.
   specialize (Hk k (le_refl _)).
   induction k.
    simpl in H.
    unfold bin_of_frac_part in Hk; simpl in Hk.
    rewrite Rmult_1_r in Hk.
    destruct (Rlt_dec (frac_part r) (1 / 2)) as [H1| H1]; [ easy | ].
    rewrite H in H1; simpl in H1.
    apply H1; clear H1.

bbb.
(**)
  enough (Hrk : frac_part (r * 2 ^ k) = 0%R).
   specialize (Hk k (Nat.le_refl _)).
   unfold bin_of_frac_part in Hk.
   rewrite Hrk in Hk.
   destruct (Rlt_dec 0 (1 / 2)) as [| H1]; [ easy | apply H1; lra ].

   assert (Hk' : ∀ j, k ≤ j → (1 / 2 <= frac_part (r * 2 ^ j))%R).
    intros j Hkj.
    specialize (Hk j Hkj).
    unfold bin_of_frac_part in Hk.
    remember (frac_part (r * 2 ^ j)) as x.
    destruct (Rlt_dec x (1 / 2)) as [| H]; [ easy | ].
    now apply Rnot_lt_le in H.

    clear Hk; rename Hk' into Hk.
    set (u := bin_of_frac_part r).
    set (E x := ∃ k, partial_sum u k = x).
    enough (Hb : bound E).
     enough (He : ∃ x, E x).
      set (c := completeness _ Hb He).
      destruct c as (lub & Hub & Hlub).
      set
        (v i :=
           if lt_dec i k then u i
           else if eq_nat_dec i k then true else false).
      assert (lub = partial_sum v k).
bbb.
    destruct Hkk as [Hkk| Hkk].
     subst k; rewrite pow_O, Rmult_1_r.
     unfold frac_part.
bbb.
    destruct (Rle_dec 1 r) as [Hr1| Hr1]; [ lra | ].
    exfalso; apply Rnot_le_lt in Hr1.
    remember (partial_sum (bin_of_frac_part r)) as u eqn:Hu.
    enough (Hir : ∃ k, (u k <= r < u (S k))%R).
     rewrite Hu in Hir.
     assert (Hb : ∀ k, bin_of_frac_part r k = true).
      intros k.
      simpl; unfold bin_of_frac_part.
      set (x := frac_part (r * 2 ^ k)).
      destruct (Rlt_dec x (1 / 2)) as [H1| H1]; [ | easy ].
      apply Rlt_not_le in H1.
      now specialize (Hk k).

      assert (Hps : ∀ k, (u (S k) = u k + 1 / 2 ^ S k)%R).
       intros k; subst u; unfold partial_sum.
       now rewrite partial_sum_aux_succ_all_true.

       destruct Hir as (k & Hur & Hru).
       rewrite <- Hu in Hur, Hru.
       rewrite Hps in Hru; simpl in Hru.
       set (n := (2 ^ k)%R) in Hru.
       apply Rmult_le_compat_r with (r := n) in Hur.
        2: apply pow_le; lra.

        apply Rmult_lt_compat_r with (r := n) in Hru.
         2: apply pow_lt; lra.

         rewrite Rmult_plus_distr_r in Hru.
         simpl in Hru; unfold Rdiv in Hru.
         unfold n in Hru.
         rewrite Rinv_mult_distr in Hru; [ | lra | apply pow_nonzero; lra ].
         do 2 rewrite Rmult_assoc in Hru.
         rewrite Rinv_l in Hru; [ | apply pow_nonzero; lra ].
         fold n in Hru.
         rewrite Rmult_1_r in Hru.
         rewrite fold_Rdiv in Hru.
         enough (H : (frac_part (r * 2 ^ k) < 1 / 2)%R).
          apply Rlt_not_le in H; apply H, Hk.

          fold n.
          assert (Hukn : (frac_part (u k * n) = 0)%R).
           rewrite Hu; unfold n; simpl; clear - Hb.
           unfold partial_sum.
           rewrite partial_sum_aux_mult_distr_r.
           rewrite Rmult_1_l.
           apply frac_part_partial_sum_0.
           intros j Hjk.
           rewrite Rpow_div_sub; [ | lra | easy ].
           apply frac_part_pow, (frac_part_INR 2).

           enough (IZR (Int_part (r * n)) = u k * n)%R.
            unfold frac_part; lra.

            unfold frac_part in Hukn.
            eapply Rplus_eq_compat_l in Hukn.
            rewrite Rplus_minus, Rplus_0_r in Hukn.
            rewrite Hukn; f_equal.
bbb.

unfold bin_of_frac_part in H.
destruct (Rlt_dec (frac_part (r * 2 ^ k)) (1 / 2)) as [H1| H1]; [ | easy ].
clear H.
assert (∀ j, (k < j)%nat → frac_part (r * 2 ^ j) >= 1 / 2)%R.
 intros j Hkj.
 apply Hk in Hkj.
 unfold bin_of_frac_part in Hkj.
 apply Rnot_lt_ge.
 now destruct (Rlt_dec (frac_part (r * 2 ^ j)) (1 / 2)).

 clear Hk; rename H into Hk.

bbb. 

Print partial_sum_aux.

bbb.

revert pow i Hp.
induction k; intros; [ apply fp_R0 | simpl ].
destruct (u i).
 rewrite plus_frac_part2.
  rewrite IHk, Rplus_0_r.

bbb.

  replace pow with (pow / 2 + pow / 2)%R in Hp by lra.

bbb.

apply toto.


bbb.
            induction k; [ apply fp_R0 | ].
            simpl; rewrite Hb.
bbb.
            simpl.
            destruct k.
             simpl; rewrite Hb, Rplus_0_r.
             unfold Rdiv; rewrite Rmult_1_r, Rmult_assoc.
             rewrite Rinv_l, Rmult_1_r; [ apply fp_R1 | lra ].

             destruct k.
              simpl; rewrite Hb, Hb, Rplus_0_r.
bbb.

             rewrite plus_frac_part2.

SearchAbout (frac_part R1).

             apply fp_R1.


bbb.
            destruct k; [ simpl; rewrite Rmult_0_l; apply fp_R0 | ].
vvv.

Theorem toto : ∀ k u pow i,
  frac_part (pow * 2) = 0%R
  → frac_part (partial_sum_aux k u pow i * 2 ^ k) = 0%R.
Proof.
intros * Hpow.
revert pow i Hpow.
induction k; intros; simpl; [ rewrite Rmult_0_l; apply fp_R0 | ].
remember (u i) as b eqn:Hb; symmetry in Hb.
destruct b.
 rewrite Rmult_plus_distr_r, <- Rmult_assoc.
(**)
 rewrite plus_frac_part2.
  rewrite frac_part_mult_for_0; [ | easy | ].
   rewrite Rplus_0_l.
   rewrite <- Rmult_assoc, Rmult_shuffle0, Rmult_comm.

Theorem titi : ∀ n x,
  frac_part x = 0%R ∨ frac_part x = (/ INR n)%R →
  frac_part (INR n * x) = 0%R.
Proof.
Admitted.
Show.
replace 2%R with (INR 2) at 1 by easy.
apply titi.
destruct (Req_dec (frac_part pow) 0) as [H1| H1].
 left; apply IHk.
 unfold Rdiv; rewrite Rmult_assoc, Rinv_l; [ | lra ].
 now rewrite Rmult_1_r.

 right.

bbb.

Theorem titi : ∀ n x, (n ≥ 2)%nat →
  frac_part (INR n * x) = 0%R ↔
  frac_part x = 0%R ∨ ∃ d, (d | n) ∧ frac_part x = (/ INR d)%R.
Proof.
intros * Hn.
split; intros Hx.
revert x Hx.
induction n; intros; [ easy | ].
destruct n; [ now apply Nat.succ_le_mono in Hn | ].

bbb.
 unfold Rdiv at 1; rewrite Rmult_comm, Rmult_assoc.
 rewrite Rinv_l, Rmult_1_r; [ | lra ].
 rewrite <- Rmult_assoc, Rmult_shuffle0.
 simpl in Hpow.
 rewrite plus_frac_part2.
Print partial_sum_aux.

  rewrite Rplus_comm.
  rewrite frac_part_mult_for_0; [ | apply IHk | ].
bbb.

  replace 2%R with (INR 2) at 5 by now simpl.
  rewrite frac_part_mult_nat.
   rewrite Rplus_0_r, Rmult_comm.
   simpl in Hpow.
   rewrite <- Rmult_assoc, Rmult_shuffle0 in Hpow.
bbb.

   replace 2%R with (INR 2); [ now rewrite frac_part_mult_nat | ].
   rewrite frac_part_mult_nat in Hpow.


   replace (2 ^ k)%R with (INR (2 ^ k)); [ now rewrite frac_part_mult_nat | ].
   now rewrite pow_INR.

   idtac.
   apply IHk.
bbb.

bbb.

SearchAbout (frac_part (_ * _)).

Print partial_sum_aux.

            induction k; [ simpl; rewrite Rmult_0_l; apply fp_R0 | ].
            simpl.
            remember (bin_of_frac_part r 0) as b eqn:Hb.
            symmetry in Hb.
            destruct b.
             rewrite Rmult_plus_distr_r, <- Rmult_assoc.
             unfold Rdiv at 1; rewrite Rmult_1_l.
             rewrite Rinv_l, Rmult_1_l.
bbb.

           unfold frac_part.
Theorem toto : ∀ x z,
  (IZR z <= x < IZR (z + 1))%R
  → z = Int_part x.
Admitted.
Show.

SearchAbout IZR.

bbb.
           specialize (base_Int_part (r * n)); intros (H1, H2).
assert (IZR (Int_part (r * n)) = u k * n)%R.
SearchAbout up.


bbb.
rewrite <- toto with (z := (u k * n)%R).
bbb.

Proof.
intros.
unfold partial_sum.
destruct k; simpl.


bbb.
     assert (0 < 1 - r)%R by lra.
     assert (Hk1r : ∃ k, ((1 / 2) ^ k < 1 - r)%R).
      remember (1 - r)%R as ε eqn:Hε.
      clear - H.
      apply archimed_cor1 in H.
      destruct H as (k & Hkε & Hk).
      exists k.
      eapply Rlt_trans; [ | eassumption ].
      unfold Rdiv.
      rewrite Rpow_mult_distr, pow1, Rmult_1_l.
      rewrite <- Rinv_pow; [ | lra ].
      apply Rinv_lt_contravar.
       apply Rmult_lt_0_compat; [ | apply pow_lt; lra ].
       now apply lt_INR in Hk.

       clear - Hk.
       induction k; simpl; [ lra | ].
       destruct k; [ lra | ].
       apply Rplus_lt_reg_r with (r := (-1)%R).
       rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
       eapply Rlt_trans; [ apply IHk, Nat.lt_0_succ | ].
       apply Rplus_lt_reg_r with (r := 1%R).
       rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
       rewrite double.
       apply Rplus_lt_compat_l.
       apply Rlt_pow_R1; [ lra | ].
       apply Nat.lt_0_succ.

      destruct Hk1r as (k, Hk1r).
bbb.
      specialize (archimed ε); intros (H1, H2).
assert (myarchi : ∀ ε x, (ε > 0)%R → ∃ N, (ε * INR N > x)%R).
 clear; intros * Hε.
 destruct (Rlt_dec x 0) as [H3| H3].
  exists O; simpl; lra.

  specialize (archimed (x / ε)); intros (H1, H2).
  exists (Z.to_nat (up (x / ε))).
  enough (x / ε < INR (Z.to_nat (up (x / ε))))%R.
   apply Rlt_gt.
   apply Rmult_lt_compat_r with (r := ε) in H; [ | easy ].
   unfold Rdiv in H at 1.
   rewrite Rmult_assoc, Rinv_l, Rmult_1_r in H; lra.

   rewrite INR_IZR_INZ, Z2Nat.id; [ easy | ].
SearchAbout up.

bbb.
    assert (Hk' : ∀ j, (1 / 2 <= frac_part (r * 2 ^ j))%R).
     intros j; specialize (Hk j).
     unfold bin_of_frac_part in Hk.
     remember (frac_part (r * 2 ^ j)) as x.
     destruct (Rlt_dec x (1 / 2)) as [| H]; [ easy | ].
     now apply Rnot_lt_le in H.

    set (u := bin_of_frac_part r) in Hk.
    set (E x := ∃ k, partial_sum u k = x).
    assert (Hb : bound E).
     unfold bound, E; exists 1.
     unfold is_upper_bound.
     intros x (k, Hx); subst x.
     apply partial_sum_le_1.

     assert (He : ∃ x, E x) by (now exists 0%R, 0%nat).
     set (m := completeness E Hb He).
     destruct m as (x & Hxu & Hxlu).
     unfold E, is_upper_bound in Hxu, Hxlu.
     rename x into lub; clear E Hb He.
     assert (Hpsp : ∀ k, (partial_sum u (S k) = (1 + partial_sum u k) / 2)%R).
      assert
        (H : ∀ k pow i,
         (partial_sum_aux (S k) u pow i =
          pow + partial_sum_aux k u pow i / 2)%R).
       intros k.
       induction k; intros; [ simpl; rewrite Hk; lra | ].
       remember (S k) as sk; simpl; subst sk.
       rewrite Hk; apply Rplus_eq_compat_l.
       rewrite IHk; simpl; rewrite Hk; lra.

       intros k; unfold partial_sum; rewrite H; lra.

      assert (Hek : ∀ x,
        (∃ k : ℕ, partial_sum u k = x)%R
        → (∃ k : ℕ, partial_sum u k = (1 + x) / 2)%R).
       intros x (k & Hkx).
       now exists (S k); rewrite Hpsp, Hkx.

bbb.
       assert (lub <= 1)%R.
        apply Hxlu.
        intros x Hkx.
        apply Hek in Hkx.
        destruct Hkx as (k, Hkx).
bbb.

     assert (H : ∀ k pow i,
       partial_sum_aux k (bin_of_frac_part r) pow i =
       partial_sum_aux k (λ _, true) pow i).
      intros.
      revert i pow.
      induction k; intros; [ easy | simpl; rewrite Hk ].
      apply Rplus_eq_compat_l, IHk.

      clear Hk; rename H into Hk.
      unfold partial_sum in Hxu.
      assert (H : ∀ x : ℝ,
        (∃ k : ℕ, partial_sum_aux k (λ _, true) (1 / 2) 0 = x)
        → (x <= lub)%R).
       intros * (k, H); rewrite <- Hk in H.
       now apply Hxu; exists k.

       clear Hxu; rename H into Hxu.
       unfold partial_sum in Hxlu.
       assert (H : ∀ b,
         (∀ x, (∃ k : ℕ, partial_sum_aux k (λ _, true) (1 / 2) 0 = x)
          → (x <= b)%R)
         → (lub <= b)%R).
        intros * H.
        apply Hxlu; intros * (k, H1); apply H; exists k.
        now rewrite <- Hk.

        clear Hxlu; rename H into Hxlu; clear Hk.
bbb.

     assert (Hrlub : r = lub).
      assert (lub <= r)%R.
       apply Hxlu; intros x (k & Hx); subst x.
bbb.
destruct k; [ easy | simpl ].
rewrite Hk.
pose proof Hk O as H.
unfold bin_of_frac_part in H.
simpl in H.
rewrite Rmult_1_r in H.
destruct (Rlt_dec (frac_part r) (1 / 2)) as [| Hk0]; [ easy | ].
apply Rnot_lt_le in Hk0.
unfold frac_part in Hk0.
rewrite Int_part_is_0 in Hk0; [ | easy ].
rewrite Rminus_0_r in Hk0.
clear H.
destruct k; [ now rewrite Rplus_0_r | simpl ].
rewrite Hk.
pose proof Hk 1%nat as H.
unfold bin_of_frac_part in H.
simpl in H.
rewrite Rmult_1_r in H.
destruct (Rlt_dec (frac_part (r * 2)) (1 / 2)) as [| Hk1]; [ easy | ].
apply Rnot_lt_le in Hk1.
unfold frac_part in Hk1.
replace 2%R with (INR (1 + 1)) in Hk1 at 3 by easy.
rewrite Int_part_close_to_1 in Hk1; [| now split ].
simpl in Hk1.
apply Rplus_le_compat_r with (r := 1) in Hk1.
replace (_ - 1 + 1)%R with (r * 2)%R in Hk1 by lra.
field_simplify in Hk1.
rewrite Rmult_1_r, Rmult_comm in Hk1.
field_simplify in Hk1.
rewrite Rdiv_1_r in Hk1.
apply Rmult_le_compat_l with (r := (/2)%R) in Hk1; [ | lra ].
rewrite <- Rmult_assoc in Hk1.
rewrite Rinv_l, Rmult_1_l in Hk1; [ | lra ].
field_simplify in Hk1.
rewrite Rdiv_1_r in Hk1.
clear H Hk0.
rewrite <- Rplus_assoc.
remember (1 / 2 + 1 / 2 / 2)%R as u.
field_simplify in Hequ.
rewrite Rdiv_1_r in Hequ.
replace (6 / 8)%R with (3 / 4)%R in Hequ by lra.
subst u.
bbb.
Check Int_part_close_to_1.

SearchAbout Int_part.
Theorem glop : ∀ r, (1 / 2 <= r < 1)%R → Int_part (r * 2) = 1.
Proof.
About Int_part_is_0.
bbb.

bbb.
rewrite Int_part_is_0 in Hk1; [ | ].
rewrite Rminus_0_r in Hk0.
clear H.


destruct k; simpl.
rewrite Rplus_0_r.
pose proof Hk O as Hk0.
unfold bin_of_frac_part in Hk0.
simpl in Hk0.
rewrite Rmult_1_r in Hk0.

bbb.

SearchAbout partial_sum_aux.
rewrite trunc_bool_seq_eq with (m := k); [ | easy ].
       induction k; [ easy | ].
rewrite <- Nat.add_1_l.
SearchAbout partial_sum_aux.
rewrite partial_sum_aux_add.
simpl.
unfold trunc_bool_seq.
remember (trunc_bool_seq (bin_of_frac_part r) (S k) 0) as b eqn:Hb.
symmetry in Hb.
destruct b.



rewrite Hk.
rewrite Rmult_1_r.
       simpl.
bbb.

     assert (Hx : (x = 1)%R).
      assert (Hx1 : (x <= 1)%R).
       apply Hxlu; intros y (k, Hy); subst y.
       apply partial_sum_le_1.

       assert (Hx2 : (1 <= x)%R).
        apply Rnot_lt_le.
        intros H.
        enough (Hy : ∃ y k,
          (x <= y < 1)%R ∧ partial_sum (bin_of_frac_part r) k = y).
         destruct Hy as (y & k & Hxy & Hy).
         assert (Hky : ∃ k, partial_sum (bin_of_frac_part r) k = y).
          now exists k.

          specialize (Hxu y Hky).
          destruct Hxy as (Hxy, Hy1).
          assert (H1 : x = y) by (now apply Rle_antisym).
          move H1 at top; subst y.
          clear H Hxu Hxy Hky.
          rewrite <- Hy in Hy1.
          clear -Hk Hy1.
          unfold partial_sum in Hy1.
          destruct k.
           simpl in Hy1.
bbb.
*)

Theorem bin_of_frac_part_surj : ∀ u : ℕ → bool, ∃ x : ℝ,
  x ∈ unit_interv ∧ ∀ n, bin_of_frac_part x n = u n.
Proof.
intros u.
set (s := R_of_bin_seq u).
destruct s as (lub, Hlub); simpl in Hlub.
unfold is_lub, is_upper_bound in Hlub.
destruct Hlub as (Hub, Hlub).
exists lub.
split.
 simpl; split; [ now apply Hub; exists O | ].
 apply Hlub; intros x (k & Hk); subst x.
 apply partial_sum_le_1.

 intros n; symmetry.
 unfold bin_of_frac_part.
 destruct (Rlt_dec (frac_part (lub * 2 ^ n)) (1 / 2)) as [H₁| H₁].
   (* oui mais non, il y a là le syndrôme du 0,9999... = 1;
      faut prouver la canonicité de bin_of_frac_part d'abord *)
bbb.

Theorem trunc_bool_seq_eq : ∀ z pow i m n,
  i + n <= m
  → partial_sum_aux n (bin_of_frac_part z) pow i =
    partial_sum_aux n (trunc_bool_seq (bin_of_frac_part z) m) pow i.
Proof.
intros * Hm.
revert pow i m Hm.
induction n; intros; [ easy | simpl ].
remember (bin_of_frac_part z i) as b eqn:Hb; symmetry in Hb.
remember (trunc_bool_seq (bin_of_frac_part z) m i) as b' eqn:Hb'.
symmetry in Hb'.
assert (b = b').
 subst b b'.
 unfold trunc_bool_seq.
 destruct (lt_dec i m) as [| H₁]; [ easy | ].
 exfalso; apply H₁.
 apply Nat.lt_le_trans with (m := (i + S n)%nat); [ | easy ].
 apply Nat.lt_add_pos_r; apply Nat.lt_0_succ.

 move H at top; subst b'.
 rewrite <- Nat.add_succ_comm in Hm.
 destruct b; [ now apply Rplus_eq_compat_l, IHn | now apply IHn ].
Qed.

Theorem bin_of_frac_part_true_pow_le : ∀ z pow i,
  (0 <= z)%R
  → (0 <= pow <= (1 / 2) ^ S i)%R
  → bin_of_frac_part z i = true
  → (pow <= z)%R.
Proof.
intros * Hz Hpow Hi.
revert z pow Hz Hi Hpow.
induction i; intros.
 unfold bin_of_frac_part in Hi.
 rewrite pow_O, Rmult_1_r in Hi.
 destruct (Rlt_dec (frac_part z) (1 / 2)) as [| H₁]; [ easy | ].
 clear Hi; apply Rnot_lt_le in H₁; rewrite pow_1 in Hpow.
 destruct Hpow as (Hpow₀, Hpow₁).
 eapply Rle_trans; [ eassumption | ].
 eapply Rle_trans; [ eassumption | ].
 unfold frac_part.
 apply Rplus_le_reg_r with (r := IZR (Int_part z)).
 rewrite Rplus_comm, Rplus_minus.
 replace z with (z + 0)%R at 1 by lra.
 apply Rplus_le_compat_l.
 replace 0%R with (IZR 0) by easy.
 apply IZR_le.
 replace 0%Z with (Int_part 0); [ now apply Int_part_le_compat | ].
 replace 0%Z with (Z.of_nat 0); [ now rewrite <- Int_part_INR | easy ].

 apply (Rmult_le_reg_r 2); [ lra | ].
 apply IHi.
  apply (Rmult_le_compat_r 2) in Hz; [ | lra ].
  now rewrite Rmult_0_l in Hz.

  now rewrite <- bin_of_frac_part_succ.

  split.
   destruct Hpow as (H, _).
   apply (Rmult_le_compat_r 2) in H; [ | lra ].
   now rewrite Rmult_0_l in H.

   destruct Hpow as (_, H).
   apply (Rmult_le_compat_r 2) in H; [ | lra ].
   simpl in H; simpl; lra.
Qed.

Theorem partial_sum_aux_add : ∀ u pow i j k,
  (partial_sum_aux (i + j) u pow k =
   partial_sum_aux i u pow k + partial_sum_aux j u (pow / 2 ^ i) (i + k))%R.
Proof.
intros.
revert pow j k.
induction i; intros; [ now simpl; rewrite Rplus_0_l, Rdiv_1_r | simpl ].
unfold Rdiv in IHi |-*.
rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
rewrite IHi, <- Nat.add_succ_comm.
rewrite Rmult_assoc.
destruct (u k); [ now rewrite Rplus_assoc | easy ].
Qed.

(* 0x → 10; 1x → 00 *)
Definition cantor_canon_diagonal (g : ℕ → ℕ → bool) i :=
  if zerop (i mod 2) then negb (g (i / 2) i) else false.

Definition ext_eq {A B} (f g : A → B) := ∀ a, f a = g a.

Theorem canon_seq_not_countable : ¬ (is_countable _ ext_eq Canonical_seq).
Proof.
unfold is_countable, ext_eq.
intros (g, Hcontr).
enough (Hdc : cantor_canon_diagonal g ∈ Canonical_seq).
 specialize (Hcontr (cantor_canon_diagonal g) Hdc).
 destruct Hcontr as (n, Hcontr).
 specialize (Hcontr (n * 2)%nat).
 unfold cantor_canon_diagonal in Hcontr.
 rewrite Nat.mod_mul in Hcontr; [ | easy ].
 simpl in Hcontr.
 rewrite Nat.div_mul in Hcontr; [ | easy ].
 now symmetry in Hcontr; apply no_fixpoint_negb in Hcontr.

 intros i.
 unfold cantor_canon_diagonal.
 destruct (zerop (i mod 2)) as [Hi| Hi].
  apply Nat.mod_divides in Hi; [ | easy ].
  destruct Hi as (p, Hp).
  destruct (Bool.bool_dec (g (i / 2) i) false) as [Hi| Hi].
   exists (S i).
   split; [ now apply Nat.le_le_succ_r | ].
   destruct (zerop (S i mod 2)) as [Hsi| Hsi]; [ | easy ].
   rewrite Hp, <- Nat.add_1_l, Nat.mul_comm in Hsi.
   now rewrite Nat.mod_add in Hsi.

   exists i.
   split; [ easy | ].
   destruct (zerop (i mod 2)) as [Hi2| Hi2]; [ | easy ].
   apply not_false_is_true in Hi.
   now rewrite Hi.

  exists i.
  split; [ easy | ].
  destruct (zerop (i mod 2)) as [Hi2| Hi2]; [ | easy ].
  now rewrite Hi2 in Hi.
Qed.

Lemma crophage : ∀ u,
  u ∈ Canonical_seq →
  ∀ i, u i = bin_of_frac_part (proj1_sig (R_of_bin_seq u)) i.
Proof.
intros u Hc i.
unfold bin_of_frac_part.
set (s := R_of_bin_seq u).
destruct s as (z, Hz); simpl.
unfold is_lub in Hz.
unfold is_upper_bound in Hz; simpl in Hz.
destruct Hz as (Hzub, Hzlub).
assert (∀ k, partial_sum u k <= z)%R by now intros; apply Hzub; exists k.
clear Hzub; rename H into Hzub.
assert (H : ∀ b, (∀ k, (partial_sum u k <= b)%R) → (z <= b)%R).
 intros b H; apply Hzlub.
 now intros x (k, Hk); subst x.

 clear Hzlub; rename H into Hzlub.
 destruct (Rlt_dec (frac_part (z * 2 ^ i)) (1 / 2)) as [H1| H1].

bbb.

unfold R_of_bin_seq in Hx.
bbb.
unfold R_of_bin_seq.
simpl.

bbb.

Theorem bool_seq_not_countable : ∀ g : ℕ → ℕ → bool, ¬ (FinFun.Surjective g).
Proof.
intros g Hcontr.
unfold FinFun.Surjective in Hcontr.
specialize (Hcontr (λ i, negb (g i i))).
destruct Hcontr as (n, Hn).
enough (g n n = negb (g n n)).
 eapply no_fixpoint_negb; symmetry; eassumption.

 now remember (negb (g n n)) as x; rewrite Hn; subst x.
Qed.

Print bin_of_frac_part.
Check R_of_bin_seq.

bbb.

Theorem unit_interv_not_countable : ¬ (is_countable _ unit_interv).
Proof.
intros H.
unfold is_countable in H.
destruct H as (f, Hf).
enough (Hcontr : ∃ z, z ∈ unit_interv ∧ ∀ n, f n ≠ z).
 destruct Hcontr as (a & Ha & Hnn).
 apply Hf in Ha.
 destruct Ha as (n, Hn).
 eapply Hnn; eassumption.

 clear; simpl.
 set (g n := bin_of_frac_part (f n)).
 set (d := cantor_diagonal g).
 set (rp := R_of_bin_seq d).
 destruct rp as (z, Hz).
 exists z.
 unfold is_lub in Hz.
 destruct Hz as (Hzub, Hzlub).
 unfold is_upper_bound in Hzub, Hzlub.
 unfold Rset_of_bin_seq in Hzub, Hzlub.
 simpl in Hzub, Hzlub.
 assert (∀ k, partial_sum d k <= z)%R by now intros; apply Hzub; exists k.
 clear Hzub; rename H into Hzub.
 assert (H : ∀ b, (∀ k, (partial_sum d k <= b)%R) → (z <= b)%R).
  intros b H; apply Hzlub.
  now intros x (k, Hk); subst x.

  clear Hzlub; rename H into Hzlub.
  split.
   Focus 2.
   intros n Hz.
   unfold g in d.
   unfold cantor_diagonal in d.
   remember (d n) as b eqn:Hb.
Print partial_sum.
Print partial_sum_aux.
Search partial_sum_aux.

   unfold d in Hb; simpl in Hb.
   rewrite Hz in Hb.
bbb.
   remember (g n) as u eqn:Hu.
   unfold g in Hu.
   rewrite Hz in Hu.

bbb.
   subst z.
Print bin_of_frac_part.
(*
   unfold cantor_diagonal in Hd; subst d g.
*)
pose proof Hzub n as H; simpl in H.

(*
Theorem glip : ∀ k u x,
  (partial_sum u k <= x)%R
  → ∀ i, i < k → Nat.b2n (u i) <= Nat.b2n (bin_of_frac_part x i).
Proof.
intros * Hp i Hik.
unfold partial_sum in Hp.
revert i Hik.
induction k; intros; [ now apply Nat.nlt_0_r in Hik | ].
simpl in Hp.
remember (u O) as u₀ eqn:Hu₀; symmetry in Hu₀.
destruct u₀.
Print partial_sum_aux.

bbb.

(* end of glip; return to theorem *)
assert (H1 : ∀ i, Nat.b2n (d i) <= Nat.b2n (bin_of_frac_part (f n) i)).
now eapply glip.
rewrite Hd in H1; simpl in H1.
unfold cantor_diagonal in H1; simpl in H1.
rewrite Hg in H1; simpl in H1.
bbb.
*)

(* suggestion of possible theorems, to be proved if true *)
(*
Theorem toto : ∀ x y,
  (x <= y)%R ↔
  ∀ k, (partial_sum (bin_of_frac_part x) k <= partial_sum (bin_of_frac_part y) k)%R.
Proof.
intros.
split.
 intros Hxy k.
bbb.
*)

Theorem titi : ∀ x y,
  (0 <= x < 1)%R
  → (0 <= y < 1)%R
  → (x <= y)%R ↔
    ∀ k, Nat.b2n (bin_of_frac_part x k) <= Nat.b2n (bin_of_frac_part y k).
Proof.
intros * Hx Hy.
split.
 intros Hxy k.
 unfold bin_of_frac_part.
 destruct (Rlt_dec (frac_part (x * 2 ^ k)) (1 / 2)) as [H1| H1].
  destruct (Rlt_dec (frac_part (y * 2 ^ k)) (1 / 2)) as [H2| H2]; [ easy | ].
  apply Nat.le_0_l.

  destruct (Rlt_dec (frac_part (y * 2 ^ k)) (1 / 2)) as [H2| H2]; [ | easy ].
  exfalso; apply H1; clear H1.
  revert x y Hx Hy Hxy H2.
  induction k; intros.
   simpl in H2; simpl.
   rewrite Rmult_1_r in H2 |-*.
   unfold frac_part in H2 |-*.
   rewrite Int_part_is_0 in H2; [ | easy ].
   rewrite Int_part_is_0; [ | easy ].
   rewrite Rminus_0_r in H2 |-*.
   eapply Rle_lt_trans; eassumption.
   destruct (Rlt_dec y (1 / 2)) as [H3 | H3].
    assert (H4 : (x < 1 / 2)%R).
     eapply Rle_lt_trans; [ apply Hxy | apply H3 ].

     assert (Hx' : (0 <= x * 2 < 1)%R) by lra.
     assert (Hy' : (0 <= y * 2 < 1)%R) by lra.
     assert (Hxy' : (x * 2 <= y * 2)%R) by lra.
     simpl in H2; rewrite <- Rmult_assoc in H2.
     pose proof IHk (x * 2)%R (y * 2)%R Hx' Hy' Hxy' H2 as H5.
     now simpl; rewrite <- Rmult_assoc.

    apply Rnot_lt_le in H3.
bbb.
   simpl in H2; simpl.
   rewrite <- Rmult_assoc.
   apply IHk with (y := (y * 2)%R).

bbb.

Theorem R_not_countable : ¬ (is_countable ℝ (whole_set _)).
Proof.
intros H.
unfold is_countable in H.
destruct H as (f, Hf).
assert (Hcontr : ∃ a, a ∈ whole_set _ ∧ ∀ n, f n ≠ a).
 Focus 2.
 destruct Hcontr as (a & Ha & Hnn).
 apply Hf in Ha.
 destruct Ha as (n, Hn).
 eapply Hnn; eassumption.

 clear; simpl.
bbb.

Theorem sphere_not_countable : ¬ (is_countable _ sphere).
Proof.
intros H.
unfold is_countable in H.
destruct H as (f, Hf).
assert (Hcontr : ∃ a, a ∈ sphere ∧ ∀ n, f n ≠ a).
 Focus 2.
 destruct Hcontr as (a & Ha & Hnn).
 apply Hf in Ha.
 destruct Ha as (n, Hn).
 eapply Hnn; eassumption.

 clear.

bbb.

(*
Theorem toto : ∀ k u pow i,
  (partial_sum_aux (S k) u pow i =
   partial_sum_aux 1 u pow i + partial_sum_aux k u (pow / 2) (S i))%R.
Proof.
intros; simpl.
destruct (u i); [ | now rewrite Rplus_0_l ].
now rewrite Rplus_0_r.
Qed.

Theorem partial_sum_aux_succ : ∀ k u pow i,
  (partial_sum_aux (S k) u pow i =
   (if u i then pow else 0) + partial_sum_aux k u (pow / 2) (S i))%R.
Proof.
intros; simpl.
destruct (u i); [ easy | now rewrite Rplus_0_l ].
Qed.
*)

Example int_frac_of_R_bij : FinFun.Bijective int_frac_of_R.
Proof.
unfold FinFun.Bijective.
exists R_of_int_frac.
split.
 intros x.
 remember (int_frac_of_R x) as rif eqn:Hrif.
 unfold R_of_int_frac.
 destruct (R_of_bin_seq (Rfrac rif)) as (y, Hy); simpl.
 remember (Rset_of_bin_seq (Rfrac rif)) as s eqn:Hs.
 subst rif; simpl in Hs; simpl.
 assert (y = frac_part x); [ | unfold frac_part in H; lra ].
 unfold is_lub in Hy.
 destruct Hy as (Hyub, Hylub).
 unfold is_upper_bound in Hyub, Hylub.
 remember (frac_part x) as z eqn:Hz.
 unfold Rset_of_bin_seq in Hs.
 assert (Hyz : (y <= z)%R).
  apply Hylub.
  intros z₁ Hz₁.
  pose proof Hyub z₁ Hz₁ as Hzy.
  generalize Hz₁; intros Hz'₁.
  rewrite Hs in Hz'₁; simpl in Hz'₁.
  destruct Hz'₁ as (it, Hz'₁).
  subst z₁.

Theorem toto : ∀ z it, (0 <= z)%R → (partial_sum (bin_of_frac_part z) it <= z)%R.
Proof.
intros * Hz.
unfold partial_sum.
(*
remember (bin_of_frac_part z) as u eqn:Hu.
destruct it; [ easy | simpl; subst u ].
remember (bin_of_frac_part z 0) as b eqn:Hb; symmetry in Hb.
destruct b.
(* I need a property about bin_of_frac_part... *)
Print bin_of_frac_part.
*)

Theorem titi : ∀ z i k,
  (0 <= z)%R
  → (1 - (1 / 2) ^ k +
     partial_sum_aux k (bin_of_frac_part z) ((1 / 2) ^ S i) i <= z)%R.
Proof.
intros * Hz.
revert i.
induction k; intros; [ simpl; lra | simpl ].
remember (bin_of_frac_part z i) as b eqn:Hb; symmetry in Hb.
destruct b.

bbb.
Theorem titi : ∀ z i j k,
  (partial_sum_aux i (bin_of_frac_part z) (1 / 2) j +
   partial_sum_aux k (bin_of_frac_part z) ((1 / 2) ^ S (i + j)) (i + j) <= z)%R.
Proof.
intros.
revert j k.
induction i; intros.
 simpl.
 (* no : I miss a basis case, something saying :
      (blah bla blah for 0 <= z)%R
    and I don't have that *)

bbb.
(* end of titi; return to toto *)
pose proof titi z 0 it as H.
simpl in H.
now rewrite Rplus_0_l, Rmult_1_r in H.

bbb.

(*
replace it with (0 + it)%nat by easy.
rewrite partial_sum_aux_add.

Check partial_sum_aux_add.
*)

(*
Theorem titi : ∀ z i k pow,
  (0 <= z)%R
  → bin_of_frac_part z (k + i) = true
  → (partial_sum_aux k (bin_of_frac_part z) (pow ^ S i) i + pow ^ S i / 2 ^ k <= z)%R.
Proof.
intros * Hz.
revert k pow.
induction i; intros.
Admitted. Show.

(* end of titi; return to toto *)
destruct it; [ easy | simpl ].
destruct (Rlt_dec (frac_part z) (1 / 2)) as [H₁| H₁].
*)


Theorem titi : ∀ z k i,
  (0 <= z)%R
  → (partial_sum_aux k (bin_of_frac_part z) ((1 / 2) ^ S i) i <= z)%R.
Proof.
intros * Hz.
remember (1 / 2)%R as pow eqn:Hpow.
revert z i Hz.
induction k; intros; [ easy | ].
rewrite <- Nat.add_1_r.
rewrite partial_sum_aux_add.
remember (S i) as si; simpl; subst si.
rewrite Rplus_0_r.
remember (bin_of_frac_part z (k + i)) as b eqn:Hb; symmetry in Hb.
destruct b; [ | now rewrite Rplus_0_r; apply IHk ].
Print partial_sum.

bbb.

remember (bin_of_frac_part z i) as b eqn:Hb; symmetry in Hb.
destruct b.
 Focus 2.
 pose proof IHk z (S i) Hz as H.
 remember (S i) as si; simpl in H; subst si.
 subst pow.
 unfold Rdiv in H |-*.
 rewrite Rmult_1_l in H |-*; simpl in H.
 rewrite <- Rmult_assoc in H.
 now rewrite Rmult_shuffle0 in H.

 pose proof IHk z (S i) Hz as H.
 remember (S i) as si; simpl in H; subst si.
 subst pow.
 unfold Rdiv in H |-*.
 rewrite Rmult_1_l in H |-*; simpl in H.
 rewrite <- Rmult_assoc in H.
 rewrite Rmult_shuffle0 in H.

bbb.
Show.

(* fin de titi *)
pose proof titi z it 0 Hz as H.
now rewrite pow_1 in H.
Qed.

(* fin de toto *)
apply toto; rewrite Hz; apply frac_part_in_0_1.
bbb.

  rewrite Hs in Ht; simpl in Ht.
  destruct Ht as (it, Ht).
bbb.

 assert (Hyz : ∀ ε, (0 < ε)%R → ∃ η, (0 < η < ε ∧ z - η <= y)%R).
  intros * Hε.
  remember (trunc_bool_seq (bin_of_frac_part z)) as t eqn:Ht.
  assert (Hn : ∃ n, (0 < z - partial_sum (t n) n < ε)%R).
   assert (∀ n, (0 <= z - partial_sum (t n) n < (1 / 2) ^ n)%R).
    intros n.
    split.
     unfold partial_sum.
rewrite Ht.
rewrite <- trunc_bool_seq_eq.

Theorem toto : ∀ z n pow i,
  (0 <= z)%R
  → (0 <= pow <= (1 / 2) ^ S i)%R
  → (partial_sum_aux n (bin_of_frac_part z) pow i <= z)%R.
Proof.
intros * Hz Hpow.
revert pow i Hpow.
induction n; intros; simpl; [ easy | ].
remember (bin_of_frac_part z i) as b eqn:Hb; symmetry in Hb.
destruct b; [ | apply IHn; split; simpl in Hpow; simpl; lra ].
(*
erewrite trunc_bool_seq_eq; [ | reflexivity ].
simpl; unfold trunc_bool_seq; simpl.
*)
clear IHn.
revert z pow i Hz Hpow Hb.
induction n; intros; simpl.
 simpl; rewrite Rplus_0_r.
 eapply bin_of_frac_part_true_pow_le; eassumption.

 destruct (lt_dec (S i) (S (i + S n))) as [H₁| H₁].
  remember (bin_of_frac_part (z * 2) i) as b' eqn:Hb'; symmetry in Hb'.
  destruct b'.

   pose proof IHn (z - pow).
bbb.

bbb.
(* fin de toto *)
eapply Rplus_le_reg_l.
rewrite Rplus_minus, Rplus_0_r.
apply toto.
bbb.

     induction n.
      simpl; subst z.
      rewrite Rminus_0_r.
      apply frac_part_in_0_1.

      simpl.
      remember (t (S n) 0%nat) as b eqn:Hb.
      rewrite Ht in Hb; unfold trunc_bool_seq in Hb.
      destruct (lt_dec 0 (S n)) as [H₁| H₁].
       2: exfalso; apply H₁, Nat.lt_0_succ.

       simpl in Hb; clear H₁.
       destruct (Rlt_dec (frac_part z) (1 / 2)) as [H₁| H₁]; subst b.
        rewrite Ht in IHn; rewrite Ht.
        rewrite <- trunc_bool_seq_eq in IHn; [ | easy ].
        rewrite <- trunc_bool_seq_eq; [ | easy ].
SearchAbout partial_sum_aux.
bbb.
   Focus 2.
   destruct Hn as (n, Hn).
   exists (z - partial_sum (t n) n)%R.
   split; [ easy | ].
   replace (z - (z - partial_sum (t n) n))%R with (partial_sum (t n) n) by lra.
   apply Hyub; rewrite Hs; simpl.
   exists n.
   rewrite Ht; clear.
   unfold partial_sum.
   now apply trunc_bool_seq_eq.

bbb.

Theorem pouet : ∀ u n i,
  trunc_bool_seq u (S n) i = false
  → trunc_bool_seq u (S n) = trunc_bool_seq u n.
Admitted. Show.

  erewrite pouet; [ | eassumption ].
bbb.

 destruct (Rlt_dec (frac_part z) (1 / 2)) as [H₁| H₁].


bbb.

  assert (Hn : ∃ n η, (0 < η < ε ∧ z - η = (1 / 2) ^ n)%R).
   Focus 2.
   destruct Hn as (n & η & Hη & Hn).
   exists η.
   split; [ easy | ].
   rewrite Hn.
   apply Hyub.
   rewrite Hs; simpl.
bbb.
    split; [ | easy ].
    eapply Rlt_trans; [ | eassumption ].
    apply pow_lt; lra.

  assert (Hn : ∃ n η, (1 / 2 ^ n < η < ε)%R).
   Focus 2.
   destruct Hn as (n & η & Hn & Hη).
   exists η.
   split.
    assert (H : (1 / 2 ^ n = (1 / 2) ^ n)%R).
     clear Hn.
     induction n; simpl; [ lra | rewrite <- IHn ].
     unfold Rdiv; do 3 rewrite Rmult_1_l.
     apply Rinv_mult_distr; [ lra | apply pow_nonzero; lra ].

     rewrite H in Hn.
     split; [ | easy ].
     eapply Rlt_trans; [ | eassumption ].
     apply pow_lt; lra.

    apply Hyub.
    rewrite Hs; simpl.
bbb.

  apply Hyub; rewrite Hs; simpl.
  remember (bin_of_frac_part z) as u eqn:Hu.
   (* non : il faut que ça tombe juste, exactement *)
Print bin_of_frac_part.
bbb.

 assert (Hyz : (y <= z)%R).
  apply Hyb.
  intros t Ht.
  rewrite Hs in Ht; simpl in Ht.
  destruct Ht as (it, Ht); subst t.

bbb.

Theorem glop : ∀ z it,
  (0 <= z < 1)%R
  → (partial_sum (bin_of_frac_part z) it <= z)%R.
Proof.
intros * Hz.
unfold partial_sum.
(*
revert z Hz.
induction it; intros; [ easy | simpl ].
destruct (Rlt_dec (frac_part (z * 2)) (1/2)) as [H₁| H₁].
bbb.
*)

Theorem glip : ∀ z it pow i,
  (0 <= z < 1/2^i)%R
  → (pow <= 1/2^(S i))%R
  → (partial_sum_aux it (bin_of_frac_part z) pow i <= z)%R.
Proof.
intros * Hz Hpow.
revert z i pow Hz Hpow.
induction it; intros; [ easy | simpl ].
remember (bin_of_frac_part z i) as b eqn:Hb; symmetry in Hb.
destruct b as [H₁| H₁].
 destruct i.
  rewrite pow_O, Rdiv_1_r in Hz; rewrite pow_1 in Hpow; simpl in Hb.
  unfold frac_part in Hb.
  rewrite Int_part_is_0 in Hb; [ | lra ].
  rewrite Rminus_0_r in Hb.
  destruct (Rlt_dec z (1 / 2)) as [H₁| H₁]; [ easy | clear Hb ].
  apply Rnot_lt_le in H₁.
  assert (Hz' : (0 <= z - 1 / 2 < 1 / 1)%R) by lra.
  assert (Hpow' : (pow <= 1 / 2 ^ 1)%R) by now rewrite pow_1.
  pose proof IHit (z - 1 / 2)%R O pow Hz' Hpow'.
  destruct it; [ simpl; lra | ].
  simpl in H; simpl.
  unfold frac_part in H.
  rewrite Int_part_is_0 in H; [ | lra ].
  rewrite Rminus_0_r in H.
  unfold frac_part.
  rewrite Rdiv_1_r in Hz'.
  rewrite Int_part_is_0.
bbb.
; [ | lra ].
  rewrite Rminus_0_r in H.
  unfold frac_part.

bbb.
intros * Hz Hpow.
revert z pow it Hz Hpow.
induction i; intros.
 rewrite pow_O in Hz; rewrite pow_1 in Hpow.
 rewrite Rdiv_1_r in Hz.
 revert z Hz.
 induction it; intros; [ easy | simpl ].
(**)
 unfold frac_part.
 rewrite Int_part_is_0; [ | lra ].
 rewrite Rminus_0_r.
 destruct (Rlt_dec z (1 / 2)) as [H₁| H₁].
 destruct it; simpl; [ easy | ].
(**)
 unfold frac_part.
 rewrite Int_part_is_0; [ | lra ].
 rewrite Rminus_0_r.
 destruct (Rlt_dec (z * 2) (1 / 2)) as [H₂| H₂].
 destruct it; simpl; [ easy | ].
(**)
 unfold frac_part.
 rewrite Int_part_is_0; [ | lra ].
 rewrite Rminus_0_r.
 destruct (Rlt_dec (z * 2 * 2) (1 / 2)) as [H₃| H₃].
 destruct it; simpl; [ easy | ].
(**)
 unfold frac_part.
 rewrite Int_part_is_0; [ | lra ].
 rewrite Rminus_0_r.
 destruct (Rlt_dec (z * 2 * 2 * 2) (1 / 2)) as [H₄| H₄].
 destruct it; simpl; [ easy | ].
(**)
 unfold frac_part.
 rewrite Int_part_is_0; [ | lra ].
 rewrite Rminus_0_r.

bbb.


2: split; [ easy | ].

bbb.

intros * Hz Hpow.
revert z pow i Hz Hpow.
induction it; intros; [ easy | simpl ].
remember (bin_of_frac_part z i) as b eqn:Hb; symmetry in Hb.
destruct b.
 simpl in Hb.
 pose proof IHit (z - pow)%R pow.
bbb.

 Focus 2.
 apply IHit; [ easy | ].
 apply Rmult_le_reg_r with (r := 2%R); [ lra | ].
 replace (pow / 2 * 2)%R with pow by lra.
 eapply Rle_trans; [ eassumption | ].
 remember (S i) as si.
 rewrite Rmult_comm; simpl.
 apply Rmult_le_reg_r with (r := (2 ^ si)%R); [ apply pow_lt; lra | ].
 remember (2 ^ si)%R as x.
 assert (x ≠ 0)%R.
  intros H; rewrite H in Heqx; symmetry in Heqx; revert Heqx.
  apply pow_nonzero; lra.

  unfold Rdiv.
  do 2 rewrite Rmult_1_l.
  rewrite Rinv_l; [ | easy ].
  rewrite Rinv_mult_distr; [ | lra | easy ].
  do 2 rewrite Rmult_assoc.
  rewrite Rinv_l; [ lra | easy ].

 simpl.
 clear -Hz Hpow Hb.
 revert z pow i Hz Hpow Hb.
 induction it; intros.
  simpl; rewrite Rplus_0_r.
  revert z pow Hz Hpow Hb.
  induction i; intros.
   simpl in Hb.
   destruct (Rlt_dec (frac_part z) (1/2)) as [H₁| H₁]; [ easy | ].
   apply Rnot_lt_le in H₁.
   unfold frac_part in H₁.
   rewrite Int_part_is_0 in H₁; [ | easy ].
   simpl in H₁; rewrite Rminus_0_r in H₁.
   simpl in Hpow; rewrite Rmult_1_r in Hpow.
   now apply Rle_trans with (r2 := (1/2)%R).

   simpl in Hb.
bbb.
   pose proof IHi (z * 2)%R.
bbb.

 remember (Z.to_nat z) as n eqn:Hn.
SearchAbout Z.of_nat.
 Check IZN.

 apply Rlt_le_incl.

destruct (Z_lt_ge_dec z 0) as [H₁| H₁].
 apply Z.


induction z as [| p| p]; [ now apply Rle_not_lt in Hx1 | | ].
bbb.

 simpl in Hgt, Hle.
 induction p; simpl; [ exfalso | exfalso | easy ].
  simpl in Hgt, Hle.
  pose proof le_Pmult_nat p 2.
  destruct (Pos.iter_op Init.Nat.add p 2).
   apply Nat.nlt_ge in H; apply H, Nat.lt_0_succ.

   simpl in Hgt, Hle.
   destruct n.
    apply Nat.nlt_ge in H; apply H, Nat.lt_succ_diag_r.

    apply Rle_trans with (r1 := 1 + 1 - x) in Hle.
     unfold "_-_", sub_notation in Hle.
     unfold "_+_", add_notation in Hle.
     apply Rlt_not_le in Hx2; apply Hx2.
     unfold one, one_notation in Hle; lra.

     assert (0 <= INR (S n))%R; [ apply pos_INR | lra ].

  remember (INR (Pos.to_nat p~0)) as y.
bbb.

SearchAbout (INR (Pos.to_nat _)).
  assert ((1 <= INR (Pos.to_nat p~0))%R).
Focus 2.
clear Heqy.


bbb.
  pose proof pos_INR_nat_of_P p~0 as H.
SearchAbout INR.
bbb.

(* return to glop *)
Check glip.
apply glip; simpl; lra.
Qed.
bbb.

Theorem glup : ∀ x, (0 <= x < 1)%R → frac_part x = x.
Proof.
intros * Hx.
unfold frac_part.
bbb.

SearchAbout frac_part.
bbb.
Rfracp_in_0_1: ∀ x : ℝ, (0 <= frac_part x < 1)%R
   unfold frac_part in H₁.



   unfold "_-_", sub_notation in H₁.
bbb.

Theorem Int_part_

bbb.
   unfold frac_part, Int_part in H₁.
   unfold "_-_", sub_notation in H₁.
   pose proof archimed z.
   rewrite minus_IZR in H₁; simpl in H₁.

SearchAbout up.
bbb.

revert z pow Hz Hb.
induction i; intros; simpl in Hb.
 destruct (Rlt_dec (frac_part (z * 2)) (1/2)) as [H₁| H₁]; [ easy | clear Hb ].
 apply Rnot_lt_le in H₁.
Focus 2.
 assert (Hz2 : (0 <= z * 2)%R) by lra.
 pose proof IHi (z * 2)%R Hz2 Hb.
 destruct it.
  simpl in H.
  simpl.


bbb.

clear IHit.
 revert z pow i Hz Hpow Hb.
 induction it; intros.
  simpl.
Focus 2.
simpl.
remember (bin_of_frac_part (z * 2) i) as b' eqn:Hb'; symmetry in Hb'.
destruct b'.
 assert (pow / 2 <= 1/2)%R by lra.
 pose proof IHit z (pow/2)%R (S i) Hz H Hb'.
 (* shit, ça marche pas *)

bbb.

 eapply Rle_trans.
  2: apply IHit with (pow := pow).

  apply Rplus_le_compat_l.

bbb.

(* glip works for glop *)
apply glip; [ easy | lra ].

bbb.

(* glop works *)
apply glop.
pose proof archimed x as H; lra.
bbb.

(**)
Print bin_of_frac_part.
assert (0 <= z < 1)%R
clear Hz Hs.

revert z.
induction it; intros.
simpl.

bbb.
  induction it; simpl; [ rewrite Hz; pose proof (archimed x); lra | ].
  destruct (Z.eq_dec (Int_part (z * 2) mod 2) 0) as [H₁| H₁].
bbb.

Theorem glop : ∀ u it pow i,
  (0 < pow)%R
  → u i = false
  → (partial_sum_aux it u (pow / 2) (S i) <=
     partial_sum_aux (S it) u pow i)%R.
Proof.
intros * Hpow Hui.
revert pow i Hui Hpow.
destruct it; intros; simpl; [ rewrite Hui; apply Rle_refl | ].
remember (u (S i)) as usi eqn:Husi; symmetry in Husi.
rewrite Hui; apply Rle_refl.
Qed.

eapply Rle_trans.
 apply glop; [ lra | now simpl; rewrite H₁ ].

 simpl; rewrite H₁; simpl.
 eapply Rle_trans; [ | apply IHit ].
 (* no: I have an extra iteration...
    but... pow is smaller... it may work... I have to try another
    lemma for this *)

Theorem toto : ∀ u it pow i,
  (0 < pow)%R
  → (partial_sum_aux it u (pow / 2) (S i) <=
     pow / 2 ^ it + partial_sum_aux it u pow i)%R.
Proof.
intros * Hpow.
Admitted. Show.

(* return to theorem *)


eapply Rle_trans; [ apply toto; lra | ].


eapply Rle_trans; [ apply Rplus_le_compat_l, IHit | ].

; [ eapply IHit | ].



intros * Hpow Hit.
revert pow i Hpow.
induction it; intros; [ now apply Nat.nlt_0_r in Hit | ].
simpl; clear Hit.
remember (u (S i)) as usi eqn:Husi; symmetry in Husi.
remember (u i) as ui eqn:Hui; symmetry in Hui.
destruct usi.
 destruct ui.
  rewrite <- Rplus_assoc.
  apply Rplus_le_compat; [ lra | ].

  destruct it; [ apply Rle_refl | ].
  eapply Rle_trans; [ | apply IHit ]; try lra.
  apply Nat.lt_0_succ.

 destruct it.
  simpl.

bbb.

Theorem glop : ∀ z it pow i,
  (0 <= z < 1)%R
  → (0 < pow <= 1/2^(S i))%R
  → (partial_sum_aux it (bin_of_frac_part z) pow i <= z)%R.
Proof.
intros * Hz Hpow.
revert z pow i Hz Hpow.
induction it; intros; [ easy | simpl ].
remember (bin_of_frac_part z i) as b eqn:Hb.
symmetry in Hb.
destruct b.
 destruct it.
  simpl.
  destruct i.
   simpl in Hb.
   destruct (Z.eq_dec (Int_part (z * 2) mod 2) 0) as [H₁| H₁]; [ easy | ].
   clear Hb.
   assert (H2 : (2 > 0)%Z) by (apply Z.gt_lt_iff, Z.lt_0_2).
   pose proof Zdiv.Z_mod_lt (Int_part (z * 2)) 2 H2 as H.
   clear H2.
   remember (Int_part (z * 2) mod 2)%Z as n eqn:Hn.
   destruct H as (Hn₁, Hn₂).
   destruct (Z.eq_dec n 0) as [H₂| H₂]; [ easy | ].
   destruct (Z.eq_dec n 1) as [H₃| H₃].
    subst n.
    clear H₂ Hn₂ Hn₁ H₁.
    unfold Int_part in H₃.
    unfold "_-_", sub_notation in H₃.

bbb.

Theorem toto : ∀ z, bin_of_frac_part z 0 = false → (z <= 1/2)%R.
Admitted. Show.

Theorem titi : ∀ z, bin_of_frac_part z 0 = true → (1/2 <= z)%R.
Admitted. Show.

induction i.
 destruct b.
(*
 apply titi in Hb.
*)
 simpl in Hb.
 destruct (Z.eq_dec (Int_part (z * 2) mod 2) 0) as [H₁| H₁]; [ easy | ].
 clear Hb; unfold Int_part in H₁.
 unfold "_-_", sub_notation in H₁.
 assert (H : up (z * 2) = 1).
  destruct (Z.eq_dec (up (z * 2)) 1) as [H₂| H₂]; [ easy | ].
  exfalso; apply H₁; clear H₁.

 exfalso; apply H₁; clear H₁.


 pose proof archimed (2 * z) as H.
 destruct H as (Hz₁, Hz₂).


bbb.

 assert (up (z * 2) = 1)

 pose proof archimed z as H.
 destruct H as (H

bbb.

 

Print partial_sum_aux.

 simpl.


bbb.

(* return to int_frac_of_R_bij *)
apply glop; [ | lra ].
pose proof archimed x as H; lra.

bbb.

apply glop; lra.

bbb.

  induction it.
   rewrite Hz; simpl.
   pose proof archimed x as H; lra.

   simpl.
bbb.

Example int_frac_of_R_bij :
  FinFun.Injective int_frac_of_R ∧
  FinFun.Surjective int_frac_of_R.
Proof.
split.
 intros x y Hxy.
 unfold int_frac_of_R in Hxy.
 injection Hxy; clear Hxy; intros Hf Hi.
Check archimed.
Print FinFun.Bijective.
bbb.

Example R_is_uncountable : is_uncountable_infinite R.
Proof.
intros f.
bbb.

Theorem equidec_sphere_with_and_without_fixpoints : ∀ (s := set_equiv),
  equidecomposable _ sphere sphere_but_fixpoints.
Proof.
intros.
assert (∃ p₁, p₁ ∈ sphere ∖ D).
unfold "∈", "∖".
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
