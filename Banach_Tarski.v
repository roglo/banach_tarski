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
      if u i then (pow + partial_sum_aux k' u (pow / 2) (S i))%R
      else partial_sum_aux k' u (pow / 2)%R (S i)
  end.

Definition partial_sum u k := partial_sum_aux k u (1/2)%R 0.

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

Theorem partial_sum_le_1 : ∀ u k, (partial_sum u k <= 1)%R.
Proof.
intros.
assert (Hlt : (0 < 1 / 2)%R) by lra.
pose proof partial_sum_aux_le_2_pow u k (1/2) 0 Hlt.
now replace (2 * (1/2))%R with 1%R in H by lra.
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

Definition unit_interv := mkset (λ x, (0 <= x < 1)%R).

(* 0x → 10; 1x → 00 *)
Definition cantor_canon_diagonal (g : ℕ → ℕ → bool) i :=
  if zerop (i mod 2) then negb (g (i / 2) i) else false.

Definition Canonical_seq := mkset (λ u, ∀ i, ∃ j, i ≤ j ∧ u j = false).

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

Theorem converted_real_is_canonical : ∀ r, bin_of_frac_part r ∈ Canonical_seq.
Proof.
intros r i.
enough (H : ¬ (∀ j, i ≤ j → bin_of_frac_part r j = true)).
 apply classic.
 intros Hj; apply H; clear H; intros j Hij.
 apply classic.
 intros H; apply Hj; clear Hj.
 exists j; split; [ easy | ].
 now apply not_true_iff_false in H.

 intros Hj.
 assert
   (Hk : ∃ k,
    (k = O ∧ ∀ j, bin_of_frac_part r j = true) ∨
    (bin_of_frac_part r k = false ∧
     ∀ j, k < j → bin_of_frac_part r j = true)).
  induction i.
   exists O.
   left; split; [ easy | ].
   intros j.
   apply Hj, Nat.le_0_l.

   destruct (Bool.bool_dec (bin_of_frac_part r i) false) as [Hi'| Hi'].
    exists i; now right; split.

    apply IHi.
    intros j Hij.
    destruct (lt_dec i j) as [H| H]; [ now apply Hj | ].
    apply Nat.nlt_ge in H.
    apply Nat.le_antisymm in H; [ | easy ].
    now apply not_false_iff_true in Hi'; subst j.

  clear Hj.
  destruct Hk as (k & Hk).
  destruct Hk as [(H, Hk) | (H, Hk)].
   subst k.
   enough (r = 1)%R.
    subst r.
    unfold bin_of_frac_part in Hk.
    specialize (Hk O).
    rewrite Rmult_1_l, pow_O in Hk.
    destruct (Rlt_dec (frac_part 1) (1 / 2)) as [H| H]; [ easy | ].
    apply H.
    unfold frac_part.
    replace 1%R with (INR 1) by easy.
    rewrite Int_part_INR; simpl; lra.

    set (E x := ∃ k, partial_sum (bin_of_frac_part r) k = x).
    assert (Hb : bound E).
     unfold bound, E; exists 1.
     unfold is_upper_bound.
     intros x (k, Hx); subst x.
     apply partial_sum_le_1.

     assert (He : ∃ x, E x) by (now exists 0%R, 0%nat).
     set (m := completeness E Hb He).
     destruct m as (x & Hxu & Hxlu).
     unfold E, is_upper_bound in Hxu, Hxlu.
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
