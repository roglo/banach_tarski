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

Definition is_countable U A := ∃ f : ℕ → U, ∀ a, a ∈ A → ∃ n, f n = a.

(*
Theorem paths_are_countable :
  is_countable (list free_elem) (mkset (λ _, True)).
Proof.
unfold is_countable.
Check nat_of_path.
*)

Theorem paths_are_countable : ∃ (f : list free_elem → nat),
  (∀ el₁ el₂, el₁ ≠ el₂ → f el₁ ≠ f el₂).
Proof.
exists nat_of_path.
intros el₁ el₂ H Hnp; apply H.
now apply nat_of_path_injective.
Qed.

Theorem classic : ∀ (P : Prop), ¬¬P → P.
Proof.
intros * HnP.
now destruct (EM P).
Qed.

Add Parametric Morphism {U} : (@is_countable U)
 with signature (@set_eq _ set_equiv) ==> iff
 as is_countable_morph.
Proof.
intros E F HEF.
split; intros H; destruct H as (f, H); exists f; intros x Hx; now apply H, HEF.
Qed.

Theorem uncountable_sub_countable_not_empty : ∀ {U} (A B : set U),
  not (is_countable _ A)
  → is_countable _ B
  → B ⊂ A
  → ∃ x, x ∈ A ∖ B.
Proof.
intros * HA HB HBA.
apply classic.
intros HnE.
assert (HnA : ∀ x, x ∉ A ∖ B) by (now intros x Hx; apply HnE; exists x).
clear HnE.
set (s := @set_equiv U).
assert (HAB : (A = B)%S); [ | now rewrite HAB in HA ].
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

Fixpoint R_to_bin x n :=
  match n with
  | 0 => if Rlt_dec (frac_part x) (1/2) then false else true
  | S n' => R_to_bin (x * 2)%R n'
  end.

Definition int_frac_of_R x :=
  mkraif (Int_part x) (R_to_bin (frac_part x)).

Fixpoint bin_to_R_aux it (u : ℕ → bool) pow i :=
  match it with
  | 0 => 0%R
  | S it' =>
      if u i then (pow + bin_to_R_aux it' u (pow / 2) (S i))%R
      else bin_to_R_aux it' u (pow / 2)%R (S i)
  end.

Definition bin_to_R u it := bin_to_R_aux it u (1/2)%R 0.

Theorem bin_to_R_aux_le_2_pow : ∀ u it pow i,
  (0 < pow)%R
  → (bin_to_R_aux it u pow i <= 2 * pow)%R.
Proof.
intros * Hpow.
revert pow i Hpow.
induction it; intros; simpl; [ lra | ].
remember (u i) as b eqn:Hb; symmetry in Hb.
destruct b.
 replace (2 * pow)%R with (pow + pow)%R by lra.
 apply Rplus_le_compat; [ lra | ].
 replace pow with (2 * (pow / 2))%R at 2 by lra.
 apply IHit; lra.

 apply Rle_trans with (r2 := pow); [ | lra ].
 replace pow with (2 * (pow / 2))%R at 2 by lra.
 apply IHit; lra.
Qed.

Theorem bin_to_R_le_1 : ∀ u it, (bin_to_R u it <= 1)%R.
Proof.
intros.
assert (Hlt : (0 < 1 / 2)%R) by lra.
pose proof bin_to_R_aux_le_2_pow u it (1/2) 0 Hlt.
now replace (2 * (1/2))%R with 1%R in H by lra.
Qed.

Definition Rset_of_bin_seq u := mkset (λ x, ∃ it, bin_to_R u it = x).

Theorem Rset_of_bin_seq_bound : ∀ u, bound (setp (Rset_of_bin_seq u)).
Proof.
intros.
unfold bound.
exists 1.
unfold is_upper_bound.
intros x HE; unfold Rset_of_bin_seq in HE.
destruct HE as (it, HE); subst x.
apply bin_to_R_le_1.
Qed.

Theorem Rset_of_bin_seq_non_empty : ∀ u, ∃ x, x ∈ Rset_of_bin_seq u.
Proof.
intros.
unfold Rset_of_bin_seq; simpl.
now exists (bin_to_R u 0), 0%nat.
Qed.

Definition R_of_bin_seq u :=
  completeness (setp (Rset_of_bin_seq u)) (Rset_of_bin_seq_bound u)
    (Rset_of_bin_seq_non_empty u).

Definition R_of_int_frac rif :=
  (IZR (Rint rif) + proj1_sig (R_of_bin_seq (Rfrac rif)))%R.

Definition trunc_bool_seq u n i := if lt_dec i n then u i else false.

Theorem trunc_bool_seq_eq : ∀ z pow i m n,
  i + n <= m
  → bin_to_R_aux n (R_to_bin z) pow i =
    bin_to_R_aux n (trunc_bool_seq (R_to_bin z) m) pow i.
Proof.
intros * Hm.
revert pow i m Hm.
induction n; intros; [ easy | simpl ].
remember (R_to_bin z i) as b eqn:Hb; symmetry in Hb.
remember (trunc_bool_seq (R_to_bin z) m i) as b' eqn:Hb'.
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

Theorem R_to_bin_true_pow_le : ∀ z pow i,
  (0 <= z)%R
  → (0 <= pow <= (1 / 2) ^ S i)%R
  → R_to_bin z i = true
  → (pow <= z)%R.
Proof.
intros * Hz Hpow Hi.
revert z pow Hz Hi Hpow.
induction i; intros.
 simpl in Hi.
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
 apply IHi; [ | easy | ].
  apply (Rmult_le_compat_r 2) in Hz; [ | lra ].
  now rewrite Rmult_0_l in Hz.

  split.
   destruct Hpow as (H, _).
   apply (Rmult_le_compat_r 2) in H; [ | lra ].
   now rewrite Rmult_0_l in H.

   destruct Hpow as (_, H).
   apply (Rmult_le_compat_r 2) in H; [ | lra ].
   simpl in H; simpl; lra.
Qed.

Theorem bin_to_R_aux_succ : ∀ k u pow i,
  (bin_to_R_aux (S k) u pow i =
   (if u i then pow else 0) + bin_to_R_aux k u (pow / 2) (S i))%R.
Proof.
intros; simpl.
destruct (u i); [ easy | now rewrite Rplus_0_l ].
Qed.

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

Theorem toto : ∀ z it, (0 <= z)%R → (bin_to_R (R_to_bin z) it <= z)%R.
Proof.
intros * Hz.
unfold bin_to_R.

Theorem titi : ∀ z k i,
  (0 <= z)%R
  → (bin_to_R_aux k (R_to_bin z) ((1 / 2) ^ S i) i <= z)%R.
Proof.
intros * Hz.
remember (1 / 2)%R as pow eqn:Hpow.
revert z i Hz.
induction k; intros; [ easy | ].
rewrite bin_to_R_aux_succ.
bbb.

remember (R_to_bin z i) as b eqn:Hb; symmetry in Hb.
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

(* fin de tutu *)


(* fin de titi *)
pose proof titi z it 0 Hz as H.
now rewrite pow_1 in H.
Qed.

(* fin de toto *)
rewrite <- Hz'₁.
apply toto; rewrite Hz; apply frac_part_in_0_1.
bbb.

  rewrite Hs in Ht; simpl in Ht.
  destruct Ht as (it, Ht).
bbb.

 assert (Hyz : ∀ ε, (0 < ε)%R → ∃ η, (0 < η < ε ∧ z - η <= y)%R).
  intros * Hε.
  remember (trunc_bool_seq (R_to_bin z)) as t eqn:Ht.
  assert (Hn : ∃ n, (0 < z - bin_to_R (t n) n < ε)%R).
   assert (∀ n, (0 <= z - bin_to_R (t n) n < (1 / 2) ^ n)%R).
    intros n.
    split.
     unfold bin_to_R.
rewrite Ht.
rewrite <- trunc_bool_seq_eq.

Theorem toto : ∀ z n pow i,
  (0 <= z)%R
  → (0 <= pow <= (1 / 2) ^ S i)%R
  → (bin_to_R_aux n (R_to_bin z) pow i <= z)%R.
Proof.
intros * Hz Hpow.
revert pow i Hpow.
induction n; intros; simpl; [ easy | ].
remember (R_to_bin z i) as b eqn:Hb; symmetry in Hb.
destruct b; [ | apply IHn; split; simpl in Hpow; simpl; lra ].
(*
erewrite trunc_bool_seq_eq; [ | reflexivity ].
simpl; unfold trunc_bool_seq; simpl.
*)
clear IHn.
revert z pow i Hz Hpow Hb.
induction n; intros; simpl.
 simpl; rewrite Rplus_0_r.
 eapply R_to_bin_true_pow_le; eassumption.

 destruct (lt_dec (S i) (S (i + S n))) as [H₁| H₁].
  remember (R_to_bin (z * 2) i) as b' eqn:Hb'; symmetry in Hb'.
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
SearchAbout bin_to_R_aux.
bbb.
   Focus 2.
   destruct Hn as (n, Hn).
   exists (z - bin_to_R (t n) n)%R.
   split; [ easy | ].
   replace (z - (z - bin_to_R (t n) n))%R with (bin_to_R (t n) n) by lra.
   apply Hyub; rewrite Hs; simpl.
   exists n.
   rewrite Ht; clear.
   unfold bin_to_R.
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
  remember (R_to_bin z) as u eqn:Hu.
   (* non : il faut que ça tombe juste, exactement *)
Print R_to_bin.
bbb.

 assert (Hyz : (y <= z)%R).
  apply Hyb.
  intros t Ht.
  rewrite Hs in Ht; simpl in Ht.
  destruct Ht as (it, Ht); subst t.

bbb.

Theorem glop : ∀ z it,
  (0 <= z < 1)%R
  → (bin_to_R (R_to_bin z) it <= z)%R.
Proof.
intros * Hz.
unfold bin_to_R.
(*
revert z Hz.
induction it; intros; [ easy | simpl ].
destruct (Rlt_dec (frac_part (z * 2)) (1/2)) as [H₁| H₁].
bbb.
*)

Theorem glip : ∀ z it pow i,
  (0 <= z < 1/2^i)%R
  → (pow <= 1/2^(S i))%R
  → (bin_to_R_aux it (R_to_bin z) pow i <= z)%R.
Proof.
intros * Hz Hpow.
revert z i pow Hz Hpow.
induction it; intros; [ easy | simpl ].
remember (R_to_bin z i) as b eqn:Hb; symmetry in Hb.
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
remember (R_to_bin z i) as b eqn:Hb; symmetry in Hb.
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
remember (R_to_bin (z * 2) i) as b' eqn:Hb'; symmetry in Hb'.
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
Print R_to_bin.
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
  → (bin_to_R_aux it u (pow / 2) (S i) <=
     bin_to_R_aux (S it) u pow i)%R.
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
  → (bin_to_R_aux it u (pow / 2) (S i) <=
     pow / 2 ^ it + bin_to_R_aux it u pow i)%R.
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
  → (bin_to_R_aux it (R_to_bin z) pow i <= z)%R.
Proof.
intros * Hz Hpow.
revert z pow i Hz Hpow.
induction it; intros; [ easy | simpl ].
remember (R_to_bin z i) as b eqn:Hb.
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

Theorem toto : ∀ z, R_to_bin z 0 = false → (z <= 1/2)%R.
Admitted. Show.

Theorem titi : ∀ z, R_to_bin z 0 = true → (1/2 <= z)%R.
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

 

Print bin_to_R_aux.

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
