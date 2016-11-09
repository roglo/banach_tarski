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

Compute (nat_of_path []).
Compute (nat_of_path [ạ]).
Compute (nat_of_path [ạ⁻¹]).
Compute (nat_of_path [ḅ]).
Compute (nat_of_path [ḅ⁻¹]).

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

Theorem paths_are_countable : ∃ (f : list free_elem → nat),
  (∀ el₁ el₂, el₁ ≠ el₂ → f el₁ ≠ f el₂).
Proof.
exists nat_of_path.
intros el₁ el₂ H Hnp; apply H.
now apply nat_of_path_injective.
Qed.

Definition is_uncountable_infinite A := ∀ f : nat → A, ∃ x, ∀ n, f n ≠ x.

Record int_frac := mkraif { Rint : ℤ; Rfrac : ℕ → bool }.

Definition Rfloor x := up x - 1.
Definition Rfracp x := x - IZR (Rfloor x).

Theorem Rflacp_in_0_1 : ∀ x, (0 <= Rfracp x)%R ∧ (Rfracp x < 1)%R.
Proof.
intros x.
pose proof archimed x as Ha.
destruct Ha as (Hgt, Hle).
unfold Rfracp, Rfloor.
unfold "_-_", sub_notation.
split.
 rewrite minus_IZR; simpl.
 apply Rplus_le_compat_l with (r := - (IZR (up x) - x)) in Hle.
 rewrite Rplus_opp_l in Hle.
 unfold "_-_", "-_", sub_notation, opp_notation in Hle; lra.

 rewrite minus_IZR; simpl; lra.
Qed.

Fixpoint Rfrac_to_bin x n :=
  match n with
  | 0 => if Z.eq_dec (Rfloor (x * 2)%R) 0 then false else true
  | S n' => Rfrac_to_bin (x * 2)%R n'
  end.

Definition int_frac_of_R x :=
  mkraif (Rfloor x) (Rfrac_to_bin (Rfracp x)).

Fixpoint bin_to_Rfrac_aux it (u : ℕ → bool) pow i :=
  match it with
  | 0 => 0%R
  | S it' =>
      if u i then (pow + bin_to_Rfrac_aux it' u (pow / 2) (S i))%R
      else bin_to_Rfrac_aux it' u (pow / 2)%R (S i)
  end.

Definition bin_to_Rfrac u it := bin_to_Rfrac_aux it u (1/2)%R 0.

Theorem bin_to_Rfrac_aux_le_2_pow : ∀ u it pow i,
  (0 < pow)%R
  → (bin_to_Rfrac_aux it u pow i <= 2 * pow)%R.
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

Theorem bin_to_Rfrac_le_1 : ∀ u it, (bin_to_Rfrac u it <= 1)%R.
Proof.
intros.
assert (Hlt : (0 < 1 / 2)%R) by lra.
pose proof bin_to_Rfrac_aux_le_2_pow u it (1/2) 0 Hlt.
now replace (2 * (1/2))%R with 1%R in H by lra.
Qed.

Definition Rset_of_bin_seq u := mkset (λ x, ∃ it, bin_to_Rfrac u it = x).

Theorem Rset_of_bin_seq_bound : ∀ u, bound (setp (Rset_of_bin_seq u)).
Proof.
intros.
unfold bound.
exists 1.
unfold is_upper_bound.
intros x HE; unfold Rset_of_bin_seq in HE.
destruct HE as (it, HE); subst x.
apply bin_to_Rfrac_le_1.
Qed.

Theorem Rset_of_bin_seq_non_empty : ∀ u, ∃ x, x ∈ Rset_of_bin_seq u.
Proof.
intros.
unfold Rset_of_bin_seq; simpl.
now exists (bin_to_Rfrac u 0), 0%nat.
Qed.

Definition R_of_bin_seq u :=
  completeness (setp (Rset_of_bin_seq u)) (Rset_of_bin_seq_bound u)
    (Rset_of_bin_seq_non_empty u).

Definition R_of_int_frac rif :=
  (IZR (Rint rif) + proj1_sig (R_of_bin_seq (Rfrac rif)))%R.

Example int_frac_of_R_bij : FinFun.Bijective int_frac_of_R.
Proof.
unfold FinFun.Bijective.
exists R_of_int_frac.
split.
 intros x.
 remember (int_frac_of_R x) as rif eqn:Hrif.
 unfold R_of_int_frac.
 remember (R_of_bin_seq (Rfrac rif)) as c eqn:Hc.
 symmetry in Hc.
 destruct c as (y, Hy); simpl.
 unfold R_of_bin_seq in Hc.
 unfold is_lub in Hy.
 destruct Hy as (Hyub, Hyb).
(**)
 set (s := Rset_of_bin_seq (Rfrac rif)) in *.
 unfold is_upper_bound in Hyub, Hyb.
 subst rif; simpl.
(*
 clear Hc.
 remember (Rset_of_bin_seq (Rfrac rif)) as s eqn:Hs.
 unfold is_upper_bound in Hyub, Hyb.
 subst rif; simpl in Hs; simpl.
*)
 assert ((x - IZR (Rfloor x) = y)%R); [ | lra ].
 unfold Rfloor.
 unfold "_-_", sub_notation.
 rewrite minus_IZR; simpl.
 replace _ with (x + 1 - IZR (up x))%R by lra.
 (* ça va pas, ça: il faudrait que y soit le m du Hc *)
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
