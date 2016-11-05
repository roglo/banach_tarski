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
   apply Rplus_le_reg_pos_r in H₁; [ | apply Rle_0_sqr ].
   apply Rplus_le_reg_pos_r in H₁; [ | apply Rle_0_sqr ].
   apply Rplus_le_reg_pos_r in H₂; [ | apply Rle_0_sqr ].
   apply Rplus_le_reg_pos_r in H₂; [ | apply Rle_0_sqr ].
   clear - H₁ H₂.
   rewrite <- Rsqr_1 in H₁ at 4.
   rewrite <- Rsqr_1 in H₂ at 6.
   apply Rsqr_le_abs_0 in H₁.
   apply Rsqr_le_abs_0 in H₂.
   rewrite Rabs_R1 in H₁, H₂.
   unfold Rabs in H₁, H₂.
   destruct (Rcase_abs (x - 3)), (Rcase_abs (x - 6)); lra.

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
intros p; split; [ intros (H3, H6) | easy ].
unfold sphere_but_fixpoints in H3, H6.
simpl in H3, H6.
bbb.

Theorem separated_spheres : ∀ (s := set_equiv),
  (xtransl 3 sphere ∩ xtransl 6 sphere = ∅)%S.
Proof.
intros p; split; [ intros (H3, H6) | easy ].
bbb.

Theorem equidec_sphere_with_and_without_fixpoints :
  equidecomposable set_equiv sphere sphere_but_fixpoints.
Proof.
bbb.

Theorem Banach_Tarski_paradox : ∀ (s := set_equiv),
  equidecomposable _ sphere (xtransl 3 sphere ∪ xtransl 6 sphere)%S.
Proof.
etransitivity; [ | etransitivity ].
 2: apply Banach_Tarski_paradox_but_fixpoints.

 apply equidec_sphere_with_and_without_fixpoints.

 apply equidec_union.
  apply separated_spheres_without_fixpoints.

  apply separated_spheres.

  apply equidec_transl; symmetry.
  apply equidec_sphere_with_and_without_fixpoints.

  apply equidec_transl; symmetry.
  apply equidec_sphere_with_and_without_fixpoints.
Qed.

Check Banach_Tarski_paradox.
