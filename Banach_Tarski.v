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
Require Import Partition OrbitRepr Transformation Equidecomp.

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
 eapply r_decomposed_4; try eassumption; reflexivity.

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
   split; [ intros (H₁, H₂) | contradiction ].
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

  constructor; [ exists (Xtransl 3); reflexivity | ].
  constructor; [ exists (Comb (Xtransl 3) (Rot ạ)); reflexivity | ].
  constructor; [ exists (Xtransl 6); reflexivity | ].
  constructor; [ exists (Comb (Xtransl 6) (Rot ḅ)); reflexivity | ].
  constructor.
Qed.

Check Banach_Tarski_paradox_but_fixpoints.

Theorem Banach_Tarski_paradox :
  equidecomposable set_equiv sphere (xtransl 3 sphere ∪ xtransl 6 sphere)%S.
Proof.
set (s := set_equiv).
pose proof TTCA _ same_orbit equiv_same_orbit as H.
destruct H as (f & Hu & Hm).
remember (mkcf _ _ f Hm Hu) as Hosf.
remember (mkos _ f) as os eqn:Hos.
clear HeqHosf.
bbb.
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

bbb.
