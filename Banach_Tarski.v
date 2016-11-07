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

Fixpoint path_of_nat_aux it (n : nat) :=
  match it with
  | O => []
  | S it' =>
      match n with
      | 0 => ạ :: []
      | 1 => ạ⁻¹ :: []
      | 2 => ḅ :: []
      | 3 => ḅ⁻¹ :: []
      | _ =>
          let l := path_of_nat_aux it' ((n - 4) / 3) in
          match (n - 4) / 3 with
          | 0 =>
              match (n - 4) mod 3 with 0 => ạ | 1 => ḅ | _ => ḅ⁻¹ end :: l
          | 1 =>
              match (n - 4) mod 3 with 0 => ạ⁻¹ | 1 => ḅ | _ => ḅ⁻¹ end :: l
          | 2 =>
              match (n - 4) mod 3 with 0 => ạ | 1 => ạ⁻¹ | _ => ḅ end :: l
          | 3 =>
              match (n - 4) mod 3 with 0 => ạ | 1 => ạ⁻¹ | _ => ḅ⁻¹ end :: l

          | 4 =>
              match (n - 4) mod 3 with 0 => ạ | 1 => ḅ | _ => ḅ⁻¹ end :: l
          | 5 =>
              match (n - 4) mod 3 with 0 => ạ | 1 => ạ⁻¹ | _ => ḅ end :: l
          | 6 =>
              match (n - 4) mod 3 with 0 => ạ | 1 => ạ⁻¹ | _ => ḅ⁻¹ end :: l
          | 7 =>
              match (n - 4) mod 3 with 0 => ạ⁻¹ | 1 => ḅ | _ => ḅ⁻¹ end :: l

          | _ =>
              []
          end
      end
  end.

Definition path_of_nat n := path_of_nat_aux (S n) n.

Compute (path_of_nat 0).
Compute (path_of_nat 1).
Compute (path_of_nat 2).
Compute (path_of_nat 3).
Compute (path_of_nat 4).
Compute (path_of_nat 5).
Compute (path_of_nat 6).
Compute (path_of_nat 7).
Compute (path_of_nat 8).
Compute (path_of_nat 9).
Compute (path_of_nat 10).
Compute (path_of_nat 11).
Compute (path_of_nat 12).
Compute (path_of_nat 13).
Compute (path_of_nat 14).
Compute (path_of_nat 15).
Compute (path_of_nat 16).
Compute (path_of_nat 17).
Compute (path_of_nat 18).
Compute (path_of_nat 19).
Compute (path_of_nat 20).
Compute (path_of_nat 21).
Compute (path_of_nat 22).
Compute (path_of_nat 23).
Compute (path_of_nat 24).
Compute (path_of_nat 25).
Compute (path_of_nat 26).
Compute (path_of_nat 27).
Compute (path_of_nat 28).

(*
Definition path_of_nat n := path_of_nat_aux (S n) n.

Fixpoint path_of_nat_aux it n :=
  match it with
  | O => []
  | S it' =>
      let l :=
        match n / 4 with
        | 0 => []
        | S n' => path_of_nat_aux it' n'
        end
      in
      match n mod 4 with
      | 0 => ạ
      | 1 => ạ⁻¹
      | 2 => ḅ
      | _ => ḅ⁻¹
      end :: l
  end.

Definition path_of_nat n := path_of_nat_aux (S n) n.
*)

bbb.

Theorem toto : ∃ (f : nat → list free_elem),
  (∀ n, norm_list (f n) = f n) ∧
  (∀ m n, m ≠ n → f m ≠ f n) ∧ (∀ el, ∃ n, f n = el).
Proof.
bbb.

Theorem glop : ∃ (f : nat → point),
  (∀ n, f n ∈ D) ∧ (∀ m n, m ≠ n → f m ≠ f n) ∧ (∀ p, ∃ n, f n = p).
Proof.
bbb.

Theorem equidec_sphere_with_and_without_fixpoints : ∀ (s := set_equiv),
  equidecomposable _ sphere sphere_but_fixpoints.
Proof.
intros.
assert (∃ p₁, p₁ ∈ sphere ∖ D).
unfold "∈", "∖".
found.

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
