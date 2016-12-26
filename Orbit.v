(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List Relations.
Import ListNotations.
Require Import Reals Nsatz.

Require Import Misc Words Normalize Reverse Matrix Pset.

Notation "'√'" := sqrt.
Notation "x '≤' y" := (Rle x y) : R_scope.

Definition same_orbit x y := ∃ el, fold_right rotate x el = y.

Theorem same_orbit_refl : reflexive _ same_orbit.
Proof. now intros; exists []. Qed.

Theorem same_orbit_sym : symmetric _ same_orbit.
Proof.
intros p₁ p₂ (el, H); simpl in H.
exists (rev_path el).
revert p₁ p₂ H.
induction el as [| e]; intros; [ now symmetry | simpl in H; simpl ].
unfold rev_path; simpl.
rewrite map_app; simpl.
rewrite fold_right_app; simpl.
apply IHel; rewrite <- H.
now rewrite rotate_neg_rotate.
Qed.

Theorem same_orbit_trans : transitive _ same_orbit.
Proof.
intros p₁ p₂ p₃ (el₁, H₁) (el₂, H₂); simpl in H₁, H₂.
exists (el₂ ++ el₁).
now rewrite fold_right_app, H₁, H₂.
Qed.

Add Parametric Relation : _ same_orbit
 reflexivity proved by same_orbit_refl
 symmetry proved by same_orbit_sym
 transitivity proved by same_orbit_trans
 as same_orbit_rel.

Definition equiv_same_orbit : equiv point same_orbit :=
  conj same_orbit_refl (conj same_orbit_trans same_orbit_sym).

Definition not_in_fixpoints :=
  mkset (λ p, ∀ el, norm_list el ≠ [] → fold_right rotate p el ≠ p).

Theorem not_in_fixpoints_one_path : ∀ f p e₁ e₂ el el₂ el₁ el₃,
  p ∈ not_in_fixpoints
  → fold_right rotate p el = f p
  → fold_right rotate (f p) el₁ = p
  → norm_list el = el₂ ++ [e₁]
  → norm_list el₁ = e₂ :: el₃
  → e₂ ≠ negf e₁
  → False.
Proof.
intros f p e₁ e₂ el el₂ el₁ el₃ Hnf Hel H₆ H₂ H₄ Hd.
rewrite rotate_rotate_norm in Hel, H₆.
rewrite <- Hel in H₆.
rewrite <- fold_right_app in H₆.
revert H₆.
apply Hnf.
intros H.
apply norm_list_app_is_nil in H.
 rewrite H₄, H₂ in H.
 apply rev_path_eq_eq in H.
 rewrite rev_path_involutive, rev_path_app in H.
 apply not_eq_sym in Hd.
 now injection H.

 now rewrite norm_list_idemp.

 now rewrite norm_list_idemp.
Qed.

Definition orbit_selector := choice_function same_orbit.

Definition sphere_ray r := mkset (λ '(P x y z), (x² + y² + z² = r²)%R).
Definition sphere := mkset (λ '(P x y z), (x² + y² + z² <= 1)%R).

Definition D :=
  mkset
    (λ p, ∃ el p₁, same_orbit p p₁
     ∧ norm_list el ≠ [] ∧ fold_right rotate p₁ el = p₁).

Arguments D : simpl never.

Definition sphere_but_fixpoints := sphere ∖ D.

Theorem on_sphere_ray_after_rotation : ∀ p m r,
  p ∈ sphere_ray r
  → is_rotation_matrix m
  → mat_vec_mul m p ∈ sphere_ray r.
Proof.
intros * His Hm.
destruct p as (x, y, z).
unfold sphere_ray in His; simpl in His.
unfold sphere_ray; simpl.
unfold is_rotation_matrix in Hm.
destruct Hm as (Hm, Hd).
unfold mat_det in Hd.
unfold mat_mul, mat_id in Hm; simpl in Hm.
injection Hm; clear Hm; intros H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ H₉.
nsatz.
Qed.

Theorem in_sphere_after_rotation : ∀ p m,
  p ∈ sphere
  → is_rotation_matrix m
  → mat_vec_mul m p ∈ sphere.
Proof.
intros * His Hrm.
destruct p as (x, y, z).
remember (P x y z) as p eqn:HP.
remember (x² + y² + z²)%R as r eqn:Hr; symmetry in Hr.
assert (Hos : p ∈ sphere_ray (√ r)).
 subst p; simpl; rewrite Rsqr_sqrt; [ easy | subst r ].
 apply nonneg_sqr_vec_norm.

 pose proof on_sphere_ray_after_rotation _ _ _ Hos Hrm as H.
 unfold sphere in His.
 unfold sphere_ray in H.
 unfold sphere.
 subst p; simpl in *.
 now rewrite H, <- Hos.
Qed.

Theorem in_sphere_after_rotate : ∀ p e,
  p ∈ sphere
  → rotate e p ∈ sphere.
Proof.
intros * His.
apply in_sphere_after_rotation; [ easy | ].
apply rotate_is_rotation_matrix.
Qed.

Theorem same_orbit_rotate : ∀ e p₁ p₂,
  same_orbit p₁ p₂
  → same_orbit (rotate e p₁) (rotate e p₂).
Proof.
intros * Hso.
destruct Hso as (el, Hr).
exists (e :: el ++ [negf e]); simpl.
rewrite fold_right_app; simpl.
rewrite rotate_neg_rotate.
now f_equal.
Qed.

Theorem no_fixpoint_after_rotate : ∀ p e, p ∉ D → rotate e p ∉ D.
Proof.
intros * His Hr; apply His; clear His.
unfold D in Hr; simpl in Hr.
unfold D; simpl.
destruct Hr as (el & p₁ & Hso & Hn & Hr).
exists el, p₁.
split; [ | easy ].
destruct Hso as (el₁ & Hso).
exists (el₁ ++ [e]).
now rewrite fold_right_app.
Qed.
