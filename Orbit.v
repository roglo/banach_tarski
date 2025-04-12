(* Banach-Tarski paradox. *)

From Stdlib Require Import Utf8 List Relations.
From Stdlib Require Import Reals Nsatz.
Import ListNotations.

Require Import Misc MiscReals Words Normalize Reverse Matrix Pset.

Definition same_orbit x y := ∃ el, (mat_of_path el * x)%vec = y.

Theorem same_orbit_refl : reflexive _ same_orbit.
Proof. now exists []; rewrite mat_vec_mul_id. Qed.

Theorem same_orbit_sym : symmetric _ same_orbit.
Proof.
intros p₁ p₂ (el, H); simpl in H.
exists (rev_path el).
revert p₁ p₂ H.
induction el as [| e]; intros; [ now rewrite mat_vec_mul_id in H |-* | ].
rewrite rev_path_cons, mat_of_path_app, mat_vec_mul_assoc.
apply IHel; rewrite <- H, <- mat_vec_mul_assoc.
rewrite <- mat_of_path_app, rev_path_single; simpl.
now rewrite mat_of_path_negf.
Qed.

Theorem same_orbit_trans : transitive _ same_orbit.
Proof.
intros p₁ p₂ p₃ (el₁, H₁) (el₂, H₂); simpl in H₁, H₂.
exists (el₂ ++ el₁).
now rewrite mat_of_path_app, mat_vec_mul_assoc, H₁, H₂.
Qed.

Add Parametric Relation : _ same_orbit
 reflexivity proved by same_orbit_refl
 symmetry proved by same_orbit_sym
 transitivity proved by same_orbit_trans
 as same_orbit_rel.

Definition equiv_same_orbit : equiv vector same_orbit :=
  conj same_orbit_refl (conj same_orbit_trans same_orbit_sym).

Definition not_in_fixpoints :=
  mkset (λ p, ∀ el, norm_list el ≠ [] → fold_right rotate p el ≠ p).

Theorem not_in_fixpoints_one_path : ∀ f p e₁ e₂ el el₂ el₁ el₃,
  p ∈ not_in_fixpoints
  → (mat_of_path el * p)%vec = f p
  → (mat_of_path el₁ * (f p))%vec = p
  → norm_list el = el₂ ++ [e₁]
  → norm_list el₁ = e₂ :: el₃
  → e₂ ≠ negf e₁
  → False.
Proof.
intros f p e₁ e₂ el el₂ el₁ el₃ Hnf Hel H₆ H₂ H₄ Hd.
rewrite rotate_rotate_norm in Hel, H₆.
rewrite <- Hel in H₆.
rewrite <- mat_vec_mul_assoc in H₆.
rewrite <- mat_of_path_app in H₆.
revert H₆.
rewrite <- rotate_vec_mul.
apply Hnf.
intros H.
apply norm_list_app_is_nil in H. {
  rewrite H₄, H₂ in H.
  apply rev_path_eq_eq in H.
  rewrite rev_path_involutive, rev_path_app in H.
  apply not_eq_sym in Hd.
  now injection H.
} {
  now rewrite norm_list_idemp.
} {
  now rewrite norm_list_idemp.
}
Qed.

Definition orbit_selector := choice_function same_orbit.

Definition sphere r := mkset (λ '(V x y z), (x² + y² + z² = r²)%R).
Definition ball := mkset (λ '(V x y z), (x² + y² + z² <= 1)%R).

Theorem on_sphere_norm : ∀ p r, (0 ≤ r)%R → p ∈ sphere r ↔ ‖p‖ = r.
Proof.
intros (x, y, z) r Hr; simpl.
split; intros Hp. {
  now rewrite Hp; apply sqrt_Rsqr.
}
apply (f_equal Rsqr) in Hp.
rewrite Rsqr_sqrt in Hp; [ easy | ].
apply nonneg_sqr_vec_norm.
Qed.

Theorem in_its_sphere : ∀ v, v ∈ sphere ‖v‖.
Proof.
intros (x, y, z); simpl.
rewrite Rsqr_sqrt; [ easy | ].
apply nonneg_sqr_vec_norm.
Qed.

Theorem on_sphere_after_rotation : ∀ p m r,
  p ∈ sphere r
  → is_rotation_matrix m
  → (m * p)%vec ∈ sphere r.
Proof.
intros * His Hm.
destruct p as (x, y, z).
unfold sphere in His; simpl in His.
unfold sphere; simpl.
unfold is_rotation_matrix in Hm.
destruct Hm as (Hm, Hd).
unfold mat_det in Hd.
unfold mat_mul, mat_id in Hm; simpl in Hm.
injection Hm; clear Hm; intros H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ H₉.
progress unfold Rsqr in His.
progress unfold Rsqr.
nsatz.
Qed.

Theorem in_ball_after_rotation : ∀ p m,
  p ∈ ball
  → is_rotation_matrix m
  → mat_vec_mul m p ∈ ball.
Proof.
intros * His Hrm.
destruct p as (x, y, z).
remember (V x y z) as p eqn:HP.
remember (x² + y² + z²)%R as r eqn:Hr; symmetry in Hr.
assert (Hos : p ∈ sphere (√ r)). {
  subst p; simpl; rewrite Rsqr_sqrt; [ easy | subst r ].
  apply nonneg_sqr_vec_norm.
}
pose proof on_sphere_after_rotation _ _ _ Hos Hrm as H.
unfold ball in His.
unfold sphere in H.
unfold ball.
subst p; simpl in *.
now rewrite H, <- Hos.
Qed.

Theorem in_ball_after_rotate : ∀ p e,
  p ∈ ball
  → rotate e p ∈ ball.
Proof.
intros * His.
apply in_ball_after_rotation; [ easy | ].
apply rotate_is_rotation_matrix.
Qed.
