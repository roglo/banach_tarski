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

Definition same_orbit x y := ∃ el, fold_right rotate x el = y.

Theorem same_orbit_refl : reflexive _ same_orbit.
Proof. intros; exists []; easy. Qed.

Theorem same_orbit_sym : symmetric _ same_orbit.
Proof.
intros p₁ p₂ (el, H); simpl in H.
unfold same_orbit; simpl.
exists (rev (map negf el)).
revert p₁ p₂ H.
induction el as [| e]; intros; [ symmetry; easy | simpl in H; simpl ].
rewrite fold_right_app; simpl.
apply IHel; rewrite <- H.
rewrite rotate_neg_rotate.
easy.
Qed.

Theorem same_orbit_trans : transitive _ same_orbit.
Proof.
intros p₁ p₂ p₃ (el₁, H₁) (el₂, H₂); simpl in H₁, H₂.
unfold same_orbit; simpl.
exists (el₂ ++ el₁).
rewrite fold_right_app, H₁, H₂; easy.
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
 injection H; intros; easy.

 rewrite norm_list_idemp; easy.

 rewrite norm_list_idemp; easy.
Qed.

Definition orbit_selector := choice_function same_orbit.

Definition sphere_ray r := mkset (λ '(P x y z), (x² + y² + z² = r)%R).
Definition sphere := mkset (λ '(P x y z), (x² + y² + z² <= 1)%R).

Definition orbit_without_fixpoint :=
  mkset
    (λ p, ∀ el p₁, same_orbit p p₁
     → norm_list el ≠ [] → fold_right rotate p₁ el ≠ p₁).

Definition sphere_but_fixpoints :=
  mkset (λ p, p ∈ sphere ∧ p ∈ orbit_without_fixpoint).

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
assert (Hos : p ∈ sphere_ray r) by (subst p; easy).
pose proof on_sphere_ray_after_rotation _ _ _ Hos Hrm as H.
unfold sphere in His.
unfold sphere_ray in H.
unfold sphere.
subst p; simpl in *.
rewrite H, <- Hos; easy.
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

Theorem no_fixpoint_after_rotate : ∀ p e,
  p ∈ orbit_without_fixpoint
  → rotate e p ∈ orbit_without_fixpoint.
Proof.
intros * His.
unfold orbit_without_fixpoint in His.
intros el p₁ Hso Hel.
remember (negf e :: rev_path el ++ e :: [])  as el₁ eqn:Hel₁.
remember (norm_list el₁) as el₂ eqn:Hel₂.
symmetry in Hel₂.
destruct el₂ as [| e₂].
 exfalso; subst el₁; apply Hel.
 apply norm_list_is_nil_between in Hel₂.
 rewrite <- rev_path_norm_list in Hel₂.
 apply rev_path_is_nil in Hel₂; easy.

 apply same_orbit_rotate with (e := negf e) in Hso.
 rewrite rotate_neg_rotate in Hso.
 assert (Hn : norm_list el₁ ≠ []) by (now rewrite Hel₂).
 pose proof His el₁ (rotate (negf e) p₁) Hso Hn.
 intros Hr; apply H; clear H.
 rewrite <- Hr at 1.
 rewrite <- fold_right_cons, <- fold_right_app.
 rewrite Hel₁, cons_comm_app, app_comm_cons.
 rewrite <- app_assoc.
 simpl; f_equal.
 rewrite rotate_rotate_norm.
 rewrite norm_list_cancel_in.
 rewrite <- rotate_rotate_norm.
 apply app_path_rev_path.
Qed.
