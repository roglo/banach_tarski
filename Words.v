(* Banach-Tarski paradox. *)

From Stdlib Require Import Utf8 List Relations Wf_nat.
Import ListNotations.
Require Import a.Misc.

Inductive letter := la | lb.

Inductive free_elem := FE : letter → bool → free_elem.

Notation "'ạ'" := (FE la false).
Notation "'ạ⁻¹'" := (FE la true).
Notation "'ḅ'" := (FE lb false).
Notation "'ḅ⁻¹'" := (FE lb true).

Definition negf '(FE t d) := FE t (negb d).

Theorem letter_dec : ∀ l1 l2 : letter, {l1 = l2} + {l1 ≠ l2}.
Proof.
intros.
now destruct l1, l2; try (now left); right.
Defined.

Theorem free_elem_dec : ∀ e₁ e₂ : free_elem, { e₁ = e₂ } + { e₁ ≠ e₂ }.
Proof.
intros.
destruct e₁ as (t₁, d₁).
destruct e₂ as (t₂, d₂).
destruct (letter_dec t₁ t₂) as [H₁| H₁]; [ subst t₂ | ]. {
  destruct (Bool.bool_dec d₁ d₂) as [H₂| H₂]; [ subst d₂ | ]. {
    now left.
  } {
    right; intros H; apply H₂.
    now injection H.
  }
} {
  right; intros H; apply H₁.
  now injection H.
}
Qed.

Theorem letter_dec_diag : ∀ t, letter_dec t t = left (eq_refl _).
Proof.
intros t.
destruct (letter_dec t t) as [p| p]; [ | exfalso; now apply p ].
destruct t; refine (match p with eq_refl => eq_refl end).
Qed.

Definition letter_opp '(FE l₁ d₁) '(FE l₂ d₂) :=
  if letter_dec l₁ l₂ then
    if Bool.bool_dec d₁ d₂ then False else True
  else False.

Theorem letter_opp_dec : ∀ e₁ e₂,
  {letter_opp e₁ e₂} + {not (letter_opp e₁ e₂)}.
Proof.
intros.
destruct e₁ as (x₁, d₁).
destruct e₂ as (x₂, d₂); simpl.
destruct (letter_dec x₁ x₂) as [Hx| Hx]; [ | now right ].
destruct (Bool.bool_dec d₁ d₂) as [Hd| Hd]; [ | left; constructor ].
now right.
Defined.

Theorem letter_opp_inv : ∀ x d, letter_opp (FE x d) (FE x (negb d)).
Proof.
intros.
unfold letter_opp.
now rewrite letter_dec_diag, bool_dec_negb_r.
Qed.

Theorem letter_opp_iff : ∀ x₁ d₁ x₂ d₂,
  letter_opp (FE x₁ d₁) (FE x₂ d₂)
  ↔ x₁ = x₂ ∧ d₂ = negb d₁.
Proof.
intros x₁ d₁ x₂ d₂.
split; intros H. {
  unfold letter_opp in H.
  destruct (letter_dec x₁ x₂) as [H₁| H₁]; [ | easy ].
  split; [ easy | ].
  destruct (Bool.bool_dec d₁ d₂) as [H₂| H₂]; [ easy | ].
  now apply neq_negb, not_eq_sym.
} {
  destruct H; subst x₂ d₂.
  apply letter_opp_inv.
}
Qed.

Theorem letter_opp_negf : ∀ e₁ e₂, letter_opp e₁ e₂ ↔ e₁ = negf e₂.
Proof.
intros.
destruct e₁ as (t₁, d₁).
destruct e₂ as (t₂, d₂).
split; intros H. {
  apply letter_opp_iff in H.
  destruct H; subst t₂ d₂; simpl.
  now rewrite Bool.negb_involutive.
} {
  injection H; intros; subst; simpl.
  now rewrite letter_dec_diag, bool_dec_negb_l.
}
Qed.

Theorem no_fixpoint_negf : ∀ e, negf e ≠ e.
Proof.
intros * H.
destruct e as (t, d).
injection H.
apply Bool.no_fixpoint_negb.
Qed.

Theorem negf_involutive : ∀ e, negf (negf e) = e.
Proof.
intros (t, d); simpl.
now rewrite Bool.negb_involutive.
Qed.

Theorem letter_opp_negf_r : ∀ e, letter_opp e (negf e).
Proof.
intros.
apply letter_opp_negf.
now rewrite negf_involutive.
Qed.

Theorem letter_opp_sym : ∀ e₁ e₂, letter_opp e₁ e₂ → letter_opp e₂ e₁.
Proof.
intros * H.
apply letter_opp_negf in H.
subst e₁.
apply letter_opp_negf_r.
Qed.

Theorem negf_eq_eq : ∀ e₁ e₂, negf e₁ = negf e₂ → e₁ = e₂.
Proof.
intros e₁ e₂ Hn.
destruct e₁ as (t₁, d₁).
destruct e₂ as (t₂, d₂).
simpl in Hn.
injection Hn; intros H₁ H₂; subst.
now apply negb_eq_eq in H₁; subst d₁.
Qed.
