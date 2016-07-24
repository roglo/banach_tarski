Require Import Utf8.
Require Import List.

Section Free_Group.

(* a = E la false
   a⁻¹ = E la true
   b = E lb false
   b⁻¹ = E lb true *)

(*
Inductive letter := la | lb.
*)
Variable letter : Type.
Variable la : letter.
Variable lb : letter.
Variable la_neq_lb : la ≠ lb.
Variable only_letters : ∀ l, { l = la } + { l = lb }.

Inductive free_elem := E : letter → bool → free_elem.
Record F₂ := mkF₂ { str : list free_elem }.

Notation "'a'" := (E la false).
Notation "'a⁻¹'" := (E la true).
Notation "'b'" := (E lb false).
Notation "'b⁻¹'" := (E lb true).

Variable letter_dec : ∀ l1 l2 : letter, {l1 = l2} + {l1 ≠ l2}.
(*
Theorem letter_dec : ∀ l1 l2 : letter, {l1 = l2} + {l1 ≠ l2}.
Proof.
intros.
destruct l1, l2; try (left; reflexivity); right; intros H; discriminate H.
Qed.
*)

Definition letter_opp '(E l₁ d₁) '(E l₂ d₂) :=
  if letter_dec l₁ l₂ then
    if Bool.bool_dec d₁ d₂ then False else True
  else False.

Theorem letter_opp_dec : ∀ e₁ e₂,
  {letter_opp e₁ e₂} + {not (letter_opp e₁ e₂)}.
Proof.
intros.
destruct e₁ as (x₁, d₁).
destruct e₂ as (x₂, d₂); simpl.
destruct (letter_dec x₁ x₂) as [Hx| Hx].
 destruct (Bool.bool_dec d₁ d₂) as [Hd| Hd]; [ | left; constructor ].
 right; intros H; contradiction.

 right; intros H; contradiction.
Qed.

Fixpoint norm_list el :=
  match el with
  | nil => nil
  | e₁ :: el₁ =>
      match norm_list el₁ with
      | nil => e₁ :: nil
      | e₂ :: el₂ => if letter_opp_dec e₁ e₂ then el₂ else e₁ :: e₂ :: el₂
      end
  end.

Definition norm s := mkF₂ (norm_list (str s)).

Theorem norm_list_norm_list : ∀ el, norm_list (norm_list el) = norm_list el.
Proof.
intros el.
induction el as [| e]; [ reflexivity | simpl ].
remember (norm_list el) as el' eqn:Hel'; symmetry in Hel'.
destruct el' as [| e']; [ reflexivity | ].
destruct (letter_opp_dec e e') as [H| H].
 unfold letter_opp in H.
 destruct e as (x, d).
 destruct e' as (x', d').
 destruct (letter_dec x x') as [Hx| Hx].
  subst x'.
  destruct (Bool.bool_dec d d') as [Hd| Hd]; [ contradiction | clear H ].
  simpl in IHel.
  remember (norm_list el') as el'' eqn:Hel''; symmetry in Hel''.
  destruct el'' as [| e''].
   injection IHel; clear IHel; intros H; assumption.

   destruct (letter_opp_dec (E x d') e'') as [He| He].
    subst el''.
    simpl in He.
    destruct e'' as (x'', d'').
    destruct (letter_dec x x'') as [Hx| Hx].
     subst x''.
     destruct (Bool.bool_dec d' d'') as [Hd'| Hd']; [ contradiction | ].
     clear He.
bbb.

Theorem norm_norm : ∀ s, norm (norm s) = norm s.
Proof.
intros.
destruct s as (el).
unfold norm; simpl; f_equal.
bbb.

Definition start_with x s :=
  match str (norm s) with
  | nil => False
  | e :: el => x = e
  end.
Definition is_empty s := str (norm s) = nil.

Definition Sw x := { s | start_with x s }.
Definition Empty := { s | is_empty s }.

Theorem decomposed_4 : ∀ s, is_empty s ∨
  start_with a s ∨ start_with a⁻¹ s ∨ start_with b s ∨ start_with b⁻¹ s.
Proof.
intros s.
unfold is_empty, start_with.
remember (norm s) as ns eqn:Hns; symmetry in Hns.
destruct ns as (el); simpl.
destruct el as [| e]; [ left; reflexivity | right ].
destruct e as (x, d).
destruct (only_letters x); subst x.
 destruct d; [ right; left; reflexivity | left; reflexivity ].

 right; right.
 destruct d; [ right; reflexivity | left; reflexivity ].
Qed.

(* s in xS(y) *)
Definition start_with2 x y s :=
  ∃ t, norm s = norm (mkF₂ (x :: str t)) ∧ start_with y t.

Theorem empty_start_with2_a_ai : ∀ s, is_empty s → start_with2 a a⁻¹ s.
Proof.
intros s H.
unfold is_empty in H.
unfold start_with2.
remember (norm s) as ns eqn:Hns; symmetry in Hns.
destruct ns as (el).
simpl in H; subst el.
exists (mkF₂ (a⁻¹ :: nil)); simpl.
unfold start_with, norm; simpl.
split; [ | reflexivity ].
destruct (letter_dec la la) as [H| H]; [ reflexivity | ].
exfalso; apply H; reflexivity.
Qed.

Theorem decomposed_2_a : ∀ s, start_with2 a a⁻¹ s ∨ start_with a s.
Proof.
intros s.
destruct (decomposed_4 s) as [H| [H| [H| [H|H]]]].
 left; apply empty_start_with2_a_ai; assumption.

 right; assumption.

 unfold start_with in H.
 unfold start_with2; simpl.
 remember (norm s) as ns eqn:Hns; symmetry in Hns.
 destruct ns as (el); simpl in H.
 destruct el as [| e el]; [ contradiction | ].
 subst e; unfold start_with; rewrite Hns; simpl.
 left.
 exists (mkF₂ (a⁻¹ :: a⁻¹ :: el)).
 split.
  simpl.
  remember (a⁻¹ :: el) as el' eqn:Hel'.

Theorem toto : ∀ el, norm (mkF₂ (a :: a⁻¹ :: el)) = norm (mkF₂ el).
Proof.
Admitted. Show.

symmetry.
etransitivity; [ apply toto | ].
rewrite <- Hns.
bbb.

  simpl; unfold norm; simpl.
  destruct (letter_dec la la) as [H| H].
   f_equal; clear H.
   destruct el as [| e el] ; [ reflexivity | ].
   destruct e as (x, d).
   destruct (letter_dec la x) as [H| H].
    subst x.
    destruct d.
     simpl; f_equal.
     destruct el as [| e el]; [ reflexivity | ].
     destruct e as (x, d).
     destruct (letter_dec la x) as [H| H].
      subst x.
      destruct d.
       simpl; f_equal.
       destruct el as [| e el]; [ reflexivity | ].


bbb.

End Free_Group.
