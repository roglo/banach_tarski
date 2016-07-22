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

Fixpoint normalise_list_free_elem el :=
  match el with
  | nil => nil
  | E l₁ d₁ :: nil => el
  | E l₁ d₁ :: (E l₂ d₂ :: el₂) as el₁ =>
      if letter_dec l₁ l₂ then
        if Bool.bool_dec d₁ d₂ then E l₁ d₁ :: normalise_list_free_elem el₁
        else normalise_list_free_elem el₂
      else E l₁ d₁ :: normalise_list_free_elem el₁
  end.

Definition norm s := mkF₂ (normalise_list_free_elem (str s)).

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

(* s ∈ xS(y) ↔
   ∃ t, t ∈ S(y) ∧ s ≡ norm (xt) *)

Definition start_with2 x y s :=
  ∃ t, start_with y t ∧ s = norm (mkF₂ (x :: str t)).

End Free_Group.

bbb.

Theorem decomposed_2_a : ∀ s, start_with2 a a⁻¹ s ∨ start_with a s.
intros s.
destruct s as (el).
destruct el as [| (x, d) el].
 left.
 exists (mkF₂ (a⁻¹ :: nil)); simpl.
 split; [ reflexivity | ].
 unfold norm; simpl.
 destruct (letter_dec la la) as [H| H]; [ reflexivity | ].
 exfalso; apply H; reflexivity.

 revert x d.
 induction el as [| (x1, d1)]; intros.
  destruct (only_letters x); subst x.
   destruct d; [ left | right; reflexivity ].
   unfold start_with2; simpl.
   exists (mkF₂ (a⁻¹ :: a⁻¹ :: nil)).
   unfold start_with, norm; simpl.
   destruct (letter_dec la la) as [| H]; [ split; reflexivity | ].
   exfalso; apply H; reflexivity.

   left.
   unfold start_with2; simpl.
   exists (mkF₂ (a⁻¹ :: E lb d :: nil)); simpl.
   split.
    unfold start_with; simpl.
    destruct (letter_dec la lb) as [H| H]; [ | reflexivity ].
    exfalso; revert H; apply la_neq_lb.

    unfold norm; simpl.
    destruct (letter_dec la la) as [H| H]; [ reflexivity | ].
    exfalso; apply H; reflexivity.

  destruct (only_letters x); subst x.
   destruct d.
    left.
    unfold start_with2; simpl.
    exists (mkF₂ (a⁻¹ :: a⁻¹ :: E x1 d1 :: el)).
    split.
     unfold start_with; simpl.
     destruct (letter_dec la la) as [H| H]; [ reflexivity | ].
     exfalso; apply H; reflexivity.

     unfold norm; simpl.
     destruct (letter_dec la la) as [H| H].
      clear H.
      destruct (letter_dec la x1) as [H| H].
       subst x1.
       destruct d1.
        f_equal; f_equal.
        destruct el as [| (x, d)]; [ reflexivity | ].
        destruct (letter_dec la x) as [H| H].
         subst x.
         destruct (Bool.bool_dec true d) as [H| H].
          f_equal; subst d.
faux.
bbb.

End Free_Group.
