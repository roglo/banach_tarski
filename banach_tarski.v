Require Import Utf8.
Require Import List.

Section Free_Group.

(* a = E la false
   a⁻¹ = E la true
   b = E lb false
   b⁻¹ = E lb true *)

Inductive letter := la | lb.
Inductive free_elem := E : letter → bool → free_elem.
Record F₂ := mkF₂ { str : list free_elem }.

Notation "'a'" := (E la false).
Notation "'a⁻¹'" := (E la true).
Notation "'b'" := (E lb false).
Notation "'b⁻¹'" := (E lb true).

Theorem letter_dec : ∀ l1 l2 : letter, {l1 = l2} + {l1 ≠ l2}.
Proof.
intros.
destruct l1, l2; try (left; reflexivity); right; intros H; discriminate H.
Qed.

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
destruct x.
 destruct d; [ right; left; reflexivity | left; reflexivity ].
 right; right.
 destruct d; [ right; reflexivity | left; reflexivity ].
Qed.

(* s ∈ xS(y) ↔
   ∃ t, t ∈ S(y) ∧ s ≡ norm (xt) *)

Definition start_with2 x y s :=
  ∃ t, start_with y t ∧ s = norm (mkF₂ (x :: str t)).

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

 destruct x.
  destruct d.
   left.
   unfold start_with2; simpl.
   destruct el as [| (x, d) el].
    exists (mkF₂ (a⁻¹ :: a⁻¹ :: nil)).
    unfold start_with, norm; simpl.
    destruct (letter_dec la la) as [| H]; [ split; reflexivity | ].
    exfalso; apply H; reflexivity.

    destruct x.
     destruct d.
      exists (mkF₂ (a⁻¹ :: a⁻¹ :: normalise_list_free_elem (a⁻¹ :: el))).
      unfold start_with, norm; simpl.
      destruct (letter_dec la la) as [H| H].
       split; [ reflexivity | f_equal; clear H ].
       destruct el as [| (x, d) el].
       destruct (letter_dec la la) as [| H]; [ reflexivity | ].
       exfalso; apply H; reflexivity.
       destruct (letter_dec la x) as [H| H].
        subst x.
        destruct d.
         simpl.
         destruct (letter_dec la la) as [H| H].
          clear H; f_equal.
          destruct el as [| (x, d) el].
           destruct (letter_dec la la) as [H| H]; [ reflexivity | ].
           exfalso; apply H; reflexivity.

           destruct (letter_dec la x) as [H| H].
            subst x.
            destruct d.
            destruct (letter_dec la la) as [H| H].
             f_equal.
faux.
bbb.

End Free_Group.
