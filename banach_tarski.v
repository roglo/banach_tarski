Require Import Utf8.
Require Import List.

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

Definition F₂_normalise s := mkF₂ (normalise_list_free_elem (str s)).

Definition start_with x s :=
  match str (F₂_normalise s) with
  | nil => False
  | e :: el => x = e
  end.
Definition is_empty s := str (F₂_normalise s) = nil.

Definition SW x := { s | start_with x s }.
Definition Empty := { s | is_empty s }.

Theorem decomposed_4 : (F₂ = Empty + SW a + SW a⁻¹ + SW b + SW b⁻¹)%type.
Proof.
Abort.

Theorem decomposed_4 : ∀ s, is_empty s ∨
  start_with a s ∨ start_with a⁻¹ s ∨ start_with b s ∨ start_with b⁻¹ s.
Proof.
intros s.
unfold is_empty, start_with.
remember (F₂_normalise s) as ns eqn:Hns; symmetry in Hns.
destruct ns as (el); simpl.
destruct el as [| e]; [ left; reflexivity | right ].
destruct e as (x, d).
destruct x.
 destruct d; [ right; left; reflexivity | left; reflexivity ].
 right; right.
 destruct d; [ right; reflexivity | left; reflexivity ].
Qed.

(*
Definition start_with_2 x y s :=
  match str (F₂_normalise s) with
  | nil => False
  | e :: el => ...
*)

Theorem decomposed_2_with_a : ∀ s,
  start_with_2 a a⁻¹ s ∨ start_with a s.
ah bin non...
