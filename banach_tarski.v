Require Import Utf8.
Require Import List.

(* a = E a false
   a⁻¹ = E a true
   b = E b false
   b⁻¹ = E b true *)
Inductive letter := a | b.
Inductive free_elem := E : letter → bool → free_elem.
Record string := mkstring { str : list free_elem }.

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

Definition normalise_string s := mkstring (normalise_list_free_elem (str s)).

Definition is_S x s :=
  match str (normalise_string s) with
  | nil => False
  | E l d :: el => x = (l, d)
  end.

Definition is_empty s := str (normalise_string s) = nil.

Theorem decomposed_4 : ∀ s, is_empty s ∨
  is_S (a, false) s ∨ is_S (a, true) s ∨ is_S (b, false) s ∨ is_S (b, true) s.
Proof.
intros s.
unfold is_empty, is_S.
remember (normalise_string s) as ns eqn:Hns; symmetry in Hns.
destruct ns as (el); simpl.
destruct el as [| e]; [ left; reflexivity | right ].
destruct e as (x, d).
destruct x.
 destruct d; [ right; left; reflexivity | left; reflexivity ].
 right; right.
 destruct d; [ right; reflexivity | left; reflexivity ].
Qed.

Theorem decomposed_2_with_a : ∀ s,
  is_S (a, true) ∨ is_S (a, false) s.
ah bin non...
