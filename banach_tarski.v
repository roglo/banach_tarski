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
