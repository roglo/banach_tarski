(* Banach-Tarski paradox. *)
(* Coq v8.6 *)

Require Import Utf8 QArith.
Require Import Countable.

Theorem Pos_is_countable : is_countable positive.
Proof.
unfold is_countable.
exists Pos.of_nat.
intros p.
exists (Pos.to_nat p).
apply Pos2Nat.id.
Qed.

Theorem unit_is_countable : is_countable unit.
Proof.
exists (λ n, tt).
intros a; exists O.
now destruct a.
Qed.

Theorem Z_is_countable : is_countable Z.
Proof.
specialize (countable_sum_types _ _ Pos_is_countable Pos_is_countable).
intros Hs.
specialize (countable_sum_types _ _ unit_is_countable Hs).
intros Hc.
set (f c := match c with inl p => Z.pos p | inr p => Z.neg p end).
set (g c := match c with inl tt => 0%Z | inr d => f d end).
subst f.
enough (H : FinFun.Surjective g).
 now specialize (countable_surjection _ _ g Hc H).

 subst g.
 unfold FinFun.Surjective.
 intros z.
 exists
   (match z with
    | 0%Z => inl tt | Z.pos p => inr (inl p) | Z.neg p => inr (inr p) end).
 now destruct z.
Qed.

Theorem Q_is_countable : is_countable Q.
Proof.
set (A := (Z * positive)%type).
set (f x := Qmake (fst x) (snd x)).
apply (countable_surjection A Q f).
 apply countable_product_types; [ apply Z_is_countable | ].
 apply Pos_is_countable.

 unfold FinFun.Surjective, f, A; simpl.
 intros (n, d).
 now exists (n, d).
Qed.
