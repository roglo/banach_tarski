(* Banach-Tarski paradox. *)
(* Coq v8.6 *)

Require Import Utf8 Bool.

(* Rémi Nollet's code, modified *)

Theorem Cantor : ∀ E (F : E → (E → bool)), ∃ f : E → bool, ∀ x, f x ≠ F x x.
Proof.
intros E F; exists (fun e => negb (F e e)); intros x H.
exact (no_fixpoint_negb _ H).
Qed.

Lemma Cantor_gen : ∀ E X Y (Yss : Y → Prop),
  ∀ (sX : E → X) (sY : Y → (E → bool)),
  ∀ (sX_surj : ∀ e, ∃ x, sX x = e),
  ∀ (sY_surj : ∀ f, ∃ y, Yss y ∧ ∀ x, sY y x = f x),
  ∀ f : X → Y, ∃ y, ∀ x, Yss y ∧ y ≠ f x.
Proof.
intros * sX_surj sY_surj F.
destruct Cantor with E (fun e => sY (F (sX e))) as [f H].
destruct sY_surj with f as [y Hy]; subst.
destruct Hy as (Hy, Hyf).
exists y; intros x; split; [ easy | ]; subst.
destruct sX_surj with x as [e]; subst.
specialize (H e).
now intros H2; apply H; subst.
Qed.

(* End Rémi Nollet's code *)
