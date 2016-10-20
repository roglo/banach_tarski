(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List NPeano Compare_dec.
Import ListNotations.

Require Import Pset.

Definition is_partition {A} {S : set_model A} E Ep :=
  (E = ⋃ Ep)%S ∧
  ∀ i j, i ≠ j → (Ep.[i] ∩ Ep.[j] = ∅)%S.

Theorem is_partition_group_first_2_together :
  ∀ A (s := set_equiv) (F : set A) P₁ P₂ Pl,
  is_partition F (P₁ :: P₂ :: Pl)
  → is_partition F (P₁ ∪ P₂ :: Pl).
Proof.
intros * Hp.
destruct Hp as (Hu & Hi).
split.
 unfold union_list, union, set_eq in Hu |-*.
 subst s; simpl in Hu |-*.
 intros x.
 pose proof Hu x as H₁.
 destruct H₁ as (H₁ & H₂).
 split; intros H.
  apply H₁ in H.
  destruct H as [H| H]; [ left; left; assumption | ].
  destruct H as [H| H]; [ left; right; assumption | ].
  right; assumption.

  apply H₂.
  destruct H as [[H| H]| H]; [ left; assumption | right; left; assumption | ].
  right; right; assumption.

 intros i j Hij; subst s.
 destruct i.
  unfold intersection, set_eq; simpl.
  intros x.
  split; [ | contradiction ].
  intros (H₁, H₂).
  destruct j; [ apply Hij; reflexivity | clear Hij ].
  destruct H₁ as [H₁| H₁].
   eapply Hi with (i := O) (j := S (S j)); [ intros H; discriminate H | ].
   unfold intersection; simpl.
   split; eassumption.

   eapply Hi with (i := 1%nat) (j := S (S j)); [ intros H; discriminate H | ].
   unfold intersection; simpl.
   split; eassumption.

  unfold intersection, union, set_eq; simpl.
  intros x.
  split; [ | contradiction ].
  intros (H₁ & H₂).
  destruct j.
   destruct H₂ as [H₂| H₂].
    eapply Hi with (i := O) (j := S (S i)); [ intros H; discriminate H | ].
    unfold intersection; simpl.
    split; eassumption.

    eapply Hi with (i := 1%nat) (j := S (S i)); [ intros H; discriminate H | ].
    unfold intersection; simpl.
    split; eassumption.

  apply Hi with (i := S (S i)) (j := S (S j)) (x := x).
   intros H; apply Hij.
   apply Nat.succ_inj; assumption.

   unfold intersection; simpl.
   split; assumption.
Qed.

Theorem is_partition_union_subtract :
  ∀ A (s := set_equiv) (F : set A) P₁ P₂ Pl (B : set A),
  is_partition F (P₁ :: P₂ :: Pl)
  → (B ⊂ P₂)%S
  → (∀ x, Decidable.decidable (x ∈ B))
  → is_partition F (P₁ ∪ B :: P₂ ∖ B :: Pl)%S.
Proof.
intros A s F P₁ P₂ Pl B Hp HB HBdec.
destruct Hp as (Hu & Hi).
split.
 unfold union_list, union, subtract, set_eq in Hu |-*.
 subst s; simpl in Hu |-*.
 intros x.
 split; intros H.
  pose proof Hu x as H₁.
  destruct H₁ as (H₁ & H₂).
  pose proof H₁ H as H₃.
  destruct H₃ as [H₃| H₃]; [ left; left; assumption | ].
  destruct H₃ as [H₃| H₃]; [ | right; right; assumption ].
  destruct (HBdec x) as [H₄| H₄]; [ left; right; assumption | ].
  right; left; split; assumption.

  apply Hu.
  destruct H as [[H₁| H₁]| [H₁| H₁]]; [ left; assumption | | | ].
   right; left; apply HB; assumption.

   right; left; destruct H₁; assumption.

   right; right; assumption.

 intros i j Hij; subst s.
 destruct i.
  unfold intersection, union, subtract, set_eq; simpl.
  intros x.
  split; [ | contradiction ].
  intros (H₁, H₂).
  destruct j; [ apply Hij; reflexivity | clear Hij ].
  destruct H₁ as [H₁| H₁].
   eapply Hi with (i := O) (j := S j); [ intros H; discriminate H | ].
   unfold intersection; simpl.
   split; [ eassumption | ].
   destruct j; [ destruct H₂; assumption | assumption ].

   eapply Hi with (i := 1%nat) (j := S j).
    destruct j; [ destruct H₂; contradiction | intros H; discriminate H ].

    unfold intersection; simpl.
    split; [ apply HB; eassumption | ].
    destruct j; [ destruct H₂; contradiction | assumption ].

  unfold intersection, union, subtract, set_eq; simpl.
  intros x.
  split; [ | contradiction ].
  intros (H₁ & H₂).
  destruct j.
   destruct H₂ as [H₂| H₂].
    eapply Hi with (i := O) (j := S i); [ intros H; discriminate H | ].
    unfold intersection; simpl.
    split; [ eassumption | ].
    destruct i; [ destruct H₁; assumption | assumption ].

    eapply Hi with (i := 1%nat) (j := S i).
     destruct i; [ | intros H; discriminate H ].
     destruct H₁; contradiction.

     unfold intersection; simpl.
     split; [ apply HB; eassumption | ].
     destruct i; [ apply HB; assumption | assumption ].

  apply Hi with (i := S i) (j := S j) (x := x).
   intros H; apply Hij; assumption.

   unfold intersection; simpl.
   split.
    destruct i; [ destruct H₁; assumption | assumption ].

    destruct j; [ destruct H₂; assumption | assumption ].
Qed.

Theorem partition_union :
  ∀ A (s := set_equiv) (F₁ F₂ : set A) P₁ P₂,
  (F₁ ∩ F₂ = ∅)%S
  → is_partition F₁ P₁
  → is_partition F₂ P₂
  → is_partition (F₁ ∪ F₂) (P₁ ++ P₂).
Proof.
intros * HFF HF₁ HF₂.
destruct HF₁ as (HF₁ & HP₁).
destruct HF₂ as (HF₂ & HP₂).
split.
 subst s; rewrite union_list_app; [ | reflexivity ].
 transitivity (F₁ ∪ ⋃ P₂).
  intros x.
  split; intros H.
   destruct H as [H| H]; [ left; assumption | right ].
   apply HF₂; assumption.

   destruct H as [H| H]; [ left; assumption | right ].
   apply HF₂; assumption.

  split; intros H.
   destruct H as [H| H]; [ left | right; assumption ].
   apply HF₁; assumption.

   destruct H as [H| H]; [ left | right; assumption ].
   apply HF₁; assumption.

 intros * Hij.
 unfold intersection, set_eq; subst s; simpl.
 intros x.
 split; intros H; [ | contradiction ].
 destruct H as (H₁, H₂).
 rewrite nth_set_app in H₁, H₂.
 destruct (lt_dec i (length P₁)) as [H₃| H₃].
  destruct (lt_dec j (length P₁)) as [H₄| H₄].
   eapply HP₁; [ eassumption | split; eassumption ].

   eapply HFF.
   split.
    apply HF₁.
    eapply nth_set_union_list; eassumption.

    destruct (lt_dec (j - length P₁) (length P₂)) as [H₅| H₅].
     apply HF₂.
     eapply nth_set_union_list; eassumption.

     apply Nat.nlt_ge in H₅.
     rewrite nth_overflow in H₂; [ contradiction | assumption ].

  apply Nat.nlt_ge in H₃.
  destruct (lt_dec j (length P₁)) as [H₄| H₄].
   apply HFF with x.
   split.
    apply HF₁.
    eapply nth_set_union_list; eassumption.

    destruct (lt_dec (i - length P₁) (length P₂)) as [H₅| H₅].
     apply HF₂.
     eapply nth_set_union_list; eassumption.

     apply Nat.nlt_ge in H₅.
     rewrite nth_overflow in H₁; [ contradiction | assumption ].

   apply Nat.nlt_ge in H₄.
   eapply HP₂; [ | split; [ apply H₁ | apply H₂] ].
   intros H.
   apply Nat.add_cancel_l with (p := length P₁) in H.
   rewrite Nat.add_sub_assoc in H; [ | assumption ].
   rewrite Nat.add_sub_assoc in H; [ | assumption ].
   rewrite Nat.add_comm, Nat.add_sub in H.
   rewrite Nat.add_comm, Nat.add_sub in H.
   contradiction.
Qed.
