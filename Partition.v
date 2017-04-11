(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List NPeano Compare_dec Setoid.
Import ListNotations.

Require Import Misc Pset.

Definition is_partition {A} (E : set A) (Ep : list (set A)) :=
  (E = ⋃ Ep)%S ∧
  ∀ i j, i ≠ j → (Ep.[i] ∩ Ep.[j] = ∅)%S.

Theorem is_partition_group_first_2_together :
  ∀ A (F : set A) P₁ P₂ Pl,
  is_partition F (P₁ :: P₂ :: Pl)
  → is_partition F (P₁ ∪ P₂ :: Pl).
Proof.
intros * Hp.
destruct Hp as (Hu & Hi).
split.
 unfold union_list, union, set_eq in Hu |-*.
 simpl in Hu |-*.
 intros x.
 pose proof Hu x as H₁.
 destruct H₁ as (H₁ & H₂).
 split; intros H.
  apply H₁ in H.
  destruct H as [H| H]; [ left; now left | ].
  destruct H as [H| H]; [ left; now right | ].
  now right.

  apply H₂.
  destruct H as [[H| H]| H]; [ now left | right; now left | ].
  right; now right.

 intros i j Hij.
 destruct i.
  unfold intersection, set_eq; simpl.
  intros x.
  split; [ | easy ].
  intros (H₁, H₂).
  destruct j; [ now apply Hij | clear Hij ].
  destruct H₁ as [H₁| H₁].
   eapply Hi with (i := O) (j := S (S j)); [ easy | ].
   unfold intersection; simpl.
   split; eassumption.

   eapply Hi with (i := 1%nat) (j := S (S j)); [ easy | ].
   unfold intersection; simpl.
   split; eassumption.

  unfold intersection, union, set_eq; simpl.
  intros x.
  split; [ | easy ].
  intros (H₁ & H₂).
  destruct j.
   destruct H₂ as [H₂| H₂].
    eapply Hi with (i := O) (j := S (S i)); [ easy | ].
    unfold intersection; simpl.
    split; eassumption.

    eapply Hi with (i := 1%nat) (j := S (S i)).
     easy.

     unfold intersection; simpl.
     split; eassumption.

  apply Hi with (i := S (S i)) (j := S (S j)) (x := x).
   intros H; apply Hij.
   now apply Nat.succ_inj.

   unfold intersection; simpl.
   now split.
Qed.

Theorem is_partition_union_subtract :
  ∀ A (F : set A) P₁ P₂ Pl (B : set A),
  is_partition F (P₁ :: P₂ :: Pl)
  → (B ⊂ P₂)%S
  → is_partition F (P₁ ∪ B :: P₂ ∖ B :: Pl)%S.
Proof.
intros A F P₁ P₂ Pl B Hp HB.
destruct Hp as (Hu & Hi).
split.
 unfold union_list, union, subtract, set_eq in Hu |-*.
 simpl in Hu |-*.
 intros x.
 split; intros H.
  pose proof Hu x as H₁.
  destruct H₁ as (H₁ & H₂).
  pose proof H₁ H as H₃.
  destruct H₃ as [H₃| H₃]; [ left; now left | ].
  destruct H₃ as [H₃| H₃]; [ | right; now right ].
  destruct (EM (x ∈ B)) as [H₄| H₄]; [ left; now right | ].
  right; left; now split.

  apply Hu.
  destruct H as [[H₁| H₁]| [H₁| H₁]]; [ now left | | | ].
   right; left; now apply HB.

   right; left; now destruct H₁.

   right; now right.

 intros i j Hij.
 destruct i.
  unfold intersection, union, subtract, set_eq; simpl.
  intros x.
  split; [ | easy ].
  intros (H₁, H₂).
  destruct j; [ now apply Hij | clear Hij ].
  destruct H₁ as [H₁| H₁].
   eapply Hi with (i := O) (j := S j); [ easy | ].
   unfold intersection; simpl.
   split; [ eassumption | ].
   destruct j; [ now destruct H₂ | easy ].

   eapply Hi with (i := 1%nat) (j := S j).
    destruct j; [ now destruct H₂ | easy ].

    unfold intersection; simpl.
    split; [ apply HB; eassumption | ].
    destruct j; [ now destruct H₂ | easy ].

  unfold intersection, union, subtract, set_eq; simpl.
  intros x.
  split; [ | easy ].
  intros (H₁ & H₂).
  destruct j.
   destruct H₂ as [H₂| H₂].
    eapply Hi with (i := O) (j := S i); [ easy | ].
    unfold intersection; simpl.
    split; [ eassumption | ].
    destruct i; [ now destruct H₁ | easy ].

    eapply Hi with (i := 1%nat) (j := S i).
     destruct i; [ | easy ].
     now destruct H₁.

     unfold intersection; simpl.
     split; [ apply HB; eassumption | ].
     destruct i; [ now apply HB | easy ].

  apply Hi with (i := S i) (j := S j) (x := x).
   intros H; now apply Hij.

   unfold intersection; simpl.
   split.
    destruct i; [ now destruct H₁ | easy ].

    destruct j; [ now destruct H₂ | easy ].
Qed.

Theorem partition_union :
  ∀ A (F₁ F₂ : set A) P₁ P₂,
  (F₁ ∩ F₂ = ∅)%S
  → is_partition F₁ P₁
  → is_partition F₂ P₂
  → is_partition (F₁ ∪ F₂) (P₁ ++ P₂).
Proof.
intros * HFF HF₁ HF₂.
destruct HF₁ as (HF₁ & HP₁).
destruct HF₂ as (HF₂ & HP₂).
split.
 rewrite union_list_app.
 transitivity (F₁ ∪ ⋃ P₂).
  intros x.
  split; intros H.
   destruct H as [H| H]; [ now left | right ].
   now apply HF₂.

   destruct H as [H| H]; [ now left | right ].
   now apply HF₂.

  split; intros H.
   destruct H as [H| H]; [ left | now right ].
   now apply HF₁.

   destruct H as [H| H]; [ left | now right ].
   now apply HF₁.

 intros * Hij.
 unfold intersection, set_eq; simpl.
 intros x.
 split; intros H; [ | easy ].
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
     now rewrite nth_overflow in H₂.

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
     now rewrite nth_overflow in H₁.

   apply Nat.nlt_ge in H₄.
   eapply HP₂; [ | split; [ apply H₁ | apply H₂] ].
   intros H.
   apply Nat.add_cancel_l with (p := length P₁) in H.
   rewrite Nat.add_sub_assoc in H; [ | easy ].
   rewrite Nat.add_sub_assoc in H; [ | easy ].
   rewrite Nat.add_comm, Nat.add_sub in H.
   rewrite Nat.add_comm, Nat.add_sub in H.
   easy.
Qed.

Theorem is_partition_single : ∀ A (E : set A), is_partition E [E].
Proof.
intros.
split; [ symmetry; now eapply union_empty_r | ].
intros * Hij.
destruct i.
 destruct j; [ exfalso; now apply Hij | ].
 destruct j.
  split; [ now intros (_, H) | easy ].
  split; [ now intros (_, H) | easy ].

 split; [ intros (H, _) | easy ].
 now destruct i.
Qed.

Add Parametric Morphism {A} : (@is_partition A)
 with signature set_eq ==> eq ==> iff
 as is_partition_morph.
Proof.
intros E F HEF SL.
unfold is_partition.
rewrite <- HEF.
now split.
Qed.

Theorem is_partition_subtract : ∀ A (E F : set A),
  F ⊂ E
  → is_partition E [F; E ∖ F].
Proof.
intros * HF.
split.
 simpl; rewrite union_empty_r.
 intros v; split; intros H.
  now destruct (EM (v ∈ F)) as [Hi| Hni]; [ left | right ].

  now destruct H as [H| H]; [ apply HF | destruct H ].

 intros i j Hij.
 destruct i.
  destruct j; [ easy | ].
  destruct j.
   intros v.
   now split; intros Hv; [ simpl in Hv | ].

   simpl; rewrite match_id.
   apply intersection_empty_r.

  destruct j.
   destruct i.
    intros v.
    now split; intros Hv; [ simpl in Hv | ].

    simpl; rewrite match_id.
    apply intersection_empty_l.

   destruct i.
    destruct j; [ easy | ].
    simpl; rewrite match_id.
    apply intersection_empty_r.

    destruct j.
     simpl; rewrite match_id.
     apply intersection_empty_l.

     simpl; do 2 rewrite match_id.
     apply intersection_empty_l.
Qed.
