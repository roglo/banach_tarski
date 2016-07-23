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

Fixpoint norm_list el :=
  match el with
  | nil => nil
  | E l₁ d₁ :: nil => el
  | E l₁ d₁ :: (E l₂ d₂ :: el₂) as el₁ =>
      if letter_dec l₁ l₂ then
        if Bool.bool_dec d₁ d₂ then E l₁ d₁ :: norm_list el₁
        else norm_list el₂
      else E l₁ d₁ :: norm_list el₁
  end.

Definition norm s := mkF₂ (norm_list (str s)).

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
  ∃ t, s = norm (mkF₂ (x :: str t)) ∧ start_with y t.

(*
Theorem glop : ∀ el,
  norm_list el = nil ↔
  el = nil ∨
  ∃ x d el', el = List.app (E x d :: el') (E x (negb d) :: nil) ∧
             norm_list el' = nil ∨
  ∃ el₁ el₂, el = List.app el₁ el₂ ∧ norm_list el₁ = nil ∧
             norm_list el₂ = nil.
Proof.
intros el.
split; intros H.
 induction el as [| (x, d) el]; [ left; reflexivity | right ].
 simpl in H.
 destruct el as [| (x1, d1) el]; [ discriminate H | ].
 destruct (letter_dec x x1) as [H₁| H₁].
  subst x1.
  destruct (Bool.bool_dec d d1) as [H₁| H₁]; [ discriminate H | ].
  destruct d1.
   apply Bool.not_true_iff_false in H₁; subst d.
bbb.
*)

Theorem empty_start_with2_a_ai : ∀ s, is_empty s → start_with2 a a⁻¹ s.
Proof.
intros s H.
unfold is_empty in H.
unfold start_with2.
bbb.

destruct s as (el); simpl in H.
unfold start_with2.
bbb.

exists (mkF₂ (a⁻¹ :: el)).
split.
 Focus 2.
bbb.

destruct el as [| (x1, d1)].
 exists (mkF₂ (a⁻¹ :: nil)); clear H; simpl.
 split; [ | reflexivity ].
 unfold norm; simpl.
 destruct (letter_dec la la) as [H| H]; [ reflexivity | ].
 exfalso; apply H; reflexivity.

 revert x1 d1 H.
 induction el as [| (x2, d2)]; intros; [ discriminate H | ].
 simpl in H.
 destruct (letter_dec x1 x2) as [H₁| H₁].
  subst x2.
  destruct (Bool.bool_dec d1 d2) as [H₁| H₁]; [ discriminate H | ].
  unfold start_with2; simpl.
  exists (mkF₂ (a⁻¹ :: el)).
  split; simpl.
bbb.

   destruct el as [| (x3, d3)]; [ | reflexivity ].
   simpl in H; simpl.
   destruct el as [| (x4, d4)]; [ discriminate H | ].
   destruct (letter_dec x3 x4) as [H₂| H₂].
    subst x4.
    destruct (Bool.bool_dec d3 d4) as [H₂| H₂]; [ discriminate H | ].
    destruct (letter_dec x3 la) as [H₃| H₃].
     subst x3.
     destruct d3.
bbb.
  split; [ reflexivity | simpl ].
  destruct (letter_dec x1 la) as [H₂| H₂].
   subst x1.
bbb.

Theorem decomposed_2_a : ∀ s, start_with2 a a⁻¹ s ∨ start_with a s.
Proof.
intros s.
destruct (decomposed_4 s) as [H| [H| [H| [H|H]]]].
 left.
bbb.
 exists (mkF₂ (a⁻¹ :: str s)).
 split.
  unfold start_with; simpl.
  destruct s as (el); simpl.
   unfold is_empty in H; simpl in H.
   destruct el as [| (x, d)]; [ reflexivity | ].
   simpl in H.
   destruct el as [| (x1, d1)]; [ discriminate H | ].
   destruct (letter_dec x x1) as [H₁| H₁].
    subst x1.
    destruct (Bool.bool_dec d d1) as [H₁| H₁]; [ discriminate H | ].
    destruct (letter_dec la x) as [H₂| H₂].
     subst x.
     destruct d; [ reflexivity | simpl ].
     destruct el as [| (x2, d2)].
      destruct d1; [ reflexivity | ].
      exfalso; apply H₁; reflexivity.

destruct (letter_dec la x2) as [H₂| H₂].
subst x2.
destruct (Bool.bool_dec d1 d2) as [H₂| H₂].
subst d2.
destruct d1; [ reflexivity | ].
exfalso; apply H₁; reflexivity.
simpl in H.
destruct el as [| (x3, d3)]; [discriminate H | ].
destruct (letter_dec la x3) as [H₃| H₃].
subst x3.
simpl.
bbb.

simpl in H.
split; [ reflexivity | simpl ].
 unfold norm; simpl.
 destruct (letter_dec la la) as [H₁| H₁].
  unfold is_empty in H.

, norm, norm_list in H.
  simpl in H.

bbb.
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

bbb.
1 subgoal, subgoal 1 (ID 119)
  
  letter : Type
  la, lb : letter
  la_neq_lb : la ≠ lb
  only_letters : ∀ l : letter, {l = la} + {l = lb}
  letter_dec : ∀ l1 l2 : letter, {l1 = l2} + {l1 ≠ l2}
  x1 : letter
  d1 : bool
  el : list free_elem
  IHel : ∀ (x : letter) (d : bool),
         start_with2 a a⁻¹ {| str := E x d :: el |}
         ∨ start_with a {| str := E x d :: el |}
  x : letter
  d : bool
  ============================
   start_with2 a a⁻¹ {| str := E x d :: E x1 d1 :: el |}
   ∨ start_with a {| str := E x d :: E x1 d1 :: el |}

bbb.

  destruct (only_letters x); subst x.
   destruct d.

pose proof IHel x1 d1 as H.
destruct H as [H| H].
destruct H as (s, (H₁, H₂)).
unfold norm in H₂.
injection H₂; clear H₂; intros H₂.
destruct s as (el').
simpl in H₂.

    left.
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
