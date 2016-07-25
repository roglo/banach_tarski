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

Definition letter_opp '(E l₁ d₁) '(E l₂ d₂) :=
  if letter_dec l₁ l₂ then
    if Bool.bool_dec d₁ d₂ then False else True
  else False.

Theorem letter_opp_dec : ∀ e₁ e₂,
  {letter_opp e₁ e₂} + {not (letter_opp e₁ e₂)}.
Proof.
intros.
destruct e₁ as (x₁, d₁).
destruct e₂ as (x₂, d₂); simpl.
destruct (letter_dec x₁ x₂) as [Hx| Hx].
 destruct (Bool.bool_dec d₁ d₂) as [Hd| Hd]; [ | left; constructor ].
 right; intros H; contradiction.

 right; intros H; contradiction.
Qed.

Fixpoint norm_list el :=
  match el with
  | nil => nil
  | e₁ :: el₁ =>
      match norm_list el₁ with
      | nil => e₁ :: nil
      | e₂ :: el₂ => if letter_opp_dec e₁ e₂ then el₂ else e₁ :: e₂ :: el₂
      end
  end.

Definition norm s := mkF₂ (norm_list (str s)).

(**)
Theorem norm_list_impossible_consecutive : ∀ x d el el₁ el₂,
  norm_list el ≠ el₁ ++ E x d :: E x (negb d) :: el₂.
Proof.
intros.
revert el₁.
induction el as [| e₁]; intros; [ intros H; destruct el₁; discriminate H | ].
simpl; remember (norm_list el) as nl eqn:Hnl in |-*; symmetry in Hnl.
destruct nl as [| e₂].
 clear; intros H.
 destruct el₁ as [| e₂]; intros; [ discriminate H | simpl in H ].
 injection H; clear H; intros; subst e₂.
 destruct el₁; discriminate H.

 destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
  intros H.
  assert (H₂ : e₂ :: nl = e₂ :: el₁ ++ E x d :: E x (negb d) :: el₂).
   f_equal; assumption.

   rewrite <- Hnl in H₂.
   apply IHel with (el₁ := e₂ :: el₁), H₂.

  unfold letter_opp in H₁.
  destruct e₁ as (x₁, d₁).
  destruct e₂ as (x₂, d₂).
  destruct (letter_dec x₁ x₂) as [H₂| H₂].
   subst x₂.
   destruct (Bool.bool_dec d₁ d₂) as [H₂| H₂].
   2: exfalso; apply H₁; constructor.
   clear H₁; subst d₂.

bbb.


intros.
revert x d el₁ el₂.
induction el as [| e₁ el]; intros.
 intros H; destruct el₁; discriminate H.

 simpl.
 rename el₂ into el₃.
 destruct el as [| e₃ el].
  simpl; intros H.
  destruct el₁ as [| e₄]; [ discriminate H | ].
  destruct el₁; discriminate H.

  remember (norm_list (e₃ :: el)) as nl eqn:Hnl.
  symmetry in Hnl.
  destruct nl as [| e₂].
   clear; intros H.
   destruct el₁ as [| e₂]; intros; [ discriminate H | simpl in H ].
   injection H; clear H; intros; subst e₂.
   revert H; clear; intros.
   destruct el₁; discriminate H.

   destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
    simpl in Hnl.
    remember (norm_list el) as el₄ eqn:Hel₄; symmetry in Hel₄.
    destruct el₄ as [| e₄].
    injection Hnl; clear Hnl; intros; subst e₃ nl.
    intros H; destruct el₁; discriminate H.

    destruct (letter_opp_dec e₃ e₄) as [H₂| H₂].
     subst el₄.

bbb.
  simpl.
  destruct el as [| e3].
   simpl.
   destruct (letter_opp_dec e1 e2) as [H1| H1].
    intros H; destruct el1; discriminate H.

    destruct el1 as [| e3].
    intros H; injection H; clear H; intros; subst e1 e2 el2.
    apply H1; unfold letter_opp.
    destruct (letter_dec x x) as [H2| H2].
     destruct (Bool.bool_dec d (negb d)) as [H3| H3]; [ | constructor ].
     destruct d; discriminate H3.

     apply H2; reflexivity.

   intros H.
   destruct el1 as [| e4]; [ discriminate H | ].
   destruct el1; discriminate H.
bbb.
*)

Theorem norm_list_impossible_start : ∀ x d el el',
  norm_list el ≠ E x d :: E x (negb d) :: el'.
Proof.
intros.
destruct el as [| e₁]; [ intros H; discriminate H | simpl ].
remember (norm_list el) as nl eqn:Hnl; symmetry in Hnl.
destruct nl as [| e₂]; [ intros H; discriminate H | ].
destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
Print norm_list.
intros H.
SearchAbout (_ :: _ = _ :: _).
assert (H₂ : e₂ :: nl = e₂ :: E x d :: E x (negb d) :: el').
 f_equal; assumption.

 rewrite <- Hnl in H₂.

bbb.

remember (norm_list el) as nl eqn:Hnl; symmetry in Hnl.
revert x d el el' Hnl.
induction nl as [| e₁]; intros; [ intros H; discriminate H | ].
intros H; injection H; clear H.
intros; subst e₁ nl.

revert x d el'.
induction el as [| e1 el]; intros; [ intros H; discriminate H | simpl ].
destruct el as [| e2 el]; [ intros H; discriminate H | ].
remember (norm_list (e2 :: el)) as nl eqn:Hnl; symmetry in Hnl.
destruct nl as [| e3 nl]; [ intros H; discriminate H | ].
destruct (letter_opp_dec e1 e3) as [H1| H1].
bbb.


revert x d el.
induction el' as [| e1 el']; intros.
 destruct el as [| e1 el]; [ intros H; discriminate H | simpl ].
 destruct el as [| e2 el]; [ intros H; discriminate H | simpl ].
 destruct el as [| e3 el]; simpl.
  destruct (letter_opp_dec e1 e2) as [H1| H1]; [ intros H; discriminate H | ].
  intros H; injection H; clear H; intros; subst e1 e2.
  apply H1; unfold letter_opp.
  destruct (letter_dec x x) as [H2| H2].
   destruct (Bool.bool_dec d (negb d)) as [H3| H3]; [  | constructor ].
   destruct d; discriminate H3.

   apply H2; reflexivity.
bbb.


intros.
revert x d el'.
induction el as [| e1 el]; intros; [ intros H; discriminate H | simpl ].
destruct el as [| e2 el]; [ intros H; discriminate H | simpl ].
destruct el as [| e3 el]; simpl.
 destruct (letter_opp_dec e1 e2) as [H1| H1]; [ intros H; discriminate H |  ].
 intros H; injection H; clear H.
 intros; subst e1 e2 el'; simpl in H1.
 destruct (letter_dec x x) as [H| H]; [ clear H | apply H; reflexivity ].
 destruct (Bool.bool_dec d (negb d)) as [H| H]; [  | apply H1; constructor ].
 destruct d; discriminate H.

 destruct el as [| e4 el]; simpl.
  destruct (letter_opp_dec e2 e3) as [H| H]; [ intros H1; discriminate H1 |  ].
  destruct (letter_opp_dec e1 e2) as [H1| H1].
   intros H2; discriminate H2.

   intros H2; injection H2; clear H2; intros; subst e1 e2 el'.
   apply H1; unfold letter_opp.
   destruct (letter_dec x x) as [H2| H2].
    destruct (Bool.bool_dec d (negb d)) as [H3| H3]; [  | constructor ].
    destruct d; discriminate H3.

    apply H2; reflexivity.

  destruct el as [| e5 el]; simpl.
   destruct (letter_opp_dec e3 e4) as [H1| H1].
    destruct (letter_opp_dec e1 e2) as [| H2]; [ intros H; discriminate H | ].
    intros H; injection H; clear H; intros; subst e1 e2 el'.
    apply H2; unfold letter_opp.
    destruct (letter_dec x x) as [H| H]; [ clear H | apply H; reflexivity ].
    destruct (Bool.bool_dec d (negb d)) as [H| H]; [  | constructor ].
    destruct d; discriminate H.

    destruct (letter_opp_dec e2 e3) as [H2| H2].
     destruct (letter_opp_dec e1 e4) as [H3| H3].
      intros H; discriminate H.

      intros H; injection H; clear H; intros; subst e1 e4 el'.
      apply H3; unfold letter_opp.
      destruct (letter_dec x x) as [H| H]; [ clear H | apply H; reflexivity ].
      destruct (Bool.bool_dec d (negb d)) as [H| H]; [  | constructor ].
      destruct d; discriminate H.

     destruct (letter_opp_dec e1 e2) as [H3| H3].
      intros H; injection H; clear H; intros; subst e3 e4 el'.
      apply H1; unfold letter_opp.
      destruct (letter_dec x x) as [H| H]; [ clear H | apply H; reflexivity ].
      destruct (Bool.bool_dec d (negb d)) as [H| H]; [  | constructor ].
      destruct d; discriminate H.

      simpl.
      intros H; injection H; clear H; intros; subst e1 e2 el'.
      apply H3; unfold letter_opp.
      destruct (letter_dec x x) as [H| H]; [ clear H | apply H; reflexivity ].
      destruct (Bool.bool_dec d (negb d)) as [H| H]; [  | constructor ].
      destruct d; discriminate H.
bbb.

revert x d el'.
induction el as [| (x1, d1) el]; intros; [ intros H; discriminate H | ].
simpl.
remember (norm_list el) as el'' eqn:Hel''; symmetry in Hel''.
destruct el'' as [| (x2, d2) el'']; [ intros H; discriminate H | ].
destruct (letter_opp_dec (E x1 d1) (E x2 d2)) as [H1| H1].
 unfold letter_opp in H1.
 destruct (letter_dec x1 x2) as [H2| H2].
  subst x2.
  destruct (Bool.bool_dec d1 d2) as [H2| H2]; [ contradiction | clear H1 ].
  destruct (Bool.bool_dec d d2) as [H1| H1].
   subst d2.
bbb.
pose proof IHel x1 d as H1.
eapply H1.
f_equal.
bbb.

Theorem norm_list_norm_list : ∀ el, norm_list (norm_list el) = norm_list el.
Proof.
intros el.
induction el as [| e]; [ reflexivity | simpl ].
remember (norm_list el) as el' eqn:Hel'; symmetry in Hel'.
destruct el' as [| e']; [ reflexivity | ].
destruct (letter_opp_dec e e') as [H| H].
 unfold letter_opp in H.
 destruct e as (x, d).
 destruct e' as (x', d').
 destruct (letter_dec x x') as [Hx| Hx].
  subst x'.
  destruct (Bool.bool_dec d d') as [Hd| Hd]; [ contradiction | clear H ].
  simpl in IHel.
  remember (norm_list el') as el'' eqn:Hel''; symmetry in Hel''.
  destruct el'' as [| e''].
   injection IHel; clear IHel; intros H; assumption.

   destruct (letter_opp_dec (E x d') e'') as [He| He].
    subst el''.
    simpl in He.
    destruct e'' as (x'', d'').
    destruct (letter_dec x x'') as [Hx| Hx].
     exfalso; subst x''.
     destruct (Bool.bool_dec d' d'') as [Hd'| Hd']; [ contradiction | ].
     clear He.
     destruct d''.
      apply Bool.not_true_iff_false in Hd'; subst d'.
      revert Hel''; apply norm_list_impossible_start.
bbb.

Theorem norm_norm : ∀ s, norm (norm s) = norm s.
Proof.
intros.
destruct s as (el).
unfold norm; simpl; f_equal.
bbb.

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
  ∃ t, norm s = norm (mkF₂ (x :: str t)) ∧ start_with y t.

Theorem empty_start_with2_a_ai : ∀ s, is_empty s → start_with2 a a⁻¹ s.
Proof.
intros s H.
unfold is_empty in H.
unfold start_with2.
remember (norm s) as ns eqn:Hns; symmetry in Hns.
destruct ns as (el).
simpl in H; subst el.
exists (mkF₂ (a⁻¹ :: nil)); simpl.
unfold start_with, norm; simpl.
split; [ | reflexivity ].
destruct (letter_dec la la) as [H| H]; [ reflexivity | ].
exfalso; apply H; reflexivity.
Qed.

Theorem decomposed_2_a : ∀ s, start_with2 a a⁻¹ s ∨ start_with a s.
Proof.
intros s.
destruct (decomposed_4 s) as [H| [H| [H| [H|H]]]].
 left; apply empty_start_with2_a_ai; assumption.

 right; assumption.

 unfold start_with in H.
 unfold start_with2; simpl.
 remember (norm s) as ns eqn:Hns; symmetry in Hns.
 destruct ns as (el); simpl in H.
 destruct el as [| e el]; [ contradiction | ].
 subst e; unfold start_with; rewrite Hns; simpl.
 left.
 exists (mkF₂ (a⁻¹ :: a⁻¹ :: el)).
 split.
  simpl.
  remember (a⁻¹ :: el) as el' eqn:Hel'.

Theorem toto : ∀ el, norm (mkF₂ (a :: a⁻¹ :: el)) = norm (mkF₂ el).
Proof.
Admitted. Show.

symmetry.
etransitivity; [ apply toto | ].
rewrite <- Hns.
bbb.

  simpl; unfold norm; simpl.
  destruct (letter_dec la la) as [H| H].
   f_equal; clear H.
   destruct el as [| e el] ; [ reflexivity | ].
   destruct e as (x, d).
   destruct (letter_dec la x) as [H| H].
    subst x.
    destruct d.
     simpl; f_equal.
     destruct el as [| e el]; [ reflexivity | ].
     destruct e as (x, d).
     destruct (letter_dec la x) as [H| H].
      subst x.
      destruct d.
       simpl; f_equal.
       destruct el as [| e el]; [ reflexivity | ].


bbb.

End Free_Group.
