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

Theorem letter_opp_x_xi : ∀ x d, letter_opp (E x d) (E x (negb d)).
Proof.
intros.
unfold letter_opp.
destruct (letter_dec x x) as [H| H]; [ clear H | apply H; reflexivity ].
destruct (Bool.bool_dec d (negb d)) as [H| H]; [ | constructor ].
destruct d; discriminate H.
Qed.

Theorem not_letter_opp_x_x : ∀ x d, ¬ letter_opp (E x d) (E x d).
Proof.
intros.
unfold letter_opp.
destruct (letter_dec x x) as [H| H]; [ clear H | ].
 destruct (Bool.bool_dec d d) as [H| H]; [ intros H₁; assumption | ].
 exfalso; apply H; reflexivity.

 exfalso; apply H; reflexivity.
Qed.

Theorem neq_negb : ∀ x y, x ≠ y → x = negb y.
Proof.
intros.
destruct x, y; try reflexivity; exfalso; apply H; reflexivity.
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

Theorem norm_list_impossible_consecutive : ∀ x d el el₁ el₂,
  norm_list el ≠ el₁ ++ E x d :: E x (negb d) :: el₂.
Proof.
intros.
revert el₁.
induction el as [| e₁]; intros; [ intros H; destruct el₁; discriminate H | ].
simpl; remember (norm_list el) as nl eqn:Hnl; symmetry in Hnl.
destruct nl as [| e₂].
 clear; intros H.
 destruct el₁ as [| e₂]; intros; [ discriminate H | simpl in H ].
 injection H; clear H; intros; subst e₂.
 destruct el₁; discriminate H.

 destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
  pose proof IHel (e₂ :: el₁) as H₂; simpl in H₂.
  intros H; apply H₂; f_equal; apply H.

  unfold letter_opp in H₁.
  destruct e₁ as (x₁, d₁).
  destruct e₂ as (x₂, d₂).
  destruct (letter_dec x₁ x₂) as [H₂| H₂].
   subst x₂.
   destruct (Bool.bool_dec d₁ d₂) as [H₂| H₂].
    clear H₁; subst d₂.
    destruct el₁ as [| e₁].
     simpl; intros H.
     injection H; clear H; intros H₁ H₂ H₃ H₄ H₅.
     subst d₁; destruct d; discriminate H₄.

     simpl; intros H.
     injection H; clear H; intros H₁ H₂; subst e₁.
     eapply IHel, H₁.

    exfalso; apply H₁; constructor.

   clear H₁.
   destruct el₁ as [| e₁].
    simpl; intros H.
    injection H; clear H; intros H₁ H₃ H₄ H₅ H₆.
    subst x₁ x₂; apply H₂; reflexivity.

    simpl; intros H.
    injection H; clear H; intros H₁ H₃.
    eapply IHel, H₁.
Qed.

Theorem norm_list_impossible_start : ∀ x d el el',
  norm_list el ≠ E x d :: E x (negb d) :: el'.
Proof.
intros.
apply (norm_list_impossible_consecutive x d el nil el').
Qed.

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
 destruct (letter_dec x x') as [Hx| Hx]; [ | contradiction ].
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
   destruct (letter_dec x x'') as [Hx| Hx]; [ | contradiction ].
   exfalso; subst x''.
   destruct (Bool.bool_dec d' d'') as [Hd'| Hd']; [ contradiction | ].
   clear He.
   destruct d''.
    apply Bool.not_true_iff_false in Hd'; subst d'.
    revert Hel''; apply norm_list_impossible_start.

    apply Bool.not_false_iff_true in Hd'; subst d'.
    revert Hel''; apply norm_list_impossible_start.

   injection IHel; intros H; apply H.

 remember (e' :: el') as el'' eqn:Hel''; simpl.
 destruct el'' as [| e'']; [ reflexivity | ].
 rewrite IHel.
 destruct (letter_opp_dec e e'') as [H₁| H₁]; [ | reflexivity ].
 injection Hel''; clear Hel''; intros; subst e'' el''.
 contradiction.
Qed.

Theorem norm_norm : ∀ s, norm (norm s) = norm s.
Proof.
intros.
unfold norm; f_equal.
apply norm_list_norm_list.
Qed.

Theorem norm_list_subst : ∀ e el el',
  norm_list el = el' → norm_list (e :: el) = norm_list (e :: el').
Proof.
intros e el el' Hel.
subst el'; simpl.
rewrite norm_list_norm_list.
reflexivity.
Qed.

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
destruct (letter_opp_dec a a⁻¹) as [H| H]; [ reflexivity | ].
exfalso; apply H, letter_opp_x_xi.
Qed.

Theorem norm_list_x_xi : ∀ x d el,
  norm_list (E x d :: E x (negb d) :: el) = norm_list el.
Proof.
intros.
remember (E x d) as xd eqn:Hxd.
remember (E x (negb d)) as xe eqn:Hxe.
move xe before xd.
simpl.
remember (norm_list el) as el' eqn:Hel'; symmetry in Hel'.
destruct el' as [| e el'].
 destruct (letter_opp_dec xd xe) as [H₁| H₁]; [ reflexivity | ].
 exfalso; subst xd xe; apply H₁, letter_opp_x_xi.

 destruct (letter_opp_dec xe e) as [H₁| H₁].
  unfold letter_opp in H₁.
  destruct xe as (x₁, d₁).
  injection Hxe; clear Hxe; intros; subst x₁ d₁.
  destruct e as (x₂, d₂).
  destruct (letter_dec x x₂) as [H₂| H₂]; [ | contradiction ].
  destruct (Bool.bool_dec (negb d) d₂) as [H₃| H₃]; [ contradiction | ].
  clear H₁; apply not_eq_sym in H₃.
  apply neq_negb in H₃.
  rewrite Bool.negb_involutive in H₃; subst x₂ d₂.
  rewrite <- Hxd in Hel'; rewrite <- Hxd.
  destruct el' as [| e']; [ reflexivity | ].
  destruct (letter_opp_dec xd e') as [H₁| H₁]; [ | reflexivity ].
  exfalso; subst xd.
  unfold letter_opp in H₁.
  destruct e' as (x₁, d₁).
  destruct (letter_dec x x₁) as [H₂| H₂]; [ | contradiction ].
  destruct (Bool.bool_dec d d₁) as [H₃| H₃]; [ contradiction | clear H₁ ].
  apply not_eq_sym, neq_negb in H₃; subst x₁ d₁.
  revert Hel'; apply norm_list_impossible_start.

  destruct (letter_opp_dec xd xe) as [H₂| H₂]; [ reflexivity | exfalso ].
  subst xd xe.
  apply H₂, letter_opp_x_xi.
Qed.

Theorem norm_x_xi : ∀ x d el,
  norm (mkF₂ (E x d :: E x (negb d) :: el)) = norm (mkF₂ el).
Proof.
intros.
unfold norm; f_equal.
remember norm_list as f; simpl; subst f.
apply norm_list_x_xi.
Qed.

Theorem start_with_xi_start_with2_x_xi : ∀ s x,
  start_with (E x true) s
  → start_with2 (E x false) (E x true) s.
Proof.
intros s x H.
unfold start_with in H.
unfold start_with2; simpl.
destruct s as (el); simpl in H.
unfold norm.
remember norm_list as f; simpl; subst f.
remember (norm_list el) as ns eqn:Hns; symmetry in Hns.
destruct ns as [| x₁]; [ contradiction | subst x₁ ].
exists (mkF₂ (E x true :: E x true :: ns)).
remember norm_list as f; simpl; subst f.
rewrite norm_list_x_xi.
rewrite <- Hns.
split; [ f_equal; symmetry; apply norm_list_norm_list | ].
unfold start_with; simpl.
rewrite Hns; simpl.
remember (norm_list ns) as ns₁ eqn:Hns₁; symmetry in Hns₁.
set (xt := E x true).
destruct ns₁ as [| e₁].
 destruct (letter_opp_dec xt xt) as [H₁| H₁]; [ | reflexivity ].
 revert H₁; apply not_letter_opp_x_x.

 destruct (letter_opp_dec xt e₁) as [H₁| H₁].
  destruct ns₁ as [| e₂]; [ reflexivity | ].
  destruct (letter_opp_dec xt e₂) as [H₂| H₂].
   exfalso; subst xt.
   unfold letter_opp in H₁, H₂.
   destruct e₁ as (x₁, d₁).
   destruct e₂ as (x₂, d₂).
   destruct (letter_dec x x₁) as [H₃| H₃].
    destruct (Bool.bool_dec true d₁) as [H₄| H₄]; [ contradiction | ].
    apply not_eq_sym, Bool.not_true_iff_false in H₄.
    subst x₁ d₁; clear H₁.
    destruct (letter_dec x x₂) as [H₁| H₁].
     destruct (Bool.bool_dec true d₂) as [H₄| H₄]; [ contradiction | ].
     apply not_eq_sym, Bool.not_true_iff_false in H₄.
     subst x₂ d₂; clear H₂.
bbb.

 destruct s as (el); simpl in H.
 destruct el as [| e]; [ contradiction | simpl in H ].
 destruct el as [| e₁].
  simpl in H; subst e.
  exists (mkF₂ (a⁻¹ :: a⁻¹ :: nil)); simpl.
  split; [ rewrite norm_x_xi; reflexivity | ].
  unfold start_with; simpl.
  destruct (letter_opp_dec a⁻¹ a⁻¹) as [H₁| H₁]; [ | reflexivity ].
  revert H₁; apply not_letter_opp_x_x.

  remember (norm_list (e₁ :: el)) as nl eqn:Hnl; symmetry in Hnl.
  destruct nl as [| e₂].
   subst e.
   unfold norm.
   exists (mkF₂ (a⁻¹ :: a⁻¹ :: nil)).
   remember norm_list as f; simpl; subst f.
   split.
    f_equal.
    erewrite norm_list_subst; [ | eassumption ].
    symmetry; apply norm_list_x_xi.

    unfold start_with; simpl.
    destruct (letter_opp_dec a⁻¹ a⁻¹) as [H₁| H₁]; [ | reflexivity ].
    revert H₁; apply not_letter_opp_x_x.

   destruct (letter_opp_dec e e₂) as [H₁| H₁].
    destruct nl as [| e₃]; [ contradiction | subst e₃ ].
    simpl in Hnl.
    remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
    destruct el₁ as [| e₃]; [ discriminate Hnl | ].
    destruct (letter_opp_dec e₁ e₃) as [H₂| H₂].
     subst el₁.
Admitted.
*)

Theorem decomposed_2_a : ∀ s, start_with2 a a⁻¹ s ∨ start_with a s.
Proof.
intros s.
destruct (decomposed_4 s) as [H| [H| [H| [H|H]]]].
 left; apply empty_start_with2_a_ai; assumption.

 right; assumption.

 left; apply start_with_xi_start_with2_x_xi; assumption.
bbb.

 remember (norm s) as ns eqn:Hns; symmetry in Hns.
 destruct ns as (el); simpl in H.
 destruct el as [| e el]; [ contradiction | ].
 subst e; unfold start_with; rewrite Hns; simpl.
 left.
 exists (mkF₂ (a⁻¹ :: a⁻¹ :: el)).
 split.
  simpl.
  remember (a⁻¹ :: el) as el' eqn:Hel'.
  unfold norm; f_equal.
  remember norm_list as f; simpl; subst f; simpl.
  remember (norm_list el') as el'' eqn:Hel''; symmetry in Hel''.
  destruct el'' as [| e'' ].
  destruct (letter_opp_dec a a⁻¹) as [H₁| H₁].
   destruct el' as [| e']; [ discriminate Hel' | ].
   injection Hel'; clear Hel'; intros; subst e' el'.
   simpl in Hel''.
   remember (norm_list el) as el' eqn:Hel'; symmetry in Hel'.
   destruct el' as [| e']; [ discriminate Hel'' | ].
   destruct (letter_opp_dec a⁻¹ e') as [H₂| H₂].
    subst el'.
    injection Hns; clear Hns; intros.

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
