Require Import Utf8.
Require Import List.

Theorem neq_negb : ∀ x y, x ≠ y → x = negb y.
Proof.
intros.
destruct x, y; try reflexivity; exfalso; apply H; reflexivity.
Qed.

Theorem cons_to_app : ∀ A (x : A) l, x :: l = (x :: nil) ++ l.
Proof. reflexivity. Qed.

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

Theorem letter_opp_iff : ∀ x₁ d₁ x₂ d₂,
  letter_opp (E x₁ d₁) (E x₂ d₂)
  ↔ x₁ = x₂ ∧ d₂ = negb d₁.
Proof.
intros x₁ d₁ x₂ d₂.
split; intros H.
 unfold letter_opp in H.
 destruct (letter_dec x₁ x₂) as [H₁| H₁]; [ | contradiction ].
 split; [ assumption | ].
 destruct (Bool.bool_dec d₁ d₂) as [H₂| H₂]; [ contradiction | ].
 apply neq_negb, not_eq_sym; assumption.

 destruct H; subst x₂ d₂.
 apply letter_opp_x_xi.
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

Theorem norm_list_single : ∀ e, norm_list (e :: nil) = e :: nil.
Proof. reflexivity. Qed.

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
revert x el Hns.
induction ns as [| e]; intros.
 rewrite Hns; unfold start_with; simpl.
 set (e := E x true).
 destruct (letter_opp_dec e e) as [H₁| H₁]; [ | reflexivity ].
 revert H₁; apply not_letter_opp_x_x.

 rewrite Hns; unfold start_with; simpl.
 remember (norm_list ns) as ns₁ eqn:Hns₁; symmetry in Hns₁.
 destruct ns₁ as [| e₁].
  set (e₁ := E x true).
  destruct (letter_opp_dec e₁ e) as [H₁| H₁]; [ reflexivity | ].
  destruct (letter_opp_dec e₁ e₁) as [H₂| H₂]; [ | reflexivity ].
  exfalso; revert H₂; apply not_letter_opp_x_x.

  destruct (letter_opp_dec e e₁) as [H₁| H₁].
   exfalso.
   destruct e as (x₁, d₁).
   destruct e₁ as (x₂, d₂).
   apply letter_opp_iff in H₁.
   destruct H₁; subst x₂ d₂.
Theorem glop : ∀ el el₁ el₂,
  norm_list el = el₁ ++ el₂
  → norm_list el = norm_list el₁ ++ norm_list el₂.
Proof.
intros el el₁ el₂ Hel.
revert el el₁ Hel.
induction el₂ as [| e]; intros.
 rewrite app_nil_r in Hel; rewrite app_nil_r.
 rewrite <- norm_list_norm_list, Hel.
 reflexivity.

 rewrite cons_to_app in Hel.
 rewrite app_assoc in Hel.
 apply IHel₂ in Hel.
 rewrite Hel.
Theorem pouet : ∀ el₁ el₂,
  norm_list (el₁ ++ el₂) = norm_list (norm_list el₁ ++ norm_list el₂).
Proof.
intros.
revert el₁.
induction el₂ as [| e₂]; intros.
 simpl; do 2 rewrite app_nil_r.
 symmetry; apply norm_list_norm_list.

 rewrite cons_to_app.
 rewrite app_assoc, IHel₂.
 revert e₂ el₂ IHel₂.
 induction el₁ as [| e₁]; intros.
  do 2 rewrite app_nil_l.
  remember norm_list as f; simpl; subst f.
  rewrite norm_list_norm_list.
  symmetry; rewrite cons_to_app.
  apply IHel₂.

  rewrite <- cons_to_app.
  rewrite <- IHel₂.
  remember norm_list as f; simpl; subst f.
  simpl.
Abort. (*
bbb.

  simpl; rewrite norm_list_norm_list.
  remember (norm_list el₂) as el₃ eqn:Hel₂; symmetry in Hel₂.
  destruct el₃ as [| e₃]; [ reflexivity | ].
  destruct (letter_opp_dec e₂ e₃) as [H₁| H₁].
   unfold letter_opp in H₁.
   destruct e₂ as (x₂, d₂).
   destruct e₃ as (x₃, d₃).
   destruct (letter_dec x₂ x₃) as [H₂| H₂].
    destruct (Bool.bool_dec d₂ d₃) as [H₃| H₃]; [ contradiction | ].
    apply not_eq_sym, neq_negb in H₃.
    subst x₃ d₃; clear H₁.
    destruct el₃ as [| e₃]; [ reflexivity | simpl ].
    remember (norm_list el₃) as el₄ eqn:Hel₃; symmetry in Hel₃.
    destruct el₄ as [| e₄].
     f_equal.


SearchAbout norm_list.
*)
Theorem agaga : ∀ el e el₁,
  norm_list el = e :: el₁
  → el₁ = norm_list el₁.
Proof.
intros el e el₁ Hel.
revert e el₁ Hel.
induction el as [| e₁]; intros; [ discriminate Hel | simpl in Hel ].
remember (norm_list el) as el₂ eqn:Hel₂; symmetry in Hel₂.
destruct el₂ as [| e₂]; [ injection Hel; intros; subst el₁; reflexivity | ].
destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
 subst el₂.
 pose proof IHel e₂ (e :: el₁) (eq_refl _) as H₂.
 symmetry in H₂.
 simpl in H₂.
 remember (norm_list el₁) as el₂ eqn:Hel₃; symmetry in Hel₃.
 destruct el₂ as [| e₃]; [ injection H₂; intros; subst el₁; reflexivity | ].
 destruct (letter_opp_dec e e₃) as [H₃| H₃].
  subst el₂; exfalso.
bbb.

 destruct el as [| e₃]; [ discriminate Hel₂ | simpl in Hel₂ ].
 remember (norm_list el) as el₃ eqn:Hel₃; symmetry in Hel₃.
 destruct el₃ as [| e₄]; [ discriminate Hel₂ | ].
 destruct (letter_opp_dec e₃ e₄) as [H₂| H₂].
  subst el₃.
  destruct el as [| e₅]; [ discriminate Hel₃ | simpl in Hel₃ ].
  remember (norm_list el) as el₂ eqn:Hel₄; symmetry in Hel₄.
  destruct el₂ as [| e₆]; [ discriminate Hel₃ | ].
  destruct (letter_opp_dec e₅ e₆) as [H₃| H₃].
   subst el₂.

(*
revert e el Hel.
induction el₁ as [| e₁]; intros; [ reflexivity | ].
simpl.
remember (norm_list el₁) as el₂ eqn:Hel₂; symmetry in Hel₂.
destruct el₂ as [| e₂].
 f_equal.
*)
revert e el₁ Hel.
induction el as [| e₁]; intros; [ discriminate Hel | ].
simpl in Hel.
remember (norm_list el) as el₂ eqn:Hel₂ in Hel; symmetry in Hel₂.
destruct el₂ as [| e₂].
 injection Hel; clear Hel; intros; subst e₁ el₁; reflexivity.

 destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
  subst el₂.
  apply IHel in Hel₂.

Theorem oups2 : ∀ e el el',
  norm_list el = e :: el'
  → el' = norm_list el'.
Proof.
intros e el el' Hel.
remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
revert e el el' Hel₁ Hel.
induction el₁ as [| e₁]; intros; [ discriminate Hel | ].
injection Hel; clear Hel; intros; subst e el₁.
bbb.

revert e el' Hel.
induction el as [| e₁]; intros; [ discriminate Hel | ].
simpl in Hel.
remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
destruct el₁ as [| e₂].
 injection Hel; clear Hel; intros; subst e₁ el'.
 reflexivity.

bbb.
 destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
  subst el₁.
  destruct e₁ as (x₁, d₁).
  destruct e₂ as (x₂, d₂).
  apply letter_opp_iff in H₁.
  destruct H₁; subst x₂ d₂.

remember (norm_list el') as el₁ eqn:Hel₁; symmetry in Hel₁.
destruct el₁ as [| e₁].
 f_equal.

bbb.

symmetry in Hel₂.
eapply oups2; eassumption.

bbb.

Theorem oups : ∀ e el₁ el₂,
  norm_list (e :: el₁) = e :: el₂
  → el₂ = norm_list el₂.
Proof.
intros e el₁ el₂ Hel.
revert e el₂ Hel.
induction el₁ as [| e₁]; intros.
 injection Hel; intros; subst el₂; reflexivity.

 simpl in Hel.
 remember (norm_list el₁) as el₃ eqn:Hel₁; symmetry in Hel₁.
 destruct el₃ as [| e₃].
  destruct (letter_opp_dec e e₁) as [H₁| H₁]; [ discriminate Hel | ].
  injection Hel; clear Hel; intros; subst el₂.
  reflexivity.

  destruct (letter_opp_dec e₁ e₃) as [H₁| H₁].
   destruct el₃ as [| e₂].
    injection Hel; clear Hel; intros; subst el₂; reflexivity.

    destruct (letter_opp_dec e e₂) as [H₂| H₂].
     subst el₃.
     unfold letter_opp in H₂.
     destruct e as (x, d).
     destruct e₂ as (x₂, d₂).
     destruct (letter_dec x x₂) as [H₃| H₃]; [ | contradiction ].
     destruct (Bool.bool_dec d d₂) as [H₄| H₄]; [ contradiction | ].
     apply neq_negb in H₄; subst x₂ d; clear H₂.
     exfalso; revert Hel₁.
     rewrite cons_to_app.
     apply norm_list_impossible_consecutive.

     injection Hel; clear Hel; intros; subst el₂.
bbb.

symmetry in Hel₂.
eapply oups; eassumption.

bbb.

eapply agaga; eassumption.
contradiction.

bbb.

rewrite pouet.
remember (norm_list el₁) as el₃ eqn:Hel₃; symmetry in Hel₃.
destruct el₃ as [| e₃].
 simpl.
 remember (norm_list el₂) as el₄ eqn:Hel₄; symmetry in Hel₄.
 destruct el₄ as [| e₂]; [ reflexivity | ].
 destruct (letter_opp_dec e e₂) as [H₁| H₁]; [ | reflexivity ].
 exfalso.

simpl.



bbb.

 rewrite <- app_comm_cons in Hel.

 simpl.
 remember (norm_list el) as el₃ eqn:Hel₃; symmetry in Hel₃.
 destruct el₃ as [| e₁]; [ discriminate Hel | ].
 injection Hel; clear Hel; intros; subst e₁ el₃.
bbb.

 remember (norm_list el₁) as el₃ eqn:Hel₃; symmetry in Hel₃.
 destruct el₃ as [| e₁].
  simpl.
  remember (norm_list el₂) as el₄ eqn:Hel₄; symmetry in Hel₄.
  destruct el₄ as [| e₂].

bbb.
 simpl in Hel; simpl.
 destruct el₁; [ | discriminate Hel ].
 destruct el₂; [ reflexivity | discriminate Hel ].

 simpl in Hel; simpl.
 remember (norm_list el) as ns eqn:Hns; symmetry in Hns.
 destruct ns as [| e₁].

bbb.

pose proof glop el (E x true :: E x₁ d₁ :: nil) ns Hns as H.
rewrite Hns₁ in H.
simpl in H.
destruct (letter_opp_dec (E x true) (E x₁ d₁)) as [H₁| H₁].
 simpl in H.
 apply letter_opp_iff in H₁; simpl in H₁.
 destruct H₁; subst x₁ d₁; simpl in Hns₁, H.
 revert Hns; apply norm_list_impossible_start.

 simpl in H; revert H.
 apply norm_list_impossible_consecutive with (el₁ := E x true :: nil).
bbb.

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
bbb.

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
