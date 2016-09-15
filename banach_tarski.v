(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)

Require Import Utf8.
Require Import List.
Require Import Relations.
Import ListNotations.

Theorem neq_negb : ∀ x y, x ≠ y → x = negb y.
Proof.
intros.
destruct x, y; try reflexivity; exfalso; apply H; reflexivity.
Qed.

Theorem negb_neq : ∀ b₁ b₂, negb b₁ ≠ b₂ → b₁ = b₂.
Proof.
intros b₁ b₂ H.
destruct b₁, b₂; try reflexivity; exfalso; apply H; reflexivity.
Qed.

Theorem negb_eq_eq : ∀ b₁ b₂, negb b₁ = negb b₂ → b₁ = b₂.
Proof.
intros b₁ b₂ Hn.
destruct b₁, b₂; [ reflexivity | | | reflexivity ]; discriminate Hn.
Qed.

Theorem cons_comm_app {A} : ∀ (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. reflexivity. Qed.

Definition xor (A B : Prop) : Prop := A ∧ ¬B ∨ ¬A ∧ B.
Notation "x ⊕ y" := (xor x y) (at level 85, right associativity).

Notation "∃ ! x .. y , p" :=
  (ex (unique (fun x => .. (ex (unique (fun y => p))) ..)))
  (at level 200, x binder, right associativity,
   format "'[' ∃ ! '/ '  x .. y , '/ '  p ']'")
  : type_scope.

(* Step 1 *)

Section Free_Group.

(* a = E la false
   a⁻¹ = E la true
   b = E lb false
   b⁻¹ = E lb true *)

Inductive letter := la | lb.

Inductive free_elem := E : letter → bool → free_elem.
Record F₂ := mkF₂ { str : list free_elem }.

Notation "'ạ'" := (E la false).
Notation "'ạ⁻¹'" := (E la true).
Notation "'ḅ'" := (E lb false).
Notation "'ḅ⁻¹'" := (E lb true).

Definition negf '(E t d) := E t (negb d).

Theorem letter_dec : ∀ l1 l2 : letter, {l1 = l2} + {l1 ≠ l2}.
Proof.
intros.
destruct l1, l2; try (left; reflexivity); right; intros H; discriminate H.
Defined.

Theorem letter_dec_diag : ∀ t, letter_dec t t = left (eq_refl _).
Proof.
intros t.
destruct (letter_dec t t) as [p| p]; [ | exfalso; apply p; reflexivity ].
destruct t; refine (match p with eq_refl => eq_refl end).
Qed.

Definition letter_opp '(E l₁ d₁) '(E l₂ d₂) :=
  if letter_dec l₁ l₂ then
    if Bool.bool_dec d₁ d₂ then False else True
  else False.

Definition false_neq_negb_false : false ≠ negb false :=
  λ p, False_ind False
    (eq_ind false (λ e : bool, if e then False else True) I true p).

Definition true_neq_negb_true : true ≠ negb true :=
  λ p, False_ind False
   (eq_ind true (λ e : bool, if e then True else False) I false p).

Theorem bool_dec_negb_r : ∀ b,
  Bool.bool_dec b (negb b) =
  right (if b return _ then true_neq_negb_true else false_neq_negb_false).
Proof. intros b; destruct b; reflexivity. Qed.

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
Defined.

Theorem letter_opp_inv : ∀ x d, letter_opp (E x d) (E x (negb d)).
Proof.
intros.
unfold letter_opp.
rewrite letter_dec_diag, bool_dec_negb_r.
constructor.
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
 apply letter_opp_inv.
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

Theorem negf_involutive : ∀ e, negf (negf e) = e.
Proof.
intros (t, d); simpl.
rewrite Bool.negb_involutive; reflexivity.
Qed.

Theorem norm_list_no_consec : ∀ e el el₁ el₂,
  norm_list el ≠ el₁ ++ e :: negf e :: el₂.
Proof.
intros e el el₁ el₂.
revert el₁.
induction el as [| e₁]; intros; [ intros H; destruct el₁; discriminate H | ].
simpl; remember (norm_list el) as nl eqn:Hnl; symmetry in Hnl.
destruct nl as [| e₂].
 clear; intros H.
 destruct el₁ as [| e₂]; intros; [ discriminate H | simpl in H ].
 injection H; clear H; intros; subst e₂.
 destruct el₁; discriminate H.

 destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
  intros H; subst nl.
  pose proof IHel (e₂ :: el₁) as H₂; simpl in H₂.
  apply H₂; reflexivity.

  unfold letter_opp in H₁.
  destruct e₁ as (x₁, d₁).
  destruct e₂ as (x₂, d₂).
  destruct (letter_dec x₁ x₂) as [H₂| H₂].
   subst x₂.
   destruct (Bool.bool_dec d₁ d₂) as [H₂| H₂].
    clear H₁; subst d₂.
    destruct el₁ as [| e₁].
     simpl; intros H.
     injection H; clear H; intros H₁ H₂ H₃; subst e.
     simpl in H₂.
     injection H₂; clear H₂; intros H.
     symmetry in H; revert H; apply Bool.no_fixpoint_negb.

     simpl; intros H.
     injection H; clear H; intros H₁ H₂; subst e₁.
     eapply IHel, H₁.

    exfalso; apply H₁; constructor.

   clear H₁.
   destruct el₁ as [| e₁].
    simpl; intros H.
    injection H; clear H; intros H₁ H₃ H₄; subst e.
    simpl in H₃.
    injection H₃; clear H₃; intros; subst x₂ d₂.
    apply H₂; reflexivity.

    simpl; intros H.
    injection H; clear H; intros H₁ H₃.
    eapply IHel, H₁.
Qed.

Theorem norm_list_no_consec2 : ∀ e el el₁ el₂,
  norm_list el ≠ el₁ ++ negf e :: e :: el₂.
Proof.
intros e el el₁ el₂.
pose proof norm_list_no_consec (negf e) el el₁ el₂ as H.
rewrite negf_involutive in H; assumption.
Qed.

Theorem norm_list_no_start : ∀ e el el₂,
  norm_list el ≠ e :: negf e :: el₂.
Proof.
intros e el el₂.
apply norm_list_no_consec with (el₁ := []).
Qed.

Theorem norm_list_no_start2 : ∀ e el el₂,
  norm_list el ≠ negf e :: e :: el₂.
Proof.
intros e el el₂.
apply norm_list_no_consec2 with (el₁ := []).
Qed.

(*
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

Theorem norm_list_impossible_consecutive2 : ∀ x d el el₁ el₂,
  norm_list el ≠ el₁ ++ E x (negb d) :: E x d :: el₂.
Proof.
intros.
remember (negb d) as d₁ eqn:Hd.
apply Bool.negb_sym in Hd; subst d.
apply norm_list_impossible_consecutive.
Qed.

Theorem norm_list_impossible_start : ∀ x d el el',
  norm_list el ≠ E x d :: E x (negb d) :: el'.
Proof.
intros.
apply (norm_list_impossible_consecutive x d el nil el').
Qed.

Theorem norm_list_impossible_start2 : ∀ x d el el',
  norm_list el ≠ E x (negb d) :: E x d :: el'.
Proof.
intros.
apply (norm_list_impossible_consecutive2 x d el nil el').
Qed.
*)

Theorem norm_list_cancel : ∀ el e,
  norm_list (e :: negf e :: el) = norm_list el.
Proof.
intros el (t, d).
revert t d.
induction el as [| (t₁, d₁)]; intros.
 simpl; rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.

 remember (E t₁ d₁ :: el) as el₁ eqn:Hel₁.
 symmetry in Hel₁; simpl.
 remember (norm_list el₁) as el₂ eqn:Hel₂.
 symmetry in Hel₂; simpl.
 destruct el₂ as [| (t₂, d₂)].
  rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.

  subst el₁.
  destruct (letter_dec t t₂) as [H₁| H₁].
   subst t₂.
   destruct (Bool.bool_dec (negb d) d₂) as [H₁| H₁].
    subst d₂.
    rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.

    apply negb_neq in H₁; subst d₂.
    destruct el₂ as [| (t₂, d₂)]; [ reflexivity | ].
    destruct (letter_dec t t₂) as [H₁| H₁]; [ | reflexivity ].
    subst t₂.
    destruct (Bool.bool_dec d d₂) as [H₁| H₁]; [ reflexivity | ].
    apply not_eq_sym, neq_negb in H₁; subst d₂.
    exfalso; revert Hel₂; apply norm_list_no_start.

   rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.
Qed.

Theorem norm_list_cancel_in : ∀ el₁ el₂ e,
  norm_list (el₁ ++ e :: negf e :: el₂) =
  norm_list (el₁ ++ el₂).
Proof.
intros.
revert el₂ e.
induction el₁ as [| e₁]; intros.
 do 2 rewrite app_nil_l.
 apply norm_list_cancel.

 simpl; rewrite IHel₁; reflexivity.
Qed.

(*
Theorem norm_list_cancel_start : ∀ el t d,
  norm_list (E t d :: E t (negb d) :: el) = norm_list el.
Proof.
intros el t d.
revert t d.
induction el as [| (t₁, d₁)]; intros.
 Transparent letter_opp_dec.
 simpl; rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.

 remember (E t₁ d₁ :: el) as el₁ eqn:Hel₁.
 symmetry in Hel₁; simpl.
 remember (norm_list el₁) as el₂ eqn:Hel₂.
 symmetry in Hel₂; simpl.
 destruct el₂ as [| (t₂, d₂)].
  rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.

  subst el₁.
  destruct (letter_dec t t₂) as [H₁| H₁].
   subst t₂.
   destruct (Bool.bool_dec (negb d) d₂) as [H₁| H₁].
    subst d₂.
    rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.

    apply negb_neq in H₁; subst d₂.
    destruct el₂ as [| (t₂, d₂)]; [ reflexivity | ].
    destruct (letter_dec t t₂) as [H₁| H₁]; [ | reflexivity ].
    subst t₂.
    destruct (Bool.bool_dec d d₂) as [H₁| H₁]; [ reflexivity | ].
    apply not_eq_sym, neq_negb in H₁; subst d₂.
    exfalso; revert Hel₂; apply norm_list_no_start.

   rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.
Qed.

Theorem norm_list_cancel_inside : ∀ el₁ el₂ t d,
  norm_list (el₁ ++ E t d :: E t (negb d) :: el₂) =
  norm_list (el₁ ++ el₂).
Proof.
intros.
revert el₂ t d.
induction el₁ as [| e₁]; intros.
 do 2 rewrite app_nil_l.
 apply norm_list_cancel_start.

 simpl; rewrite IHel₁; reflexivity.
Qed.
*)

Theorem is_normal : ∀ el₁ el₂ el₃,
  norm_list (el₁ ++ norm_list el₂ ++ el₃) =
  norm_list (el₁ ++ el₂ ++ el₃).
Proof.
intros.
revert el₁ el₃.
induction el₂ as [| e₂]; intros; [ reflexivity | simpl ].
remember (norm_list el₂) as el eqn:Hel₂; symmetry in Hel₂.
destruct el as [| e].
 simpl in IHel₂; simpl.
 rewrite cons_comm_app, app_assoc.
 rewrite IHel₂, <- app_assoc; reflexivity.

 destruct (letter_opp_dec e₂ e) as [H₁| H₁].
  destruct e as (t, d).
  destruct e₂ as (t₂, d₂).
  apply letter_opp_iff in H₁.
  destruct H₁; subst t d.
  rewrite cons_comm_app.
  do 2 rewrite app_assoc.
  rewrite <- IHel₂.
  do 2 rewrite <- app_assoc; simpl.
  rewrite norm_list_cancel_in.
  reflexivity.

  rewrite cons_comm_app.
  do 2 rewrite app_assoc.
  rewrite <- IHel₂.
  do 2 rewrite <- app_assoc.
  reflexivity.
Qed.

Theorem norm_list_norm_list : ∀ el, norm_list (norm_list el) = norm_list el.
Proof.
intros el.
pose proof is_normal [] el [] as H.
simpl in H; do 2 rewrite app_nil_r in H.
assumption.
Qed.

Theorem norm_list_cons : ∀ el e,
  norm_list (e :: el) = e :: el
  → norm_list el = el.
Proof.
intros el e Hn.
revert e Hn.
induction el as [| e₁]; intros; [ reflexivity | ].
remember (e₁ :: el) as el₁ eqn:Hel.
simpl in Hn.
remember (norm_list el₁) as el₂ eqn:Hel₁; symmetry in Hel₁.
destruct el₂ as [| e₂].
 injection Hn; clear Hn; intros; subst; discriminate H.

 destruct (letter_opp_dec e e₂) as [H₁| H₁].
  subst el₁ el₂.
  destruct e as (t, d).
  destruct e₂ as (t₂, d₂).
  apply letter_opp_iff in H₁.
  destruct H₁; subst t₂ d₂.
  pose proof norm_list_no_start2 (E t d) (e₁ :: el) (e₁ :: el) as H.
  contradiction.

  injection Hn; clear Hn; intros; subst el₁.
  assumption.
Qed.

Definition empty s := str (norm s) = nil.
Definition start_with x s :=
  match str (norm s) with
  | nil => False
  | e :: el => x = e
  end.

Notation "s = '∅'" := (empty s) (at level 70).
Notation "s ≠ '∅'" := (¬ empty s) (at level 70).
Notation "s '∈' 'Ṣ' ( x )" := (start_with x s)
  (at level 70, format "s  '∈'  Ṣ ( x )").

Theorem decomposed_4 : ∀ s,
  s = ∅ ⊕ s ∈ Ṣ(ạ) ⊕ s ∈ Ṣ(ạ⁻¹) ⊕ s ∈ Ṣ(ḅ) ⊕ s ∈ Ṣ(ḅ⁻¹).
Proof.
intros s.
unfold empty, start_with.
remember (norm s) as ns eqn:Hns; symmetry in Hns.
destruct ns as (el); simpl.
destruct el as [| e].
 left; split; [ reflexivity | ].
 intros H.
 destruct H as [(H, _)| (_, H)]; [ contradiction | ].
 destruct H as [(H, _)| (_, H)]; [ contradiction | ].
 destruct H as [(H, _)| (_, H)]; contradiction.

 right.
 split; [ intros H; discriminate H | ].
 destruct e as (x, d).
 destruct x.
  destruct d.
   right; split; [ intros H; discriminate H | ].
   left; split; [ reflexivity | ].
   intros [(H, _)| (_, H)]; discriminate H.

   left; split; [ reflexivity | ].
   intros [(H, _)| (_, [(H, _)| (_, H)])]; discriminate H.

  right; split; [ intros H; discriminate H | ].
  right; split; [ intros H; discriminate H | ].
  destruct d.
   right; split; [ intros H; discriminate H | reflexivity ].

   left; split; [ reflexivity | intros H; discriminate H ].
Qed.

Theorem decomposed_4_or : ∀ s, empty s ∨
  start_with ạ s ∨ start_with ạ⁻¹ s ∨ start_with ḅ s ∨ start_with ḅ⁻¹ s.
Proof.
intros s.
unfold empty, start_with.
remember (norm s) as ns eqn:Hns; symmetry in Hns.
destruct ns as (el); simpl.
destruct el as [| e]; [ left; reflexivity | right ].
destruct e as (x, d).
destruct x.
 destruct d; [ right; left; reflexivity | left; reflexivity ].

 right; right.
 destruct d; [ right; reflexivity | left; reflexivity ].
Qed.

(* definition start_with2 x y s ↔ s in xS(y) *)
Definition start_with2 x y s :=
  ∃ t, norm s = norm (mkF₂ (x :: str t)) ∧ start_with y t.

Notation "s '∈' x 'Ṣ' ( y )" := (start_with2 x y s)
  (at level 70, x at level 0, format "s  '∈'  x  Ṣ ( y )").

Theorem empty_start_with2 : ∀ s x d,
  empty s
  → start_with2 (E x d) (E x (negb d)) s.
Proof.
intros s x d H.
unfold empty in H.
unfold start_with2.
remember (norm s) as ns eqn:Hns; symmetry in Hns.
destruct ns as (el).
simpl in H; subst el.
exists (mkF₂ (E x (negb d) :: nil)); simpl.
unfold start_with, norm; simpl.
split; [ | reflexivity ].
rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.
Qed.

Theorem norm_list_inv : ∀ x d el,
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
 exfalso; subst xd xe; apply H₁, letter_opp_inv.

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
  revert Hel'; apply norm_list_no_start.

  destruct (letter_opp_dec xd xe) as [H₂| H₂]; [ reflexivity | exfalso ].
  subst xd xe.
  apply H₂, letter_opp_inv.
Qed.

Theorem start_with_start_with2 : ∀ s x y d,
  not (x = y ∧ d = false)
  → start_with (E y d) s
  → start_with2 (E x false) (E x true) s.
Proof.
intros s x y d H₁ H.
unfold start_with in H.
unfold start_with2; simpl.
destruct s as (el); simpl in H.
remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
destruct el₁ as [| e₁]; [ contradiction | subst e₁ ].
unfold norm.
remember norm_list as f; simpl; subst f.
rewrite Hel₁.
exists (mkF₂ (E x true :: E y d :: el₁)).
remember norm_list as f; simpl; subst f.
rewrite norm_list_inv.
rewrite <- Hel₁, norm_list_norm_list.
split; [ reflexivity | ].
unfold start_with; simpl.
rewrite norm_list_norm_list, Hel₁.
destruct (letter_dec x y) as [H₂| H₂]; [ | reflexivity ].
destruct d; [ reflexivity | ].
subst y; exfalso; apply H₁; split; reflexivity.
Qed.

Theorem decomposed_2 : ∀ s x,
  start_with2 (E x false) (E x true) s ⊕ start_with (E x false) s.
Proof.
intros s x.
destruct (decomposed_4 s) as [(H, _)| (_, H)].
 left; split; [ apply empty_start_with2; assumption | ].
 unfold empty in H; unfold start_with.
 rewrite H; intros H'; assumption.

 destruct H as [(H, _)| (_, H)].
 destruct x.
  right; split; [ intros (t, (Hn, Ht)) | assumption ].
  unfold start_with in H, Ht; rewrite Hn in H; simpl in H.
  unfold norm in Ht; simpl in Ht.
  remember (norm_list (str t)) as el eqn:Hel; symmetry in Hel.
  destruct el as [| e]; [ contradiction | subst e ].
  destruct (letter_opp_dec ạ ạ⁻¹) as [H₁| H₁].
   destruct el as [| e]; [ contradiction | subst e ].
   revert Hel; apply norm_list_no_start.

   apply H₁, letter_opp_inv.

  left; split.
   eapply start_with_start_with2; [ | eassumption ].
   intros (H₁, _); discriminate H₁.

   intros H₁.
   unfold start_with in H, H₁.
   destruct (str (norm s)); [ contradiction | subst f; discriminate H₁ ].

  destruct H as [(H, _)| (_, H)].
  left; split.
   eapply start_with_start_with2; [ | eassumption ].
   intros (_, H₁); discriminate H₁.

   intros H₁.
   unfold start_with in H, H₁.
   destruct (str (norm s)); [ contradiction | subst f; discriminate H₁ ].

   destruct H as [(H, _)| (_, H)].
    destruct x.
     left; split.
      eapply start_with_start_with2; [ | eassumption ].
      intros (H₁, _); discriminate H₁.

      intros H₁.
      unfold start_with in H, H₁.
      destruct (str (norm s)); [ contradiction | subst f; discriminate H₁ ].

     right; split; [ | assumption ].
     unfold start_with in H.
     intros (t, (Hn, Ht)).
     rewrite Hn in H; simpl in H.
     unfold start_with, norm in Ht; simpl in Ht.
     remember (norm_list (str t)) as el eqn:Hel; symmetry in Hel.
     destruct el as [| e]; [ contradiction | subst e ].
     destruct (letter_opp_dec ḅ ḅ⁻¹) as [H₁| H₁].
      destruct el as [| e]; [ contradiction | subst e ].
      revert Hel; apply norm_list_no_start.

      apply H₁, letter_opp_inv.

    left; split.
     eapply start_with_start_with2; [ | eassumption ].
     intros (_, H₁); discriminate H₁.

     intros H₁.
     unfold start_with in H, H₁.
     destruct (str (norm s)); [ contradiction | subst f; discriminate H₁ ].
Qed.

Theorem decomposed_2_or : ∀ s x,
  start_with2 (E x false) (E x true) s ∨ start_with (E x false) s.
Proof.
intros s x.
destruct (decomposed_4_or s) as [H| [H| [H| [H|H]]]].
 left; apply empty_start_with2; assumption.

 destruct x as [H₁| H₁]; [ right; assumption | ].
 left.
 eapply start_with_start_with2; [ | eassumption ].
 intros (H₁, _); discriminate H₁.

 left.
 eapply start_with_start_with2; [ | eassumption ].
 intros (_, H₁); discriminate H₁.

 destruct x as [H₁| H₁]; [ | right; assumption ].
 left.
 eapply start_with_start_with2; [ | eassumption ].
 intros (H₁, _); discriminate H₁.

 left.
 eapply start_with_start_with2; [ | eassumption ].
 intros (_, H₁); discriminate H₁.
Qed.

Theorem decomposed_2_a : ∀ s, s ∈ ạ Ṣ(ạ⁻¹) ⊕ s ∈ Ṣ(ạ) .
Proof. intros; apply decomposed_2. Qed.

Theorem decomposed_2_b : ∀ s, s ∈ ḅ Ṣ(ḅ⁻¹) ⊕ s ∈ Ṣ(ḅ) .
Proof. intros; apply decomposed_2. Qed.

End Free_Group.

(* Step 2 *)

Require Import Reals Psatz.

Notation "'ℝ'" := R.
Notation "'ℤ'" := Z.
Notation "'ℕ'" := nat.

Notation "'√'" := sqrt.

(* to prevent 'simpl' to expand 2*a, 3*a, and so on, into matches *)
Arguments Nat.modulo _ _ : simpl nomatch.
Arguments Z.mul _ _ : simpl nomatch.

Theorem Rdiv_0_l : ∀ x, (0 / x = 0)%R.
Proof.
intros x; unfold Rdiv; apply Rmult_0_l.
Qed.

Theorem Rdiv_1_r : ∀ x, (x / 1 = x)%R.
Proof.
intros x; lra.
Qed.

Theorem Rmult5_sqrt2_sqrt5 : ∀ a b c d, (0 <= b)%R →
  (a * √ b * c * d * √ b)%R = (a * b * c * d)%R.
Proof.
intros a b c d Hb.
rewrite Rmult_comm, <- Rmult_assoc; f_equal.
rewrite <- Rmult_assoc; f_equal.
rewrite Rmult_comm, Rmult_assoc; f_equal.
apply sqrt_sqrt; assumption.
Qed.

Section Rotation.

Notation "'ạ'" := (E la false).
Notation "'ạ⁻¹'" := (E la true).
Notation "'ḅ'" := (E lb false).
Notation "'ḅ⁻¹'" := (E lb true).

Check decomposed_4.
Check decomposed_2_a.
Check decomposed_2_b.

Inductive point := P : ℝ → ℝ → ℝ → point.
Record matrix := mkmat
  { a₁₁ : ℝ; a₁₂ : ℝ; a₁₃ : ℝ;
    a₂₁ : ℝ; a₂₂ : ℝ; a₂₃ : ℝ;
    a₃₁ : ℝ; a₃₂ : ℝ; a₃₃ : ℝ }.

Definition mat_vec_mul mat '(P x y z) :=
  P (a₁₁ mat * x + a₁₂ mat * y + a₁₃ mat * z)
    (a₂₁ mat * x + a₂₂ mat * y + a₂₃ mat * z)
    (a₃₁ mat * x + a₃₂ mat * y + a₃₃ mat * z).

Definition rot_x := mkmat
  1         0         0
  0         (1/3)     (-2*√2/3)
  0         (2*√2/3)  (1/3).
Definition rot_inv_x := mkmat
  1         0         0
  0         (1/3)     (2*√2/3)
  0         (-2*√2/3) (1/3).
Definition rot_z := mkmat
  (1/3)     (-2*√2/3) 0
  (2*√2/3)  (1/3)     0
  0         0         1.
Definition rot_inv_z := mkmat
  (1/3)     (2*√2/3)  0
  (-2*√2/3) (1/3)     0
  0         0         1.

Definition rotate e pt :=
  match e with
  | ạ => mat_vec_mul rot_x pt
  | ạ⁻¹ => mat_vec_mul rot_inv_x pt
  | ḅ => mat_vec_mul rot_z pt
  | ḅ⁻¹ => mat_vec_mul rot_inv_z pt
  end.

Definition rev_path el := map negf (rev el).

Definition rotate_param e '(a, b, c, N) :=
  match e with
  | ạ => ((3 * a)%Z, (b - 2 * c)%Z, (4 * b + c)%Z, S N)
  | ạ⁻¹ => ((3 * a)%Z, (b + 2 * c)%Z, (- 4 * b + c)%Z, S N)
  | ḅ => ((a - 4 * b)%Z, (b + 2 * a)%Z, (3 * c)%Z, S N)
  | ḅ⁻¹ => ((a + 4 * b)%Z, (b - 2 * a)%Z, (3 * c)%Z, S N)
  end.

Theorem negf_eq_eq : ∀ e₁ e₂, negf e₁ = negf e₂ → e₁ = e₂.
Proof.
intros e₁ e₂ Hn.
destruct e₁ as (t₁, d₁).
destruct e₂ as (t₂, d₂).
simpl in Hn.
injection Hn; intros H₁ H₂; subst.
apply negb_eq_eq in H₁; subst d₁; reflexivity.
Qed.

Theorem rotate_param_rotate : ∀ el x y z n a b c N,
  fold_right rotate_param (x, y, z, n) el = (a, b, c, N)
  ↔ fold_right rotate (P (IZR x / 3^n) (IZR y * √2 / 3^n) (IZR z / 3^n)) el =
      P (IZR a / 3^N) (IZR b*√2 / 3^N) (IZR c / 3^N)
    ∧ N = n + length el.
Proof.
intros el x y z n a₁ b₁ c₁ N₁.
split.
 intros Hr.
 simpl in Hr; simpl.
 revert a₁ b₁ c₁ N₁ Hr.
 induction el as [| (t, d)]; intros.
  simpl; simpl in Hr; rewrite Nat.add_0_r.
  injection Hr; intros; subst; simpl.
  split; reflexivity.

  simpl in Hr; simpl.
  remember (fold_right rotate_param (x, y, z, n) el) as rp eqn:Hrp.
  symmetry in Hrp.
  destruct rp as (((a, b), c), N).
  pose proof IHel _ _ _ _ (eq_refl _) as H.
  destruct H as (H, HN).
  erewrite H.
  simpl in Hr; simpl; unfold Rdiv.
  progress repeat rewrite Rmult_1_l.
  progress repeat rewrite Rmult_0_l.
  progress repeat rewrite Rplus_0_l.
  progress repeat rewrite Rplus_0_r.
  progress repeat rewrite <- Rmult_assoc.
  rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
  rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
  destruct t, d; injection Hr; clear Hr; intros; subst a₁ b₁ c₁ N₁ N; simpl.
   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

 intros Hr.
 revert x y z n a₁ b₁ c₁ N₁ Hr.
 induction el as [| e] using rev_ind; intros.
  simpl in Hr; simpl; rewrite Nat.add_0_r in Hr.
  destruct Hr as (Hr, Hn); subst N₁.
  unfold Rdiv in Hr.
  injection Hr; intros Hz Hy Hx.
  f_equal; f_equal; f_equal.
   apply Rmult_eq_reg_r, eq_IZR in Hx; [ assumption | ].
   apply Rinv_neq_0_compat, pow_nonzero; lra.

   apply Rmult_eq_reg_r in Hy.
    apply Rmult_eq_reg_r in Hy; [ | apply sqrt2_neq_0 ].
    apply eq_IZR; assumption.

    apply Rinv_neq_0_compat, pow_nonzero; lra.

   apply Rmult_eq_reg_r, eq_IZR in Hz; [ assumption | ].
   apply Rinv_neq_0_compat, pow_nonzero; lra.

  simpl in Hr; destruct Hr as (Hr, HN).
  rewrite app_length, Nat.add_1_r in HN.
  rewrite <- Nat.add_succ_comm in HN.
  simpl; destruct e as (t, d).
  rewrite fold_right_app; simpl.
  rewrite fold_right_app in Hr; simpl in Hr.
  destruct t, d.
   apply IHel; split; [ | assumption ].
   rewrite <- Hr; simpl.
   unfold Rdiv.
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
   rewrite plus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   f_equal; f_equal.
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].

   apply IHel; split; [ | assumption ].
   rewrite <- Hr; simpl.
   unfold Rdiv.
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   progress repeat rewrite mult_IZR.
   rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
   rewrite minus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   f_equal; f_equal.
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].

   apply IHel; split; [ | assumption ].
   rewrite <- Hr; simpl.
   unfold Rdiv.
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   progress repeat rewrite mult_IZR.
   rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   f_equal; f_equal.
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].

   apply IHel; split; [ | assumption ].
   rewrite <- Hr; simpl.
   unfold Rdiv.
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   progress repeat rewrite mult_IZR.
   rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
   rewrite minus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   f_equal; f_equal.
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
Qed.

Theorem rot_rot_inv_x : ∀ pt,
  mat_vec_mul rot_x (mat_vec_mul rot_inv_x pt) = pt.
Proof.
intros.
unfold mat_vec_mul; simpl.
destruct pt as (x, y, z).
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rplus_0_l.
f_equal.
 field_simplify; simpl.
 unfold Rdiv.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite RMicromega.Rinv_1.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 field_simplify; reflexivity.

 unfold Rdiv.
 field_simplify; simpl.
 progress repeat rewrite Rmult_1_r.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 field_simplify; reflexivity.
Qed.

Theorem rot_inv_rot_x : ∀ pt,
  mat_vec_mul rot_inv_x (mat_vec_mul rot_x pt) = pt.
Proof.
intros.
unfold mat_vec_mul; simpl.
destruct pt as (x, y, z).
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rplus_0_l.
f_equal.
 field_simplify; simpl.
 unfold Rdiv.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite RMicromega.Rinv_1.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 field_simplify; reflexivity.

 unfold Rdiv.
 field_simplify; simpl.
 progress repeat rewrite Rmult_1_r.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 field_simplify; reflexivity.
Qed.

Theorem rot_rot_inv_z : ∀ pt,
  mat_vec_mul rot_z (mat_vec_mul rot_inv_z pt) = pt.
Proof.
intros.
unfold mat_vec_mul; simpl.
destruct pt as (x, y, z).
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rplus_0_l.
f_equal.
 field_simplify; simpl.
 unfold Rdiv.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite RMicromega.Rinv_1.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 field_simplify; reflexivity.

 unfold Rdiv.
 field_simplify; simpl.
 progress repeat rewrite Rmult_1_r.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 field_simplify; reflexivity.
Qed.

Theorem rot_inv_rot_z : ∀ pt,
  mat_vec_mul rot_inv_z (mat_vec_mul rot_z pt) = pt.
Proof.
intros.
unfold mat_vec_mul; simpl.
destruct pt as (x, y, z).
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rplus_0_l.
f_equal.
 field_simplify; simpl.
 unfold Rdiv.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite RMicromega.Rinv_1.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 field_simplify; reflexivity.

 unfold Rdiv.
 field_simplify; simpl.
 progress repeat rewrite Rmult_1_r.
 rewrite sqrt_sqrt; [ | lra ].
 field_simplify; simpl.
 unfold Rdiv.
 field_simplify; reflexivity.
Qed.

Theorem list_nil_app_dec {A} : ∀ (l : list A),
  {l = []} + {∃ x l', l = l' ++ [x]}.
Proof.
intros l.
destruct l as [| x]; [ left; reflexivity | right ].
revert x.
induction l as [| y] using rev_ind; intros; [ exists x, []; reflexivity | ].
exists y, (x :: l); reflexivity.
Qed.

Theorem norm_list_app_diag : ∀ el₁ el₂,
  norm_list (el₁ ++ el₂) = el₁ ++ el₂ → norm_list el₁ = el₁.
Proof.
intros el₁ el₂ Hn.
revert el₂ Hn.
induction el₁ as [| e₁]; intros; [ reflexivity | simpl ].
generalize Hn; intros Hn₁.
rewrite <- app_comm_cons in Hn₁.
apply norm_list_cons, IHel₁ in Hn₁.
rewrite Hn₁.
destruct el₁ as [| e₂]; [ reflexivity | ].
destruct (letter_opp_dec e₁ e₂) as [H₁| H₁]; [ exfalso | reflexivity ].
destruct e₁ as (t₁, d₁).
destruct e₂ as (t₂, d₂).
apply letter_opp_iff in H₁.
destruct H₁; subst t₂ d₂.
revert Hn; apply norm_list_no_start.
Qed.

Theorem rotate_prop : ∀ p t d el el₁ el₂ e a b c,
  t = lb ∧ p = (1, 0, 0, O)%Z ∨
  t = la ∧ p = (0, 0, 1, O)%Z
  → el₁ = el₂ ++ [E t d]
  → el = e :: el₁
  → norm_list el = el
  → fold_right rotate_param p el₁ = (a, b, c, length el₁)
  → (b mod 3)%Z ≠ 0%Z
  → match e with
    | ạ => ((b - 2 * c) mod 3)%Z ≠ 0%Z
    | ạ⁻¹ => ((b + 2 * c) mod 3)%Z ≠ 0%Z
    | ḅ => ((b + 2 * a) mod 3)%Z ≠ 0%Z
    | ḅ⁻¹ => ((b - 2 * a) mod 3)%Z ≠ 0%Z
    end.
Proof.
intros p t d el el₁ el₂ e a b c.
intros Htp Hel₁ Hel Hn Hp Hb'.
rewrite Hel₁ in Hp at 2; simpl in Hp.
remember (length el₂) as len eqn:Hlen.
destruct el₂ as [| e₁].
 simpl in Hlen; subst len; simpl in Hel.
 subst el₁; simpl in Hp.
 destruct Htp as [(Ht, Hq)| (Ht, Hq)]; subst t p.
  destruct d; injection Hp; intros; subst.
   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_no_start.

   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_no_start.

  destruct d; injection Hp; intros; subst.
   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_no_start.

   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_no_start.

 rewrite Hel₁ in Hel; simpl in Hel.
 generalize Hn; intros H₂.
 do 2 rewrite app_comm_cons in Hel.
 rewrite Hel in H₂.
 apply norm_list_app_diag in H₂.
 destruct len; [ discriminate Hlen | ].
 simpl in Hlen; apply eq_add_S in Hlen.
 rewrite Hel₁, fold_right_app in Hp.
 simpl in Hp.
 remember (rotate_param (E t d) p) as p₁ eqn:Hp₁.
 remember (fold_right rotate_param p₁ el₂) as p' eqn:Hp'.
 symmetry in Hp'.
 destruct p' as (((a', b'), c'), N').
 simpl in Hp.
 destruct e₁ as (t₁, d₁); destruct t₁, d₁.
  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
   remember (b' + 2 * c' + 2 * (-4 * b' + c') + 3 * b' * 3)%Z as x eqn:Hx.
   ring_simplify in Hx; subst x.
   replace 4%Z with (2 * 2)%Z by reflexivity.
   rewrite <- Z.mul_assoc, <- Z.mul_add_distr_l.
   intros H; apply Hb'.
   apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
   apply Z.gauss in H; [ | reflexivity ].
   destruct H as (k, H); rewrite H.
   apply Z.mod_mul; intros; discriminate.

   exfalso; revert Hn; rewrite Hel.
   apply norm_list_no_start.

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   exfalso; revert Hn; rewrite Hel.
   apply norm_list_no_start.

   rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
   remember (b' - 2 * c' - 2 * (4 * b' + c') + 3 * b' * 3)%Z as x eqn:Hx.
   ring_simplify in Hx; subst x.
   replace 4%Z with (2 * 2)%Z by reflexivity.
   rewrite <- Z.mul_assoc, <- Z.mul_sub_distr_l.
   intros H; apply Hb'.
   apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
   apply Z.gauss in H; [ | reflexivity ].
   destruct H as (k, H); rewrite H.
   apply Z.mod_mul; intros; discriminate.

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub at 1; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub at 1; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
   remember (b' - 2 * a' - 2 * (a' + 4 * b') + 3 * b' * 3)%Z as x eqn:Hx.
   ring_simplify in Hx; subst x.
   replace 4%Z with (2 * 2)%Z by reflexivity.
   rewrite <- Z.mul_assoc, <- Z.mul_sub_distr_l.
   intros H; apply Hb'.
   apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
   apply Z.gauss in H; [ | reflexivity ].
   destruct H as (k, H); rewrite H.
   apply Z.mod_mul; intros; discriminate.

   exfalso; revert Hn; rewrite Hel.
   apply norm_list_no_start.

  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   exfalso; revert Hn; rewrite Hel.
   apply norm_list_no_start.

   rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
   remember (b' + 2 * a' + 2 * (a' - 4 * b') + 3 * b' * 3)%Z as x eqn:Hx.
   ring_simplify in Hx; subst x.
   replace 4%Z with (2 * 2)%Z by reflexivity.
   rewrite <- Z.mul_assoc, <- Z.mul_add_distr_l.
   intros H; apply Hb'.
   apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
   apply Z.gauss in H; [ | reflexivity ].
   destruct H as (k, H); rewrite H.
   apply Z.mod_mul; intros; discriminate.
Qed.

Theorem rotate_param_b_nonzero : ∀ p t d el el₁ a b c,
  t = lb ∧ p = (1, 0, 0, O)%Z ∨
  t = la ∧ p = (0, 0, 1, O)%Z
  → el = el₁ ++ [E t d]
  → norm_list el = el
  → fold_right rotate_param p el = (a, b, c, length el)
  → (b mod 3 ≠ 0)%Z.
Proof.
intros p t d el el₁ a b c Htp Hel Hn Hu.
remember (length el₁) as len eqn:Hlen; symmetry in Hlen.
revert el el₁ d a b c Hel Hn Hu Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len.
 apply length_zero_iff_nil in Hlen; subst el₁.
 subst el; simpl in Hu.
 destruct Htp as [(Ht, Hp)| (Ht, Hp)]; subst t p.
  destruct d; injection Hu; intros; subst; intros H; discriminate H.
  destruct d; injection Hu; intros; subst; intros H; discriminate H.

 destruct el₁ as [| e₁]; [ discriminate Hlen | simpl in Hlen ].
 apply eq_add_S in Hlen.
 rewrite <- app_comm_cons in Hel.
 remember (el₁ ++ [E t d]) as el₂ eqn:Hel₁.
 generalize Hn; intros H₁; rewrite Hel in H₁.
 apply norm_list_cons in H₁.
 rewrite Hel in Hu; simpl in Hu.
 remember (fold_right rotate_param p el₂) as v eqn:Hp.
 symmetry in Hp.
 destruct v as (((a', b'), c'), N').
 assert (Hss : len < S len) by apply Nat.lt_succ_diag_r.
 assert (N' = S len); [ | subst N' ].
  destruct e₁ as (t₁, d₁).
  rewrite Hel₁, app_length, Nat.add_1_r in Hu.
  destruct t₁, d₁; simpl in Hu; injection Hu; intros; subst; reflexivity.

  rewrite <- Hlen in Hp.
  replace (S (length el₁)) with (length el₂) in Hp.
   pose proof IHlen _ Hss _ _ _ _ _ _ Hel₁ H₁ Hp Hlen as Hb'; subst len.
   pose proof rotate_prop p t d el el₂ el₁ e₁ a' b' c' Htp Hel₁ Hel Hn Hp Hb'.
   destruct e₁ as (t₁, d₁).
   destruct t₁, d₁; injection Hu; intros; subst; assumption.

   subst; rewrite app_length, Nat.add_1_r; reflexivity.
Qed.

(* "we claim that w(1,0,0) has the form (a,b√2,c)/3^k where a,b,c are
    integers and b is not divisible by 3" (Stan Wagon) *)

Theorem rotate_1_0_0_b_nonzero : ∀ w el el₁ d,
  el = el₁ ++ [E lb d]
  → norm_list el = el
  → w = (λ p, fold_right rotate p el)
  → ∃ a b c k,
    w (P 1 0 0) = P (IZR a/3^k) (IZR b*√2/3^k) (IZR c/3^k) ∧
    (b mod 3 ≠ 0)%Z.
Proof.
intros w el el₁ d Hel Hn Hw.
subst w.
remember (fold_right rotate_param (1, 0, 0, O)%Z el) as u eqn:Hu.
symmetry in Hu; destruct u as (((a, b), c), len).
generalize Hu; intros Hv.
apply rotate_param_rotate in Hv; simpl in Hv.
rewrite Rmult_0_l, Rdiv_0_l, Rdiv_1_r in Hv.
destruct Hv as (Hv, Hlen).
rewrite Hv.
exists a, b, c, len.
split; [ reflexivity | clear Hv ].
symmetry in Hlen.
rewrite Hel in Hlen; simpl in Hlen.
rewrite app_length, Nat.add_1_r in Hlen.
destruct len; [ discriminate Hlen | ].
apply eq_add_S in Hlen; subst len.
replace (S (length el₁)) with (length el) in Hu.
 eapply rotate_param_b_nonzero; try eassumption.
 left; split; reflexivity.

 subst; rewrite app_length, Nat.add_1_r; reflexivity.
Qed.

Theorem rotate_0_0_1_b_nonzero : ∀ w el el₁ d,
  el = el₁ ++ [E la d]
  → norm_list el = el
  → w = (λ p, fold_right rotate p el)
  → ∃ a b c k,
    w (P 0 0 1) = P (IZR a/3^k) (IZR b*√2/3^k) (IZR c/3^k) ∧
    (b mod 3 ≠ 0)%Z.
Proof.
intros w el el₁ d Hel Hn Hw.
subst w.
remember (fold_right rotate_param (0, 0, 1, O)%Z el) as u eqn:Hu.
symmetry in Hu; destruct u as (((a, b), c), len).
generalize Hu; intros Hv.
apply rotate_param_rotate in Hv; simpl in Hv.
rewrite Rmult_0_l, Rdiv_0_l, Rdiv_1_r in Hv.
destruct Hv as (Hv, Hlen).
rewrite Hv.
exists a, b, c, len.
split; [ reflexivity | clear Hv ].
symmetry in Hlen.
rewrite Hel in Hlen; simpl in Hlen.
rewrite app_length, Nat.add_1_r in Hlen.
destruct len; [ discriminate Hlen | ].
apply eq_add_S in Hlen; subst len.
replace (S (length el₁)) with (length el) in Hu.
 eapply rotate_param_b_nonzero; try eassumption.
 right; split; reflexivity.

 subst; rewrite app_length, Nat.add_1_r; reflexivity.
Qed.

Theorem rotate_1_0_0_is_diff : ∀ el el₁ d,
  el = el₁ ++ [E lb d]
  → norm_list el = el
  → fold_right rotate (P 1 0 0) el ≠ P 1 0 0.
Proof.
intros el el₁ d Hel Hn.
remember (λ p, fold_right rotate p el) as w eqn:Hw.
pose proof rotate_1_0_0_b_nonzero w el el₁ d Hel Hn Hw as H.
destruct H as (a, (b, (c, (k, (Hp, Hm))))).
rewrite Hw in Hp.
rewrite Hp; intros H.
injection H; intros Hc Hb Ha.
apply Rmult_integral in Hb.
destruct Hb as [Hb| Hb].
 apply Rmult_integral in Hb.
 destruct Hb as [Hb| Hb].
  apply eq_IZR_R0 in Hb; subst b; apply Hm; reflexivity.

  revert Hb; apply sqrt2_neq_0.

 apply Rmult_eq_compat_r with (r := (3 ^ k)%R) in Hb.
 rewrite Rinv_l in Hb; [ lra | apply pow_nonzero; lra ].
Qed.

Theorem rotate_0_0_1_is_diff : ∀ el el₁ d,
  el = el₁ ++ [E la d]
  → norm_list el = el
  → fold_right rotate (P 0 0 1) el ≠ P 0 0 1.
Proof.
intros el el₁ d Hel Hn.
remember (λ p, fold_right rotate p el) as w eqn:Hw.
pose proof rotate_0_0_1_b_nonzero w el el₁ d Hel Hn Hw as H.
destruct H as (a, (b, (c, (k, (Hp, Hm))))).
rewrite Hw in Hp.
rewrite Hp; intros H.
injection H; intros Hc Hb Ha.
apply Rmult_integral in Hb.
destruct Hb as [Hb| Hb].
 apply Rmult_integral in Hb.
 destruct Hb as [Hb| Hb].
  apply eq_IZR_R0 in Hb; subst b; apply Hm; reflexivity.

  revert Hb; apply sqrt2_neq_0.

 apply Rmult_eq_compat_r with (r := (3 ^ k)%R) in Hb.
 rewrite Rinv_l in Hb; [ lra | apply pow_nonzero; lra ].
Qed.

Theorem rev_path_cons : ∀ e el,
  rev_path (e :: el) = rev_path el ++ rev_path [e].
Proof.
intros e el.
unfold rev_path; simpl.
rewrite map_app; reflexivity.
Qed.

Theorem rev_path_app : ∀ el₁ el₂,
  rev_path (el₁ ++ el₂) = rev_path el₂ ++ rev_path el₁.
Proof.
intros el₁ el₂.
revert el₁.
induction el₂ as [| (t, d)]; intros; [ rewrite app_nil_r; reflexivity | ].
rewrite rev_path_cons, cons_comm_app, app_assoc, IHel₂.
rewrite <- app_assoc; f_equal; simpl.
clear el₂ IHel₂.
induction el₁ as [| e₁]; [ reflexivity | ].
simpl; rewrite rev_path_cons; rewrite IHel₁.
simpl; f_equal; symmetry.
rewrite rev_path_cons; reflexivity.
Qed.

Theorem rev_path_involutive : ∀ el, rev_path (rev_path el) = el.
Proof.
intros el.
induction el as [| (t, d)]; [ reflexivity | simpl ].
rewrite rev_path_cons, rev_path_app.
rewrite IHel; simpl; rewrite Bool.negb_involutive.
reflexivity.
Qed.

Theorem norm_app_rev_path_path : ∀ el, norm_list (rev_path el ++ el) = [].
Proof.
induction el as [| e]; [ reflexivity | ].
rewrite rev_path_cons, <- app_assoc.
destruct e as (t, d); simpl.
destruct d; rewrite norm_list_cancel_in; assumption.
Qed.

Theorem norm_app_path_rev_path : ∀ el, norm_list (el ++ rev_path el) = [].
Proof.
intros el.
remember (rev_path el) as rp.
replace el with (rev_path (rev_path el)) by apply rev_path_involutive.
subst rp; apply norm_app_rev_path_path.
Qed.

Theorem rotate_rotate_neg : ∀ e p, rotate e (rotate (negf e) p) = p.
Proof.
intros (t, d) p; simpl.
destruct t, d; simpl.
 rewrite rot_inv_rot_x; reflexivity.
 rewrite rot_rot_inv_x; reflexivity.
 rewrite rot_inv_rot_z; reflexivity.
 rewrite rot_rot_inv_z; reflexivity.
Qed.

Theorem rotate_neg_rotate : ∀ e p, rotate (negf e) (rotate e p) = p.
Proof.
intros (t, d) p; simpl.
destruct t, d; simpl.
 rewrite rot_rot_inv_x; reflexivity.
 rewrite rot_inv_rot_x; reflexivity.
 rewrite rot_rot_inv_z; reflexivity.
 rewrite rot_inv_rot_z; reflexivity.
Qed.

Theorem rev_path_nil : rev_path [] = [].
Proof. reflexivity. Qed.

Theorem rev_path_single : ∀ e, rev_path [e] = [negf e].
Proof. intros e; reflexivity. Qed.

Theorem app_rev_path_path : ∀ p el,
  fold_right rotate p (el ++ rev_path el) = p.
Proof.
intros.
revert p.
induction el as [| e]; intros; [ reflexivity | simpl ].
rewrite rev_path_cons, app_assoc, fold_right_app.
rewrite IHel; apply rotate_rotate_neg.
Qed.

Theorem app_path_rev_path : ∀ p el,
  fold_right rotate p (rev_path el ++ el) = p.
Proof.
intros.
revert p.
induction el as [| e] using rev_ind; intros; [ reflexivity | simpl ].
rewrite rev_path_app; simpl.
rewrite app_assoc, fold_right_app; simpl.
rewrite IHel; apply rotate_neg_rotate.
Qed.

Theorem norm_list_dec : ∀ el,
  { norm_list el = el } +
  { ∃ el₁ t d el₂, el = el₁ ++ E t d :: E t (negb d) :: el₂ }.
Proof.
intros el.
induction el as [| e]; [ left; reflexivity | ].
destruct IHel as [IHel| IHel].
 simpl.
 rewrite IHel.
 destruct el as [| e₁]; [ left; reflexivity | ].
 destruct (letter_opp_dec e e₁) as [H₁| H₁]; [ right | left; reflexivity ].
 destruct e as (t, d).
 destruct e₁ as (t₁, d₁).
 apply letter_opp_iff in H₁.
 destruct H₁; subst t₁ d₁.
 exists [], t, d, el.
 reflexivity.

 right.
 destruct IHel as (el₁, (t, (d, (el₂, IHel)))).
 exists (e :: el₁), t, d, el₂; subst el.
 reflexivity.
Qed.

Theorem rev_path_is_nil : ∀ el, rev_path el = [] → el = [].
Proof.
intros el Hr.
destruct el as [| e]; [ reflexivity | ].
rewrite rev_path_cons, rev_path_single in Hr.
destruct (rev_path el); discriminate Hr.
Qed.

Theorem rev_path_eq_eq : ∀ el₁ el₂,
  rev_path el₁ = rev_path el₂ → el₁ = el₂.
Proof.
intros el₁ el₂ Hr.
revert el₂ Hr.
induction el₁ as [| e₁]; intros.
 rewrite rev_path_nil in Hr.
 symmetry in Hr; apply rev_path_is_nil in Hr.
 destruct Hr; reflexivity.

 rewrite rev_path_cons, rev_path_single in Hr.
 destruct el₂ as [| e₂].
  rewrite rev_path_nil in Hr.
  destruct (rev_path el₁); discriminate Hr.

  rewrite rev_path_cons, rev_path_single in Hr.
  apply app_inj_tail in Hr.
  destruct Hr as (Hr, Hn).
  apply IHel₁ in Hr.
  apply negf_eq_eq in Hn.
  subst el₁ e₁; reflexivity.
Qed.

Theorem norm_list_rev_path : ∀ el,
  norm_list el = el → norm_list (rev_path el) = rev_path el.
Proof.
intros el Hel.
induction el as [| e] using rev_ind; [ reflexivity | ].
rewrite rev_path_app; simpl.
generalize Hel; intros Hn.
apply norm_list_app_diag in Hn.
rewrite IHel; [ | assumption ].
remember (rev_path el) as el₁ eqn:Hel₁.
symmetry in Hel₁.
destruct el₁ as [| e₁]; [ reflexivity | ].
destruct (letter_opp_dec (negf e) e₁) as [H₁| H₁]; [ | reflexivity ].
exfalso.
destruct e as (t, d).
destruct e₁ as (t₁, d₁).
apply letter_opp_iff in H₁; rewrite Bool.negb_involutive in H₁.
destruct H₁; subst t₁ d₁.
rewrite <- rev_path_involutive in Hel₁.
rewrite rev_path_cons, rev_path_single in Hel₁.
simpl in Hel₁.
apply rev_path_eq_eq in Hel₁.
rewrite Hel₁ in Hel.
rewrite <- app_assoc in Hel; simpl in Hel.
revert Hel.
apply norm_list_no_consec2 with (e := E t d).
Qed.

Theorem rev_path_norm_list : ∀ el,
  rev_path (norm_list el) = norm_list (rev_path el).
Proof.
intros el.
remember (length el) as len eqn:Hlen.
symmetry in Hlen.
revert el Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len.
 apply length_zero_iff_nil in Hlen; subst el; reflexivity.

 destruct (norm_list_dec el) as [H₁| H₁].
  generalize H₁; intros H₂.
  apply norm_list_rev_path in H₂.
  rewrite H₁, H₂.
  reflexivity.

  destruct H₁ as (el₁, (t, (d, (el₂, Hs)))).
  generalize Hs; intros H.
  rewrite H, norm_list_cancel_in.
  rewrite rev_path_app, rev_path_cons, rev_path_cons.
  do 2 rewrite rev_path_single.
  do 2 rewrite <- app_assoc; simpl.
  rewrite Bool.negb_involutive.
  rewrite norm_list_cancel_in.
  rewrite <- rev_path_app.
  apply IHlen with (m := length (el₁ ++ el₂)); [ | reflexivity ].
  rewrite <- Hlen, H; simpl.
  do 2 rewrite app_length; simpl.
  apply Nat.add_lt_mono_l.
  etransitivity; eapply Nat.lt_succ_diag_r.
Qed.

Theorem rotate_simpl : ∀ el₁ el₂ e p,
  fold_right rotate p (el₁ ++ e :: negf e :: el₂) =
  fold_right rotate p (el₁ ++ el₂).
Proof.
intros.
do 2 rewrite fold_right_app; simpl.
rewrite rotate_rotate_neg; reflexivity.
Qed.

Theorem all_points_in_orbit_1_0_0_are_different :
  ∀ p₁ p₂ el₁ el₂ el'₁ el'₂ d₁ d₂,
  fold_right rotate (P 1 0 0) el₁ = p₁
  → fold_right rotate (P 1 0 0) el₂ = p₂
  → el₁ = el'₁ ++ [E lb d₁]
  → el₂ = el'₂ ++ [E lb d₂]
  → norm_list el₁ = el₁
  → norm_list el₂ = el₂
  → el₁ ≠ el₂
  → p₁ ≠ p₂.
Proof.
intros p₁ p₂ el₁ el₂ el'₁ el'₂ d₁ d₂ Hp₁ Hp₂ Hel₁ Hel₂ Hn₁ Hn₂ Hd Hp.
move Hp at top; subst p₂; rename p₁ into p.
assert (H : fold_right rotate (P 1 0 0) (rev_path el₂ ++ el₁) = P 1 0 0).
 rewrite fold_right_app, Hp₁, <- Hp₂.
 rewrite <- fold_right_app.
 rewrite app_path_rev_path; reflexivity.

 destruct (norm_list_dec (rev_path el₂ ++ el₁)) as [H₁| H₁].
  revert H; rewrite Hel₁, app_assoc.
  rewrite Hel₁, app_assoc in H₁.
  remember (rev_path el₂ ++ el'₁) as el₄ eqn:Hel₄.
  remember (el₄ ++ [E lb d₁]) as el₃ eqn:Hel₃.
  pose proof rotate_1_0_0_is_diff el₃ el₄ d₁ Hel₃ H₁ as H₂.
  apply H₂.

  destruct H₁ as (el₃, (t, (d, (el₄, Hs)))).
  rewrite Hs, rotate_simpl in H.
bbb.

SearchAbout (fold_right rotate).
bbb.
rewrite <- app_assoc, <- Hel₁ in Hel₃.
bbb.
  eapply rotate_1_0_0_is_diff; [ rewrite <- app_comm_cons; f_equal | ].
  rewrite <- Hel₁.
bbb.

; assumption.

  destruct H₁ as (el₃, (t, (d, (el₄, H₁)))).
clear H Hp₁ Hel₁.
revert el₃ H₁.
induction el₁ as [| e₁]; intros.
 rewrite <- Hn₂ in H₁; simpl in H₁.
bbb.
rewrite rev_path_norm_list in H₁.
revert H₁; apply norm_list_impossible_consecutive.
destruct el₃ as [| e₃].
 simpl in H₁.
 injection H₁; clear H₁; intros H₁ H; subst e₁.


  rewrite <- Hn₁, <- Hn₂ in H₁.
SearchAbout rev_path.

SearchAbout (norm_list _ ++ _).

bbb.
  rewrite H₁ in H.
  rewrite fold_left_app in H.
Theorem toto : ∀ el t d p,
  fold_left rotate (E t d :: E t (negb d) :: el) p = fold_left rotate el p.
Proof.
Admitted. Show.

  rewrite toto in H.
  rewrite <- fold_left_app in H.
  rewrite Hel₁ in H₁.
  simpl in H₁.
  destruct el₃ as [| e₃]; simpl in H₁.
   injection H₁; clear H₁; intros H₁ H₂ H₃; subst t d.
   destruct el'₁ as [| e'₁]; simpl in H₁.
   destruct (list_nil_app_dec el₂) as [H₂| (e₂, (el₃, H₂))]; subst el₂.
    discriminate H₂.

    rewrite H₂ in H₁.
    rewrite rev_path_app in H₁; simpl in H₁.
    destruct e₂ as (t₂, d₃); simpl in H₁.
    injection H₁; clear H₁; intros; subst t₂ el₄.

bbb.

 apply norm_list_app_diag with (el₂ := el₂).
 rewrite <- app_assoc.

  apply toto.

  rewrite rev_path_app.
  rewrite rev_path_involutive.

bbb.

Theorem rotate_from_point_in_orbit_1_0_0_is_diff : ∀ p,
  (∃ el, fold_left rotate el (P 1 0 0) = p)
  → ∀ el, el ≠ []
  → norm_list el = el
  → fold_left rotate el p ≠ p.
Proof.
intros p (elp, Horb) el Hne Hel Hr.
assert (fold_left rotate 
vvv.

remember (fold_left rotate el) as w eqn:Hw.
pose proof rotate_0_0_1_b_nonzero w el el₁ d Hel Hn Hw as H.
destruct H as (a, (b, (c, (k, (Hp, Hm))))).
rewrite Hp; intros H.
injection H; intros Hc Hb Ha.
apply Rmult_integral in Hb.
destruct Hb as [Hb| Hb].
 apply Rmult_integral in Hb.
 destruct Hb as [Hb| Hb].
  apply eq_IZR_R0 in Hb; subst b; apply Hm; reflexivity.

  revert Hb; apply sqrt2_neq_0.

 apply Rmult_eq_compat_r with (r := (3 ^ k)%R) in Hb.
 rewrite Rinv_l in Hb; [ lra | apply pow_nonzero; lra ].
Qed.

Definition no_rotation := ([] : list free_elem).
Definition is_identity el := ∀ p, fold_left rotate el p = p.

Theorem rotate_0 : is_identity no_rotation.
Proof. intros p; reflexivity. Qed.

Theorem nonempty_rotation_is_not_identity : ∀ el,
  norm_list el = el
  → el ≠ no_rotation
  → ¬ (is_identity el).
Proof.
intros el Hel Hr Hn.
unfold no_rotation in Hr.
destruct el as [| e]; [ apply Hr; reflexivity | clear Hr ].
destruct e as (t, d); destruct t.
 pose proof Hn (P 0 0 1) as H; revert H.
 destruct d; eapply rotate_0_0_1_is_diff; try eassumption; reflexivity.

 pose proof Hn (P 1 0 0) as H; revert H.
 destruct d; eapply rotate_1_0_0_is_diff; try eassumption; reflexivity.
Qed.

Theorem toto : ∀ p₁ p₂ m,
  p₂ = mat_vec_mul m p₁
  → ∀ el,
    fold_left rotate el p₂ = fold_left rotate el (mat_vec_mul m p₁).
(* ah oui mais c'est trivialement trivial, ça ; j'eusse aimé pouvoir
   plutôt intervertir le chemin et la multiplication par m, mais c'est
   pas commutatif, dans l'espace ! *)
Abort.

End Rotation.

Check nonempty_rotation_is_not_identity.

Section Orbit.

Definition same_orbit x y := ∃ el, fold_left rotate el x = y.

Theorem same_orbit_refl : reflexive _ same_orbit.
Proof. intros; exists []; reflexivity. Qed.

Theorem same_orbit_sym : symmetric _ same_orbit.
Proof.
intros p₁ p₂ (el, H); simpl in H.
unfold same_orbit; simpl.
exists (rev (map negf el)).
revert p₁ p₂ H.
induction el as [| e]; intros; [ symmetry; assumption | simpl in H; simpl ].
rewrite fold_left_app; simpl.
apply IHel in H; rewrite H.
destruct e as (t, d); destruct t, d; simpl.
 apply rot_rot_inv_x.
 apply rot_inv_rot_x.
 apply rot_rot_inv_z.
 apply rot_inv_rot_z.
Qed.

Theorem same_orbit_trans : transitive _ same_orbit.
Proof.
intros p₁ p₂ p₃ (el₁, H₁) (el₂, H₂); simpl in H₁, H₂.
unfold same_orbit; simpl.
exists (el₁ ++ el₂).
rewrite fold_left_app, H₁, H₂; reflexivity.
Qed.

Add Parametric Relation : _ same_orbit
 reflexivity proved by same_orbit_refl
 symmetry proved by same_orbit_sym
 transitivity proved by same_orbit_trans
 as same_orbit_rel.

(*
Require Import ChoiceFacts.
Axiom func_choice : FunctionalChoice.
Print FunctionalChoice_on.
*)
Axiom func_choice : ∀ A B (R : A → B → Prop),
  (∀ x, ∃ y, R x y) → ∃ f, ∀ x : A, R x (f x).

Axiom well_ordering : ∀ A,
  ∃ (R : A → A → Prop),
  ∀ P, (∃ x, P x) → ∃ ! y, P y ∧ ∀ z, P z → R y z.

Definition total_order A (R : relation A) := ∀ x y, R x y ∨ R y x.

(* definition of well-ordering above does not require R to be an order
   but actually, it is possible to deduce it from its definition; it
   is also a total order *)
Theorem well_ordering_ordered : ∀ A,
  ∃ (R : A → A → Prop), order _ R ∧ total_order _ R ∧
  ∀ P, (∃ x, P x) → ∃ ! y, P y ∧ ∀ z, P z → R y z.
Proof.
intros A.
pose proof well_ordering A as H.
destruct H as (R, H).
assert (Hrefl : reflexive _ R).
 intros x.
 pose proof H (eq x) (ex_intro _ x eq_refl) as Hx.
 destruct Hx as (y, ((Hy, Hz), Hu)).
 destruct Hy; apply Hz; reflexivity.

 assert (Hasym : antisymmetric _ R).
  intros x y Hxy Hyx.
  set (Q t := t = x ∨ t = y).
  pose proof H Q (ex_intro _ x (or_introl eq_refl)) as Hx.
  destruct Hx as (t, ((Ht, Hmin), Huniq)).
  destruct Ht; subst t.
   apply Huniq.
   split; [ right; reflexivity | ].
   intros z Hz.
   destruct Hz; subst z; [ assumption | apply Hrefl ].

   symmetry; apply Huniq.
   split; [ left; reflexivity | ].
   intros z Hz.
   destruct Hz; subst z; [ apply Hrefl | assumption ].

  assert (Htrans : transitive _ R).
   intros x y z Hxy Hyz.
   set (Q t := t = x ∨ t = y ∨ t = z).
   pose proof H Q (ex_intro _ x (or_introl eq_refl)) as Hx.
   destruct Hx as (t, ((Ht, Hmin), Huniq)).
   destruct Ht as [| [|]]; subst t.
    apply Hmin; right; right; reflexivity.

    pose proof Hmin x (or_introl eq_refl) as Hyx.
    pose proof Hasym _ _ Hxy Hyx; subst y; assumption.

    pose proof Hmin y (or_intror (or_introl eq_refl)) as Hzy.
    pose proof Hasym _ _ Hyz Hzy; subst y; assumption.

    exists R.
    split; [ split; assumption | ].
    split; [ | assumption ].
    intros x y.
    set (Q t := t = x ∨ t = y).
    pose proof H Q (ex_intro _ x (or_introl eq_refl)) as Hx.
    destruct Hx as (t, ((Ht, Hmin), Huniq)).
    destruct Ht; subst t.
     left; apply Hmin; right; reflexivity.
     right; apply Hmin; left; reflexivity.
Qed.

(* ok, this is a great theorem, but I don't like the fact that I had to
   use both the axiom of well-ordering *and* the axiom of choice, which
   are supposed to be equivalent; it is because the axiom of well ordering
   is used for all the sphere (well ordering all points of the sphere),
   which is used then to select a specific point (the "minimum" one) to
   each orbit using... the axiom of choice *)
Theorem same_choice_in_same_orbit : ∃ f : point → point,
  (∀ x, same_orbit x (f x)) ∧
  (∀ x y, same_orbit x y ↔ f x = f y).
Proof.
assert
  (H : ∃ le, order _ le ∧
   ∀ x, ∃! y, same_orbit x y ∧ ∀ z, same_orbit x z → le y z).
 pose proof well_ordering_ordered point as H.
 destruct H as (R, (Ho, (Htot, H))).
 exists R.
 split; [ assumption | intros x; apply H; exists x; reflexivity ].

 destruct H as (le, (Ho, H)).
 apply func_choice in H.
 destruct H as (f, Hf).
 exists f; split.
  intros x.
  pose proof Hf x as Hx.
  unfold unique in Hx.
  destruct Hx as ((Hxfx, Hlex), Hx); assumption.

  intros x y.
  pose proof Hf x as Hx.
  unfold unique in Hx; simpl in Hx.
  destruct Hx as ((Hxfx, Hlex), Hx).
  pose proof Hf y as Hy.
  unfold unique in Hy; simpl in Hy.
  destruct Hy as ((Hyfy, Hley), Hy).
  split.
   intros Hxy.
   destruct Ho as (_, _, Hoa).
   apply Hoa.
    apply Hlex.
    etransitivity; [ eapply Hxy | eassumption ].

    apply Hley.
    etransitivity; [ symmetry; eassumption | apply Hxfx ].

   intros Hfxy.
   etransitivity; [ eapply Hxfx | rewrite Hfxy; symmetry; apply Hyfy ].
Qed.

Check same_choice_in_same_orbit.

Definition in_image {A B} (f : A → B) := λ x, ∃ y, x = f y.

(* the orbits of the image of f form a partition of the sphere
   1/ ∀ x, x in the orbit of someone in the image of f,
   2/ ∀ x y two different points in the image of x, their orbits
      are different. *)

Theorem orbit_partition : ∃ f : point → point,
  (∀ x, ∃ y, same_orbit (f y) x) ∧
  (∀ x y, in_image f x → in_image f y → x ≠ y → ¬ same_orbit x y).
Proof.
pose proof same_choice_in_same_orbit as H.
destruct H as (f, (Hxfx, Hiff)).
exists f; split.
 intros x.
 exists x; symmetry.
 apply Hxfx.

 intros x y Hx Hy Hneq.
 destruct Hx as (x', Hx).
 destruct Hy as (y', Hy).
 intros H; apply Hneq.
 subst x y; apply Hiff.
 etransitivity; [ apply Hxfx | ].
 etransitivity; [ eassumption | ].
 symmetry; apply Hxfx.
Qed.

End Orbit.
