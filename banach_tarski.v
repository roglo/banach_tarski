(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

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

Theorem cons_to_app {A} : ∀ (e : A) el, e :: el = [e] ++ el.
Proof. reflexivity. Qed.

Theorem fold_right_cons {A B} : ∀ f (x : A) (y : B) l,
  fold_right f x (y :: l) = f y (fold_right f x l).
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
Record F2 := mkF₂ { str : list free_elem }.

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

Theorem free_elem_dec : ∀ e₁ e₂ : free_elem, { e₁ = e₂ } + { e₁ ≠ e₂ }.
Proof.
intros.
destruct e₁ as (t₁, d₁).
destruct e₂ as (t₂, d₂).
destruct (letter_dec t₁ t₂) as [H₁| H₁]; [ subst t₂ | ].
 destruct (Bool.bool_dec d₁ d₂) as [H₂| H₂]; [ subst d₂ | ].
  left; reflexivity.

  right; intros H; apply H₂.
  injection H; intros; assumption.

 right; intros H; apply H₁.
 injection H; intros; assumption.
Qed.

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

Definition negb_true_neq_true : negb true ≠ true := false_neq_negb_false.
Definition negb_false_neq_false : negb false ≠ false := true_neq_negb_true.

Theorem bool_dec_negb_l : ∀ b,
  Bool.bool_dec (negb b) b =
  right (if b return _ then negb_true_neq_true else negb_false_neq_false).
Proof. intros b; destruct b; reflexivity. Qed.

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

Theorem letter_opp_negf : ∀ e₁ e₂, letter_opp e₁ e₂ ↔ e₁ = negf e₂.
Proof.
intros.
destruct e₁ as (t₁, d₁).
destruct e₂ as (t₂, d₂).
split; intros H.
 apply letter_opp_iff in H.
 destruct H; subst t₂ d₂; simpl.
 rewrite Bool.negb_involutive; reflexivity.

 injection H; intros; subst; simpl.
 rewrite letter_dec_diag, bool_dec_negb_l.
 constructor.
Qed.

Theorem no_fixpoint_negf : ∀ e, negf e ≠ e.
Proof.
intros * H.
destruct e as (t, d).
injection H.
apply Bool.no_fixpoint_negb.
Qed.

Theorem not_letter_opp_diag : ∀ e, ¬ letter_opp e e.
Proof.
intros e H.
apply letter_opp_negf in H; symmetry in H.
revert H; apply no_fixpoint_negf.
Qed.

Theorem negf_involutive : ∀ e, negf (negf e) = e.
Proof.
intros (t, d); simpl.
rewrite Bool.negb_involutive; reflexivity.
Qed.

Theorem letter_opp_negf_l : ∀ e, letter_opp (negf e) e.
Proof.
intros.
apply letter_opp_negf; reflexivity.
Qed.

Theorem letter_opp_negf_r : ∀ e, letter_opp e (negf e).
Proof.
intros.
apply letter_opp_negf.
rewrite negf_involutive; reflexivity.
Qed.

Theorem letter_opp_sym : ∀ e₁ e₂, letter_opp e₁ e₂ → letter_opp e₂ e₁.
Proof.
intros * H.
apply letter_opp_negf in H.
subst e₁.
apply letter_opp_negf_r.
Qed.

Theorem negf_ạ : negf ạ = ạ⁻¹.
Proof. reflexivity. Qed.

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

Theorem norm_list_cancel2 : ∀ el e,
  norm_list (negf e :: e :: el) = norm_list el.
Proof.
intros el e.
pose proof norm_list_cancel el (negf e) as H.
rewrite negf_involutive in H.
assumption.
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

Theorem norm_list_cancel_in2 : ∀ el₁ el₂ e,
  norm_list (el₁ ++ negf e :: e :: el₂) =
  norm_list (el₁ ++ el₂).
Proof.
intros.
pose proof norm_list_cancel_in el₁ el₂ (negf e) as H.
rewrite negf_involutive in H; assumption.
Qed.

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
  apply letter_opp_negf in H₁; subst e₂.
  rewrite cons_comm_app.
  do 2 rewrite app_assoc.
  rewrite <- IHel₂.
  do 2 rewrite <- app_assoc; simpl.
  rewrite norm_list_cancel_in2.
  reflexivity.

  rewrite cons_comm_app.
  do 2 rewrite app_assoc.
  rewrite <- IHel₂.
  do 2 rewrite <- app_assoc.
  reflexivity.
Qed.

Theorem norm_list_idemp : ∀ el, norm_list (norm_list el) = norm_list el.
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
  apply letter_opp_negf in H₁; subst e el₂.
  exfalso; revert Hel₁; apply norm_list_no_start.

  injection Hn; clear Hn; intros; subst el₁.
  assumption.
Qed.

Theorem norm_list_cons_cons : ∀ e₁ e el el₁,
  norm_list el = e₁ :: el₁
  → e₁ ≠ negf e
  → norm_list (e :: norm_list el) = e :: norm_list el.
Proof.
intros * Hn Hnf; simpl.
rewrite norm_list_idemp, Hn.
destruct (letter_opp_dec e e₁) as [H₁| H₁]; [ | reflexivity ].
exfalso; apply Hnf, letter_opp_negf, letter_opp_sym.
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
rewrite <- Hel₁, norm_list_idemp.
split; [ reflexivity | ].
unfold start_with; simpl.
rewrite norm_list_idemp, Hel₁.
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

Fixpoint split_at_cancel el :=
  match el with
  | [] => None
  | [e₁] => None
  | e₁ :: (e₂ :: el₂) as el₁ =>
      if letter_opp_dec e₁ e₂ then Some ([], e₁, el₂)
      else
       match split_at_cancel el₁ with
       | Some (el₃, e₃, el₄) => Some (e₁ :: el₃, e₃, el₄)
       | None => None
       end
  end.

Theorem norm_dec : ∀ el,
  { norm_list el = el } +
  { ∃ el₁ e el₂, split_at_cancel el = Some (el₁, e, el₂) }.
Proof.
intros el.
induction el as [| e]; [ left; reflexivity | ].
destruct IHel as [H₁| H₁].
 simpl; rewrite H₁.
 destruct el as [| e₁]; [ left; reflexivity | ].
 simpl in H₁.
 destruct (letter_opp_dec e e₁) as [H₂| H₂]; [ | left; reflexivity ].
 right; exists [], e, el; reflexivity.

 right.
 destruct H₁ as (el₁, (e₁, (el₂, Hs))); simpl.
 destruct el as [| e₂]; [ discriminate Hs | ].
 destruct (letter_opp_dec e e₂) as [H₁| H₁].
  exists [], e, el; reflexivity.

  rewrite Hs.
  exists (e :: el₁), e₁, el₂; reflexivity.
Qed.

Theorem split_at_cancel_some : ∀ el el₁ el₂ e,
  split_at_cancel el = Some (el₁, e, el₂)
  → el = el₁ ++ e :: negf e :: el₂.
Proof.
intros el el₁ el₂ e Hs.
revert e el₁ el₂ Hs.
induction el as [| e₁]; intros; [ discriminate Hs | ].
simpl in Hs.
destruct el as [| e₂]; [ discriminate Hs | ].
destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
 injection Hs; clear Hs; intros; subst e el₁ el₂; simpl.
 f_equal; f_equal.
 apply letter_opp_sym, letter_opp_negf in H₁.
 assumption.

 remember (split_at_cancel (e₂ :: el)) as u eqn:Hu.
 symmetry in Hu.
 destruct u as [((el₃, e₃), el₄)| ]; [ | discriminate Hs ].
 injection Hs; clear Hs; intros; subst el₁ e₃ el₄; simpl.
 f_equal.
 apply IHel; reflexivity.
Qed.

End Free_Group.

(* Step 2 *)

Require Import Reals Psatz Nsatz.

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

Theorem Rplus_shuffle0 : ∀ n m p : ℝ, (n + m + p)%R = (n + p + m)%R.
Proof.
intros.
rewrite Rplus_comm, <- Rplus_assoc.
f_equal; apply Rplus_comm.
Qed.

Theorem Rmult_shuffle0 : ∀ n m p : ℝ, (n * m * p)%R = (n * p * m)%R.
Proof.
intros.
rewrite Rmult_comm, <- Rmult_assoc.
f_equal; apply Rmult_comm.
Qed.

Theorem fold_Rminus : ∀ a b, (a + - b = a - b)%R.
Proof. reflexivity. Qed.

Theorem fold_Rsqr : ∀ a, (a * a = a²)%R.
Proof. reflexivity. Qed.

Definition determinant a b c d := (a * d - b * c)%R.

Theorem fold_determinant : ∀ a b c d, (a * d - b * c)%R = determinant a b c d.
Proof. reflexivity. Qed.

Theorem determinant_comm : ∀ a b c d,
  determinant a b c d = determinant d c b a.
Proof. intros; unfold determinant; ring. Qed.

Theorem Rsolve_system_equation_2_variables : ∀ a b c a' b' c' x y,
  (determinant a b a' b' ≠ 0)%R
  → (a * x + b * y = c)%R
  → (a' * x + b' * y = c')%R
  → x = (determinant c b c' b' / determinant a b a' b')%R ∧
    y = (determinant a c a' c' / determinant a b a' b')%R.
Proof.
assert (solve_1_var : ∀ a b c a' b' c' x y,
  (determinant a b a' b' ≠ 0)%R
  → (a * x + b * y = c)%R
  → (a' * x + b' * y = c')%R
  → x = (determinant c b c' b' / determinant a b a' b')%R).
 intros a b c a' b' c' x y Hd H₁ H₂.
 apply Rmult_eq_compat_r with (r := b') in H₁.
 apply Rmult_eq_compat_r with (r := b) in H₂.
 rewrite Rmult_plus_distr_r in H₁, H₂.
 apply Rplus_eq_compat_r with (r := (- (c' * b))%R) in H₁.
 replace (c' * b)%R with (b * c')%R in H₁ at 2 by apply Rmult_comm.
 rewrite <- H₂ in H₁.
 do 2 rewrite fold_Rminus in H₁.
 rewrite fold_determinant in H₁.
 ring_simplify in H₁.
 replace (a * x * b')%R with (x * a * b')%R in H₁ by ring.
 do 2 rewrite Rmult_assoc in H₁.
 rewrite <- Rmult_minus_distr_l in H₁.
 rewrite fold_determinant in H₁.
 rewrite <- H₁; field; assumption.

 intros a b c a' b' c' x y Hd H₁ H₂.
 split; [ eapply solve_1_var; eassumption | ].
 rewrite Rplus_comm in H₁, H₂.
 rewrite determinant_comm in Hd.
 setoid_rewrite determinant_comm.
 eapply solve_1_var; eassumption.
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

Definition mat_of_elem e :=
  match e with
  | ạ => rot_x
  | ạ⁻¹ => rot_inv_x
  | ḅ => rot_z
  | ḅ⁻¹ => rot_inv_z
  end.

Definition rotate e pt := mat_vec_mul (mat_of_elem e) pt.

Definition rev_path el := map negf (rev el).

Definition rotate_param e '(a, b, c, N) :=
  match e with
  | ạ => ((3 * a)%Z, (b - 2 * c)%Z, (4 * b + c)%Z, S N)
  | ạ⁻¹ => ((3 * a)%Z, (b + 2 * c)%Z, (- 4 * b + c)%Z, S N)
  | ḅ => ((a - 4 * b)%Z, (b + 2 * a)%Z, (3 * c)%Z, S N)
  | ḅ⁻¹ => ((a + 4 * b)%Z, (b - 2 * a)%Z, (3 * c)%Z, S N)
  end.

Definition mat_mul m₁ m₂ :=
  mkmat
    (a₁₁ m₁ * a₁₁ m₂ + a₁₂ m₁ * a₂₁ m₂ + a₁₃ m₁ * a₃₁ m₂)
    (a₁₁ m₁ * a₁₂ m₂ + a₁₂ m₁ * a₂₂ m₂ + a₁₃ m₁ * a₃₂ m₂)
    (a₁₁ m₁ * a₁₃ m₂ + a₁₂ m₁ * a₂₃ m₂ + a₁₃ m₁ * a₃₃ m₂)
    (a₂₁ m₁ * a₁₁ m₂ + a₂₂ m₁ * a₂₁ m₂ + a₂₃ m₁ * a₃₁ m₂)
    (a₂₁ m₁ * a₁₂ m₂ + a₂₂ m₁ * a₂₂ m₂ + a₂₃ m₁ * a₃₂ m₂)
    (a₂₁ m₁ * a₁₃ m₂ + a₂₂ m₁ * a₂₃ m₂ + a₂₃ m₁ * a₃₃ m₂)
    (a₃₁ m₁ * a₁₁ m₂ + a₃₂ m₁ * a₂₁ m₂ + a₃₃ m₁ * a₃₁ m₂)
    (a₃₁ m₁ * a₁₂ m₂ + a₃₂ m₁ * a₂₂ m₂ + a₃₃ m₁ * a₃₂ m₂)
    (a₃₁ m₁ * a₁₃ m₂ + a₃₂ m₁ * a₂₃ m₂ + a₃₃ m₁ * a₃₃ m₂).

Definition mat_id :=
  mkmat
    1 0 0
    0 1 0
    0 0 1.

Delimit Scope mat_scope with mat.
Notation "m₁ * m₂" := (mat_mul m₁ m₂) : mat_scope.

Theorem mat_mul_id_r : ∀ m, mat_mul m mat_id = m.
Proof.
intros m.
unfold mat_mul, mat_id; simpl.
progress repeat rewrite Rmult_1_r.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
destruct m; reflexivity.
Qed.

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
    ∧ N = (n + length el)%nat.
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
  destruct t, d; injection Hr; clear Hr; intros; subst a₁ b₁ c₁ N₁ N; simpl.
   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   unfold Rdiv.
   rewrite Rmult5_sqrt2_sqrt5; [ f_equal; lra | lra ].

   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   unfold Rdiv.
   rewrite Rmult5_sqrt2_sqrt5; [ f_equal; lra | lra ].

   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   unfold Rdiv.
   rewrite Rmult5_sqrt2_sqrt5; [ f_equal; lra | lra ].

   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   unfold Rdiv.
   rewrite Rmult5_sqrt2_sqrt5; [ f_equal; lra | lra ].

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
apply letter_opp_negf in H₁; subst e₁.
revert Hn; apply norm_list_no_start2.
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
 apply letter_opp_sym, letter_opp_negf in H₁; subst e₁.
 destruct e as (t, d).
 exists [], t, d, el.
 reflexivity.

 right.
 destruct IHel as (el₁, (t, (d, (el₂, IHel)))).
 exists (e :: el₁), t, d, el₂; subst el.
 reflexivity.
Qed.

Theorem norm_list_is_cons : ∀ el e el₁,
  norm_list el = e :: el₁ → norm_list el₁ = el₁.
Proof.
intros * H.
destruct (norm_list_dec el₁) as [H₁| H₁]; [ assumption | ].
destruct H₁ as (el₂ & t & d & el₃ & H₁).
subst el₁.
exfalso; revert H.
replace (E t (negb d)) with (negf (E t d)) by reflexivity.
rewrite app_comm_cons.
apply norm_list_no_consec.
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

(* because of Require Import Nsatz, there is a semantic error here
Theorem rev_path_single : ∀ e, rev_path [e] = [negf e].
*)
Theorem rev_path_single : ∀ e, rev_path [e] = negf e :: [].
Proof. intros e; reflexivity. Qed.

Theorem rev_path_nil : rev_path [] = [].
Proof. reflexivity. Qed.

Theorem rev_path_is_nil : ∀ el, rev_path el = [] → el = [].
Proof.
intros el Hr.
destruct el as [| e]; [ reflexivity | ].
rewrite rev_path_cons, rev_path_single in Hr.
destruct (rev_path el); discriminate Hr.
Qed.

Theorem rev_path_eq_eq : ∀ el₁ el₂,
  rev_path el₁ = rev_path el₂ ↔ el₁ = el₂.
Proof.
intros el₁ el₂.
split; [ | intros H; subst; reflexivity ].
intros Hr.
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
apply letter_opp_sym, letter_opp_negf in H₁.
rewrite negf_involutive in H₁; subst e₁.
rewrite <- rev_path_involutive in Hel₁.
rewrite rev_path_cons, rev_path_single in Hel₁.
simpl in Hel₁.
apply -> rev_path_eq_eq in Hel₁.
rewrite Hel₁ in Hel.
rewrite <- app_assoc in Hel; simpl in Hel.
revert Hel.
apply norm_list_no_consec2.
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

Theorem split_app_eq {A} : ∀ el₁ el₂ el₃ el₄ : list A,
  el₁ ++ el₂ = el₃ ++ el₄
  → { ∃ el, el₃ = el₁ ++ el ∧ el₂ = el ++ el₄ } +
    { ∃ el, el₁ = el₃ ++ el ∧ el₄ = el ++ el₂ }.
Proof.
intros el₁ el₂ el₃ el₄ Hel.
revert el₂ el₃ el₄ Hel.
induction el₁ as [| e₁]; intros.
 left; exists el₃.
 split; [ reflexivity | assumption ].

 destruct el₃ as [| e₃].
  right; exists (e₁ :: el₁).
  split; [ reflexivity | symmetry; assumption ].

  simpl in Hel.
  injection Hel; clear Hel; intros; subst e₃.
  apply IHel₁ in H.
  destruct H as [H| H].
   left; destruct H as (el, (H₁, H₂)); subst el₂ el₃.
   exists el; split; reflexivity.

   right; destruct H as (el, (H₁, H₂)); subst el₁ el₄.
   exists el; split; reflexivity.
Qed.

Theorem norm_list_app_split : ∀ el₁ el₂ el₃ el₄ e,
  norm_list el₁ ++ norm_list el₂ = el₃ ++ e :: negf e :: el₄
  → norm_list el₁ = el₃ ++ [e] ∧ norm_list el₂ = negf e :: el₄.
Proof.
intros el₁ el₂ el₃ el₄ e Hn.
apply split_app_eq in Hn.
destruct Hn as [(el, (H₁, H₂))| (el, (H₁, H₂))].
 exfalso; revert H₂; apply norm_list_no_consec.

 rewrite cons_to_app in H₂.
 apply split_app_eq in H₂.
 destruct H₂ as [(el', (H₂, H₃))| (el', (H₂, H₃))].
  subst el.
  destruct el' as [| e'].
   rewrite app_nil_r in H₁.
   rewrite app_nil_l in H₃; symmetry in H₃.
   split; assumption.

   simpl in H₃.
   injection H₃; clear H₃; intros H₂ H₃; subst e'.
   exfalso; revert H₁; apply norm_list_no_consec.

  destruct el as [| e₁].
   simpl in H₂; subst el'.
   exfalso; revert H₃; apply norm_list_no_start.

   simpl in H₂.
   injection H₂; clear H₂; intros H₂ H₄; subst e₁.
   symmetry in H₂.
   apply app_eq_nil in H₂.
   destruct H₂; subst el el'.
   split; assumption.
Qed.  

Theorem norm_list_app_is_nil : ∀ el₁ el₂,
  el₁ = norm_list el₁
  → el₂ = norm_list el₂
  → norm_list (el₁ ++ el₂) = []
  → el₂ = rev_path el₁.
Proof.
intros el₁ el₂ Hel₁ Hel₂ Hn.
symmetry in Hel₁, Hel₂.
remember (length (el₁ ++ el₂)) as len eqn:Hlen.
symmetry in Hlen.
rewrite <- Hel₁, <- Hel₂, rev_path_norm_list.
revert el₁ el₂ Hel₁ Hel₂ Hn Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct (norm_list_dec (el₁ ++ el₂)) as [H₁| H₁].
 rewrite H₁ in Hn.
 apply app_eq_nil in Hn.
 destruct Hn; subst el₁ el₂; reflexivity.

 destruct H₁ as (el₃ & t & d & el₄ & H₁).
 rewrite H₁, app_length, Nat.add_comm in Hlen.
 destruct len; [ discriminate Hlen | ].
 destruct len; [ discriminate Hlen | simpl in Hlen ].
 do 2 apply -> Nat.succ_inj_wd in Hlen.
 rewrite Nat.add_comm, <- app_length in Hlen.
 assert (H₂ : len < S (S len)).
  transitivity (S len); apply Nat.lt_succ_diag_r.

  rewrite <- Hel₁, <- Hel₂ in H₁.
  apply norm_list_app_split in H₁.
  destruct H₁ as (H₃, H₄).
  rewrite Hel₁ in H₃; rewrite H₃ in Hel₁.
  apply norm_list_app_diag in Hel₁.
  rewrite Hel₂ in H₄; rewrite H₄ in Hel₂.
  apply norm_list_cons in Hel₂.
  rewrite H₃, H₄ in Hn.
  rewrite <- app_assoc, <- cons_comm_app in Hn.
  rewrite norm_list_cancel_in in Hn.
  pose proof IHlen len H₂ el₃ el₄ Hel₁ Hel₂ Hn Hlen as H.
  rewrite Hel₂, <- rev_path_norm_list, Hel₁ in H.
  rewrite H₃, H₄, H, rev_path_app.
  reflexivity.
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
 apply rot_inv_rot_x.
 apply rot_rot_inv_x.
 apply rot_inv_rot_z.
 apply rot_rot_inv_z.
Qed.

Theorem rotate_neg_rotate : ∀ e p, rotate (negf e) (rotate e p) = p.
Proof.
intros (t, d) p; simpl.
destruct t, d; simpl.
 apply rot_rot_inv_x.
 apply rot_inv_rot_x.
 apply rot_rot_inv_z.
 apply rot_inv_rot_z.
Qed.

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

Theorem rotate_cancel_in : ∀ el₁ el₂ e p,
  fold_right rotate p (el₁ ++ e :: negf e :: el₂) =
  fold_right rotate p (el₁ ++ el₂).
Proof.
intros.
do 2 rewrite fold_right_app; simpl.
rewrite rotate_rotate_neg; reflexivity.
Qed.

Theorem rotate_cancel_start : ∀ el e p,
  fold_right rotate p (e :: negf e :: el) =
  fold_right rotate p el.
Proof.
intros.
pose proof rotate_cancel_in [] el e p as H.
apply H.
Qed.

Theorem rotate_rotate_norm : ∀ el p,
  fold_right rotate p el = fold_right rotate p (norm_list el).
Proof.
intros el p.
remember (length el) as len eqn:Hlen; symmetry in Hlen.
revert el p Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct (norm_list_dec el) as [H₁| H₁]; [ rewrite H₁; reflexivity | ].
destruct H₁ as (el₁ & t & d & el₂ & H₁).
subst el.
rewrite rotate_cancel_in, norm_list_cancel_in.
destruct len; [ destruct el₁; discriminate Hlen | ].
destruct len.
 destruct el₁; [ discriminate Hlen | simpl in Hlen ].
 destruct el₁; discriminate Hlen.

 apply IHlen with len.
  transitivity (S len); apply Nat.lt_succ_diag_r.

  clear - Hlen.
  revert len el₂ Hlen.
  induction el₁ as [| e₁]; intros.
   simpl in Hlen; simpl.
   do 2 apply Nat.succ_inj in Hlen; assumption.

   simpl in Hlen; simpl.
   apply Nat.succ_inj in Hlen.
   destruct len.
    destruct el₁; [ discriminate Hlen | simpl in Hlen ].
    destruct el₁; discriminate Hlen.

    f_equal.
    apply IHel₁; assumption.
Qed.

Theorem length_rev_path : ∀ el, length (rev_path el) = length el.
Proof.
intros el.
induction el as [| e]; [ reflexivity | simpl ].
rewrite rev_path_cons, app_length; simpl.
rewrite IHel, Nat.add_1_r; reflexivity.
Qed.

Theorem rotate_rev_path : ∀ el p₁ p₂,
  fold_right rotate p₁ el = p₂
  → fold_right rotate p₂ (rev_path el) = p₁.
Proof.
intros el p₁ p₂ Hr.
revert p₁ p₂ Hr.
induction el as [| e]; intros; [ symmetry; assumption | ].
simpl in Hr.
rewrite rev_path_cons, rev_path_single, fold_right_app; simpl.
apply IHel; rewrite <- Hr.
rewrite rotate_neg_rotate.
reflexivity.
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
(* perhaps I should generalize that to any starting point which is
   a fixpoint? something like that... *)
assert (Hp : fold_right rotate (P 1 0 0) (rev_path el₂ ++ el₁) = P 1 0 0).
 rewrite fold_right_app, Hp₁, <- Hp₂.
 rewrite <- fold_right_app.
 rewrite app_path_rev_path; reflexivity.

 clear p Hp₁ Hp₂.
 remember (length (rev_path el₂ ++ el₁)) as len eqn:Hlen.
 symmetry in Hlen.
 revert el₁ el₂ el'₁ el'₂ d₁ d₂ Hel₁ Hel₂ Hn₁ Hn₂ Hd Hlen Hp.
 induction len as (len, IHlen) using lt_wf_rec; intros.
 destruct len.
  rewrite app_length in Hlen.
  apply Nat.eq_add_0 in Hlen.
  destruct Hlen as (Hl₁, Hl₂).
  apply length_zero_iff_nil in Hl₁.
  apply length_zero_iff_nil in Hl₂.
  apply rev_path_is_nil in Hl₁.
  move Hl₁ at top; move Hl₂ at top; subst el₁ el₂.
  destruct el'₁; discriminate Hel₁.

  destruct (norm_dec (rev_path el₂ ++ el₁)) as [H₁| H₁].
   revert Hp; rewrite Hel₁, app_assoc.
   rewrite Hel₁, app_assoc in H₁.
   remember (rev_path el₂ ++ el'₁) as el₄ eqn:Hel₄.
   remember (el₄ ++ [E lb d₁]) as el₃ eqn:Hel₃.
   pose proof rotate_1_0_0_is_diff el₃ el₄ d₁ Hel₃ H₁ as H₂.
   apply H₂.

   destruct H₁ as (el₄, (e, (el₃, Ht))).
   generalize Ht; intros Hs.
   apply split_at_cancel_some in Hs.
   rewrite Hs, rotate_cancel_in in Hp.
   rewrite Hs in Hlen.
   rewrite app_length in Hlen; simpl in Hlen.
   do 2 rewrite Nat.add_succ_r in Hlen.
   apply Nat.succ_inj in Hlen.
   rewrite <- length_rev_path in Hlen.
   rewrite <- app_length in Hlen.
   destruct len; [ discriminate Hlen | ].
   apply Nat.succ_inj in Hlen.
   rewrite <- Hn₁, <- Hn₂ in Hs.
   rewrite rev_path_norm_list in Hs.
   apply norm_list_app_split in Hs.
   destruct Hs as (Hs₂, Hs₁).
   rewrite <- rev_path_norm_list in Hs₂.
   apply rev_path_eq_eq in Hs₂.
   rewrite rev_path_involutive, rev_path_app in Hs₂; simpl in Hs₂.
   rewrite Hn₁ in Hs₁.
   rewrite Hn₂ in Hs₂.
   destruct el₁ as [| e₁]; [ discriminate Hs₁ | ].
   injection Hs₁; clear Hs₁; intros; subst e₁ el₃.
   apply norm_list_cons in Hn₁.
   destruct el'₁ as [| e'₁].
    simpl in Hel₁.
    injection Hel₁; clear Hel₁; intros H₁ H₂; subst el₁.
    rewrite <- negf_involutive in H₂.
    apply negf_eq_eq in H₂; subst e; simpl in Ht.
    rewrite Bool.negb_involutive in Ht.
    rewrite negf_involutive in Hd, Hs₂.
    clear Hn₁.
    rewrite app_nil_r in Hlen, Hp.
    destruct el₄ as [| (t₄, d₄)].
     rewrite rev_path_nil in Hs₂.
     apply Hd; symmetry; assumption.

     rewrite rev_path_cons, rev_path_single in Hs₂; simpl in Hs₂.
     rewrite Hel₂, app_comm_cons in Hs₂.
     apply app_inj_tail in Hs₂.
     destruct Hs₂ as (Hs₂, Hs₃).
     injection Hs₃; clear Hs₃; intros; subst t₄ d₂ el'₂.
     clear Hd.
     generalize Hn₂; intros Hn₁.
     apply norm_list_rev_path in Hn₁.
     rewrite Hel₂ in Hn₁.
     rewrite rev_path_app, rev_path_single in Hn₁.
     remember norm_list as f; simpl in Hn₁; subst f.
     rewrite Bool.negb_involutive in Hn₁.
     rewrite rev_path_cons, rev_path_involutive in Hn₁.
     rewrite app_comm_cons in Hn₁.
     apply norm_list_app_diag in Hn₁.
     apply norm_list_rev_path in Hn₁.
     rewrite rev_path_cons, rev_path_single in Hn₁.
     simpl in Hn₁.
     apply rotate_rev_path in Hp.
     rewrite rev_path_cons, rev_path_single in Hp; simpl in Hp.
     revert Hp.
     eapply rotate_1_0_0_is_diff; [ reflexivity | assumption ].

    simpl in Hel₁.
    injection Hel₁; clear Hel₁; intros H₁ H₂; subst e'₁.
    destruct el₄ as [| (t₄, d₄)].
     revert Hp; simpl.
     eapply rotate_1_0_0_is_diff; eassumption.

     rewrite rev_path_cons, rev_path_single in Hs₂; simpl in Hs₂.
     rewrite Hel₂, app_comm_cons in Hs₂.
     apply app_inj_tail in Hs₂.
     destruct Hs₂ as (Hs₂, Hs₃).
     injection Hs₃; clear Hs₃; intros; subst t₄ d₂ el'₂.
     apply rotate_rev_path in Hp.
     rewrite rev_path_app in Hp.
     remember (rev_path (E lb d₄ :: el₄)) as el₃ eqn:Hel₃.
     revert Hp.
     rewrite rev_path_cons, rev_path_single in Hel₃; simpl in Hel₃.
     rewrite <- app_comm_cons, <- Hel₃ in Hel₂.
     rewrite Hel₂ in Hd.
     assert (Hd₂ : el₁ ≠ el₃) by (intros H; apply Hd; f_equal; assumption).
     apply not_eq_sym in Hd₂.
     rewrite Hel₂ in Hn₂.
     apply norm_list_cons in Hn₂.
     rewrite app_length, Nat.add_comm in Hlen.
     eapply IHlen; try eassumption.
     * etransitivity; eapply Nat.lt_succ_diag_r.
     * rewrite app_length, length_rev_path; assumption.
Qed.

Definition on_sphere_ray r '(P x y z) := (x² + y² + z² = r)%R.
Definition on_sphere '(P x y z) := (x² + y² + z² = 1)%R.

Theorem tagada : ∀ el,
  el ≠ []
  → norm_list el = el
  → ∃ p₁ p₂, on_sphere p₁ ∧ on_sphere p₂ ∧ ∀ p, on_sphere p →
    p ≠ p₁ → p ≠ p₂ → fold_right rotate p el ≠ p.
Proof.
intros el Hel Hn.
destruct (list_nil_app_dec el) as [H₁| H₁].
 subst el; exfalso; apply Hel; reflexivity.

 destruct H₁ as (e, (el₁, Hel₁)).
 clear Hel; rename Hel₁ into Hel.
 subst el; rename el₁ into el.
 destruct e as (t, d); destruct t.
  revert d Hn.
  induction el as [| e] using rev_ind; intros.
   rewrite app_nil_l.
   exists (P 1 0 0), (P (-1) 0 0).
   split; [ simpl; rewrite Rsqr_0, Rsqr_1; lra | ].
   split; [ simpl; rewrite Rsqr_0, <- Rsqr_neg, Rsqr_1; lra | ].
   intros p Hsp Hp₁ Hp₂; simpl.
   unfold on_sphere in Hsp.
   unfold mat_vec_mul, rot_inv_x; simpl.
   destruct p as (x, y, z).
   assert (H :
      ∀ u, (u = 2%R) ∨ (u = (-2)%R)
      → P x (1 / 3 * y + u * √ 2 / 3 * z) ((- u) * √ 2 / 3 * y + 1 / 3 * z) ≠
        P x y z).
    intros u Hu H.
    injection H; clear H; intros Hz Hy; move Hy after Hz.
    apply Rplus_eq_compat_r with (r := (- 1 * y)%R) in Hy.
    apply Rplus_eq_compat_r with (r := (- 1 * z)%R) in Hz.
    ring_simplify in Hy.
    ring_simplify in Hz.
    replace (1/3 * y - y)%R with (- (2/3) * y)%R in Hy by field.
    unfold Rminus in Hz.
    rewrite Rplus_assoc in Hz.
    replace (1/3 * z + - z)%R with (- (2/3) * z)%R in Hz by field.
    eapply Rsolve_system_equation_2_variables in Hy; [ | | eassumption ].
     unfold determinant in Hy.
     progress repeat rewrite Rmult_0_l in Hy.
     progress repeat rewrite Rmult_0_r in Hy.
     unfold Rdiv in Hy.
     do 2 rewrite <- Rmult_assoc in Hy.
     rewrite Rmult5_sqrt2_sqrt5 in Hy; [ | lra ].
     rename Hz into H₂.
     destruct Hy as (Hy, Hz).
     ring_simplify in Hy.
     ring_simplify in Hz.
     subst y z.
     ring_simplify in Hsp.
     rewrite Rsqr_0, Rmult_0_r, Rplus_0_r in Hsp.
     rewrite <- Rsqr_1 in Hsp.
     apply Rsqr_eq in Hsp.
     destruct Hsp; subst x; exfalso; [ apply Hp₁ | apply Hp₂ ]; reflexivity.

     unfold determinant, Rdiv.
     do 2 rewrite <- Rmult_assoc.
     rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
     intros H; ring_simplify in H.
     destruct Hu; subst u; lra.

    unfold rotate; simpl.
    destruct d; simpl.
     progress repeat rewrite Rmult_1_l.
     progress repeat rewrite Rmult_0_l.
     progress repeat rewrite Rplus_0_l.
     progress repeat rewrite Rplus_0_r.
     apply H; left; reflexivity.

     progress repeat rewrite Rmult_1_l.
     progress repeat rewrite Rmult_0_l.
     progress repeat rewrite Rplus_0_l.
     progress repeat rewrite Rplus_0_r.
     replace (2 * √2)%R with (- (- 2) * √2)%R by lra.
     apply H; right; reflexivity.

   apply norm_list_app_diag in Hn.
   destruct e as (t₁, d₁).
    destruct t₁.
    pose proof IHel d₁ Hn as H.
    destruct H as (p₁, (p₂, (Hps₁, (Hps₂, Hp)))).
    exists p₁, p₂.
    split; [ assumption | ].
    split; [ assumption | ].
    intros p Hps Hp₁ Hp₂.
    pose proof Hp p Hps Hp₁ Hp₂ as H.
    intros Hr; apply H; clear H.
    rewrite fold_right_app in Hr.
Abort. (* à compléter *)

Definition mat_transp m :=
  mkmat 
   (a₁₁ m) (a₂₁ m) (a₃₁ m)
   (a₁₂ m) (a₂₂ m) (a₃₂ m)
   (a₁₃ m) (a₂₃ m) (a₃₃ m).

Definition mat_det m :=
  (a₁₁ m * (a₂₂ m * a₃₃ m - a₃₂ m * a₂₃ m) +
   a₁₂ m * (a₂₃ m * a₃₁ m - a₃₃ m * a₂₁ m) +
   a₁₃ m * (a₂₁ m * a₃₂ m - a₃₁ m * a₂₂ m))%R.

Arguments mat_det m%mat.

Theorem mat_transp_mul : ∀ m₁ m₂,
  mat_transp (mat_mul m₁ m₂) = mat_mul (mat_transp m₂) (mat_transp m₁).
Proof.
intros m₁ m₂.
unfold mat_transp, mat_mul; simpl; f_equal; ring.
Qed.

Theorem mat_mul_assoc : ∀ m₁ m₂ m₃,
  (m₁ * (m₂ * m₃) = m₁ * m₂ * m₃)%mat.
Proof.
intros m₁ m₂ m₃.
unfold mat_mul; simpl; f_equal; ring.
Qed.

Theorem mat_det_mul : ∀ m₁ m₂,
  mat_det (m₁ * m₂) = (mat_det m₂ * mat_det m₁)%R.
Proof.
intros m₁ m₂.
unfold mat_det; simpl; ring.
Qed.

(* A is a rotation matrix iff
   - A tr(A) = I
   - det A = 1
 *)
Definition is_rotation_matrix A :=
  mat_mul A (mat_transp A) = mat_id ∧
  mat_det A = 1%R.

Theorem rot_x_is_rotation_matrix : is_rotation_matrix rot_x.
Proof.
unfold is_rotation_matrix, mat_transp, mat_mul, mat_det; simpl.
unfold mat_id, Rdiv.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite <- Rmult_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | lra ]).
split; [ f_equal; field | field ].
Qed.

Theorem rot_inv_x_is_rotation_matrix : is_rotation_matrix rot_inv_x.
Proof.
unfold is_rotation_matrix, rot_inv_x, mat_transp, mat_mul, mat_det; simpl.
unfold mat_id, Rdiv.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite <- Rmult_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | lra ]).
split; [ f_equal; field | field ].
Qed.

Theorem rot_z_is_rotation_matrix : is_rotation_matrix rot_z.
Proof.
unfold is_rotation_matrix, mat_transp, mat_mul, mat_det; simpl.
unfold mat_id, Rdiv.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rminus_0_l.
progress repeat rewrite Rminus_0_r.
progress repeat rewrite Ropp_mult_distr_l.
progress repeat rewrite <- Rmult_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | lra ]).
split; [ f_equal; field | field ].
Qed.

Theorem rot_inv_z_is_rotation_matrix : is_rotation_matrix rot_inv_z.
Proof.
unfold is_rotation_matrix, rot_inv_x, mat_transp, mat_mul, mat_det; simpl.
unfold mat_id, Rdiv.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rminus_0_l.
progress repeat rewrite Rminus_0_r.
progress repeat rewrite Ropp_mult_distr_l.
progress repeat rewrite <- Rmult_assoc.
progress repeat (rewrite Rmult5_sqrt2_sqrt5; [ | lra ]).
split; [ f_equal; field | field ].
Qed.

Theorem rotate_is_rotation_matrix : ∀ e, is_rotation_matrix (mat_of_elem e).
Proof.
intros (t, d); destruct t, d.
 apply rot_inv_x_is_rotation_matrix.
 apply rot_x_is_rotation_matrix.
 apply rot_inv_z_is_rotation_matrix.
 apply rot_z_is_rotation_matrix.
Qed.

Theorem path_is_rotation : ∀ el m,
  m = fold_right mat_mul mat_id (map mat_of_elem el)
  → is_rotation_matrix m.
Proof.
intros el m Hm.
revert m Hm.
induction el as [| e]; intros.
 subst m; simpl; unfold is_rotation_matrix, mat_det; simpl.
 rewrite mat_mul_id_r.
 split; [ reflexivity | ring ].

 simpl in Hm.
 remember (fold_right mat_mul mat_id (map mat_of_elem el)) as m₁ eqn:Hm₁.
 pose proof IHel m₁ eq_refl as Hr.
 unfold is_rotation_matrix in Hr.
 unfold is_rotation_matrix.
 destruct Hr as (Hr & Hd).
 rewrite Hm.
 rewrite mat_transp_mul, mat_mul_assoc.
 setoid_rewrite <- mat_mul_assoc at 2.
 rewrite Hr, mat_mul_id_r.
 rewrite mat_det_mul, Hd, Rmult_1_l.
 apply rotate_is_rotation_matrix.
Qed.

(* sources:
   - wikipedia "rotation matrix"
   - http://www.euclideanspace.com/maths/geometry/rotations/
       conversions/matrixToAngle
   does not work if the rotation is 0 or π; but it cannot
   happen in our case *)
Definition rotation_fixpoint (m : matrix) k :=
  let x := (a₃₂ m - a₂₃ m)%R in
  let y := (a₁₃ m - a₃₁ m)%R in
  let z := (a₂₁ m - a₁₂ m)%R in
  P (k * x) (k * y) (k * z).

(* other possible definition suggested by Guillaume Hanrot *)
Definition rotation_fixpoint2 (m : matrix) k :=
  let x := (a₁₂ m * a₂₃ m + (- a₂₂ m + 1) * a₁₃ m)%R in
  let y := (a₁₃ m * a₂₁ m + (- a₁₁ m + 1) * a₂₃ m)%R in
  let z := ((a₁₁ m - 1) * (a₂₂ m - 1) - a₂₁ m * a₁₂ m)%R in
  P (k * x) (k * y) (k * z).

Theorem matrix_fixpoint_ok : ∀ m p k,
  is_rotation_matrix m
  → p = rotation_fixpoint m k
  → mat_vec_mul m p = p.
Proof.
intros m p k Hrm Hn.
subst p.
unfold rotation_fixpoint.
unfold is_rotation_matrix in Hrm.
destruct Hrm as (Ht & Hd).
unfold mat_det in Hd.
unfold mat_mul, mat_transp, mat_id in Ht; simpl in Ht.
injection Ht; clear Ht; intros H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ H₉.
simpl.
setoid_rewrite fold_Rsqr in H₁.
setoid_rewrite fold_Rsqr in H₅.
setoid_rewrite fold_Rsqr in H₉.
move H₉ after H₁; move H₅ after H₁.
move H₄ before H₂; move H₇ before H₃; move H₈ before H₆.
clear H₄ H₇ H₈; move H₆ after H₂.
move Hd before H₉.
rename H₆ into H₁₁; rename H₂ into H₂₁; rename H₃ into H₃₁.
rename H₁ into H₃; rename H₅ into H₂; rename H₉ into H₁.
f_equal; nsatz.
Qed.

Definition fixpoint_of_path el :=
 let m := fold_right mat_mul mat_id (map mat_of_elem el) in
 let '(P x y z) := rotation_fixpoint m 1 in
 let r := √ (x² + y² + z²) in
 P (x / r) (y / r) (z / r).

Definition no_rotation := ([] : list free_elem).
Definition is_identity el := ∀ p, fold_right rotate p el = p.

Theorem rotate_0 : is_identity no_rotation.
Proof. intros p; reflexivity. Qed.

Theorem nonempty_rotation_is_not_identity : ∀ el,
  norm_list el = el
  → el ≠ no_rotation
  → ¬ (is_identity el).
Proof.
intros el Hel Hr Hn.
unfold no_rotation in Hr.
destruct (list_nil_app_dec el) as [| H]; [ contradiction | clear Hr ].
destruct H as (e, (el', H₁)).
destruct e as (t, d); destruct t.
 pose proof Hn (P 0 0 1) as H; revert H.
 destruct d; eapply rotate_0_0_1_is_diff; try eassumption; reflexivity.

 pose proof Hn (P 1 0 0) as H; revert H.
 destruct d; eapply rotate_1_0_0_is_diff; try eassumption; reflexivity.
Qed.

End Rotation.

Section Orbit.

Definition same_orbit x y := ∃ el, fold_right rotate x el = y.

Theorem same_orbit_refl : reflexive _ same_orbit.
Proof. intros; exists []; reflexivity. Qed.

Theorem same_orbit_sym : symmetric _ same_orbit.
Proof.
intros p₁ p₂ (el, H); simpl in H.
unfold same_orbit; simpl.
exists (rev (map negf el)).
revert p₁ p₂ H.
induction el as [| e]; intros; [ symmetry; assumption | simpl in H; simpl ].
rewrite fold_right_app; simpl.
apply IHel; rewrite <- H.
rewrite rotate_neg_rotate.
reflexivity.
Qed.

Theorem same_orbit_trans : transitive _ same_orbit.
Proof.
intros p₁ p₂ p₃ (el₁, H₁) (el₂, H₂); simpl in H₁, H₂.
unfold same_orbit; simpl.
exists (el₂ ++ el₁).
rewrite fold_right_app, H₁, H₂; reflexivity.
Qed.

Add Parametric Relation : _ same_orbit
 reflexivity proved by same_orbit_refl
 symmetry proved by same_orbit_sym
 transitivity proved by same_orbit_trans
 as same_orbit_rel.

Definition equiv_same_orbit : equiv point same_orbit :=
  conj same_orbit_refl (conj same_orbit_trans same_orbit_sym).

(* Type-theoretical Choice Axiom *)
Axiom TTCA : ∀ (A : Type) (R : A → A → Prop), equiv A R →
  ∃ f : A → A, (∀ x : A, R x (f x)) ∧ (∀ x y, R x y → f x = f y).

Theorem same_choice_in_same_orbit : ∃ f : point → point,
  (∀ x, same_orbit x (f x)) ∧
  (∀ x y, same_orbit x y ↔ f x = f y).
Proof.
pose proof (TTCA _ _ equiv_same_orbit) as H.
destruct H as (f, (Hx, Hxy)).
exists f; split; [ apply Hx | ].
intros x y.
split; intros H; [ apply Hxy, H | ].
transitivity (f x); [ apply Hx | ].
transitivity (f y); [ destruct H; reflexivity | symmetry; apply Hx ].
Qed.

Definition in_image {A B} (f : A → B) := λ x, ∃ y, x = f y.

(* the orbits of the image of f form a partition of the sphere
   1/ ∀ x, x is in the orbit of someone in the image of f,
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

Notation "'ạ'" := (E la false).
Notation "'ạ⁻¹'" := (E la true).
Notation "'ḅ'" := (E lb false).
Notation "'ḅ⁻¹'" := (E lb true).

Definition not_in_fixpoints p :=
  ∀ el, norm_list el ≠ [] → fold_right rotate p el ≠ p.

Theorem same_orbit_imp_representant : ∀ f p p₁ el₁,
  (∀ p₁ p₂ : point, same_orbit p₁ p₂ → f p₁ = f p₂)
  → (∀ p : point, same_orbit p (f p))
  → p = f p
  → fold_right rotate (f p₁) el₁ = p
  → f p₁ = p.
Proof.
intros f p p₁ el₁ Hoe Ho H₁ Hr.
pose proof Ho p₁ as Hp₁.
unfold same_orbit in Hp₁.
destruct Hp₁ as (el₃ & Hp₁).
rewrite <- Hp₁, <- fold_right_app in Hr.
rewrite H₁; apply Hoe.
exists (el₁ ++ el₃); assumption.
Qed.

Theorem not_in_fixpoints_one_path : ∀ f p e₁ e₂ el el₂ el₁ el₃,
  not_in_fixpoints p
  → fold_right rotate p el = f p
  → fold_right rotate (f p) el₁ = p
  → norm_list el = el₂ ++ [e₁]
  → norm_list el₁ = e₂ :: el₃
  → e₂ ≠ negf e₁
  → False.
Proof.
intros f p e₁ e₂ el el₂ el₁ el₃ Hnf Hel H₆ H₂ H₄ Hd.
rewrite rotate_rotate_norm in Hel, H₆.
rewrite <- Hel in H₆.
rewrite <- fold_right_app in H₆.
revert H₆.
apply Hnf.
intros H.
apply norm_list_app_is_nil in H.
 rewrite H₄, H₂ in H.
 apply rev_path_eq_eq in H.
 rewrite rev_path_involutive, rev_path_app in H.
 apply not_eq_sym in Hd.
 injection H; intros; contradiction.

 rewrite norm_list_idemp; reflexivity.

 rewrite norm_list_idemp; reflexivity.
Qed.

Theorem not_in_fixpoints_one_path2 : ∀ p e e₁ el₄ el₁ el el₃,
  not_in_fixpoints p
  → fold_right rotate p (el ++ rev_path (e :: el₄)) = p
  → norm_list el = e₁ :: el₁
  → norm_list el₃ = negf e₁ :: e :: el₄
  → False.
Proof.
intros * Hnf Hel Hel₁ H₅.
revert Hel; apply Hnf.
intros H.
pose proof is_normal [] el (rev_path (e :: el₄)) as H₁.
do 2 rewrite app_nil_l in H₁.
rewrite <- H₁ in H; clear H₁.
rewrite rev_path_cons, rev_path_single in H; simpl in H.
apply norm_list_app_is_nil in H.
 rewrite Hel₁ in H.
 apply rev_path_eq_eq in H.
 rewrite rev_path_app in H.
 do 2 rewrite rev_path_involutive in H.
 simpl in H; rewrite negf_involutive in H.
 injection H; intros; subst e₁.
 revert H₅; apply norm_list_no_start2.

 rewrite norm_list_idemp; reflexivity.

 symmetry.
 rewrite <- rev_path_single, <- rev_path_app; simpl.
 rewrite <- rev_path_norm_list; f_equal.
 eapply norm_list_is_cons; eassumption.
Qed.

Definition R_eq_dec_on := ∀ x y : ℝ, { (x = y)%R } + { (x ≠ y)%R }.

Theorem Pdec : R_eq_dec_on → ∀ p₁ p₂ : point, { p₁ = p₂ } + { p₁ ≠ p₂ }.
Proof.
 intros Rdec (x₁, y₁, z₁) (x₂, y₂, z₂).
 destruct (Rdec x₁ x₂) as [| H₁]; [ subst x₂ | right ].
  destruct (Rdec y₁ y₂) as [| H₂]; [ subst y₂ | right ].
   destruct (Rdec z₁ z₂) as [| H₃]; [ subst z₂; left; reflexivity | right ].
   intros H; apply H₃.
   injection H; clear H; intros; subst; reflexivity.

   intros H; apply H₂.
   injection H; clear H; intros; subst; reflexivity.

  intros H; apply H₁.
  injection H; clear H; intros; subst; reflexivity.
Qed.

Record choice_function {A} (R : A → A → Prop) f := mkcf
  { cf_repr_uniqueness : ∀ x y, R x y → f x = f y;
    cf_repr_membership : ∀ x, R x (f x) }.

Definition orbit_selector := choice_function same_orbit.

Definition in_sphere '(P x y z) := (x² + y² + z² <= 1)%R.

Definition all_but_fixpoints p :=
  in_sphere p ∧
  ∀ el p₁, same_orbit p p₁
  → norm_list el ≠ [] → fold_right rotate p₁ el ≠ p₁.

Theorem on_sphere_ray_after_rotation : ∀ p m r,
  on_sphere_ray r p
  → is_rotation_matrix m
  → on_sphere_ray r (mat_vec_mul m p).
Proof.
intros * His Hm.
destruct p as (x, y, z).
unfold on_sphere_ray in His.
unfold on_sphere_ray; simpl.
unfold is_rotation_matrix in Hm.
destruct Hm as (Hm, Hd).
unfold mat_det in Hd.
unfold mat_mul, mat_id in Hm; simpl in Hm.
injection Hm; clear Hm; intros H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ H₉.
nsatz.
Qed.

Theorem in_sphere_after_rotation : ∀ p m,
  in_sphere p
  → is_rotation_matrix m
  → in_sphere (mat_vec_mul m p).
Proof.
intros * His Hrm.
destruct p as (x, y, z).
remember (P x y z) as p eqn:HP.
remember (x² + y² + z²)%R as r eqn:Hr; symmetry in Hr.
assert (Hos : on_sphere_ray r p) by (subst p; assumption).
pose proof on_sphere_ray_after_rotation _ _ _ Hos Hrm as H.
unfold in_sphere in His.
unfold on_sphere_ray in H.
unfold in_sphere.
subst p; simpl in *.
rewrite H, <- Hos; assumption.
Qed.

Theorem in_sphere_after_rotate : ∀ p e,
  in_sphere p
  → in_sphere (rotate e p).
Proof.
intros * His.
apply in_sphere_after_rotation; [ assumption | ].
apply rotate_is_rotation_matrix.
Qed.

Delimit Scope set_scope with S.

Class set_model A := mksm
  { set_eq : (A → Prop) → (A → Prop) → Prop }.

Definition empty_set {A} (_ : A) := False.

Definition intersection {A} (E₁ E₂ : A → Prop) :=
  λ x, E₁ x ∧ E₂ x.
Definition union {A} (E₁ E₂ : A → Prop) :=
  λ x, E₁ x ∨ E₂ x.
Definition union_list {A} (Ei : list (A → Prop)) :=
  fold_right union empty_set Ei.
Definition nth_set {A} i (Ei : list (A → Prop)) :=
  List.nth i Ei empty_set.

Notation "a = b" := (set_eq a b) : set_scope.
Notation "'∅'" := (empty_set) : set_scope.
Notation "E₁ '⋂' E₂" := (intersection E₁ E₂) (at level 40) : set_scope.
Notation "E₁ '⋃' E₂" := (union E₁ E₂) (at level 50) : set_scope.
Notation "'∐' Es" := (union_list Es) (at level 60) : set_scope.
Notation "E .[ i ]" := (nth_set i E) (at level 1, format "E .[ i ]")
: set_scope.

Definition is_partition {A} {S : set_model A} E Ep :=
  (E = ∐ Ep)%S ∧
  ∀ i j, i ≠ j → (Ep.[i] ⋂ Ep.[j] = ∅)%S.

Definition set_equiv {A} := mksm A (λ (E₁ E₂ : A → Prop), ∀ x, E₁ x ↔ E₂ x).

Theorem set_eq_refl A : reflexive _ (@set_eq A set_equiv).
Proof. intros P x; split; intros; assumption. Qed.

Theorem set_eq_sym A : symmetric _ (@set_eq A set_equiv).
Proof.
intros P₁ P₂ HPP x.
destruct (HPP x) as (H₁, H₂).
split; intros H; [ apply H₂, H | apply H₁, H ].
Qed.

Theorem set_eq_trans A : transitive _ (@set_eq A set_equiv).
Proof.
intros P₁ P₂ P₃ H₁₂ H₂₃ x.
destruct (H₁₂ x) as (H₁, H₂).
destruct (H₂₃ x) as (H₃, H₄).
split; intros H; [ apply H₃, H₁, H | apply H₂, H₄, H ].
Qed.

Add Parametric Relation A : (A → Prop) (@set_eq A set_equiv)
 reflexivity proved by (set_eq_refl A)
 symmetry proved by (set_eq_sym A)
 transitivity proved by (set_eq_trans A)
 as set_eq_rel.

Theorem union_empty_r : ∀ A s, s = set_equiv →
  ∀ (F : A → Prop), (F ⋃ ∅ = F)%S.
Proof.
intros * Hs *.
subst s; intros x.
split; intros H; [ | left; assumption ].
destruct H as [H| H]; [ assumption | contradiction ].
Qed.

Theorem union_comm : ∀ A s, s = set_equiv → ∀ (E F : A → Prop),
  (E ⋃ F = F ⋃ E)%S.
Proof.
intros * Hs E *; subst s; intros x.
apply or_comm.
Qed.

Theorem union_assoc : ∀ A s, s = set_equiv → ∀ (E F G : A → Prop),
  (E ⋃ (F ⋃ G) = (E ⋃ F) ⋃ G)%S.
Proof.
intros * Hs E *.
unfold set_eq, union; subst s; intros x.
split; intros H.
 destruct H as [H| [H| H]].
  left; left; assumption.
  left; right; assumption.
  right; assumption.

 destruct H as [[H| H]| H].
  left; assumption.
  right; left; assumption.
  right; right; assumption.
Qed.

Theorem union_list_app : ∀ A s, s = set_equiv → ∀ (P₁ P₂ : list (A → Prop)),
  (∐ (P₁ ++ P₂) = (∐ P₁) ⋃ (∐ P₂))%S.
Proof.
intros * Hs *.
revert P₁.
induction P₂ as [| Q]; intros.
 rewrite app_nil_r; simpl; subst s.
 rewrite union_empty_r; reflexivity.

 rewrite cons_comm_app, app_assoc; simpl; subst s.
 rewrite IHP₂, union_assoc; [ | reflexivity ].
 intros x.
 split; intros H.
  destruct H as [H| H]; [ left | right; assumption ].
  unfold union_list in H.
  rewrite fold_right_app in H.
  simpl in H.
  clear - H.
  induction P₁ as [| R P₁].
   simpl in H; simpl.
   destruct H as [H| H]; [ right; assumption | contradiction ].

   simpl in H.
   destruct H as [H| H]; [ simpl; left; left; assumption | ].
   apply IHP₁ in H.
   destruct H as [H| H]; [ simpl; left; right; assumption | ].
   right; assumption.

  destruct H as [H| H]; [ left | right; assumption ].
  unfold union_list.
  rewrite fold_right_app; simpl.
  clear - H.
  induction P₁ as [| R P₁].
   simpl in H; simpl; left.
   destruct H; [ contradiction | assumption ].

   simpl in H; simpl.
   destruct H.
    destruct H; [ left; assumption | right ].
    apply IHP₁; left; assumption.

    right; apply IHP₁; right; assumption.
Qed.

Theorem nth_set_union_list : ∀ A (P : list (A → Prop)) i x,
  i < length P → (P.[i])%S x → (∐ P)%S x.
Proof.
intros A P i x Hi H.
revert P H Hi.
induction i; intros P H Hi.
 destruct P as [| E P]; [ contradiction | left; assumption ].

 destruct P as [| E P]; [ contradiction | simpl in Hi ].
 apply Nat.succ_lt_mono in Hi.
 right; apply IHi; assumption.
Qed.

Theorem nth_set_app : ∀ A s, s = set_equiv → ∀ (P₁ P₂ : list (A → Prop)) i,
  ((P₁ ++ P₂).[i] =
   if lt_dec i (length P₁) then P₁.[i] else P₂.[i-length P₁])%S.
Proof.
intros * Hs *.
unfold nth_set, union, set_eq; subst s; simpl; intros.
destruct (lt_dec i (length P₁)) as [H₁| H₁].
 rewrite app_nth1; [ reflexivity | assumption ].

 rewrite app_nth2; [ reflexivity | apply Nat.nlt_ge; assumption ].
Qed.

Theorem is_partition_group_first_2_together :
  ∀ A s, s = set_equiv →
  ∀ (F : A → Prop) P₁ P₂ Pl,
  is_partition F (P₁ :: P₂ :: Pl)
  → is_partition F (union P₁ P₂ :: Pl).
Proof.
intros * Hs * Hp.
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
  unfold nth_set, intersection, set_eq; simpl.
  intros x.
  split; [ | contradiction ].
  intros (H₁, H₂).
  destruct j; [ apply Hij; reflexivity | clear Hij ].
  destruct H₁ as [H₁| H₁].
   apply Hi with (i := O) (j := S (S j)); [ intros H; discriminate H | ].
   unfold nth_set, intersection; simpl.
   split; assumption.

   apply Hi with (i := 1%nat) (j := S (S j)); [ intros H; discriminate H | ].
   unfold nth_set, intersection; simpl.
   split; assumption.

  unfold nth_set, intersection, union, set_eq; simpl.
  intros x.
  split; [ | contradiction ].
  intros (H₁ & H₂).
  destruct j.
   destruct H₂ as [H₂| H₂].
    apply Hi with (i := O) (j := S (S i)); [ intros H; discriminate H | ].
    unfold nth_set, intersection; simpl.
    split; assumption.

    apply Hi with (i := 1%nat) (j := S (S i)); [ intros H; discriminate H | ].
    unfold nth_set, intersection; simpl.
    split; assumption.

  apply Hi with (i := S (S i)) (j := S (S j)).
   intros H; apply Hij.
   apply Nat.succ_inj; assumption.

   unfold nth_set, intersection; simpl.
   split; assumption.
Qed.

Theorem partition_union :
  ∀ A s, s = set_equiv →
  ∀ (F₁ F₂ : A → Prop) P₁ P₂,
  (F₁ ⋂ F₂ = ∅)%S
  → is_partition F₁ P₁
  → is_partition F₂ P₂
  → is_partition (F₁ ⋃ F₂)%S (P₁ ++ P₂).
Proof.
intros * Hs F₁ F₂ * HFF HF₁ HF₂.
destruct HF₁ as (HF₁ & HP₁).
destruct HF₂ as (HF₂ & HP₂).
split.
 subst s; rewrite union_list_app; [ | reflexivity ].
 transitivity (F₁ ⋃ ∐ P₂)%S.
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
 apply (nth_set_app _ _ eq_refl) in H₁.
 apply (nth_set_app _ _ eq_refl) in H₂.
 destruct (lt_dec i (length P₁)) as [H₃| H₃].
  destruct (lt_dec j (length P₁)) as [H₄| H₄].
   eapply HP₁; [ eassumption | split; assumption ].

   apply HFF.
   split.
    apply HF₁.
    eapply nth_set_union_list; eassumption.

    destruct (lt_dec (j - length P₁) (length P₂)) as [H₅| H₅].
     apply HF₂.
     eapply nth_set_union_list; eassumption.

     apply Nat.nlt_ge in H₅.
     unfold nth_set in H₂.
     rewrite nth_overflow in H₂; [ contradiction | assumption ].

  apply Nat.nlt_ge in H₃.
  destruct (lt_dec j (length P₁)) as [H₄| H₄].
   apply HFF.
   split.
    apply HF₁.
    eapply nth_set_union_list; eassumption.

    destruct (lt_dec (i - length P₁) (length P₂)) as [H₅| H₅].
     apply HF₂.
     eapply nth_set_union_list; eassumption.

     apply Nat.nlt_ge in H₅.
     unfold nth_set in H₁.
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

Class sel_model {A} := mkos
  { os_fun : A → A }.

Definition EE {os : sel_model} :=
  λ p, all_but_fixpoints p ∧ p = os_fun p.
Definition SS {os : sel_model} e := λ p,
  all_but_fixpoints p ∧
  ∃ el el₁,
  norm_list el = e :: el₁ ∧ fold_right rotate (os_fun p) el = p.
Definition rot {os : @sel_model point} e (E : point → Prop) := λ p,
  E (rotate (negf e) p).

Theorem empty_set_not_full_set : ∀ f os, os = mkos _ f →
  ∀ e p, EE p → SS e p → False.
Proof.
intros f os Hos e p He Hs; subst os.
destruct He as (Hinf & He); simpl in He.
destruct Hs as (Hjnf & el & el₁ & Hn & Hs); simpl in Hs.
rewrite <- He in Hs.
eapply Hinf; [ reflexivity | | eassumption ].
intros H; rewrite Hn in H; discriminate H.
Qed.

Theorem start_with_same : ∀ f os, os = mkos _ f →
  ∀ e₁ e₂ p, SS e₁ p → SS e₂ p → e₁ = e₂.
Proof.
intros f os Hos (ti, di) (tj, dj) p Hsi Hsj; subst os.
destruct Hsi as (Hinf & eli & eli₁ & Hni & Hsi); simpl in Hsi.
destruct Hsj as (Hjnf & elj & elj₁ & Hnj & Hsj); simpl in Hsj.
eapply rotate_rev_path in Hsj.
destruct ti, tj.
+destruct di, dj; [ reflexivity | exfalso | exfalso | reflexivity ].
 *eapply not_in_fixpoints_one_path; try eassumption.
   intros el Hn.
   apply Hjnf; [ reflexivity | assumption ].

   rewrite <- rev_path_norm_list, Hnj.
   rewrite rev_path_cons, rev_path_single; reflexivity.

   intros H; discriminate H.

 *eapply not_in_fixpoints_one_path; try eassumption.
   intros el Hn.
   apply Hjnf; [ reflexivity | assumption ].

   rewrite <- rev_path_norm_list, Hnj.
   rewrite rev_path_cons, rev_path_single; reflexivity.

   intros H; discriminate H.

+exfalso.
 eapply not_in_fixpoints_one_path; try eassumption.
  intros el Hn.
  apply Hjnf; [ reflexivity | assumption ].

  rewrite <- rev_path_norm_list, Hnj.
  rewrite rev_path_cons, rev_path_single; reflexivity.

  intros H; discriminate H.

+exfalso.
 eapply not_in_fixpoints_one_path; try eassumption.
  intros el Hn.
  apply Hjnf; [ reflexivity | assumption ].

  rewrite <- rev_path_norm_list, Hnj.
  rewrite rev_path_cons, rev_path_single; reflexivity.

  intros H; discriminate H.

+destruct di, dj; [ reflexivity | exfalso | exfalso | reflexivity ].
 *eapply not_in_fixpoints_one_path; try eassumption.
   intros el Hn.
   apply Hjnf; [ reflexivity | assumption ].

   rewrite <- rev_path_norm_list, Hnj.
   rewrite rev_path_cons, rev_path_single; reflexivity.

   intros H; discriminate H.

 *eapply not_in_fixpoints_one_path; try eassumption.
   intros el Hn.
   apply Hjnf; [ reflexivity | assumption ].

   rewrite <- rev_path_norm_list, Hnj.
   rewrite rev_path_cons, rev_path_single; reflexivity.

   intros H; discriminate H.
Qed.

Theorem fold_right_single {A B} (f : A → B → B) x y :
  fold_right f x [y] = f y x.
Proof. reflexivity. Qed.

Theorem not_start_with_rot :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ e p, SS e p → rot e (SS (negf e)) p → False.
Proof.
intros f (Hoe, Ho) os Hos e p Hs Hr; simpl in Hr; subst os.
destruct Hs as (Hnf & el & el₁ & Hn & Hs); simpl in Hs.
destruct Hr as (Hrnf & elr & elr₁ & Hnr & Hsr); simpl in Hsr.
assert (Hr : f p = f (rotate (negf e) p)).
 apply Hoe.
 exists (negf e :: []); reflexivity.

 rewrite <- Hr in Hsr.
 eapply rotate_rev_path in Hsr.
 rewrite <- fold_right_single, <- fold_right_app in Hsr.
 rewrite <- Hsr in Hs.
 rewrite <- fold_right_app in Hs.
 rewrite rotate_rotate_norm in Hs.
 pose proof is_normal [] el (rev_path elr ++ [negf e]) as H.
 do 2 rewrite app_nil_l in H.
 rewrite <- H in Hs; clear H.
 rewrite <- is_normal in Hs.
 rewrite <- rev_path_norm_list in Hs.
 rewrite Hnr in Hs.
 rewrite <- rotate_rotate_norm in Hs.
 rewrite rev_path_cons in Hs.
 rewrite rev_path_single in Hs.
 rewrite <- app_assoc in Hs.
 simpl in Hs.
 rewrite negf_involutive in Hs.
 rewrite app_assoc in Hs.
 rewrite rotate_cancel_in in Hs.
 rewrite app_nil_r in Hs.
 eapply Hnf; [ reflexivity | | eassumption ].
 intros H.
 apply norm_list_app_is_nil in H.
 2 : symmetry; apply norm_list_idemp.
 2 : rewrite <- rev_path_norm_list; eapply norm_list_is_cons in Hnr.
 2 : rewrite Hnr; reflexivity.
 apply -> rev_path_eq_eq in H.
 rewrite H, Hn in Hnr.
 revert Hnr; apply norm_list_no_start2.
Qed.

Theorem r_decomposed_5 :
  R_eq_dec_on
  → ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition all_but_fixpoints [EE; SS ạ; SS ạ⁻¹; SS ḅ; SS ḅ⁻¹].
Proof.
intros Rdec s Hs f (Hoe, Ho) os Hos; subst os s.
split.
*unfold is_partition; intros p.
 split.
 -intros Hnf.
  unfold union_list; simpl; unfold union.
  destruct (Pdec Rdec p (f p)) as [H₁| H₁]; [ left; split; assumption | ].
  right.
  pose proof Ho p as H.
  destruct H as (el, Hel).
  remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
  destruct (list_nil_app_dec el₁) as [H₂| (e & el₂ & H₂)]; subst el₁.
  +rewrite rotate_rotate_norm, H₂ in Hel; contradiction.

  +destruct e as (t, d); destruct t, d.
    left; split; [ assumption | ].
    exists (rev_path el), (rev_path el₂).
    split; [ | apply rotate_rev_path; assumption ].
    rewrite <- rev_path_norm_list, H₂, rev_path_app; reflexivity.

    right; left; split; [ assumption | ].
    exists (rev_path el), (rev_path el₂).
    split; [ | apply rotate_rev_path; assumption ].
    rewrite <- rev_path_norm_list, H₂, rev_path_app; reflexivity.

    right; right; left; split; [ assumption | ].
    exists (rev_path el), (rev_path el₂).
    split; [ | apply rotate_rev_path; assumption ].
    rewrite <- rev_path_norm_list, H₂, rev_path_app; reflexivity.

    right; right; right; left; split; [ assumption | ].
    exists (rev_path el), (rev_path el₂).
    split; [ | apply rotate_rev_path; assumption ].
    rewrite <- rev_path_norm_list, H₂, rev_path_app; reflexivity.

 -intros Hul.
  unfold union_list in Hul; simpl in Hul; unfold union in Hul.
  destruct Hul as [Hul| [Hul| [Hul| [Hul| [Hul| Hul]]]]].
  +destruct Hul as (Hnf, Hul); simpl in Hul.
   apply Hnf; assumption.

  +destruct Hul as (Hnf, Hul); simpl in Hul.
   apply Hnf; assumption.

  +destruct Hul as (Hnf, Hul); simpl in Hul.
   apply Hnf; assumption.

  +destruct Hul as (Hnf, Hul); simpl in Hul.
   apply Hnf; assumption.

  +destruct Hul as (Hnf, Hul); simpl in Hul.
   apply Hnf; assumption.

  +contradiction.

*intros i j Hij p.
 split; [ | contradiction ].
 unfold nth_set.
 intros (Hi, Hj); unfold empty_set.
 destruct i; [ simpl in Hi | ].
  destruct j; [ exfalso; apply Hij; reflexivity | clear Hij ].
  destruct Hi as (Hinf & Hi); simpl in Hi.
  destruct j.
   eapply empty_set_not_full_set; [ reflexivity | | eassumption ].
   split; assumption.

   destruct j.
    eapply empty_set_not_full_set; [ reflexivity | | eassumption ].
    split; assumption.

    destruct j.
     eapply empty_set_not_full_set; [ reflexivity | | eassumption ].
     split; assumption.

     destruct j; [ | destruct j; contradiction ].
     eapply empty_set_not_full_set; [ reflexivity | | eassumption ].
     split; assumption.

 destruct i; [ simpl in Hi | ].
  destruct j; [ clear Hij | ].
   eapply empty_set_not_full_set; [ reflexivity | eassumption | eassumption ].

   destruct j; [ exfalso; apply Hij; reflexivity | clear Hij ].
   destruct j; [ simpl in Hj | ].
    eapply start_with_same in Hi; [ | reflexivity | eassumption ].
    discriminate Hi.

    destruct j; [ simpl in Hj | ].
     eapply start_with_same in Hi; [ | reflexivity | eassumption ].
     discriminate Hi.

     destruct j; [ simpl in Hj | destruct j; contradiction ].
     eapply start_with_same in Hi; [ | reflexivity | eassumption ].
     discriminate Hi.

  destruct i; [ simpl in Hi | ].
   destruct j; [ clear Hij | ].
    eapply empty_set_not_full_set; [ reflexivity | eassumption | eassumption ].

    destruct j; [ simpl in Hj | ].
     eapply start_with_same in Hi; [ | reflexivity | eassumption ].
     discriminate Hi.

     destruct j; [ exfalso; apply Hij; reflexivity | clear Hij ].
     destruct j; [ simpl in Hj | ].
      eapply start_with_same in Hi; [ | reflexivity | eassumption ].
      discriminate Hi.

      destruct j; [ simpl in Hj | destruct j; contradiction ].
      eapply start_with_same in Hi; [ | reflexivity | eassumption ].
      discriminate Hi.

   destruct i; [ simpl in Hi | ].
    destruct j; [ clear Hij | ].
     eapply empty_set_not_full_set; [ reflexivity | | ]; eassumption.

     destruct j; [ simpl in Hj | ].
      eapply start_with_same in Hi; [ | reflexivity | eassumption ].
      discriminate Hi.

      destruct j; [ simpl in Hj | ].
       eapply start_with_same in Hi; [ | reflexivity | eassumption ].
       discriminate Hi.

       destruct j; [ exfalso; apply Hij; reflexivity | clear Hij ].
       destruct j; [ simpl in Hj | destruct j; contradiction ].
       eapply start_with_same in Hi; [ | reflexivity | eassumption ].
       discriminate Hi.

    destruct i; [ simpl in Hi | ].
     destruct j; [ clear Hij | ].
      eapply empty_set_not_full_set; [ reflexivity | | ]; eassumption.

      destruct j; [ simpl in Hj | ].
       eapply start_with_same in Hi; [ | reflexivity | eassumption ].
       discriminate Hi.

       destruct j; [ simpl in Hj | ].
        eapply start_with_same in Hi; [ | reflexivity | eassumption ].
        discriminate Hi.

        destruct j; [ simpl in Hj | ].
         eapply start_with_same in Hi; [ | reflexivity | eassumption ].
         discriminate Hi.

         destruct j; [ exfalso; apply Hij; reflexivity | clear Hij ].
         destruct j; contradiction.

     destruct i; contradiction.
Qed.

Theorem r_decomposed_4 :
  R_eq_dec_on
  → ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition all_but_fixpoints [(EE ⋃ SS ạ)%S; SS ạ⁻¹; SS ḅ; SS ḅ⁻¹].
Proof.
intros Rdec s Hs f HoeHo os Hos.
pose proof r_decomposed_5 Rdec s Hs f HoeHo os Hos as H.
eapply is_partition_group_first_2_together; eassumption.
Qed.

Theorem r_decomposed_2 :
  ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ e,
    is_partition all_but_fixpoints [SS e; rot e (SS (negf e))].
Proof.
intros s Hs f (Hoe, Ho) os Hos e; subst os s.
split.
*unfold is_partition; intros p.
 split.
 -intros Hnf.
  unfold union_list; simpl; unfold union.
  pose proof Ho p as H.
  apply same_orbit_sym in H.
  destruct H as (el, Hel).
  remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
  destruct el₁ as [| e₁].
   +rewrite rotate_rotate_norm, Hel₁ in Hel; simpl in Hel.
   clear Hel₁.
   right; left.
   unfold rot, SS.
   split.
    split.
     destruct Hnf as (His, _).
     apply in_sphere_after_rotate; assumption.

     intros el₁ p₁ Hp Hn.
     apply Hnf; [ | assumption ].
     destruct Hp as (el₂ & Hp).
     exists (el₂ ++ [negf e]).
     rewrite fold_right_app; assumption.

    exists (negf e :: []), [].
    split; [ reflexivity | simpl ].
    assert (H : f p = f (rotate (negf e) p)).
     apply Hoe.
     exists (negf e :: []); reflexivity.

     rewrite <- H, Hel; reflexivity.

   +destruct (free_elem_dec e e₁) as [H₁| H₁]; [ subst e₁ | ].
     left; split; [ assumption | ].
     exists el, el₁; split; assumption.

     right; left.
     unfold rot, SS.
     split.
      split.
       destruct Hnf as (His, _).
       apply in_sphere_after_rotate; assumption.

       intros el₂ p₁ Hp Hn.
       apply Hnf; [ | assumption ].
       destruct Hp as (el₃ & Hp).
       exists (el₃ ++ [negf e]).
       rewrite fold_right_app; assumption.

      assert (H : f p = f (rotate (negf e) p)).
       apply Hoe.
       exists (negf e :: []); reflexivity.

       simpl; rewrite <- H.
       exists (negf e :: el), (e₁ :: el₁); simpl.
       rewrite Hel₁, Hel.
       destruct (letter_opp_dec (negf e) e₁) as [H₂| H₂].
        exfalso.
        apply letter_opp_negf in H₂.
        apply H₁, negf_eq_eq; assumption.

        split; reflexivity.

 -intros Hul.
  destruct Hul as [(H, _)| [(H, _)| Hul]]; [ assumption | | contradiction ].
  split.
   destruct H as (His, _).
   apply in_sphere_after_rotate with (e := e) in His.
   rewrite rotate_rotate_neg in His; assumption.

   intros el p₁ Hso Hn.
   apply H; [ | assumption ].
   etransitivity; [ | eassumption ].
   exists (e :: []).
   apply rotate_rotate_neg.

*intros i j Hij p.
 split; [ | contradiction ].
 unfold nth_set.
 intros (Hi, Hj); unfold empty_set.
 destruct i; [ simpl in Hi | ].
  destruct j; [ exfalso; apply Hij; reflexivity | clear Hij ].
  destruct j; [ | destruct j; contradiction ].
  simpl in Hj.
  eapply not_start_with_rot in Hi; try eassumption; [ | reflexivity ].
  split; assumption.

  destruct i; [ simpl in Hi | ].
   destruct j; [ simpl in Hj; clear Hij | ].
    eapply not_start_with_rot in Hj; try eassumption; [ | reflexivity ].
    split; assumption.

    destruct j; [ apply Hij; reflexivity | clear Hij ].
    destruct j; contradiction.

   destruct i; contradiction.
Qed.

Theorem r_decomposed_2_a :
  ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition all_but_fixpoints [SS ạ; rot ạ (SS ạ⁻¹)].
Proof.
intros.
eapply r_decomposed_2; eassumption.
Qed.

Theorem r_decomposed_2_b :
  ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition all_but_fixpoints [SS ḅ; rot ḅ (SS ḅ⁻¹)].
Proof.
intros.
eapply r_decomposed_2; eassumption.
Qed.

End Orbit.

Section Equidecomposability.

Add Parametric Morphism {A} : (@is_partition A set_equiv)
  with signature @set_eq A set_equiv ==> eq ==> iff
  as is_partition_morph.
Proof.
intros E F HEF P.
unfold is_partition.
unfold set_eq in HEF; simpl in HEF.
unfold set_eq; simpl.
split; intros (H₁, H₂).
 split; [ | assumption ].
 intros x.
 split; intros H; [ apply H₁, HEF; assumption | apply HEF, H₁; assumption ].

 split; [ | assumption ].
 intros x.
 split; intros H; [ apply H₁, HEF; assumption | apply HEF, H₁; assumption ].
Qed.


Delimit Scope set_scope with S.

Notation "'ạ'" := (E la false).
Notation "'ạ⁻¹'" := (E la true).
Notation "'ḅ'" := (E lb false).
Notation "'ḅ⁻¹'" := (E lb true).

Notation "a = b" := (set_eq a b) : set_scope.
Notation "'∅'" := (empty_set) : set_scope.
Notation "E₁ '⋂' E₂" := (intersection E₁ E₂) (at level 40) : set_scope.
Notation "E₁ '⋃' E₂" := (union E₁ E₂) (at level 50) : set_scope.
Notation "'∐' Es" := (union_list Es) (at level 60) : set_scope.
Notation "E .[ i ]" := (nth_set i E) (at level 1) : set_scope.

(* "rot ạ" is an example of a member of the group *)
Check rot.

Definition xtransl dx (S : point → Prop) '(P x y z) := S (P (x + dx) y z).

Definition transf_group (os : sel_model) :=
  λ (g : (point → Prop) → (point → Prop)),
  (g = rot (E la false)) ∨
  (∃ dx, g = xtransl dx).

Check transf_group.

Definition G f := transf_group (mkos _ f).

Definition equidecomposable (s : set_model point) G E₁ E₂ :=
  ∃ P₁ P₂, is_partition E₁ P₁ ∧ is_partition E₂ P₂ ∧ length P₁ = length P₂ ∧
  List.Forall2 (λ S₁ S₂, ∃ g, G g ∧ g S₁ = S₂) P₁ P₂.

Theorem Banach_Tarski_paradox :
  R_eq_dec_on
  → ∀ s f os, s = set_equiv → orbit_selector f → os = mkos _ f →
    equidecomposable s (G f) all_but_fixpoints
      (union (xtransl 3 all_but_fixpoints) (xtransl 6 all_but_fixpoints)).
Proof.
intros Rdec s f os Hs Hosf Hos.
exists [(EE ⋃ SS ạ)%S; SS ạ⁻¹; SS ḅ; SS ḅ⁻¹].
exists
  (map (xtransl 3) [SS ạ; rot ạ (SS ạ⁻¹)] ++
   map (xtransl 6) [SS ḅ; rot ḅ (SS ḅ⁻¹)])%S; simpl.
split; [ eapply r_decomposed_4; try eassumption | ].
split.
 pose proof r_decomposed_2_a s Hs f Hosf os Hos as Ha.
 pose proof r_decomposed_2_b s Hs f Hosf os Hos as Hb.
Theorem toto : ∀ s f, s = set_equiv → orbit_selector f →
  ∀ (F : point → Prop) P g,
  G f g → is_partition F P → is_partition (g F) (map g P).
  (* probably missing that g is member of a "good" group *)
Proof.
intros * Hs Ho F P * HG HP.
unfold is_partition in HP |-*.
destruct HP as (HF, HP).
split.
 destruct HG as [HG| HG].
  (* rot ạ *)
  subst g.
  unfold set_eq; subst s; simpl.
  intros x.
  split.
   intros Ha.
   revert F HF Ha.
   induction P as [| Q P]; intros; [ exfalso; eapply HF; eassumption | ].
   simpl in HF; simpl.
   generalize Ha; intros H.
   apply HF in H; simpl in H.
   destruct H as [H| H]; [ left; assumption | right ].
   eapply IHP; [ | simpl; reflexivity | eassumption ].
   intros i j Hij.
   unfold set_eq; simpl; intros y.
   assert (HSij : S i ≠ S j).
    intros HSij; apply Hij, Nat.succ_inj; assumption.

    pose proof HP (S i) (S j) HSij y as HP; simpl in HP.
    destruct HP as (HQ, _).
    split; [ intros (HPi, HPj) | contradiction ].
    apply HQ; split; assumption.

   intros Hma.
bbb.

Show.
 apply toto with (g := xtransl 3) in Ha; simpl in Ha; [ | assumption ].
 apply toto with (g := xtransl 6) in Hb; simpl in Hb; [ | assumption ].
 eapply partition_union in Hb; [ | apply Hs | | apply Ha ].
  assumption.

  unfold intersection, set_eq; subst s; intros (x, y, z).
  split; [ intros (H₁, H₂) | contradiction ].
  unfold xtransl in H₁, H₂.
  unfold empty_set; simpl.
  destruct H₁ as (H₁, H₃).
  destruct H₂ as (H₂, H₄).
  unfold in_sphere in H₁, H₂.
  apply Rplus_le_reg_pos_r in H₁; [ | apply Rle_0_sqr ].
  apply Rplus_le_reg_pos_r in H₁; [ | apply Rle_0_sqr ].
  apply Rplus_le_reg_pos_r in H₂; [ | apply Rle_0_sqr ].
  apply Rplus_le_reg_pos_r in H₂; [ | apply Rle_0_sqr ].
  clear - H₁ H₂.
  rewrite <- Rsqr_1 in H₁ at 4.
  rewrite <- Rsqr_1 in H₂ at 6.
  apply Rsqr_le_abs_0 in H₁.
  apply Rsqr_le_abs_0 in H₂.
  rewrite Rabs_R1 in H₁, H₂.
  unfold Rabs in H₁, H₂.
  destruct (Rcase_abs (x + 3)), (Rcase_abs (x + 6)); lra.

 split; [ reflexivity | ].

bbb.

End Equidecomposability.
