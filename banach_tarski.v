(* Banach-Tarski paradox. *)
(* Inspirations:
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)

Require Import Utf8.
Require Import List.
Require Import Relations Setoid.
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

Theorem cons_to_app : ∀ A (x : A) l, x :: l = (x :: nil) ++ l.
Proof. reflexivity. Qed.

Theorem cons_comm_app {A} : ∀ (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. reflexivity. Qed.

Definition xor (A B : Prop) : Prop := A ∧ ¬B ∨ ¬A ∧ B.
Notation "x ⊕ y" := (xor x y) (at level 85, right associativity).

Theorem xor_or : ∀ P Q, P ⊕ Q → P ∨ Q.
Proof.
intros.
destruct H; [ left | right ]; destruct H; assumption.
Qed.

Theorem rev_is_nil {A} : ∀ el : list A, List.rev el = [] → el = [].
Proof.
intros el H.
induction el as [| e] using rev_ind; [ reflexivity | ].
rewrite rev_unit in H; discriminate H.
Qed.

Theorem rev_rev {A} : ∀ l₁ l₂ : list A, rev l₁ = rev l₂ → l₁ = l₂.
Proof.
intros l₁ l₂ H.
revert l₂ H.
induction l₁ as [| x]; intros.
 destruct l₂ as [| x]; [ reflexivity | exfalso ].
 simpl in H; symmetry in H.
 apply app_eq_nil in H.
 destruct H as (_, H); discriminate H.

 simpl in H.
 destruct l₂ as [| y]; [ exfalso | ].
  simpl in H; apply app_eq_nil in H.
  destruct H as (_, H); discriminate H.

  simpl in H.
  apply app_inj_tail in H.
  destruct H as (H₁, H₂); subst y; f_equal.
  apply IHl₁, H₁.
Qed.

Theorem rev_sym {A} : ∀ el₁ el₂ : list A, el₁ = rev el₂ → el₂ = rev el₁.
Proof.
intros el₁ el₂ H.
subst el₁; symmetry.
apply rev_involutive.
Qed.

(* Step 1 *)

Section Free_Group.

(* a = E la false
   a⁻¹ = E la true
   b = E lb false
   b⁻¹ = E lb true *)

Inductive letter := la | lb.

Inductive free_elem := E : letter → bool → free_elem.
Record F₂ := mkF₂ { str : list free_elem }.

Notation "x '⁺'" := (E x false) (at level 200, format "x ⁺").
Notation "x '⁻¹'" := (E x true) (at level 200, format "x ⁻¹").
Notation "'ạ'" := (E la false).
Notation "'ạ⁻¹'" := (E la true).
Notation "'ḅ'" := (E lb false).
Notation "'ḅ⁻¹'" := (E lb true).

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

Definition letter_opp '(E l₁ d₁) '(E l₂ d₂) :=
  if letter_dec l₁ l₂ then
    if Bool.bool_dec d₁ d₂ then False else True
  else False.

Theorem bool_dec_diag : ∀ b, Bool.bool_dec b b = left (eq_refl _).
Proof.
intros b.
destruct (Bool.bool_dec b b) as [p| p]; [ | exfalso; apply p; reflexivity ].
destruct b; refine (match p with eq_refl => eq_refl end).
Qed.

Definition false_neq_negb_false : false ≠ negb false :=
  λ p, False_ind False
    (eq_ind false (λ e : bool, if e then False else True) I true p).

Definition true_neq_negb_true : true ≠ negb true :=
  λ p, False_ind False
   (eq_ind true (λ e : bool, if e then True else False) I false p).

Definition negb_true_neq_true : negb true ≠ true := false_neq_negb_false.
Definition negb_false_neq_false : negb false ≠ false := true_neq_negb_true.

Theorem bool_dec_negb_r : ∀ b,
  Bool.bool_dec b (negb b) =
  right (if b return _ then true_neq_negb_true else false_neq_negb_false).
Proof. intros b; destruct b; reflexivity. Qed.

Theorem bool_dec_negb_l : ∀ b,
  Bool.bool_dec (negb b) b =
  right (if b return _ then negb_true_neq_true else negb_false_neq_false).
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

Theorem letter_opp_comm : ∀ e₁ e₂, letter_opp e₁ e₂ → letter_opp e₂ e₁.
Proof.
intros e₁ e₂ H.
unfold letter_opp in H; unfold letter_opp.
destruct e₁ as (x₁, d₁).
destruct e₂ as (x₂, d₂).
destruct (letter_dec x₁ x₂) as [H₁| H₁]; [ subst x₂ | contradiction ].
destruct (Bool.bool_dec d₁ d₂) as [H₂| H₂]; [ contradiction | clear H ].
destruct (letter_dec x₁ x₁) as [H₃| H₃]; [ | apply H₃; reflexivity ].
destruct (Bool.bool_dec d₂ d₁) as [H₄| H₄]; [ | constructor ].
symmetry in H₄; contradiction.
Qed.

Theorem letter_opp_inv : ∀ x d, letter_opp (E x d) (E x (negb d)).
Proof.
intros.
unfold letter_opp.
rewrite letter_dec_diag, bool_dec_negb_r.
constructor.
Qed.

Theorem not_letter_opp_diag : ∀ x d, ¬ letter_opp (E x d) (E x d).
Proof.
intros.
unfold letter_opp.
rewrite letter_dec_diag, bool_dec_diag.
intros H; assumption.
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

Definition normalised_list el := norm_list el = el.

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
    exfalso; revert Hel₂; apply norm_list_impossible_start.

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
  rewrite norm_list_cancel_inside.
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
  exfalso; revert Hel₁; apply norm_list_impossible_start2.

  injection Hn; clear Hn; intros; subst el₁.
  assumption.
Qed.

Theorem norm_list_is_cons : ∀ el e el₁,
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
  destruct e as (x₁, d₁).
  destruct e₃ as (x₂, d₂).
  apply letter_opp_comm in H₃.
  apply letter_opp_iff in H₃.
  destruct H₃; subst x₁ d₁.
  revert Hel₃; apply norm_list_impossible_start.

  injection H₂; clear H₂; intros; subst el₁; reflexivity.

 injection Hel; clear Hel; intros; subst e el₁.
 rewrite <- Hel₂; symmetry.
 apply norm_list_norm_list.
Qed.

Definition norm_eq x y := norm_list x = norm_list y.
Notation "x ≡ y" := (norm_eq x y) (at level 70).
Theorem fold_norm_eq : ∀ el₁ el₂,
  norm_list el₁ = norm_list el₂
  → el₁ ≡ el₂.
Proof. intros; assumption. Qed.

Definition norm_eq_refl : reflexive _ norm_eq.
Proof. intros el₁; reflexivity. Qed.

Definition norm_eq_sym : symmetric _ norm_eq.
Proof. intros el₁ el₂ H; symmetry; assumption. Qed.

Definition norm_eq_trans : transitive _ norm_eq.
Proof.
intros el₁ el₂ el₃ H₁₂ H₂₃.
etransitivity; eassumption.
Qed.

Add Parametric Relation : _ norm_eq
 reflexivity proved by norm_eq_refl
 symmetry proved by norm_eq_sym
 transitivity proved by norm_eq_trans
 as norm_eq_equivalence.

Add Parametric Morphism : (@app free_elem)
  with signature norm_eq ==> norm_eq ==> norm_eq
  as norm_eq_app_morph.
Proof.
intros el₁ el₂ Hel₁ el₃ el₄ Hel₂.
unfold "≡" in Hel₁, Hel₂ |-*.
pose proof is_normal el₁ el₃ [] as H.
rewrite Hel₂, is_normal in H.
do 2 rewrite app_nil_r in H.
rewrite <- H; clear H.
pose proof is_normal [] el₂ el₄ as H.
rewrite <- Hel₁, is_normal in H.
do 2 rewrite app_nil_l in H.
assumption.
Qed.

Theorem norm_norm : ∀ s, norm (norm s) = norm s.
Proof.
intros.
unfold norm; f_equal.
apply norm_list_norm_list.
Qed.

Theorem norm_list_eq : ∀ el el',
  norm_list el = el' → norm_list el = norm_list el'.
Proof.
intros el el' H.
rewrite <- norm_list_norm_list, H.
reflexivity.
Qed.

Theorem norm_list_subst : ∀ e el el',
  norm_list el = el' → norm_list (e :: el) = norm_list (e :: el').
Proof.
intros e el el' Hel.
subst el'; simpl.
rewrite norm_list_norm_list.
reflexivity.
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
  revert Hel'; apply norm_list_impossible_start.

  destruct (letter_opp_dec xd xe) as [H₂| H₂]; [ reflexivity | exfalso ].
  subst xd xe.
  apply H₂, letter_opp_inv.
Qed.

Theorem norm_inv : ∀ x d el,
  norm (mkF₂ (E x d :: E x (negb d) :: el)) = norm (mkF₂ el).
Proof.
intros.
unfold norm; f_equal.
remember norm_list as f; simpl; subst f.
apply norm_list_inv.
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
   revert Hel; apply norm_list_impossible_start.

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
      revert Hel; apply norm_list_impossible_start.

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

Theorem norm_nil_split_some : ∀ e el,
  norm_list (e :: el) = []
  → split_at_cancel (e :: el) ≠ None.
Proof.
intros e el Hel Hsc.
pose proof (norm_dec (e :: el)) as H.
destruct H as [H| H]; [ rewrite Hel in H; discriminate H | ].
destruct H as (el₁, (e₁, (el₂, H))).
rewrite Hsc in H; discriminate H.
Qed.

Theorem norm_nil_iff : ∀ el,
  norm_list el = []
  ↔ el = [] ∨
    ∃ el₁ el₂ t d, el = el₁ ++ E t d :: E t (negb d) :: el₂
    ∧ norm_list (el₁ ++ el₂) = [].
Proof.
intros el.
split; [ intros Hel | ].
 remember (split_at_cancel el) as sc eqn:Hsc .
 symmetry in Hsc.
 destruct el as [| e]; [ left; reflexivity | right ].
 destruct sc as [((el₁, (t, d)), el₂)| ].
  exists el₁,el₂,t,d.
  revert Hel Hsc; clear; intros; move el₂ before el₁.
  destruct el as [| e₁]; [ discriminate Hsc |  ].
  remember (e₁ :: el) as el'; simpl in Hsc; subst el'.
  destruct (letter_opp_dec e e₁) as [H₁| H₁].
   injection Hsc; clear Hsc; intros; subst.
   destruct e₁ as (t₁, d₁).
   apply letter_opp_iff in H₁.
   destruct H₁; subst t₁ d₁.
   rewrite norm_list_cancel_start in Hel.
   split; [ reflexivity | assumption ].

   remember (split_at_cancel (e₁ :: el)) as s eqn:Hs .
   symmetry in Hs.
   destruct s as [((el₃, e₃), el₄)| ]; [  | discriminate Hsc ].
   injection Hsc; clear Hsc; intros; subst el₁ e₃ el₄.
   remember (e₁ :: el) as el'.
   clear e₁ el H₁ Heqel'.
   rename el' into el.
   rewrite cons_to_app in Hel.
   rewrite cons_to_app.
   replace (e :: el₃) with ([e] ++ el₃) by apply cons_to_app.
   remember [e] as el₀.
   clear e Heqel₀.
   revert el₀ el₂ el₃ t d Hs Hel.
   induction el as [| e]; intros; [ discriminate Hs |  ].
   simpl in Hs.
   destruct el as [| e₁]; [ discriminate Hs |  ].
   destruct (letter_opp_dec e e₁) as [H₁| H₁].
    injection Hs; clear Hs; intros; subst el e el₃.
    destruct e₁ as (t₁, d₁).
    apply letter_opp_iff in H₁.
    destruct H₁; subst t₁ d₁.
    rewrite app_nil_r.
    split; [ reflexivity |  ].
    rewrite norm_list_cancel_inside in Hel; assumption.

    remember (split_at_cancel (e₁ :: el)) as u eqn:Hu ; symmetry in Hu.
    destruct u as [((el₁, e₂), el₄)| ]; [  | discriminate Hs ].
    injection Hs; clear Hs; intros; subst el₃ e₂ el₂.
    rewrite cons_comm_app, app_assoc in Hel.
    pose proof (IHel (el₀ ++ [e]) _ _ _ _ (eq_refl _) Hel) as H.
    destruct H as (H₂, H₃).
    do 2 rewrite <- app_assoc in H₃.
    do 4 rewrite cons_comm_app.
    split; [  | rewrite <- app_assoc, <- app_assoc; assumption ].
    rewrite <- app_assoc in H₂.
    simpl in H₂; simpl; rewrite H₂.
    do 3 rewrite <- app_assoc; reflexivity.

  exfalso; revert Hsc.
  apply norm_nil_split_some, Hel.

 intros [Hel | Hel]; [ subst el; reflexivity | ].
 destruct Hel as (el₁, (el₂, (t, (d, (Hel₁, Hel₂))))).
 subst el; rewrite norm_list_cancel_inside; assumption.
Qed.

End Free_Group.

(* Step 2 *)

Require Import Reals Psatz.

Notation "'ℝ'" := R.
Notation "'ℤ'" := Z.
Notation "'ℕ'" := nat.

Notation "'√'" := sqrt.

Arguments Nat.modulo _ _ : simpl nomatch.
Arguments Z.mul _ _ : simpl nomatch.
(* to prevent 'simpl' to expand 2*a, 3*a, and so on, into matches *)

Theorem Nat_mod_add_once : ∀ a b, b ≠ 0 → (a + b) mod b = a mod b.
Proof.
intros a b Hb.
replace b with (1 * b) at 1 by apply Nat.mul_1_l.
apply Nat.mod_add; assumption.
Qed.

Theorem Z_sub_sub_swap : ∀ a b c, (a - b - c)%Z = (a - c - b)%Z.
Proof. intros. ring. Qed.

Theorem Rdiv_0_l : ∀ x, (0 / x = 0)%R.
Proof.
intros x; unfold Rdiv; apply Rmult_0_l.
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

Notation "s = '∅'" := (empty s) (at level 70).
Notation "s ≠ '∅'" := (¬ empty s) (at level 70).
Notation "s '∈' 'Ṣ' ( x )" := (start_with x s)
  (at level 70, format "s  '∈'  Ṣ ( x )").
Notation "s '∈' x 'Ṣ' ( y )" := (start_with2 x y s)
  (at level 70, x at level 0, format "s  '∈'  x  Ṣ ( y )").
Notation "'ạ'" := (E la false).
Notation "'ạ⁻¹'" := (E la true).
Notation "'ḅ'" := (E lb false).
Notation "'ḅ⁻¹'" := (E lb true).
Notation "x ≡ y" := (norm_eq x y) (at level 70).

Check decomposed_4.
Check decomposed_2_a.
Check decomposed_2_b.

Theorem Rmult_shuffle0 : ∀ n m p : ℝ, (n * m * p)%R = (n * p * m)%R.
Proof.
intros.
rewrite Rmult_comm, <- Rmult_assoc.
f_equal; apply Rmult_comm.
Qed.


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

Definition rotate pt e :=
  match e with
  | ạ => mat_vec_mul rot_x pt
  | ạ⁻¹ => mat_vec_mul rot_inv_x pt
  | ḅ => mat_vec_mul rot_z pt
  | ḅ⁻¹ => mat_vec_mul rot_inv_z pt
  end.

Definition rotate_param '(a, b, c, N) e :=
  match e with
  | ạ => ((3 * a)%Z, (b - 2 * c)%Z, (4 * b + c)%Z, S N)
  | ạ⁻¹ => ((3 * a)%Z, (b + 2 * c)%Z, (- 4 * b + c)%Z, S N)
  | ḅ => ((a - 4 * b)%Z, (2 * a + b)%Z, (3 * c)%Z, S N)
  | ḅ⁻¹ => ((a + 4 * b)%Z, (- 2 * a + b)%Z, (3 * c)%Z, S N)
  end.

Theorem rotate_param_keep_dist : ∀ el x y z a b c n N,
  fold_left rotate_param el (x, y, z, n) = (a, b, c, N)
  → ((a ^ 2 + 2 * b ^ 2 + c ^ 2) * 3 ^ Z.of_nat (2 * n) =
     (x ^ 2 + 2 * y ^ 2 + z ^ 2) * 3 ^ Z.of_nat (2 * N))%Z.
Proof.
intros el x y z a b c n N Hr.
revert x y z a b c n N Hr.
induction el as [ | (t, d)]; intros.
 injection Hr; intros; subst; reflexivity.

 simpl in Hr.
 destruct t, d;
  (apply IHel in Hr;
   rewrite Nat.mul_comm, <- Nat.add_1_r, Nat.mul_comm in Hr;
   rewrite Nat.mul_add_distr_l, Nat.mul_1_r, Nat2Z.inj_add in Hr;
   rewrite Z.pow_add_r in Hr; [ | apply Nat2Z.is_nonneg | apply Z.le_0_1 ];
   rewrite Z.mul_assoc in Hr;
   replace (3 ^ Z.of_nat 2)%Z with 9%Z in Hr by reflexivity;
   apply Z.mul_reg_r with (p := 9%Z); [ intros H; discriminate H | ];
   rewrite Hr; ring_simplify; reflexivity).
Qed.

Compute (fold_left rotate_param [ḅ; ạ] (1, 0, 0, O)%Z).
Compute (fold_left rotate_param [ḅ; ạ⁻¹] (1, 0, 0, O)%Z).
Compute (fold_left rotate_param [ḅ⁻¹; ạ] (1, 0, 0, O)%Z).
Compute (fold_left rotate_param [ḅ⁻¹; ạ⁻¹] (1, 0, 0, O)%Z).

Theorem rotate_param_rotate : ∀ el x y z n a b c N,
  fold_left rotate_param el (x, y, z, n) = (a, b, c, N)
  ↔ fold_left rotate el (P (IZR x / 3^n) (IZR y * √2 / 3^n) (IZR z / 3^n)) =
      P (IZR a / 3^N) (IZR b*√2 / 3^N) (IZR c / 3^N)
    ∧ N = n + length el.
Proof.
intros el x y z n a₁ b₁ c₁ N₁.
split.
 intros Hr.
 simpl in Hr; simpl.
 revert a₁ b₁ c₁ N₁ Hr.
 induction el as [| (t, d)] using rev_ind; intros.
  simpl; simpl in Hr; rewrite Nat.add_0_r.
  injection Hr; intros; subst; simpl.
  split; reflexivity.

  rewrite fold_left_app in Hr; simpl in Hr.
  rewrite fold_left_app; simpl.
  remember (fold_left rotate_param el (x, y, z, n)) as rp eqn:Hrp.
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
   split; [ | rewrite app_length, Nat.add_assoc, Nat.add_1_r; reflexivity ].
   rewrite plus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

   split; [ | rewrite app_length, Nat.add_assoc, Nat.add_1_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

   split; [ | rewrite app_length, Nat.add_assoc, Nat.add_1_r; reflexivity ].
   rewrite plus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

   split; [ | rewrite app_length, Nat.add_assoc, Nat.add_1_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

 intros Hr.
 revert x y z n a₁ b₁ c₁ N₁ Hr.
 induction el as [| e]; intros.
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
  rewrite <- Nat.add_succ_comm in HN.
  simpl; destruct e as (t, d).
  destruct t, d.
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
Qed.

Definition fst3 {A B C D} '((a, b, c, d) : A * B * C * D) := (a, b, c).

Definition eq_mod_3 '(a₁, b₁, c₁) '(a₂, b₂, c₂) :=
  (a₁ mod 3 = a₂ mod 3)%Z ∧
  (b₁ mod 3 = b₂ mod 3)%Z ∧
  (c₁ mod 3 = c₂ mod 3)%Z.

Notation "x ≡₃ y" := (eq_mod_3 x y) (at level 70).

Definition rotate_param_mod_3 '(a, b, c) e :=
 match e with
 | ạ⁻¹ => (0%Z, ((b - c) mod 3)%Z, ((c - b) mod 3)%Z)
 | ạ => (0%Z, ((b + c) mod 3)%Z, ((b + c) mod 3)%Z)
 | ḅ⁻¹ => (((a + b) mod 3)%Z, ((a + b) mod 3)%Z, 0%Z)
 | ḅ => (((a - b) mod 3)%Z, ((b - a) mod 3)%Z, 0%Z)
 end.

Theorem rotate_params_mod : ∀ el a b c N a₁ b₁ c₁,
  fst3 (fold_left rotate_param el (a₁, b₁, c₁, N)) = (a, b, c)
  → fold_left rotate_param_mod_3 el (a₁ mod 3, b₁ mod 3, c₁ mod 3)%Z =
      (a mod 3, b mod 3, c mod 3)%Z.
Proof.
intros el a b c N a₁ b₁ c₁ Hp.
revert a b c N a₁ b₁ c₁ Hp.
induction el as [| e]; intros; [ injection Hp; intros; subst; reflexivity | ].
simpl in Hp; simpl.
destruct e as (t, d).
destruct t, d.
Focus 1.
 erewrite <- IHel; [ | eassumption ].
 f_equal; f_equal; [ f_equal | ].
  rewrite Z.mul_comm, Z.mod_mul; [ reflexivity | intros; discriminate ].

  rewrite <- Zdiv.Zminus_mod.
  rewrite <- Z.mod_add with (b := c₁); [ | intros; discriminate ].
  f_equal; ring_simplify; reflexivity.

  rewrite <- Zdiv.Zminus_mod.
  rewrite <- Z.mod_add with (b := (-b₁)%Z); [ | intros; discriminate ].
  f_equal; ring_simplify.
  reflexivity.

 erewrite <- IHel; [ | eassumption ].
 f_equal; f_equal; [ f_equal | ].
  rewrite Z.mul_comm, Z.mod_mul; [ reflexivity | intros; discriminate ].

  rewrite <- Z.add_mod; [ | intros; discriminate ].
  rewrite <- Z.mod_add with (b := (-c₁)%Z); [ | intros; discriminate ].
  f_equal; ring_simplify.
  reflexivity.

  rewrite <- Z.add_mod; [ | intros; discriminate ].
  rewrite <- Z.mod_add with (b := b₁); [ | intros; discriminate ].
  f_equal; ring_simplify.
  reflexivity.

 erewrite <- IHel; [ | eassumption ].
 f_equal; f_equal; [ f_equal | ].
  rewrite <- Z.add_mod; [ | intros; discriminate ].
  rewrite <- Z.mod_add with (b := b₁); [ | intros; discriminate ].
  f_equal; ring_simplify.
  reflexivity.

  rewrite <- Z.add_mod; [ | intros; discriminate ].
  rewrite <- Z.mod_add with (b := (-a₁)%Z); [ | intros; discriminate ].
  f_equal; ring_simplify.
  reflexivity.

  rewrite Z.mul_comm, Z.mod_mul; [ reflexivity | intros; discriminate ].

 erewrite <- IHel; [ | eassumption ].
 f_equal; f_equal; [ f_equal | ].
  rewrite <- Zdiv.Zminus_mod.
  rewrite <- Z.mod_add with (b := (-b₁)%Z); [ | intros; discriminate ].
  f_equal; ring_simplify.
  reflexivity.

  rewrite <- Zdiv.Zminus_mod.
  rewrite <- Z.mod_add with (b := a₁); [ | intros; discriminate ].
  f_equal; ring_simplify.
  reflexivity.

  rewrite Z.mul_comm, Z.mod_mul; [ reflexivity | intros; discriminate ].
Qed.

Theorem Z_mod_expr_1 : ∀ n,
  (n mod 3)%Z =
  (((n mod 3 + n mod 3) mod 3 + (n mod 3 + n mod 3) mod 3) mod 3)%Z.
Proof.
intros n.
rewrite <- Z.add_mod; [ rewrite Z.add_assoc | intros; discriminate ].
rewrite <- Z.mod_mod at 1; [ | intros; discriminate ].
set (x := (- (n mod 3))%Z); symmetry.
rewrite <- Z.mod_add with (b := x); [ subst x | intros; discriminate ].
f_equal; ring_simplify; reflexivity.
Qed.

Theorem Z_mod_expr_2 : ∀ a b,
  ((a - b) mod 3)%Z =
  ((((a - b) mod 3 - (b - a) mod 3) mod 3 -
    ((b - a) mod 3 - (a - b) mod 3) mod 3) mod 3)%Z.
Proof.
intros.
rewrite <- Zdiv.Zminus_mod, Z.sub_sub_distr.
rewrite Z.add_mod_idemp_r, Z.add_comm; [ | intros; discriminate ].
rewrite Z.add_sub_assoc.
rewrite Zdiv.Zminus_mod_idemp_r.
rewrite Z.add_sub_assoc, Z.add_comm.
do 2 rewrite <- Z.add_sub_assoc.
rewrite Z.add_mod_idemp_l; [ | intros; discriminate ].
rewrite Z_sub_sub_swap.
do 2 rewrite Z.add_sub_assoc.
rewrite Zdiv.Zminus_mod_idemp_r.
rewrite <- Z.mod_add with (b := (a - b)%Z); [ | intros; discriminate ].
f_equal; ring_simplify; reflexivity.
Qed.

Theorem Z_mod_expr_3 : ∀ a b,
  ((a - b) mod 3)%Z =
  (((b mod 3 - a mod 3) mod 3 - (a mod 3 - b mod 3) mod 3) mod 3)%Z.
Proof.
intros.
symmetry.
rewrite <- Zdiv.Zminus_mod.
rewrite <- Zdiv.Zminus_mod_idemp_l.
rewrite <- Zdiv.Zminus_mod.
set (x := ((b - a) mod 3)%Z).
rewrite <- Zdiv.Zminus_mod_idemp_r.
rewrite <- Zdiv.Zminus_mod; subst x.
rewrite <- Zdiv.Zminus_mod.
rewrite <- Z.mod_add with (b := (a - b)%Z); [  | intros; discriminate ].
f_equal; ring_simplify; reflexivity.
Qed.

Theorem Z_mod_expr_4 : ∀ a b,
  ((- a - b) mod 3)%Z =
  (((a mod 3 + b mod 3) mod 3 + (a mod 3 + b mod 3) mod 3) mod 3)%Z.
Proof.
intros.
rewrite Z.add_mod_idemp_r; [ | intros; discriminate ].
rewrite Z.add_mod_idemp_r; [ | intros; discriminate ].
rewrite Z.add_mod_idemp_l; [ | intros; discriminate ].
rewrite Z.add_assoc.
rewrite Z.add_mod_idemp_r; [ | intros; discriminate ].
rewrite Z.add_comm, Z.add_assoc.
rewrite Z.add_mod_idemp_r; [ | intros; discriminate ].
rewrite Z.add_comm.
do 2 rewrite Z.add_assoc.
rewrite Z.add_shuffle0.
rewrite Z.add_mod_idemp_r; [ | intros; discriminate ].
rewrite <- Z.mod_add with (b := (a + b)%Z); [ | intros; discriminate ].
f_equal; ring_simplify; reflexivity.
Qed.

Theorem fold_rotate_param_mod_3_succ_succ : ∀ n e p,
  0 < n
  → fold_left rotate_param_mod_3 (repeat e n) p =
    fold_left rotate_param_mod_3 (repeat e (S (S n))) p.
Proof.
intros n e p Hn.
remember (S n) as n'; simpl; subst n'.
remember (rotate_param_mod_3 p e) as p' eqn:Hp'.
revert e p p' Hp'.
induction n; intros; [ exfalso; revert Hn; apply Nat.lt_irrefl | ].
remember (S n) as n'; simpl; subst n'.
destruct n.
 simpl; subst p'; clear.
 destruct p as ((a, b), c); simpl.
 destruct e as (t, d).
 destruct t, d; simpl.
  f_equal; [ f_equal; apply Z_mod_expr_2 | apply Z_mod_expr_2 ].

  f_equal; [ f_equal; apply Z_mod_expr_1 | apply Z_mod_expr_1 ].

  f_equal; f_equal; apply Z_mod_expr_1.

  f_equal; f_equal; apply Z_mod_expr_2.

 apply IHn; [ apply Nat.lt_0_succ | subst p'; reflexivity ].
Qed.

Theorem rotate_param_app_an : ∀ el n p a b c N,
  fold_left rotate_param el p = (a, b, c, N)
  → fst3 (fold_left rotate_param (el ++ List.repeat ạ (n + 1)) p) ≡₃
      if zerop (n mod 2) then (0%Z, (b + c)%Z, (b + c)%Z)
      else (0%Z, (- b - c)%Z, (- b - c)%Z).
Proof.
intros el n p a b c N Hrp.
unfold "≡₃".
rewrite fold_left_app, Hrp; simpl.
remember (repeat ạ (n + 1)) as al.
remember (fst3 (fold_left rotate_param al (a, b, c, N))) as x eqn:Hrp₁.
subst al; symmetry in Hrp₁.
destruct x as ((a₁, b₁), c₁).
apply rotate_params_mod in Hrp₁.
revert n el p a b c N a₁ b₁ c₁ Hrp Hrp₁.
fix 1; intros.
destruct n.
 simpl in Hrp₁; simpl.
 injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
 rewrite <- Ha, <- Hb, <- Hc.
 split; [ reflexivity | ].
 split; symmetry; apply Z.add_mod; intros H; discriminate H.

 destruct n.
  simpl in Hrp₁; simpl.
  injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
  rewrite <- Ha, <- Hb, <- Hc.
  split; [ reflexivity | ].
  split; symmetry; apply Z_mod_expr_4.

  rewrite Nat.add_1_r in Hrp₁.
  rewrite <- fold_rotate_param_mod_3_succ_succ in Hrp₁.
   rewrite <- Nat.add_1_r in Hrp₁.
   pose proof (rotate_param_app_an n el p a b c N a₁ b₁ c₁ Hrp Hrp₁).
   do 2 rewrite <- Nat.add_1_r.
   rewrite <- Nat.add_assoc; simpl.
   rewrite Nat_mod_add_once; [ assumption | intros; discriminate ].

   apply Nat.lt_0_succ.
Qed.

Theorem rotate_param_app_bn : ∀ el n p a b c N,
  fold_left rotate_param el p = (a, b, c, N)
  → fst3 (fold_left rotate_param (el ++ List.repeat ḅ (n + 1)) p) ≡₃
      if zerop (n mod 2) then ((a - b)%Z, (b - a)%Z, 0%Z)
      else ((b - a)%Z, (a - b)%Z, 0%Z).
Proof.
intros el n p a b c N Hrp.
unfold "≡₃".
rewrite fold_left_app, Hrp; simpl.
remember (repeat ḅ (n + 1)) as al.
remember (fst3 (fold_left rotate_param al (a, b, c, N))) as x eqn:Hrp₁.
subst al; symmetry in Hrp₁.
destruct x as ((a₁, b₁), c₁).
apply rotate_params_mod in Hrp₁.
revert n el p a b c N a₁ b₁ c₁ Hrp Hrp₁.
fix 1; intros.
destruct n.
 simpl in Hrp₁; simpl.
 injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
 rewrite <- Ha, <- Hb, <- Hc.
 split; [ symmetry; apply Zdiv.Zminus_mod | ].
 split; [ symmetry; apply Zdiv.Zminus_mod | ].
 reflexivity.

 destruct n.
  simpl in Hrp₁; simpl.
  injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
  rewrite <- Ha, <- Hb, <- Hc.
  split; [ rewrite <- Z_mod_expr_3; reflexivity | ].
  split; [ rewrite <- Z_mod_expr_3; reflexivity | ].
  reflexivity.

  rewrite Nat.add_1_r in Hrp₁.
  rewrite <- fold_rotate_param_mod_3_succ_succ in Hrp₁.
   rewrite <- Nat.add_1_r in Hrp₁.
   pose proof (rotate_param_app_bn n el p a b c N a₁ b₁ c₁ Hrp Hrp₁).
   do 2 rewrite <- Nat.add_1_r.
   rewrite <- Nat.add_assoc; simpl.
   rewrite Nat_mod_add_once; [ assumption | intros; discriminate ].

   apply Nat.lt_0_succ.
Qed.

Theorem rotate_param_app_a1n : ∀ el n p a b c N,
  fold_left rotate_param el p = (a, b, c, N)
  → fst3 (fold_left rotate_param (el ++ List.repeat ạ⁻¹ (n + 1)) p) ≡₃
      if zerop (n mod 2) then (0%Z, (b - c)%Z, (c - b)%Z)
      else (0%Z, (c - b)%Z, (b - c)%Z).
Proof.
intros el n p a b c N Hrp.
unfold "≡₃".
rewrite fold_left_app, Hrp; simpl.
remember (repeat ạ⁻¹ (n + 1)) as al.
remember (fst3 (fold_left rotate_param al (a, b, c, N))) as x eqn:Hrp₁.
subst al; symmetry in Hrp₁.
destruct x as ((a₁, b₁), c₁).
apply rotate_params_mod in Hrp₁.
revert n el p a b c N a₁ b₁ c₁ Hrp Hrp₁.
fix 1; intros.
destruct n.
 simpl in Hrp₁; simpl.
 injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
 rewrite <- Ha, <- Hb, <- Hc.
 split; [ reflexivity | ].
 split; symmetry; apply Zdiv.Zminus_mod.

 destruct n.
  simpl in Hrp₁; simpl.
  injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
  rewrite <- Ha, <- Hb, <- Hc.
  split; [ reflexivity | ].
  split; symmetry; apply Z_mod_expr_3.

  rewrite Nat.add_1_r in Hrp₁.
  rewrite <- fold_rotate_param_mod_3_succ_succ in Hrp₁.
   rewrite <- Nat.add_1_r in Hrp₁.
   pose proof (rotate_param_app_a1n n el p a b c N a₁ b₁ c₁ Hrp Hrp₁).
   do 2 rewrite <- Nat.add_1_r.
   rewrite <- Nat.add_assoc; simpl.
   rewrite Nat_mod_add_once; [ assumption | intros; discriminate ].

   apply Nat.lt_0_succ.
Qed.

Inspect 4.

Theorem rotate_param_app_b1n : ∀ el n p a b c N,
  fold_left rotate_param el p = (a, b, c, N)
  → fst3 (fold_left rotate_param (el ++ List.repeat ḅ⁻¹ (n + 1)) p) ≡₃
      if zerop (n mod 2) then ((a + b)%Z, (a + b)%Z, 0%Z)
      else ((- a - b)%Z, (- a - b)%Z, 0%Z).
Proof.
intros el n p a b c N Hrp.
unfold "≡₃".
rewrite fold_left_app, Hrp; simpl.
remember (repeat ḅ⁻¹ (n + 1)) as al.
remember (fst3 (fold_left rotate_param al (a, b, c, N))) as x eqn:Hrp₁.
subst al; symmetry in Hrp₁.
destruct x as ((a₁, b₁), c₁).
apply rotate_params_mod in Hrp₁.
revert n el p a b c N a₁ b₁ c₁ Hrp Hrp₁.
fix 1; intros.
destruct n.
 simpl in Hrp₁; simpl.
 injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
 rewrite <- Ha, <- Hb, <- Hc.
 split; [ symmetry; apply Z.add_mod; intros H; discriminate H | ].
 split; [ symmetry; apply Z.add_mod; intros H; discriminate H | ].
 reflexivity.

 destruct n.
  simpl in Hrp₁; simpl.
  injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
  rewrite <- Ha, <- Hb, <- Hc.
  split; [ rewrite <- Z_mod_expr_4; reflexivity | ].
  split; [ rewrite <- Z_mod_expr_4; reflexivity | ].
  reflexivity.

  rewrite Nat.add_1_r in Hrp₁.
  rewrite <- fold_rotate_param_mod_3_succ_succ in Hrp₁.
   rewrite <- Nat.add_1_r in Hrp₁.
   pose proof (rotate_param_app_b1n n el p a b c N a₁ b₁ c₁ Hrp Hrp₁).
   do 2 rewrite <- Nat.add_1_r.
   rewrite <- Nat.add_assoc; simpl.
   rewrite Nat_mod_add_once; [ assumption | intros; discriminate ].

   apply Nat.lt_0_succ.
Qed.

Theorem rotate_param_app : ∀ el e n p a b c N,
  fold_left rotate_param el p = (a, b, c, N)
  → fst3 (fold_left rotate_param (el ++ repeat e (n + 1)) p) ≡₃
      match e with
      | ạ => if zerop (n mod 2) then (0, b + c, b + c)%Z
             else (0, - b - c, - b - c)%Z
      | ạ⁻¹ => if zerop (n mod 2) then (0, b - c, c - b)%Z
               else (0, c - b, b - c)%Z
      | ḅ => if zerop (n mod 2) then (a - b, b - a, 0)%Z
             else (b - a, a - b, 0)%Z
      | ḅ⁻¹ => if zerop (n mod 2) then (a + b, a + b, 0)%Z
               else (- a - b, - a - b, 0)%Z
      end.
Proof.
intros el e n p a b c N Hp.
destruct e as (t, d).
destruct t, d.
 eapply rotate_param_app_a1n; eassumption.
 eapply rotate_param_app_an; eassumption.
 eapply rotate_param_app_b1n; eassumption.
 eapply rotate_param_app_bn; eassumption.
Qed.

Theorem rotate_param_1_0_0_expr : ∀ el a b c N,
  fold_left rotate_param el (1%Z, 0%Z, 0%Z, 0) = (a, b, c, N)
  → (a ^ 2 + 2 * b ^ 2 + c ^ 2 = 9 ^ Z.of_nat N)%Z.
Proof.
intros el a b c N Hr.
apply rotate_param_keep_dist in Hr.
rewrite Nat.mul_0_r, Nat2Z.inj_0, Z.pow_0_r, Z.mul_1_r in Hr.
rewrite Nat2Z.inj_mul in Hr.
rewrite Z.pow_mul_r in Hr; try apply Nat2Z.is_nonneg.
rewrite Hr; ring_simplify; reflexivity.
Qed.

Theorem N_1_0_0 :
  fst3 (fold_left rotate_param [] (1%Z, 0%Z, 0%Z, 0)) ≡₃ (1, 0, 0)%Z.
Proof.
split; [ reflexivity | split; reflexivity ].
Qed.

Definition eq_mod_3_refl : reflexive _ eq_mod_3.
Proof.
intros ((a, b), c).
split; [ reflexivity | split; reflexivity ].
Qed.

Definition eq_mod_3_sym : symmetric _ eq_mod_3.
Proof.
intros ((a₁, b₁), c₁) ((a₂, b₂), c₂) (Ha, (Hb, Hc)).
split; [ symmetry; assumption | split; symmetry; assumption ].
Qed.

Definition eq_mod_3_trans : transitive _ eq_mod_3.
Proof.
intros ((a₁, b₁), c₁) ((a₂, b₂), c₂) ((a₃, b₃), c₃).
intros (Ha12, (Hb12, Hc12)) (Ha23, (Hb23, Hc23)).
split; [ etransitivity; eassumption | split; etransitivity; eassumption ].
Qed.

Add Parametric Relation : _ eq_mod_3
 reflexivity proved by eq_mod_3_refl
 symmetry proved by eq_mod_3_sym
 transitivity proved by eq_mod_3_trans
 as eq_mod_3_equivalence.

Theorem rotate_1_0_0_b : rotate (P 1 0 0) ḅ = P (1/3) (2*√2/3) 0.
Proof.
simpl.
progress repeat rewrite Rmult_1_r.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rplus_0_r.
reflexivity.
Qed.

Theorem rotate_1_0_0_bb :
  fold_left rotate [ḅ; ḅ] (P 1 0 0) = P (-7/9) (4*√2/9) 0.
Proof.
simpl.
unfold Rdiv.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_1_r.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite <- Rmult_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
f_equal; lra.
Qed.

Theorem rotate_1_0_0_bbb :
  fold_left rotate [ḅ; ḅ; ḅ] (P 1 0 0) = P (-23/27) (-10*√2/27) 0.
Proof.
simpl.
unfold Rdiv.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_1_r.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite Rmult_plus_distr_l.
progress repeat rewrite <- Rmult_assoc.
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
f_equal; [ | lra ].
ring_simplify; simpl.
progress repeat rewrite Rmult_1_r.
rewrite sqrt_sqrt; lra.
Qed.

Compute fold_left rotate_param [ạ] (1, 0, 0, O)%Z.
Compute fold_left rotate_param [ḅ; ạ] (1, 0, 0, O)%Z.
Compute fold_left rotate_param [ạ; ḅ] (1, 0, 0, O)%Z.
Compute fold_left rotate_param [ạ; ạ; ḅ] (1, 0, 0, O)%Z.

Record combined := mknp { first : letter; path : list (bool * nat) }.

Definition other_elem t := match t with la => lb | lb => la end.

Fixpoint combine el :=
  match el with
  | E t₁ d₁ :: el₁ =>
      let np := combine el₁ in
      if letter_dec t₁ (first np) then
        match path np with
        | (d, n) :: dnl =>
            if Bool.bool_dec d₁ d then
              {| first := t₁; path := (d, S n) :: dnl |}
            else
              match n with
              | O => {| first := other_elem t₁; path := dnl |}
              | S n' => {| first := t₁; path := (d, n') :: dnl |}
              end
        | [] => {| first := t₁; path := [(d₁, O)] |}
        end
      else {| first := t₁; path := (d₁, O) :: path np |}
  | [] => {| first := la; path := [] |}
  end.

Fixpoint rotate_step pt e n :=
  match n with
  | O => pt
  | S n' => rotate (rotate_step pt e n') e
  end.

Fixpoint rotate_combined_loop first path pt :=
  match path with
  | (d, n) :: pa =>
      let pt := rotate_step pt (E first d) (S n) in
      rotate_combined_loop (other_elem first) pa pt
  | [] => pt
  end.

Definition rotate_combined nc := rotate_combined_loop (first nc) (path nc).

Theorem mul_rot_x_rotate_step_comm : ∀ pt n,
  mat_vec_mul rot_x (rotate_step pt ạ n) =
  rotate_step (mat_vec_mul rot_x pt) ạ n.
Proof.
intros.
induction n; [ reflexivity | simpl; f_equal; apply IHn ].
Qed.

Theorem mul_rot_inv_x_rotate_step_comm : ∀ pt n,
  mat_vec_mul rot_inv_x (rotate_step pt ạ⁻¹ n) =
  rotate_step (mat_vec_mul rot_inv_x pt) ạ⁻¹ n.
Proof.
intros.
induction n; [ reflexivity | simpl; f_equal; apply IHn ].
Qed.

Theorem mul_rot_z_rotate_step_comm : ∀ pt n,
  mat_vec_mul rot_z (rotate_step pt ḅ n) =
  rotate_step (mat_vec_mul rot_z pt) ḅ n.
Proof.
intros.
induction n; [ reflexivity | simpl; f_equal; apply IHn ].
Qed.

Theorem mul_rot_inv_z_rotate_step_comm : ∀ pt n,
  mat_vec_mul rot_inv_z (rotate_step pt ḅ⁻¹ n) =
  rotate_step (mat_vec_mul rot_inv_z pt) ḅ⁻¹ n.
Proof.
intros.
induction n; [ reflexivity | simpl; f_equal; apply IHn ].
Qed.

Theorem rotate_combined_loop_succ : ∀ t d n bnl pt,
  rotate_combined_loop t ((d, S n) :: bnl) pt =
  rotate_combined_loop t ((d, n) :: bnl) (rotate pt (E t d)).
Proof.
intros.
simpl.
destruct t, d; simpl.
 f_equal; f_equal; apply mul_rot_inv_x_rotate_step_comm.

 f_equal; f_equal; apply mul_rot_x_rotate_step_comm.

 f_equal; f_equal; apply mul_rot_inv_z_rotate_step_comm.

 f_equal; f_equal; apply mul_rot_z_rotate_step_comm.
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

Theorem rotate_rotate_step_comm : ∀ pt e n,
  rotate (rotate_step pt e n) e = rotate_step (rotate pt e) e n.
Proof.
intros.
induction n; [ reflexivity | simpl; f_equal; apply IHn ].
Qed.

Theorem rot_step_rot_inv_x : ∀ pt n,
  mat_vec_mul rot_x (rotate_step (mat_vec_mul rot_inv_x pt) ạ n) =
  rotate_step pt ạ n.
Proof.
intros.
revert pt.
induction n; intros; [ apply rot_rot_inv_x | simpl ].
symmetry; rewrite <- IHn.
reflexivity.
Qed.

Theorem rotate_combined_rotate : ∀ pt el,
  rotate_combined (combine el) pt = fold_left rotate el pt.
Proof.
intros.
revert pt.
induction el as [| e]; intros; subst; [ reflexivity | ].
simpl; rewrite <- IHel.
destruct e as (t, d).
destruct (letter_dec t (first (combine el))) as [H₁| H₁].
 remember (combine el) as nc eqn:Hnc.
 remember (path nc) as bnl eqn:Hbnl.
 symmetry in Hbnl.
 destruct bnl as [| (b, n)].
  unfold rotate_combined; simpl.
  rewrite Hbnl; simpl; reflexivity.

  destruct (Bool.bool_dec d b) as [Hd| Hd]; [ subst d | ].
   unfold rotate_combined.
   rewrite Hbnl, <- H₁.
   remember rotate_combined_loop as f.
   remember rotate as g; simpl; subst f g.
   apply rotate_combined_loop_succ.

   destruct n.
    unfold rotate_combined; simpl.
    destruct t, d; simpl.
     rewrite Hbnl, <- H₁; simpl.
     apply not_eq_sym, Bool.not_true_is_false in Hd; subst b.
     rewrite rot_rot_inv_x; reflexivity.

     rewrite Hbnl, <- H₁; simpl.
     apply not_eq_sym, Bool.not_false_is_true in Hd; subst b.
     rewrite rot_inv_rot_x; reflexivity.

     rewrite Hbnl, <- H₁; simpl.
     apply not_eq_sym, Bool.not_true_is_false in Hd; subst b.
     rewrite rot_rot_inv_z; reflexivity.

     rewrite Hbnl, <- H₁; simpl.
     apply not_eq_sym, Bool.not_false_is_true in Hd; subst b.
     rewrite rot_inv_rot_z; reflexivity.

    unfold rotate_combined; simpl.
    destruct t, d; simpl.
     rewrite Hbnl, <- H₁; simpl.
     apply not_eq_sym, Bool.not_true_is_false in Hd; subst b.
     symmetry; rewrite mul_rot_x_rotate_step_comm.
     rewrite rot_rot_inv_x; reflexivity.

     rewrite Hbnl, <- H₁; simpl.
     apply not_eq_sym, Bool.not_false_is_true in Hd; subst b.
     symmetry; rewrite mul_rot_inv_x_rotate_step_comm.
     rewrite rot_inv_rot_x; reflexivity.

     rewrite Hbnl, <- H₁; simpl.
     apply not_eq_sym, Bool.not_true_is_false in Hd; subst b.
     symmetry; rewrite mul_rot_z_rotate_step_comm.
     rewrite rot_rot_inv_z; reflexivity.

     rewrite Hbnl, <- H₁; simpl.
     apply not_eq_sym, Bool.not_false_is_true in Hd; subst b.
     symmetry; rewrite mul_rot_inv_z_rotate_step_comm.
     rewrite rot_inv_rot_z; reflexivity.

 destruct t; simpl.
  destruct d.
   unfold rotate_combined; simpl; f_equal.
   destruct (first (combine el)); [ exfalso; apply H₁; reflexivity | ].
   reflexivity.

   unfold rotate_combined; simpl; f_equal.
   destruct (first (combine el)); [ exfalso; apply H₁; reflexivity | ].
   reflexivity.

  destruct d.
   unfold rotate_combined; simpl; f_equal.
   destruct (first (combine el)); [ | exfalso; apply H₁; reflexivity ].
   reflexivity.

   unfold rotate_combined; simpl; f_equal.
   destruct (first (combine el)); [ | exfalso; apply H₁; reflexivity ].
   reflexivity.
Qed.

Fixpoint uncombine_loop first path :=
  match path with
  | (b, n) :: bnl =>
      repeat (E first b) (S n) ++ uncombine_loop (other_elem first) bnl
  | [] => []
  end.

Definition uncombine nc := uncombine_loop (first nc) (path nc).

Compute combine [ạ⁻¹; ḅ⁻¹; ạ; ḅ⁻¹; ạ⁻¹; ạ; ḅ; ḅ; ḅ].
Compute uncombine (combine [ạ⁻¹; ḅ⁻¹; ạ; ḅ⁻¹; ạ⁻¹; ạ; ḅ; ḅ; ḅ]).

Theorem other_elem_involutive : ∀ t, other_elem (other_elem t) = t.
Proof. intros; destruct t; reflexivity. Qed.

Theorem fold_uncombine : ∀ f p,
  uncombine_loop f p = uncombine {| first := f; path := p |}.
Proof. reflexivity. Qed.

Theorem list_nil_app_dec {A} : ∀ (l : list A),
  {l = []} + {∃ x l', l = l' ++ [x]}.
Proof.
intros l.
destruct l as [| x]; [ left; reflexivity | right ].
revert x.
induction l as [| y] using rev_ind; intros; [ exists x, []; reflexivity | ].
exists y, (x :: l); reflexivity.
Qed.

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

Theorem mat_mul_id_l : ∀ m, mat_mul mat_id m = m.
Proof.
intros m.
unfold mat_mul, mat_id; simpl.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
destruct m; reflexivity.
Qed.

Theorem mul_rot_x_rot_inv_x_id : mat_mul rot_x rot_inv_x = mat_id.
Proof.
unfold mat_mul, mat_id; simpl; unfold Rdiv.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
progress repeat rewrite <- Rmult_assoc.
f_equal; ring_simplify; [ | reflexivity | reflexivity | ].
 progress repeat rewrite <- Rsqr_pow2.
 rewrite Rsqr_sqrt; [ | lra ].
 progress repeat rewrite Rsqr_pow2; field.

 progress repeat rewrite <- Rsqr_pow2.
 rewrite Rsqr_sqrt; [ | lra ].
 progress repeat rewrite Rsqr_pow2; field.
Qed.

Theorem mat_assoc : ∀ m₁ m₂ m₃,
  mat_mul m₁ (mat_mul m₂ m₃) = mat_mul (mat_mul m₁ m₂) m₃.
Proof.
intros.
unfold mat_mul; simpl; f_equal; ring.
Qed.

Definition rot_mat e :=
  match e with
  | ạ⁻¹ => rot_inv_x
  | ạ => rot_x
  | ḅ⁻¹ => rot_inv_z
  | ḅ => rot_z
  end.

Theorem mat_vec_mul_rotate : ∀ pt e ml,
  mat_vec_mul ml (rotate pt e) = mat_vec_mul (mat_mul ml (rot_mat e)) pt.
Proof.
intros.
destruct pt as (x, y, z); simpl.
destruct e as (t, d); destruct t, d; simpl; (f_equal; ring).
Qed.

Theorem rotate_by_mat_mul : ∀ pt el,
  fold_left rotate el pt =
  mat_vec_mul (fold_left mat_mul (rev (map rot_mat el)) mat_id) pt.
Proof.
intros pt el.
revert pt.
induction el as [| e]; intros.
 destruct pt as (x, y, z); simpl; f_equal; ring.

 simpl; rewrite IHel, fold_left_app; simpl.
 rewrite mat_vec_mul_rotate; reflexivity.
Qed.

Theorem Rdiv_eq_0 : ∀ x y, (y ≠ 0)%R → (x / y = 0)%R → x = 0%R.
Proof.
intros x y Hy H.
apply Rmult_eq_compat_r with (r := y) in H.
unfold Rdiv in H.
rewrite Rmult_comm, <- Rmult_assoc, Rmult_shuffle0 in H.
rewrite Rinv_r_simpl_r in H; [ lra | apply Hy ].
Qed.

Theorem norm_list_app : ∀ el₁ el₂ el₃,
  norm_list el₁ = el₂
  → norm_list (el₁ ++ el₃) = norm_list (el₂ ++ el₃).
Proof.
intros el₁ el₂ el₃ Hn.
pose proof is_normal [] el₁ el₃ as H; simpl in H.
rewrite Hn in H; symmetry; assumption.
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
revert Hn; apply norm_list_impossible_start.
Qed.

(* "we claim that w(1,0,0) has the form (a,b√2,c)/3^k where a,b,c are
    integers and b is not divisible by 3" *)

Theorem rotate_param_1_0_0_b_nonzero : ∀ el el₁ d a b c n,
  el = E lb d :: el₁
  → norm_list el = el
  → fold_left rotate_param el (1, 0, 0, O)%Z = (a, b, c, n + S (length el₁))
  → (b mod 3 ≠ 0)%Z.
Proof.
intros el el₁ d a b c n Hel Hn Hu.
remember (length el₁) as len eqn:Hlen; symmetry in Hlen.
revert el el₁ d a b c n Hel Hn Hu Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len.
 rewrite Nat.add_1_r in Hu.
 apply length_zero_iff_nil in Hlen; subst el₁.
 subst el; simpl in Hu.
 destruct d; injection Hu; clear Hu; intros; subst; intros H; discriminate H.

 destruct (list_nil_app_dec el₁) as [H₁| (e₁, (el₂, Hel₂))].
  subst el₁; discriminate Hlen.

  subst el₁; simpl in Hlen.
  rewrite app_length in Hlen; simpl in Hlen.
  rewrite Nat.add_1_r in Hlen.
  apply eq_add_S in Hlen.
  rewrite app_comm_cons in Hel.
  remember (E lb d :: el₂) as el₁ eqn:Hel₁.
  generalize Hn; intros H₁; rewrite Hel in H₁.
  apply norm_list_app_diag in H₁.
  rewrite Hel, fold_left_app in Hu; simpl in Hu.
  remember (fold_left rotate_param el₁ (1%Z, 0%Z, 0%Z, 0)) as v eqn:Hp.
  symmetry in Hp.
  destruct v as (((a', b'), c'), N').
  destruct e₁ as (t₁, d₁); destruct t₁, d₁; simpl in Hu.
   injection Hu; clear Hu; intros HN Hc Hb Ha; subst a b c.
   rewrite <- Nat.add_succ_comm in HN; simpl in HN.
   apply eq_add_S in HN; subst N'.
   pose proof IHlen len (Nat.lt_succ_diag_r len) el₁ el₂ d a' b' c' n Hel₁
     H₁ Hp Hlen as Hb'.
   rename a' into a; rename b' into b; rename c' into c.
   destruct (list_nil_app_dec el₂) as [H₂| (e₁, (el₃, Hel₃))].
    subst el₂; simpl in Hlen; subst len; simpl in Hel.
    subst el₁; simpl in Hp.
    rewrite Nat.add_1_r in Hp.
    destruct d; injection Hp; intros; subst; intros H; discriminate H.

    subst el₂.
    rewrite Hel₁ in Hel; simpl in Hel.
    rewrite <- app_assoc in Hel; simpl in Hel.
    generalize Hn; intros H₂.
    rewrite app_comm_cons in Hel.
    rewrite Hel in H₂.
    apply norm_list_app_diag in H₂.
    destruct len; [ destruct el₃ in Hlen; discriminate Hlen | ].
    assert (Hl : len < S (S len)) by (apply le_n_S, Nat.le_succ_diag_r).
    rewrite app_length in Hlen; simpl in Hlen.
    rewrite Nat.add_1_r in Hlen.
    apply eq_add_S in Hlen.
    remember (E lb d :: el₃) as el₂ eqn:Hel₂.
    rewrite app_comm_cons, <- Hel₂ in Hel₁.
    rewrite Hel₁, fold_left_app in Hp.
    simpl in Hp.
    remember (fold_left rotate_param el₂ (1, 0, 0, O)%Z) as p' eqn:Hp'.
    symmetry in Hp'.
    destruct p' as (((a', b'), c'), N').
    simpl in Hp.
    destruct e₁ as (t₁, d₁); destruct t₁, d₁.
     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite <- Nat.add_succ_comm in HN; simpl in HN.
     apply eq_add_S in HN; subst N'.
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
     apply norm_list_impossible_consecutive.

     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite Z.mul_assoc, Z.mul_shuffle0.
     rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite Z.mul_assoc, Z.mul_shuffle0.
     rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   injection Hu; clear Hu; intros HN Hc Hb Ha; subst a b c.
   rewrite <- Nat.add_succ_comm in HN; simpl in HN.
   apply eq_add_S in HN; subst N'.
   pose proof IHlen len (Nat.lt_succ_diag_r len) el₁ el₂ d a' b' c' n Hel₁
     H₁ Hp Hlen as Hb'.
   rename a' into a; rename b' into b; rename c' into c.
   destruct (list_nil_app_dec el₂) as [H₂| (e₁, (el₃, Hel₃))].
    subst el₂; simpl in Hlen; subst len; simpl in Hel.
    subst el₁; simpl in Hp.
    rewrite Nat.add_1_r in Hp.
    destruct d; injection Hp; intros; subst; intros H; discriminate H.

    subst el₂.
    rewrite Hel₁ in Hel; simpl in Hel.
    rewrite <- app_assoc in Hel; simpl in Hel.
    generalize Hn; intros H₂.
    rewrite app_comm_cons in Hel.
    rewrite Hel in H₂.
    apply norm_list_app_diag in H₂.
    destruct len; [ destruct el₃ in Hlen; discriminate Hlen | ].
    assert (Hl : len < S (S len)) by (apply le_n_S, Nat.le_succ_diag_r).
    rewrite app_length in Hlen; simpl in Hlen.
    rewrite Nat.add_1_r in Hlen.
    apply eq_add_S in Hlen.
    remember (E lb d :: el₃) as el₂ eqn:Hel₂.
    rewrite app_comm_cons, <- Hel₂ in Hel₁.
    rewrite Hel₁, fold_left_app in Hp.
    simpl in Hp.
    remember (fold_left rotate_param el₂ (1, 0, 0, O)%Z) as p' eqn:Hp'.
    symmetry in Hp'.
    destruct p' as (((a', b'), c'), N').
    simpl in Hp.
    destruct e₁ as (t₁, d₁); destruct t₁, d₁.
     exfalso; revert Hn; rewrite Hel.
     apply norm_list_impossible_consecutive.

     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite <- Nat.add_succ_comm in HN; simpl in HN.
     apply eq_add_S in HN; subst N'.
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

     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite Z.mul_assoc, Z.mul_shuffle0.
     unfold Z.sub; rewrite Zopp_mult_distr_l.
     rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite Z.mul_assoc, Z.mul_shuffle0.
     unfold Z.sub; rewrite Zopp_mult_distr_l.
     rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   injection Hu; clear Hu; intros HN Hc Hb Ha; subst a b c.
   rewrite <- Nat.add_succ_comm in HN; simpl in HN.
   apply eq_add_S in HN; subst N'.
   pose proof IHlen len (Nat.lt_succ_diag_r len) el₁ el₂ d a' b' c' n Hel₁
     H₁ Hp Hlen as Hb'.
   rename a' into a; rename b' into b; rename c' into c.
   destruct (list_nil_app_dec el₂) as [H₂| (e₁, (el₃, Hel₃))].
    subst el₂; simpl in Hlen; subst len; simpl in Hel.
    subst el₁; simpl in Hp.
    rewrite Nat.add_1_r in Hp.
    destruct d.
     injection Hp; intros; subst; simpl; intros H; discriminate H.

     exfalso; revert Hn; rewrite Hel; apply norm_list_impossible_start.

    subst el₂.
    rewrite Hel₁ in Hel; simpl in Hel.
    rewrite <- app_assoc in Hel; simpl in Hel.
    generalize Hn; intros H₂.
    rewrite app_comm_cons in Hel.
    rewrite Hel in H₂.
    apply norm_list_app_diag in H₂.
    destruct len; [ destruct el₃ in Hlen; discriminate Hlen | ].
    assert (Hl : len < S (S len)) by (apply le_n_S, Nat.le_succ_diag_r).
    rewrite app_length in Hlen; simpl in Hlen.
    rewrite Nat.add_1_r in Hlen.
    apply eq_add_S in Hlen.
    remember (E lb d :: el₃) as el₂ eqn:Hel₂.
    rewrite app_comm_cons, <- Hel₂ in Hel₁.
    rewrite Hel₁, fold_left_app in Hp.
    simpl in Hp.
    remember (fold_left rotate_param el₂ (1, 0, 0, O)%Z) as p' eqn:Hp'.
    symmetry in Hp'.
    destruct p' as (((a', b'), c'), N').
    simpl in Hp.
    destruct e₁ as (t₁, d₁); destruct t₁, d₁.
     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite Z.mul_assoc, Z.mul_shuffle0, Z.add_comm.
     rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite Z.mul_assoc, Z.mul_shuffle0, Z.add_comm.
     rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite <- Nat.add_succ_comm in HN; simpl in HN.
     apply eq_add_S in HN; subst N'.
     rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
     remember (-2 * (a' + 4 * b') + (-2 * a' + b') + 3 * b' * 3)%Z as x eqn:Hx.
     ring_simplify in Hx; subst x.
     replace (-4)%Z with (2 * (-2))%Z by reflexivity.
     rewrite <- Z.mul_assoc, <- Z.mul_add_distr_l.
     intros H; apply Hb'.
     apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
     apply Z.gauss in H; [ | reflexivity ].
     destruct H as (k, H); rewrite H.
     apply Z.mod_mul; intros; discriminate.

     exfalso; revert Hn; rewrite Hel.
     apply norm_list_impossible_consecutive.

   injection Hu; clear Hu; intros HN Hc Hb Ha; subst a b c.
   rewrite <- Nat.add_succ_comm in HN; simpl in HN.
   apply eq_add_S in HN; subst N'.
   pose proof IHlen len (Nat.lt_succ_diag_r len) el₁ el₂ d a' b' c' n Hel₁
     H₁ Hp Hlen as Hb'.
   rename a' into a; rename b' into b; rename c' into c.
   destruct (list_nil_app_dec el₂) as [H₂| (e₁, (el₃, Hel₃))].
    subst el₂; simpl in Hlen; subst len; simpl in Hel.
    subst el₁; simpl in Hp.
    rewrite Nat.add_1_r in Hp.
    destruct d.
     exfalso; revert Hn; rewrite Hel; apply norm_list_impossible_start.

     injection Hp; intros; subst; intros H; discriminate H.

    subst el₂.
    rewrite Hel₁ in Hel; simpl in Hel.
    rewrite <- app_assoc in Hel; simpl in Hel.
    generalize Hn; intros H₂.
    rewrite app_comm_cons in Hel.
    rewrite Hel in H₂.
    apply norm_list_app_diag in H₂.
    destruct len; [ destruct el₃ in Hlen; discriminate Hlen | ].
    assert (Hl : len < S (S len)) by (apply le_n_S, Nat.le_succ_diag_r).
    rewrite app_length in Hlen; simpl in Hlen.
    rewrite Nat.add_1_r in Hlen.
    apply eq_add_S in Hlen.
    remember (E lb d :: el₃) as el₂ eqn:Hel₂.
    rewrite app_comm_cons, <- Hel₂ in Hel₁.
    rewrite Hel₁, fold_left_app in Hp.
    simpl in Hp.
    remember (fold_left rotate_param el₂ (1, 0, 0, O)%Z) as p' eqn:Hp'.
    symmetry in Hp'.
    destruct p' as (((a', b'), c'), N').
    simpl in Hp.
    destruct e₁ as (t₁, d₁); destruct t₁, d₁.
     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite Z.mul_assoc, Z.mul_shuffle0, Z.add_comm.
     rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite Z.mul_assoc, Z.mul_shuffle0, Z.add_comm.
     rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

     exfalso; revert Hn; rewrite Hel.
     apply norm_list_impossible_consecutive.

     injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c.
     rewrite <- Nat.add_succ_comm in HN; simpl in HN.
     apply eq_add_S in HN; subst N'.
     rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
     remember (2 * (a' - 4 * b') + (2 * a' + b') + 3 * b' * 3)%Z as x eqn:Hx.
     ring_simplify in Hx; subst x.
     replace 4%Z with (2 * 2)%Z by reflexivity.
     rewrite <- Z.mul_assoc, <- Z.mul_add_distr_l.
     intros H; apply Hb'.
     apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
     apply Z.gauss in H; [ | reflexivity ].
     destruct H as (k, H); rewrite H.
     apply Z.mod_mul; intros; discriminate.
Qed.

Theorem rotate_1_0_0_b_nonzero : ∀ w el el₁ d,
  el = E lb d :: el₁
  → norm_list el = el
  → w = fold_left rotate el
  → ∃ a b c k,
    w (P 1 0 0) = P (IZR a/3^k) (IZR b*√2/3^k) (IZR c/3^k) ∧
    (b mod 3 ≠ 0)%Z.
Proof.
intros w el el₁ d Hel Hn Hw.
subst w.
remember (fold_left rotate_param el (1, 0, 0, O)%Z) as u eqn:Hu.
symmetry in Hu; destruct u as (((a, b), c), len).
generalize Hu; intros Hv.
apply rotate_param_rotate in Hv; simpl in Hv.
rewrite Rmult_0_l in Hv.
rewrite Rdiv_0_l in Hv.
replace (1/1)%R with 1%R in Hv by lra.
destruct Hv as (Hv, Hlen).
rewrite Hv.
exists a, b, c, len.
split; [ reflexivity | clear Hv ].
symmetry in Hlen.
rewrite Hel in Hlen; simpl in Hlen.
destruct len; [ subst el; discriminate Hlen | ].
apply eq_add_S in Hlen.
subst len; eapply rotate_param_1_0_0_b_nonzero with (n := O); eassumption.
Qed.

End Rotation.
