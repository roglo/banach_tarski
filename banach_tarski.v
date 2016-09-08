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

Theorem cons_comm_app {A} : ∀ (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. reflexivity. Qed.

Definition xor (A B : Prop) : Prop := A ∧ ¬B ∨ ¬A ∧ B.
Notation "x ⊕ y" := (xor x y) (at level 85, right associativity).

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

Definition rotate pt e :=
  match e with
  | ạ => mat_vec_mul rot_x pt
  | ạ⁻¹ => mat_vec_mul rot_inv_x pt
  | ḅ => mat_vec_mul rot_z pt
  | ḅ⁻¹ => mat_vec_mul rot_inv_z pt
  end.

Definition neg_rot '(E t d) := E t (negb d).

Definition rotate_param '(a, b, c, N) e :=
  match e with
  | ạ => ((3 * a)%Z, (b - 2 * c)%Z, (4 * b + c)%Z, S N)
  | ạ⁻¹ => ((3 * a)%Z, (b + 2 * c)%Z, (- 4 * b + c)%Z, S N)
  | ḅ => ((a - 4 * b)%Z, (b + 2 * a)%Z, (3 * c)%Z, S N)
  | ḅ⁻¹ => ((a + 4 * b)%Z, (b - 2 * a)%Z, (3 * c)%Z, S N)
  end.

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
   rewrite plus_IZR, minus_IZR.
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
revert Hn; apply norm_list_impossible_start.
Qed.

Theorem rotate_prop : ∀ p t d el el₁ el₂ e a b c,
  t = lb ∧ p = (1, 0, 0, O)%Z ∨
  t = la ∧ p = (0, 0, 1, O)%Z
  → el₁ = E t d :: el₂
  → el = el₁ ++ [e]
  → norm_list el = el
  → fold_left rotate_param el₁ p = (a, b, c, length el₁)
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
destruct (list_nil_app_dec el₂) as [H₂| (e₁, (el₃, Hel₃))].
 subst el₂; simpl in Hlen; subst len; simpl in Hel.
 subst el₁; simpl in Hp.
 destruct Htp as [(Ht, Hq)| (Ht, Hq)]; subst t p.
  destruct d; injection Hp; intros; subst.
   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_impossible_start.

   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_impossible_start.

  destruct d; injection Hp; intros; subst.
   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_impossible_start.

   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_impossible_start.

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
 remember (E t d :: el₃) as el₂ eqn:Hel₂.
 rewrite app_comm_cons, <- Hel₂ in Hel₁.
 rewrite Hel₁, fold_left_app in Hp.
 simpl in Hp.
 remember (fold_left rotate_param el₂ p) as p' eqn:Hp'.
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
   apply norm_list_impossible_consecutive.

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   exfalso; revert Hn; rewrite Hel.
   apply norm_list_impossible_consecutive.

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
   apply norm_list_impossible_consecutive.

  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   exfalso; revert Hn; rewrite Hel.
   apply norm_list_impossible_consecutive.

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
  → el = E t d :: el₁
  → norm_list el = el
  → fold_left rotate_param el p = (a, b, c, length el)
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

 destruct (list_nil_app_dec el₁) as [H₁| (e₁, (el₂, Hel₂))].
  subst el₁; discriminate Hlen.

  subst el₁; simpl in Hlen.
  rewrite app_length in Hlen; simpl in Hlen.
  rewrite Nat.add_1_r in Hlen.
  apply eq_add_S in Hlen.
  rewrite app_comm_cons in Hel.
  remember (E t d :: el₂) as el₁ eqn:Hel₁.
  generalize Hn; intros H₁; rewrite Hel in H₁.
  apply norm_list_app_diag in H₁.
  rewrite Hel, fold_left_app in Hu; simpl in Hu.
  remember (fold_left rotate_param el₁ p) as v eqn:Hp.
  symmetry in Hp.
  destruct v as (((a', b'), c'), N').
  assert (Hss : len < S len) by apply Nat.lt_succ_diag_r.
  assert (N' = S len); [ | subst N' ].
   destruct e₁ as (t₁, d₁).
   rewrite app_length in Hu; simpl in Hu; rewrite Nat.add_1_r in Hu.
   destruct t₁, d₁; simpl in Hu; injection Hu; intros; subst; reflexivity.

   rewrite <- Hlen in Hp.
   replace (S (length el₂)) with (length el₁) in Hp by (subst; reflexivity).
   pose proof IHlen _ Hss _ _ _ _ _ _ Hel₁ H₁ Hp Hlen as Hb'; subst len.
   pose proof rotate_prop p t d el el₁ el₂ e₁ a' b' c' Htp Hel₁ Hel Hn Hp Hb'.
   destruct e₁ as (t₁, d₁).
   destruct t₁, d₁; injection Hu; intros; subst; assumption.
Qed.

(* "we claim that w(1,0,0) has the form (a,b√2,c)/3^k where a,b,c are
    integers and b is not divisible by 3" (Stan Wagon) *)

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
rewrite Rmult_0_l, Rdiv_0_l, Rdiv_1_r in Hv.
destruct Hv as (Hv, Hlen).
rewrite Hv.
exists a, b, c, len.
split; [ reflexivity | clear Hv ].
symmetry in Hlen.
rewrite Hel in Hlen; simpl in Hlen.
destruct len; [ subst el; discriminate Hlen | ].
apply eq_add_S in Hlen.
subst len.
replace (S (length el₁)) with (length el) in Hu by (subst; reflexivity).
eapply rotate_param_b_nonzero; try eassumption.
left; split; reflexivity.
Qed.

Theorem rotate_0_0_1_b_nonzero : ∀ w el el₁ d,
  el = E la d :: el₁
  → norm_list el = el
  → w = fold_left rotate el
  → ∃ a b c k,
    w (P 0 0 1) = P (IZR a/3^k) (IZR b*√2/3^k) (IZR c/3^k) ∧
    (b mod 3 ≠ 0)%Z.
Proof.
intros w el el₁ d Hel Hn Hw.
subst w.
remember (fold_left rotate_param el (0, 0, 1, O)%Z) as u eqn:Hu.
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
destruct len; [ subst el; discriminate Hlen | ].
apply eq_add_S in Hlen.
subst len.
replace (S (length el₁)) with (length el) in Hu by (subst; reflexivity).
eapply rotate_param_b_nonzero; try eassumption.
right; split; reflexivity.
Qed.

Theorem rotate_1_0_0_is_diff : ∀ el el₁ d,
  el = E lb d :: el₁
  → norm_list el = el
  → fold_left rotate el (P 1 0 0) ≠ P 1 0 0.
Proof.
intros el el₁ d Hel Hn.
remember (fold_left rotate el) as w eqn:Hw.
pose proof rotate_1_0_0_b_nonzero w el el₁ d Hel Hn Hw as H.
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

Theorem rotate_0_0_1_is_diff : ∀ el el₁ d,
  el = E la d :: el₁
  → norm_list el = el
  → fold_left rotate el (P 0 0 1) ≠ P 0 0 1.
Proof.
intros el el₁ d Hel Hn.
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

End Rotation.

Check nonempty_rotation_is_not_identity.

Section Orbit.

Definition on_sphere '(P x y z) := (x ^ 2 + y ^ 2 + z ^ 2 = 1)%R.

Record point_on_sphere := mkorb { op : point; oi : on_sphere op }.

Definition same_orbit x y := ∃ el, fold_left rotate el x = y.

Theorem same_orbit_refl : reflexive _ same_orbit.
Proof. intros; exists []; reflexivity. Qed.

Theorem same_orbit_sym : symmetric _ same_orbit.
Proof.
intros p₁ p₂ (el, H); simpl in H.
unfold same_orbit; simpl.
exists (rev (map neg_rot el)).
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

Axiom func_choice : ∀ (A B : Type) (R : A → B → Prop),
  (∀ x : A, ∃ y : B, R x y) → ∃ f : A → B, ∀ x : A, R x (f x).
(* mmm... since same_orbit is an equivalence relation, it is reflexive;
   then, the identity function works; no need of this version of axiom
   of choice! *)

Definition select_orbit_origin :=
  func_choice point point same_orbit
    (λ x, ex_intro (same_orbit x) x (same_orbit_refl x)).

Axiom my_choice : ∀ (A B : Type) (R : A → A → Prop),
  { f : A → B | ∀ x y, R x y → f x = f y }.
(* drawback: I found nowhere this version of the axiom of choice!
   I don't know if it is a correct version! *)

Definition select_orbit_origin2 :=
  my_choice point point same_orbit.
Print select_orbit_origin2.

Goal True.
pose proof select_orbit_origin2 as H.
destruct H as (f, Hf).
Abort.

Definition is_order {A} R :=
  reflexive A R ∧ antisymmetric A R ∧ transitive A R.

Definition sub_type A := A → Prop.
Definition not_empty {A} (P : A → Prop) := ∃ x, P x.

(* My idea of what Zermelo theorem should be...
   For any type A, there exists an order R (reflexive, antisymmetric and
   transitive) such that for any non empty subset P of A, there exists
   an element y less than any other element z of P (R is well ordered). *)
Axiom Zermelo :
  ∀ (A : Type), ∃ (R : A → A → Prop), (*is_order R ∧*)
  ∀ (P : sub_type A), not_empty P → ∃ y, P y ∧ ∀ z, P z → R y z.

Theorem Zermelo_imp_total_order : ∀ A, ∃ R, ∀ (P : sub_type A) x y,
  P x → P y → R x y ∨ R y x.
Proof.
intros A.
pose proof Zermelo A as H.
destruct H as (R, (*Rord,*) Rprop).
exists R; intros P x y px py.
set (Q u := u = x ∨ u = y).
pose proof Rprop Q (ex_intro _ x (or_introl eq_refl)) as H.
destruct H as (u, (qu, H)).
destruct qu; subst u.
 left; apply H; right; reflexivity.
 right; apply H; left; reflexivity.
Qed.

Theorem Zermelo_relation_reflexive :
  ∀ A, ∃ (R : A → A → Prop), ∀ (P : sub_type A) x, P x → R x x.
Proof.
intros A.
pose proof Zermelo A as H.
destruct H as (R, Rprop).
exists R; intros P x px.
pose proof Rprop (eq x) (ex_intro _ x (eq_refl _)) as H.
destruct H as (y, (py, H)); subst y.
apply H; reflexivity.
Qed.

Theorem Zermelo_relation_antisymmetric :
  ∀ A, ∃ (R : A → A → Prop), ∀ (P : sub_type A) x y,
  P x → P y → R x y → R y x → x = y.
Proof.
intros A.
pose proof Zermelo A as H.
destruct H as (R, Rprop).
exists R; intros P x y px py Hxy Hyx.
set (Q u := u = x ∨ u = y).
pose proof Rprop Q (ex_intro _ x (or_introl eq_refl)) as H.
destruct H as (t, (qt, H)).
destruct qt; subst t.
(* not sure... *) Abort.

Theorem Zermelo_relation_transitive :
  ∀ A, ∃ (R : A → A → Prop), ∀ (P : sub_type A) x y z,
  P x → P y → P z → R x y → R y z → R x z.
Proof.
intros A.
pose proof Zermelo A as H.
destruct H as (R, Rprop).
exists R; intros P x y z px py pz Hxy Hyz.
set (Q t := t = x ∨ t = y ∨ t = z).
pose proof Rprop Q (ex_intro _ x (or_introl eq_refl)) as H.
destruct H as (t, (qt, H)).
destruct qt as [| qt]; [ subst t | destruct qt; subst t ].
 apply H; right; right; reflexivity.
(* not sure... *) Abort.

Definition orbit p :=
  match my_choice point point same_orbit with
  | exist _ f _ => f p
  end.

Theorem same_orbit_same_representant : ∀ (orb₁ orb₂ : orbit),
  orb₁ = orb₂.

End Orbit.
