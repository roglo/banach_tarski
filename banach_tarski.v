(* Banach-Tarski paradox. *)
(* translated in coq from wikipedia pen-and-paper proof *)

Require Import Utf8.
Require Import List.
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

Theorem bool_dec_negb_r : ∀ b,
  Bool.bool_dec b (negb b) =
  right (if b return _ then true_neq_negb_true else false_neq_negb_false).
Proof.
intros b.
destruct b; reflexivity.
Qed.

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
Opaque letter_opp_dec.
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
set (e := E x d).
set (ei := E x (negb d)).
destruct (letter_opp_dec e ei) as [H| H]; [ reflexivity | ].
exfalso; apply H, letter_opp_inv.
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
set (e₁ := E x true).
set (e₂ := E y d).
destruct (letter_opp_dec e₁ e₂) as [H₂| H₂]; [ subst e₁ e₂ | reflexivity ].
exfalso.
unfold letter_opp in H₂.
destruct (letter_dec x y) as [H₃| H₃]; [ | contradiction ].
destruct (Bool.bool_dec true d) as [H₄| H₄]; [ contradiction | ].
apply not_eq_sym, neq_negb in H₄; simpl in H₄.
apply H₁; split; assumption.
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
  P (a₁₁ mat * x + a₂₁ mat * y + a₃₁ mat * z)
    (a₁₂ mat * x + a₂₂ mat * y + a₃₂ mat * z)
    (a₁₃ mat * x + a₂₃ mat * y + a₃₃ mat * z).

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
  | ạ => ((3 * a)%Z, (b + 2 * c)%Z, (- 4 * b + c)%Z, S N)
  | ạ⁻¹ => ((3 * a)%Z, (b - 2 * c)%Z, (4 * b + c)%Z, S N)
  | ḅ => ((a + 4 * b)%Z, (- 2 * a + b)%Z, (3 * c)%Z, S N)
  | ḅ⁻¹ => ((a - 4 * b)%Z, (2 * a + b)%Z, (3 * c)%Z, S N)
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

Theorem rotate_param_rotate : ∀ el x y z a b c N,
  fold_left rotate_param el (x, y, z, 0) = (a, b, c, N)
  → fold_left rotate el (P (IZR x) (IZR y * √2) (IZR z)) =
      P (IZR a/3^N) (IZR b*√2/3^N) (IZR c/3^N).
Proof.
intros el x y z a₁ b₁ c₁ N₁ Hr.
simpl in Hr; simpl.
revert a₁ b₁ c₁ N₁ Hr.
induction el as [| (t, d)] using rev_ind; intros.
 simpl; simpl in Hr.
 injection Hr; intros; subst; simpl.
 f_equal; lra.

 rewrite fold_left_app in Hr; simpl in Hr.
 rewrite fold_left_app; simpl.
 remember (fold_left rotate_param el (x, y, z, 0)) as rp eqn:Hrp.
 symmetry in Hrp.
 destruct rp as (((a, b), c), N).
 erewrite IHel; [ simpl in Hr; simpl; unfold Rdiv | reflexivity ].
 progress repeat rewrite Rmult_1_l.
 progress repeat rewrite Rmult_0_l.
 progress repeat rewrite Rplus_0_l.
 progress repeat rewrite Rplus_0_r.
 progress repeat rewrite <- Rmult_assoc.
 rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
 rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
 destruct t, d; injection Hr; clear Hr; intros; subst; simpl.
  rewrite plus_IZR, minus_IZR.
  progress repeat rewrite mult_IZR.
  rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

  rewrite plus_IZR, plus_IZR.
  progress repeat rewrite mult_IZR.
  rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

  rewrite plus_IZR, minus_IZR.
  progress repeat rewrite mult_IZR.
  rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

  rewrite plus_IZR, plus_IZR.
  progress repeat rewrite mult_IZR.
  rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].
Qed.

Definition fst3 {A B C D} '((a, b, c, d) : A * B * C * D) := (a, b, c).

Definition eq_mod_3 '(a₁, b₁, c₁) '(a₂, b₂, c₂) :=
  (a₁ mod 3 = a₂ mod 3)%Z ∧
  (b₁ mod 3 = b₂ mod 3)%Z ∧
  (c₁ mod 3 = c₂ mod 3)%Z.

Notation "x ≡₃ y" := (eq_mod_3 x y) (at level 70).

Definition rotate_param_mod_3 '(a, b, c) e :=
 match e with
 | ạ⁻¹ => (0%Z, ((b + c) mod 3)%Z, ((b + c) mod 3)%Z)
 | ạ => (0%Z, ((b - c) mod 3)%Z, ((c - b) mod 3)%Z)
 | ḅ⁻¹ => (((a - b) mod 3)%Z, ((b - a) mod 3)%Z, 0%Z)
 | ḅ => (((a + b) mod 3)%Z, ((a + b) mod 3)%Z, 0%Z)
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
 erewrite <- IHel; [ | eassumption ].
 f_equal; f_equal; [ f_equal | ].
  rewrite Z.mul_comm, Z.mod_mul; [ reflexivity | intros; discriminate ].

  rewrite <- Z.add_mod; [ | intros; discriminate ].
  rewrite <- Z.mod_add with (b := (-c₁)%Z); [ | intros; discriminate ].
  f_equal; ring_simplify; reflexivity.

  rewrite <- Z.add_mod; [ | intros; discriminate ].
  rewrite <- Z.mod_add with (b := b₁); [ | intros; discriminate ].
  f_equal; ring_simplify; reflexivity.

 erewrite <- IHel; [ | eassumption ].
 f_equal; f_equal; [ f_equal | ].
  rewrite Z.mul_comm, Z.mod_mul; [ reflexivity | intros; discriminate ].

  rewrite <- Zdiv.Zminus_mod.
  rewrite <- Z.mod_add with (b := c₁); [ | intros; discriminate ].
  f_equal; ring_simplify; reflexivity.

  rewrite <- Zdiv.Zminus_mod.
  rewrite <- Z.mod_add with (b := (-b₁)%Z); [ | intros; discriminate ].
  f_equal; ring_simplify; reflexivity.

 erewrite <- IHel; [ | eassumption ].
 f_equal; f_equal; [ f_equal | ].
  rewrite <- Zdiv.Zminus_mod.
  rewrite <- Z.mod_add with (b := (- b₁)%Z); [ | intros; discriminate ].
  f_equal; ring_simplify; reflexivity.

  rewrite <- Zdiv.Zminus_mod.
  rewrite <- Z.mod_add with (b := a₁); [ | intros; discriminate ].
  f_equal; ring_simplify; reflexivity.

  rewrite Z.mul_comm, Z.mod_mul; [ reflexivity | intros; discriminate ].

 erewrite <- IHel; [ | eassumption ].
 f_equal; f_equal; [ f_equal | ].
  rewrite <- Z.add_mod; [ | intros; discriminate ].
  rewrite <- Z.mod_add with (b := b₁); [ | intros; discriminate ].
  f_equal; ring_simplify; reflexivity.

  rewrite <- Z.add_mod; [ | intros; discriminate ].
  rewrite <- Z.mod_add with (b := (- a₁)%Z); [ | intros; discriminate ].
  f_equal; ring_simplify; reflexivity.

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
  f_equal; [ f_equal; apply Z_mod_expr_1 | apply Z_mod_expr_1 ].

  f_equal; [ f_equal; apply Z_mod_expr_2 | apply Z_mod_expr_2 ].

  f_equal; f_equal; apply Z_mod_expr_2.

  f_equal; f_equal; apply Z_mod_expr_1.

 apply IHn; [ apply Nat.lt_0_succ | subst p'; reflexivity ].
Qed.

Theorem rotate_param_app_an : ∀ el n p a b c N,
  fold_left rotate_param el p = (a, b, c, N)
  → fst3 (fold_left rotate_param (el ++ List.repeat ạ (n + 1)) p) ≡₃
      if zerop (n mod 2) then (0%Z, (b - c)%Z, (c -  b)%Z)
      else (0%Z, (c - b)%Z, (b - c)%Z).
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
 split; [ reflexivity | split; symmetry; apply Zdiv.Zminus_mod ].

 destruct n.
  simpl in Hrp₁; simpl.
  injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
  rewrite <- Ha, <- Hb, <- Hc.
  split; [ reflexivity | split; symmetry; apply Z_mod_expr_3 ].

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
      if zerop (n mod 2) then ((a + b)%Z, (a + b)%Z, 0%Z)
      else ((- a - b)%Z, (- a - b)%Z, 0%Z).
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
 split; [ symmetry; apply Z.add_mod; intros; discriminate | ].
 split; [ symmetry; apply Z.add_mod; intros; discriminate | ].
 reflexivity.

 destruct n.
  simpl in Hrp₁; simpl.
  injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
  rewrite <- Ha, <- Hb, <- Hc.
  split; [ symmetry; apply Z_mod_expr_4 | ].
  split; [ symmetry; apply Z_mod_expr_4 | reflexivity ].

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
      if zerop (n mod 2) then (0%Z, (b + c)%Z, (b + c)%Z)
      else (0%Z, (- b - c)%Z, (- b - c)%Z).
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
 split; symmetry; apply Z.add_mod; intros; discriminate.

 destruct n.
  simpl in Hrp₁; simpl.
  injection Hrp₁; clear Hrp₁; intros Ha Hb Hc.
  rewrite <- Ha, <- Hb, <- Hc.
  split; [ reflexivity | ].
  split; rewrite <- Z_mod_expr_4; f_equal; ring.

  rewrite Nat.add_1_r in Hrp₁.
  rewrite <- fold_rotate_param_mod_3_succ_succ in Hrp₁.
   rewrite <- Nat.add_1_r in Hrp₁.
   pose proof (rotate_param_app_a1n n el p a b c N a₁ b₁ c₁ Hrp Hrp₁).
   do 2 rewrite <- Nat.add_1_r.
   rewrite <- Nat.add_assoc; simpl.
   rewrite Nat_mod_add_once; [ assumption | intros; discriminate ].

   apply Nat.lt_0_succ.
Qed.

Theorem rotate_param_app_b1n : ∀ el n p a b c N,
  fold_left rotate_param el p = (a, b, c, N)
  → fst3 (fold_left rotate_param (el ++ List.repeat ḅ⁻¹ (n + 1)) p) ≡₃
      if zerop (n mod 2) then ((a - b)%Z, (b - a)%Z, 0%Z)
      else ((b - a)%Z, (a - b)%Z, 0%Z).
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
      | ạ => if zerop (n mod 2) then (0, b - c, c - b)%Z
             else (0, c - b, b - c)%Z
      | ạ⁻¹ => if zerop (n mod 2) then (0, b + c, b + c)%Z
               else (0, - b - c, - b - c)%Z
      | ḅ => if zerop (n mod 2) then (a + b, a + b, 0)%Z
             else (- a - b, - a - b, 0)%Z
      | ḅ⁻¹ => if zerop (n mod 2) then (a - b, b - a, 0)%Z
               else (b - a, a - b, 0)%Z
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

Record norm_path := mknp { last : letter; path : list (bool * nat) }.

Definition other_elem t := match t with la => lb | lb => la end.

Definition path_start np :=
  if zerop (List.length (path np) mod 2) then other_elem (last np)
  else last np.

Fixpoint norm_combine el :=
  match el with
  | E t₁ d₁ :: el₁ =>
      let np := norm_combine el₁ in
      let pa := path np in
      match pa with
      | (d, n) :: p =>
          let t₂ := path_start np in
          if letter_dec t₁ t₂ then
            if Bool.bool_dec d₁ d then
              mknp (last np) ((d, S n) :: p)
            else
              match n with
              | O => mknp (last np) p
              | S n' => mknp (last np) ((d₁, n') :: p)
              end
          else
            mknp (last np) ((d₁, 0) :: pa)
      | [] =>
          mknp t₁ [(d₁, 0)]
      end
  | [] => mknp la []
  end.

Compute norm_combine [ạ⁻¹; ḅ⁻¹; ạ; ḅ⁻¹; ạ⁻¹; ạ; ḅ; ḅ; ḅ].

Inspect 8.

Fixpoint rotate_step pt e n :=
  match n with
  | O => pt
  | S n' => rotate (rotate_step pt e n') e
  end.

Fixpoint rotate_norm2_loop t path pt :=
  match path with
  | (d, n) :: pa =>
      let pt := rotate_step pt (E t d) n in
      rotate_norm2_loop (other_elem t) pa pt
  | [] => pt
  end.

Definition rotate_norm2 nc := rotate_norm2_loop (path_start nc) (path nc).

Theorem rotate_rotate_inv : ∀ pt e₁ e₂,
  letter_opp e₁ e₂ → rotate (rotate pt e₁) e₂ = pt.
Proof.
intros pt (t₁, d) (t, d₂) Hopp.
apply letter_opp_iff in Hopp.
destruct Hopp; subst; simpl.
destruct pt as (x, y, z).
destruct t, d; simpl.
 unfold mat_vec_mul; simpl; f_equal; [ field | | ].
  field_simplify; rewrite <- Rsqr_pow2, Rsqr_sqrt; lra.

  field_simplify; rewrite <- Rsqr_pow2, Rsqr_sqrt; lra.

 unfold mat_vec_mul; simpl; f_equal; [ field | | ].
  field_simplify; rewrite <- Rsqr_pow2, Rsqr_sqrt; lra.

  field_simplify; rewrite <- Rsqr_pow2, Rsqr_sqrt; lra.

 unfold mat_vec_mul; simpl; f_equal; [ | | field ].
  field_simplify; rewrite <- Rsqr_pow2, Rsqr_sqrt; lra.

  field_simplify; rewrite <- Rsqr_pow2, Rsqr_sqrt; lra.

 unfold mat_vec_mul; simpl; f_equal; [ | | field ].
  field_simplify; rewrite <- Rsqr_pow2, Rsqr_sqrt; lra.

  field_simplify; rewrite <- Rsqr_pow2, Rsqr_sqrt; lra.
Qed.

Theorem rotate_rotate_norm : ∀ pt el,
  fold_left rotate el pt = fold_left rotate (norm_list el) pt.
Proof.
intros.
revert pt.
induction el as [| e]; intros; [ reflexivity | simpl ].
rewrite IHel.
remember (norm_list el) as el₁ eqn:Hel; symmetry in Hel.
destruct el₁ as [| e₁]; [ reflexivity | simpl ].
destruct (letter_opp_dec e e₁) as [H₁| H₁]; [ | reflexivity ].
rewrite rotate_rotate_inv; [ reflexivity | assumption ].
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

Theorem norm_list_cancel_start : ∀ el t d,
  norm_list (E t d :: E t (negb d) :: el) = norm_list el.
Proof.
intros el t d.
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

Theorem toto : ∀ el pt,
  rotate_norm2 (norm_combine el) pt = fold_left rotate (norm_list el) pt.
Proof.
intros el pt.
unfold rotate_norm2.
remember (norm_combine el) as pa eqn:Hpa.
symmetry in Hpa.
destruct pa as (t, bnl).
revert el pt t Hpa.
induction bnl as [| (d, n)]; intros.
 simpl.
 destruct el as [| e]; [ reflexivity | ].
 simpl; simpl in Hpa.
  destruct e as (t₁, d₁).
  remember (path (norm_combine el)) as pa eqn:Hpa₂.
  symmetry in Hpa₂.
  destruct pa as [| (d, n) pa]; [ discriminate Hpa | ].
  unfold path_start in Hpa.
  rewrite Hpa₂ in Hpa.
  simpl in Hpa.
  destruct (zerop (S (length pa) mod 2)) as [H₁| H₁].
   remember (last (norm_combine el)) as lst eqn:Hlst.
   destruct (letter_dec t₁ (other_elem lst)) as [H₂| H₂].
    destruct (Bool.bool_dec d₁ d) as [H₃| H₃]; [ discriminate Hpa | ].
    destruct n; [ injection Hpa; intros; subst; discriminate H₁ | ].
    discriminate Hpa.

    discriminate Hpa.

   remember (last (norm_combine el)) as lst eqn:Hlst.
   destruct (letter_dec t₁ lst) as [H₂| H₂].
    destruct (Bool.bool_dec d₁ d) as [H₃| H₃]; [ discriminate Hpa | ].
    destruct n.
     injection Hpa; clear Hpa; intros; subst.
     remember (norm_list el) as el₁ eqn:Hel.
     symmetry in Hel.
     destruct el₁ as [| e₁].
      simpl.
Theorem toto : ∀ el,
  norm_list el = []
  → path (norm_combine el) = [].
Proof.
intros el Hel.

Theorem toto : ∀ el,
  norm_list el = []
  → el = [] ∨
    ∃ el₁ el₂ t d, el = el₁ ++ E t d :: E t (negb d) :: el₂
    ∧ norm_list (el₁ ++ el₂) = [].
Proof.
intros el Hel.
remember (split_at_cancel el) as sc eqn:Hsc.
symmetry in Hsc.
destruct el as [| e]; [ left; reflexivity | right ].
destruct sc as [((el₁, (t, d)), el₂) |].
 exists el₁, el₂, t, d.
 revert Hel Hsc; clear; intros; move el₂ before el₁.
(*
 revert e el el₁ t d Hel Hsc.
 induction el₂ as [| e₁]; intros.
  simpl in Hsc.
  destruct el as [| e₂]; [ discriminate Hsc | ].
  destruct (letter_opp_dec e e₂) as [H₁| H₁].
   injection Hsc; clear Hsc; intros; subst el₁ e el.
   simpl; split; [ f_equal; f_equal | reflexivity ].
   destruct e₂ as (t₁, d₁).
   apply letter_opp_iff in H₁.
   destruct H₁; subst t₁ d₁; reflexivity.

   exfalso; clear H₁.
   revert e e₂ el₁ t d Hel Hsc.
   induction el as [| e₁]; intros; [ discriminate Hsc | simpl in Hsc ].
   destruct (letter_opp_dec e₂ e₁) as [H₂| H₂].
    injection Hsc; clear Hsc; intros; subst el₁ e₂ el.
    destruct e₁ as (t₁, d₁).
    apply letter_opp_iff in H₂.
    destruct H₂; subst t₁ d₁.
    simpl in Hel; rewrite letter_dec_diag, bool_dec_negb_r in Hel.
    discriminate Hel.

    simpl in Hsc.
    destruct el as [| e₃]; [ discriminate Hsc | ].
    destruct (letter_opp_dec e₁ e₃) as [H₃| H₃].
     injection Hsc; clear Hsc; intros; subst el₁ e₁ el.
     destruct e₃ as (t₁, d₁).
     apply letter_opp_iff in H₃.
     destruct H₃; subst t₁ d₁.
*)
(*
 revert e el el₂ t d Hel Hsc.
 induction el₁ as [| e₁]; intros.
  simpl in Hsc, Hel; simpl.
  destruct el as [| e₁]; [ discriminate Hel | ].
  destruct (letter_opp_dec e e₁) as [H₁| H₁].
   injection Hsc; clear Hsc; intros; subst e el₂.
   destruct e₁ as (t₁, d₁).
   apply letter_opp_iff in H₁.
   destruct H₁; subst t₁ d₁.
   split; [ reflexivity | simpl in Hel ].
   remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
   destruct el₁ as [| (t₁, d₁)]; [ reflexivity | exfalso ].
   destruct (letter_dec t t₁) as [H₁| H₁].
    subst t₁.
    destruct (Bool.bool_dec (negb d) d₁) as [H₁| H₁].
     subst d₁.
     rewrite letter_dec_diag, bool_dec_negb_r in Hel.
     discriminate Hel.

     apply negb_neq in H₁; subst d₁.
     destruct el₁ as [| (t₂, d₂)]; [ discriminate Hel | ].
     destruct (letter_dec t t₂) as [H₂| H₂]; [ | discriminate Hel ].
     subst t₂.
     destruct (Bool.bool_dec d d₂) as [H₂| H₂]; [ discriminate Hel | ].
     apply not_eq_sym, neq_negb in H₂; subst d₂.
     revert Hel₁; apply norm_list_impossible_start.

    rewrite letter_dec_diag, bool_dec_negb_r in Hel.
    discriminate Hel.

   set (u := split_at_cancel (e₁ :: el)) in Hsc.
   destruct u as [((el₃, e₂), el₄)| ]; discriminate Hsc.

  simpl in Hsc.
  destruct el as [| e₂]; [ discriminate Hsc | ].
  destruct (letter_opp_dec e e₂) as [H₁| H₁]; [ discriminate Hsc | ].
  simpl in Hsc.
  destruct el as [| e₃]; [ discriminate Hsc | ].
  destruct (letter_opp_dec e₂ e₃) as [H₂| H₂].
   injection Hsc; clear Hsc; intros; subst e₁ el₁ e₂ el₂.
   destruct e₃ as (t₃, d₃).
   apply letter_opp_iff in H₂.
   destruct H₂; subst t₃ d₃.
   remember (E t d :: E t (negb d) :: el) as el₁.
   simpl in Hel; subst el₁.
   rewrite norm_list_cancel_start in Hel.
   split; [ reflexivity | assumption ].
*)
 destruct el as [| e₁]; [ discriminate Hsc | ].
 remember (e₁ :: el) as el'; simpl in Hsc; subst el'.
 destruct (letter_opp_dec e e₁) as [H₁| H₁].
  injection Hsc; clear Hsc; intros; subst.
  destruct e₁ as (t₁, d₁).
  apply letter_opp_iff in H₁.
  destruct H₁; subst t₁ d₁.
  rewrite norm_list_cancel_start in Hel.
  split; [ reflexivity | assumption ].

(**)
  remember (split_at_cancel (e₁ :: el)) as s eqn:Hs.
  symmetry in Hs.
  destruct s as [((el₃, e₃), el₄) | ]; [ | discriminate Hsc ].
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
  induction el as [| e]; intros; [ discriminate Hs | ].
  simpl in Hs.
  destruct el as [| e₁]; [ discriminate Hs | ].
  destruct (letter_opp_dec e e₁) as [H₁| H₁].
   injection Hs; clear Hs; intros; subst el e el₃.
   destruct e₁ as (t₁, d₁).
   apply letter_opp_iff in H₁.
   destruct H₁; subst t₁ d₁.
   rewrite app_nil_r.
   split; [ reflexivity | ].
   rewrite norm_list_cancel_inside in Hel; assumption.

   remember (split_at_cancel (e₁ :: el)) as u eqn:Hu; symmetry in Hu.
   destruct u as [((el₁, e₂), el₄)| ]; [ | discriminate Hs ].
   injection Hs; clear Hs; intros; subst el₃ e₂ el₂.
   rewrite cons_comm_app, app_assoc in Hel.
   pose proof IHel (el₀ ++ [e]) _ _ _ _ (eq_refl _) Hel as H.
   destruct H as (H₂, H₃).
   do 2 rewrite <- app_assoc in H₃.
   do 4 rewrite cons_comm_app.
   split; [ | rewrite <- app_assoc, <- app_assoc; assumption ].
   rewrite <- app_assoc in H₂.
   simpl in H₂; simpl; rewrite H₂.
   do 3 rewrite <- app_assoc; reflexivity.

 exfalso.
Theorem toto : ∀ e el,
  norm_list (e :: el) = []
  → split_at_cancel (e :: el) ≠ None.
Proof.
intros e el Hel Hsc.
revert e Hel Hsc.
induction el as [| e₁]; intros.
 rewrite norm_list_single in Hel; discriminate Hel.

 remember (e₁ :: el) as el'; simpl in Hel, Hsc; subst el'.
 destruct (letter_opp_dec e e₁) as [H₁| H₁]; [ discriminate Hsc | ].
 remember (norm_list (e₁ :: el)) as el₁ eqn:Hel₁.
 symmetry in Hel₁.
 destruct el₁ as [| e₂]; [ discriminate Hel | ].
 destruct (letter_opp_dec e e₂) as [H₂| H₂]; [ | discriminate Hel ].
 subst el₁.
 destruct e as (t₁, d₁).
 destruct e₂ as (t₂, d₂).
 apply letter_opp_iff in H₂.
 destruct H₂; subst t₂ d₂.
 simpl in Hel₁.
 remember (norm_list el) as el₁ eqn:Hel₂.
 symmetry in Hel₂.
 destruct el₁ as [| e₂].
  injection Hel₁; clear Hel₁; intros; subst e₁.
  apply H₁, letter_opp_iff; split; reflexivity.

  destruct (letter_opp_dec e₁ e₂) as [H₂| H₂].
   subst el₁.
   destruct e₁ as (t₂, d₂).
   destruct e₂ as (t₃, d₃).
   apply letter_opp_iff in H₂.
   destruct H₂; subst t₃ d₃.

bbb.


 simpl in Hel, Hsc.
 destruct el as [| e₁]; [ discriminate Hel | ].
 destruct (letter_opp_dec e e₁) as [H₁| H₁]; [ discriminate Hsc | ].
 remember (split_at_cancel (e₁ :: el)) as u eqn:Hu; symmetry in Hu.
 destruct u as [((el₁, e₂), el₂) | ]; [ discriminate Hsc | clear Hsc ].
 simpl in Hel.
 remember (norm_list el) as el₁ eqn:Hel₁.
 symmetry in Hel₁.
 destruct el₁ as [| e₂].
Focus 2.

bbb.


   induction el₀ as [| e].
    rewrite app_nil_l, norm_list_cancel_start in Hel; assumption.

    simpl.
    simpl in Hel.

bbb.
(**)
  destruct el as [| e₂]; [ discriminate Hsc | ].
  simpl in Hsc.
  destruct (letter_opp_dec e₁ e₂) as [H₂| H₂].
   injection Hsc; clear Hsc; intros; subst.
   destruct e₂ as (t₁, d₁).
   apply letter_opp_iff in H₂.
   destruct H₂; subst t₁ d₁.
   remember (E t d :: E t (negb d) :: el₂) as el₃ eqn:Hel₃.
   simpl in Hel; subst el₃.
   rewrite norm_list_cancel_start in Hel.
   split; [ reflexivity | assumption ].

   destruct el as [| e₃]; [ discriminate Hsc | simpl in Hsc ].
   destruct (letter_opp_dec e₂ e₃) as [H₃| H₃].
    injection Hsc; clear Hsc; intros; subst.
    destruct e₃ as (t₁, d₁).
    apply letter_opp_iff in H₃.
    destruct H₃; subst t₁ d₁.
    remember (E t d :: E t (negb d) :: el₂) as el₃ eqn:Hel₃.
    simpl in Hel; subst el₃.
    rewrite norm_list_cancel_start in Hel.
    split; [ reflexivity | assumption ].

bbb.

Theorem toto : ∀ el,
  norm_list el = []
  → el = [] ∨
    (∃ t d el₁, norm_list el₁ = [] ∧ el = E t d :: el₁ ++ [E t (negb d)]) ∨
    (∃ el₁ el₂,
     el₁ ≠ [] ∧ el₂ ≠ [] ∧ norm_list el₁ = [] ∧ norm_list el₂ = [] ∧
     el = el₁ ++ el₂).
Proof.
intros el Hel.
destruct el as [| e]; [ left; reflexivity | right ].
simpl in Hel.
remember (norm_list el) as el₁ eqn:Hel₁.
symmetry in Hel₁.
destruct el₁ as [| e₁]; [ discriminate Hel | ].
destruct (letter_opp_dec e e₁) as [H₁| H₁].
 subst el₁.
 destruct e as (t, d).
 destruct e₁ as (t₁, d₁).
 apply letter_opp_iff in H₁.
 destruct H₁; subst t₁ d₁.
bbb.

 remember (List.rev el) as rel eqn:Hrel.
 symmetry in Hrel.
 destruct rel as [| (t₁, d₁)].
  apply rev_is_nil in Hrel; subst el; discriminate Hel₁.

  rewrite <- rev_involutive in Hrel.
  apply rev_rev in Hrel; simpl in Hrel.
  subst el.
  remember (rev rel) as el eqn:Hel.
  clear rel Hel.
  destruct (letter_dec t₁ t) as [H₁| H₁].
   subst t₁.
   destruct (Bool.bool_dec d₁ d) as [H₂| H₂].
    subst d₁.

bbb.
  simpl in H; clear IHl₁.
  revert x H.
  induction l₁ as [| y]; intros; [ discriminate H | ].
  simpl in H.


  destruct (letter_dec t t₁) as [H₁| H₁].
   subst t₁.
   destruct (Bool.bool_dec d d₁) as [H₁| H₁].
    subst d₁; right.
bbb.

destruct el as [| e]; [ reflexivity | ].
simpl in Hel; simpl.
bbb.

induction el as [| e]; [ reflexivity | ].
simpl in Hel; simpl.
remember (norm_list el) as el₁ eqn:Hel₁.
symmetry in Hel₁.
destruct el₁ as [| e₁]; [ discriminate Hel | ].
clear IHel.
destruct (letter_opp_dec e e₁) as [H₁| H₁].
 subst el₁.
 destruct e as (t, d).
 remember (path (norm_combine el)) as pa eqn:Hpa.
 symmetry in Hpa.
 destruct pa as [| (d₁, n₁)].
destruct e as (t, d).
bbb.


  remember (path_start (norm_combine el)) as ps eqn:Hps.
  destruct (letter_dec t₁ ps) as [H₁| H₁].
   subst ps.
   destruct (Bool.bool_dec d₁ d) as [H₂| H₂]; [ discriminate Hpa | ].
   destruct n.
    injection Hpa; clear Hpa; intros; subst.
    remember (norm_list el) as el₁ eqn:Hel.
    symmetry in Hel.
    destruct el₁ as [| e₁].
     simpl.
     remember (path_start (norm_combine el)) as ps eqn:Hps.
     symmetry in Hps.
     destruct ps.
      destruct d₁.
      remember (norm_combine el) as el₁ eqn:Hel₁.
      symmetry in Hel₁.
      unfold path_start in Hps.

bbb.

Theorem toto : ∀ el pt,
  rotate_norm2 (norm_combine el) pt = fold_left rotate el pt.
Proof.
intros el pt.
unfold rotate_norm2.
remember (norm_combine el) as pa eqn:Hpa.
symmetry in Hpa.
destruct pa as (t, bnl).
revert el pt t Hpa.
induction bnl as [| (d, n)]; intros.
 simpl.
 destruct el as [| e]; [ reflexivity | ].
 exfalso; revert Hpa; clear; intros.
 revert e t Hpa.
 induction el as [| e₁]; intros; [ destruct e; discriminate Hpa | ].

bbb.

Theorem toto : ∀ el, norm_combine el = norm_combine (norm_list el).
Proof.
intros el.

induction el as [| (t, d)]; [ reflexivity | simpl ].
rewrite IHel.
remember (norm_list el) as el₁ eqn:Hel.
symmetry in Hel.
clear IHel.
revert t d el Hel.
induction el₁ as [| e₁]; intros; [ reflexivity | ].
simpl.

bbb.

Fixpoint rotate_norm2_mod_3_loop e path p :=
  match path with
  | (d, n) :: pa =>
      let '(a, b, c) := p in
      let p' :=
        match E e d with
        | ạ⁻¹ =>
            if zerop (n mod 2) then (0%Z, (- b - c)%Z, (- b - c)%Z)
            else (0%Z, (b + c)%Z, (b + c)%Z)
        | ạ =>
            if zerop (n mod 2) then (0%Z, (c - b)%Z, (b - c)%Z)
            else (0%Z, (b - c)%Z, (c - b)%Z)
        | ḅ⁻¹ =>
            if zerop (n mod 2) then ((b - a)%Z, (a - b)%Z, 0%Z)
            else ((a - b)%Z, (b - a)%Z, 0%Z)
        | ḅ =>
            if zerop (n mod 2) then ((- a - b)%Z, (- a - b)%Z, 0%Z)
            else ((a + b)%Z, (a + b)%Z, 0%Z)
        end
      in
      rotate_norm2_mod_3_loop (other_elem e) pa p'
  | [] => p
  end.

Definition rotate_norm2_mod_3 nc :=
  rotate_norm2_mod_3_loop (path_start nc) (path nc).

Theorem toto : ∀ el p,
  fold_left rotate_param_mod_3 (norm_list el) p =
  rotate_norm2_mod_3 (norm_combine el) p.
Proof.
intros el p.
remember (rotate_norm2_mod_3 (norm_combine el) p) as u eqn:Hu.
symmetry in Hu.
destruct u as ((a, b), c).
Inspect 10.
pose proof rotate_param_app (norm_list el).
remember (fold_left rotate_param (norm_list el)) as u eqn:Hv.
unfold "≡₃" in H.
SearchAbout rotate_param_mod_3.
bbb.

unfold rotate_norm2_mod_3.
revert p.
induction el as [| e]; intros; [ reflexivity | ].
simpl.

bbb.

Theorem toto : ∀ el p a b c N a' b' c' N',
  fold_left rotate_param el p = (a, b, c, N)
  → fold_left rotate_param (norm_list el) p = (a', b', c', N')
  → a = (a' * 3 ^ Z.of_nat (N - N'))%Z.
Proof.
intros el p a b c N a' b' c' N' Hr Hr'.
destruct p as (((x, y), z), n).
apply rotate_param_keep_dist in Hr.
apply rotate_param_keep_dist in Hr'.
Theorem glop : ∀ a b c, a = b → (a * c)%Z = (b * c)%Z.
Proof. intros; subst; reflexivity. Qed.
Show.
apply glop with (c := (3 ^ Z.of_nat (2 * N'))%Z) in Hr.
apply glop with (c := (3 ^ Z.of_nat (2 * N))%Z) in Hr'.
symmetry in Hr'.
rewrite Z.mul_shuffle0 in Hr'.
rewrite Hr' in Hr.
rewrite Z.mul_shuffle0 in Hr; symmetry in Hr.
rewrite Z.mul_shuffle0 in Hr; symmetry in Hr.
apply Z.mul_reg_r in Hr.

bbb.

Print rotate_param.

Definition rotate_param_by_group '(a b c N) (e, n) :=
ah, fait chier...

Theorem toto : ∀ el el₁ a b c,
  norm_list el = el₁ ++ [ḅ]
  → fold_left rotate_param (norm_list el) (1%Z, 0%Z, 0%Z, 0) = (a, b, c)
  → (b mod 3 ≠ 0)%Z.
Proof.
intros el el₁ a b c Hn Hr.
revert el₁ a b c Hn Hr.
induction el as [| e] using rev_ind; intros.
 symmetry in Hn; apply app_eq_nil in Hn.
 destruct Hn as (_, Hn); discriminate Hn.

bbb.

Theorem toto : ∀ el el₁ a b c,
  norm_list el = el₁ ++ [ḅ]
  → fold_left rotate_param_mod_3 (norm_list el) (1%Z, 0%Z, 0%Z) = (a, b, c)
  → b ≠ 0%Z.
Proof.
intros el el₁ a b c Hs Hr.
(**)
rewrite Hs in Hr.
rewrite fold_left_app in Hr; simpl in Hr.
remember (fold_left rotate_param_mod_3 el₁ (1, 0, 0)%Z) as r₁ eqn:Hr₁.
symmetry in Hr₁; destruct r₁ as ((a₁, b₁), c₁).
simpl in Hr.
injection Hr; clear Hr; intros; subst a b c.
revert a₁ b₁ c₁ Hr₁ el Hs.
induction el₁ as [| e₁] using rev_ind; intros.
 simpl in Hr₁.
 injection Hr₁; intros; subst; intros H; discriminate H.

 rewrite fold_left_app in Hr₁; simpl in Hr₁.
 simpl in Hr₁.
 destruct e₁ as (t₁, d₁).
 destruct t₁, d₁.
  remember (fold_left rotate_param_mod_3 el₁ (1, 0, 0)%Z) as r₂ eqn:Hr₂.
  symmetry in Hr₂; destruct r₂ as ((a₂, b₂), c₂).
  simpl in Hr₁.
  injection Hr₁; clear Hr₁; intros; subst.
  rewrite Z.add_0_l, Z.mod_mod; [ | intros H; discriminate H ].

Inspect 1.
bbb.
(**)
remember (norm_list el) as el₂ eqn:Hel.
symmetry in Hel.
revert el el₁ a b c Hel Hs Hr.
induction el₂ as [| e] using rev_ind; intros.
 symmetry in Hs; apply app_eq_nil in Hs.
 destruct Hs as (_, Hs); discriminate Hs.

 apply app_inj_tail in Hs.
 destruct Hs as (H₁, H₂); subst el₁ e.
 rewrite fold_left_app in Hr; simpl in Hr.
 remember (fold_left rotate_param_mod_3 el₂ (1%Z, 0%Z, 0%Z)) as r₁ eqn:Hr₁.
 symmetry in Hr₁; destruct r₁ as ((a₁, b₁), c₁).


bbb.
(**)
generalize Hr; intros H.
apply rotate_param_keep_dist in H.
do 2 rewrite Nat2Z.inj_mul in H; simpl in H.
rewrite Z.mul_1_r, Z.mul_1_l in H.
rewrite Z.pow_mul_r in H; [ | apply Zle_0_pos | apply Zle_0_nat ].
replace (3 ^ 2)%Z with 9%Z in H by reflexivity.
rename H into Hd.
(**)
rewrite Hs in Hr.
remember (1%Z, 0%Z, 0%Z, O) as p eqn:Hp.
remember (fold_left rotate_param el₁ p) as u eqn:Hu.
destruct u as (((a₁, b₁), c₁), N₁).
symmetry in Hu.
generalize Hu; intros H.
apply rotate_param_app_bn with (n := 0) in H.
simpl in H.
rewrite Hr in H; simpl in H.
destruct H as (Ha, (Hb, Hc)).
rewrite Z.mod_0_l in Hc; [| intros H; discriminate H ].
rewrite fold_left_app in Hr.
rewrite Hu in Hr; simpl in Hr.
injection Hr; clear Hr; intros; subst a b c N.
ring_simplify in Hd.
replace 18%Z with (9 * 2)%Z in Hd by reflexivity.
rewrite <- Z.mul_assoc in Hd.
do 2 rewrite <- Z.mul_add_distr_l in Hd.
rewrite <- Nat.add_1_r, Nat.add_comm in Hd.
rewrite Nat2Z.inj_add in Hd.
rewrite Z.pow_add_r in Hd.
replace (9 ^ Z.of_nat 1)%Z with 9%Z in Hd by reflexivity.
apply Z.mul_reg_l in Hd.
clear Ha Hb Hc.
revert el a₁ b₁ c₁ N₁ Hs Hd Hu.
induction el₁ as [| e₁]; intros.
 subst p; simpl in Hu.
 injection Hu; clear Hu; intros; subst a₁ b₁ c₁ N₁.
 intros H; discriminate H.

 simpl in Hu, Hs.
bbb.
 remember (fold_left rotate_param el₁ p) as v eqn:Hv.
 destruct v as (((a₂, b₂), c₂), N₂).
 symmetry in Hv.
 generalize Hv; intros H.
 apply rotate_param_app with (e := e₁) (n := 0) in H.
 simpl in H; rewrite Hu in H; simpl in H.
 destruct e₁ as (t₁, d₁).
 destruct t₁, d₁.
  destruct H as (Ha, (Hb, Hc)).
  rewrite Z.mod_0_l in Ha; [ | intros H; discriminate H ].
bbb.

generalize Hu; intros Hu2.
rewrite Hp in Hu2.
apply rotate_param_keep_dist in Hu2.
simpl in Hu2.
rewrite Z.mul_1_r, Z.mul_1_l, Nat.add_0_r in Hu2.
generalize Hv; intros Hv2.
rewrite Hp in Hv2.
apply rotate_param_keep_dist in Hv2.
simpl in Hv2.
rewrite Z.mul_1_r, Z.mul_1_l, Nat.add_0_r in Hv2.
intros H.
replace (-2 * a₁ + b₁)%Z with (b₁ - 2 * a₁)%Z in H by ring.
apply -> Z.sub_move_0_r in H; subst b₁.
apply Znumtheory.Zmod_divide in Ha; [ | intros H; discriminate H ].
destruct Ha as (k, Ha); subst a₁.
rewrite Z.mul_assoc in Hb.
rewrite Zdiv.Z_mod_mult in Hb.
rewrite <- Hb in Hc.

bbb.
(**)
revert el a b c N Hs Hr.
induction el₁ as [| e₁]; intros.
 rewrite Hs in Hr; simpl in Hr.
 injection Hr; intros; subst; intros; discriminate.

 simpl in Hs.
 destruct el as [| e]; [ discriminate Hs | ].
 simpl in Hs, Hr.
 remember (norm_list el) as el₂ eqn:Hel; symmetry in Hel.
 destruct el₂ as [| e₂].
  rewrite app_comm_cons in Hs.
  symmetry in Hs; apply app_eq_unit in Hs.
  destruct Hs as [(Hs, _)| (_, Hs)]; discriminate Hs.

  destruct (letter_opp_dec e e₂) as [He| He].
   subst el₂; simpl in Hr.
   destruct e₁ as (t₁, d₁).
   destruct t₁, d₁.
Check rotate_param_app_bn.
bbb.

(**)
revert el₁ a b c N Hs Hr.
induction el as [| e]; intros.
 symmetry in Hs; apply app_eq_nil in Hs.
 destruct Hs; discriminate.

 simpl in Hs, Hr.
 remember (norm_list el) as el₂ eqn:Hel; symmetry in Hel.
 destruct el₂ as [| e₂].
  simpl in Hr.
  destruct e as (t, d).
  destruct t.
   symmetry in Hs; apply app_eq_unit in Hs.
   destruct Hs as [(_, Hs)| (_, Hs)]; discriminate.

   destruct d; injection Hr; intros; subst; intros; discriminate.

  destruct (letter_opp_dec e e₂) as [He| He].
bbb.
(**)
induction el as [| e] using rev_ind; intros.
 symmetry in Hs; apply app_eq_nil in Hs.
 destruct Hs; discriminate.

 rewrite Hs in Hr.
 rewrite fold_left_app in Hr.
 simpl in Hr.

bbb.
 destruct e as (t, d).
 remember (1%Z, 0%Z, 0%Z, 0) as p eqn:Hp.
 destruct t, d.
  remember (fold_left rotate_param el p) as u eqn:Hu.
  symmetry in Hu.
  destruct u as (((a₁, b₁), c₁), N₁).
  pose proof rotate_param_app_a1n el 0 p _ _ _ _ Hu as H.
  simpl in H.
  unfold "≡₃" in H.
  rewrite Hr in H; simpl in H.
  destruct H as (Ha, (Hb, Hc)).
  rewrite Z.mod_0_l in Ha; [ | intros; discriminate ].
  destruct b₁, c₁.
   rewrite Z.add_0_l, Z.mod_0_l in Hb; [ | intros; discriminate ].
   rewrite Z.add_0_l, Z.mod_0_l in Hc; [ | intros; discriminate ].
   destruct el as [| e].
    simpl in Hr.
    unfold rotate_param in Hr.
    simpl in Hr; subst p.
    injection Hr; clear Hr; intros; subst a b c N.
    simpl in Hu.
    injection Hu; clear Hu; intros; subst a₁ N₁.
bbb.
  destruct a, b, c; try reflexivity.
bbb.

Theorem toto : ∀ s a b c N,
  ¬ empty s
  → rotate_1_0_0_param s = (a, b, c, N)
  → b ≠ 0%Z.
Proof.
intros s a b c N Hs Hr.
destruct s as (el).
unfold empty in Hs; simpl in Hs.
unfold rotate_1_0_0_param in Hr; simpl in Hr.
unfold rotate_1_0_0_param_of_list in Hr.
bbb.

remember (1%Z, 0%Z, 0%Z, 0) as p eqn:Hp.
revert a b c N Hr.
induction el as [| e] using rev_ind; intros.
 exfalso; apply Hs; reflexivity.

 destruct e as (t, d).
 destruct t, d.
  pose proof rotate_param_app_a1 el p as H.
  unfold "≡₃" in H.
  remember (fst3 (fold_left rotate_param (el ++ [ạ⁻¹]) p)) as u eqn:Hu.
  symmetry in Hu.
  destruct u as ((a₁, b₁), c₁).
  rewrite Hr in Hu.
  simpl in Hu.
  injection Hu; clear Hu; intros; subst a₁ b₁ c₁.
SearchAbout (fold_left _ (_ ++ _)).
  rewrite fold_left_app in Hr.
  simpl in Hr.
  remember (fold_left rotate_param el p) as u eqn:Hu.
  destruct u as (((a₁, b₁), c₁), N₁).
  simpl in Hr.
  injection Hr; clear Hr; intros; subst a b c N.
  pose proof H _ _ _ _ (eq_refl _) as H₁.
  destruct H₁ as (H₁, (H₂, H₃)).
bbb.

End Rotation.
