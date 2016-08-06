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

Theorem cons_to_app : ∀ A (x : A) l, x :: l = (x :: nil) ++ l.
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
Qed.

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
destruct (letter_dec x x) as [H| H]; [ clear H | apply H; reflexivity ].
destruct (Bool.bool_dec d (negb d)) as [H| H]; [ | constructor ].
destruct d; discriminate H.
Qed.

Theorem not_letter_opp_diag : ∀ x d, ¬ letter_opp (E x d) (E x d).
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

Arguments Z.mul x y : simpl nomatch.
(* to prevent 'simpl' to expand 2*a, 3*a, and so on, into matches *)

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
  | E la false => mat_vec_mul rot_x pt
  | E la true => mat_vec_mul rot_inv_x pt
  | E lb false => mat_vec_mul rot_z pt
  | E lb true => mat_vec_mul rot_inv_z pt
  end.

Definition map_rotate s pt := List.fold_left rotate (str s) pt.

Definition rotate_param '(a, b, c, N) e :=
  match e with
  | ạ => ((3 * a)%Z, (b + 2 * c)%Z, (- 4 * b + c)%Z, S N)
  | ạ⁻¹ => ((3 * a)%Z, (b - 2 * c)%Z, (4 * b + c)%Z, S N)
  | ḅ => ((a + 4 * b)%Z, (- 2 * a + b)%Z, (3 * c)%Z, S N)
  | ḅ⁻¹ => ((a - 4 * b)%Z, (2 * a + b)%Z, (3 * c)%Z, S N)
  end.

Definition rotate_1_0_0_param_of_list el :=
  fold_left rotate_param el (1%Z, 0%Z, 0%Z, 0).

Definition rotate_1_0_0_param s := rotate_1_0_0_param_of_list (str s).

Theorem map_1_0_0 : ∀ s a b c N,
  rotate_1_0_0_param s = (a, b, c, N)
  → map_rotate s (P 1 0 0) = P (IZR a/3^N) (IZR b*√2/3^N) (IZR c/3^N).
Proof.
intros (el) a₁ b₁ c₁ N₁ Hr.
unfold map_rotate; simpl.
unfold rotate_1_0_0_param in Hr; simpl in Hr.
unfold rotate_1_0_0_param_of_list in Hr.
revert a₁ b₁ c₁ N₁ Hr.
induction el as [| (t, d)] using rev_ind; intros.
 simpl; simpl in Hr; unfold map_rotate.
 injection Hr; intros; subst; simpl.
 f_equal; lra.

 rewrite fold_left_app in Hr; simpl in Hr.
 rewrite fold_left_app; simpl.
 remember (fold_left rotate_param el (1%Z, 0%Z, 0%Z, 0)) as rp eqn:Hrp.
 symmetry in Hrp.
 destruct rp as (((a, b), c), N).
 erewrite IHel; [ | reflexivity ].
 destruct t, d; simpl in Hr; simpl.
  injection Hr; clear Hr; intros; subst; simpl.
  unfold Rdiv.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rmult_0_l.
  repeat rewrite Rplus_0_l.
  repeat rewrite Rplus_0_r.
  repeat rewrite <- Rmult_assoc.
  rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
  rewrite plus_IZR, minus_IZR.
  repeat rewrite mult_IZR.
  rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

  injection Hr; clear Hr; intros; subst; simpl.
  unfold Rdiv.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rmult_0_l.
  repeat rewrite Rplus_0_l.
  repeat rewrite Rplus_0_r.
  repeat rewrite <- Rmult_assoc.
  rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
  do 2 rewrite plus_IZR.
  repeat rewrite mult_IZR.
  rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

  injection Hr; clear Hr; intros; subst; simpl.
  unfold Rdiv.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rmult_0_l.
  repeat rewrite Rplus_0_l.
  repeat rewrite Rplus_0_r.
  repeat rewrite <- Rmult_assoc.
  rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
  rewrite plus_IZR, minus_IZR.
  repeat rewrite mult_IZR.
  rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].

  injection Hr; clear Hr; intros; subst; simpl.
  unfold Rdiv.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rmult_0_l.
  repeat rewrite Rplus_0_l.
  repeat rewrite Rplus_0_r.
  repeat rewrite <- Rmult_assoc.
  rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
  do 2 rewrite plus_IZR.
  repeat rewrite mult_IZR.
  rewrite Rinv_mult_distr; [ f_equal; lra | lra | apply pow_nonzero; lra ].
Qed.

Theorem ex_map_1_0_0 : ∀ s,
  ∃ (a b c : ℤ) (N : ℕ),
  map_rotate s (P 1 0 0) = P (IZR a/3^N) (IZR b*√2/3^N) (IZR c/3^N).
Proof.
intros s.
remember (rotate_1_0_0_param s) as rp eqn:Hrp; symmetry in Hrp.
destruct rp as (((a, b), c), N).
erewrite map_1_0_0; [ | eassumption ].
exists a, b, c, N; reflexivity.
Qed.

Check map_1_0_0.

Theorem toto : ∀ s a b c N,
  s ≠ ∅
  → List.Forall (λ e, e = ḅ) (str (norm s))
  → rotate_1_0_0_param s = (a, b, c, N)
  → (b mod 3 = Z.of_nat N mod 2 + 1)%Z.
Proof.
intros s a b c N Hs Ha Hrp.
unfold empty in Hs; simpl in Hs.
unfold rotate_1_0_0_param in Hrp.
unfold rotate_1_0_0_param_of_list in Hrp.
unfold norm in Ha; simpl in Ha.
remember (str s) as el eqn:Hel.
clear s Hel.
remember (norm_list el) as el₁ eqn:Hel.
symmetry in Hel.
revert a b c N el Hel Hrp.
induction el₁ as [| e]; intros; [ exfalso; apply Hs; reflexivity | ].
clear Hs.
pose proof Forall_inv Ha as H; simpl in H; subst e.
destruct el₁ as [| e].

Theorem toto : ∀ el e, norm_list el = [e] → el = [e].
Proof.
intros el e Hel.
(* ah bin non, c'est faux : contre-exemple el = [e; e⁻¹; e] *)
bbb.

revert e Hel.
induction el as [| e₁]; intros; [ discriminate Hel | ].
simpl in Hel.
remember (norm_list el) as el₁ eqn:Hel₁.
symmetry in Hel₁.
destruct el₁ as [| e₂].
 injection Hel; clear Hel; intros; subst e₁; f_equal.
 clear e.
 destruct el as [| e]; [ reflexivity | ].
 simpl in Hel₁.
 remember (norm_list el) as el₁ eqn:Hel; symmetry in Hel.
 destruct el₁ as [| e₁]; [ discriminate Hel₁ | ].
 destruct (letter_opp_dec e e₁) as [H₁| H₁].
  subst el₁.
bbb.

Theorem toto : ∀ s el x y z,
  norm s = mkF₂ (ḅ :: el)
  → map_rotate (norm s) (P 1 0 0) = P x y z
  → y ≠ 0%R.
Proof.
intros s el x y z Hs Hmr.
remember (rotate_1_0_0_param (norm s)) as rp eqn:Hrp.
symmetry in Hrp.
destruct rp as (((a, b), c), N).
pose proof map_1_0_0 _ _ _ _ _ Hrp as H.
rewrite Hmr in H.
injection H; clear H; intros H₁ H₂ H₃; subst.
rewrite Hs in Hmr; simpl in Hmr.
unfold map_rotate in Hmr; simpl in Hmr.
rewrite Hs in Hrp; simpl in Hrp.
unfold rotate_1_0_0_param in Hrp; simpl in Hrp.
unfold rotate_1_0_0_param_of_list in Hrp; simpl in Hrp.
unfold Rdiv in Hmr.
progress repeat rewrite Rmult_1_l in Hmr.
progress repeat rewrite Rmult_1_r in Hmr.
progress repeat rewrite Rmult_0_r in Hmr.
progress repeat rewrite Rplus_0_r in Hmr.
intros H.
unfold Rdiv in H.
apply Rmult_integral in H.
destruct H as [H| H].
 2: revert H; apply Rinv_neq_0_compat, pow_nonzero; lra.

 apply Rmult_integral in H.
 destruct H as [H| H]; [ | revert H; apply sqrt2_neq_0 ].
 revert H; apply not_0_IZR.
 revert s a b c N Hs Hmr Hrp.
 induction el as [| e]; intros.
  injection Hrp; clear Hrp; intros; subst.
  intros H; discriminate H.

  simpl in Hrp.
  simpl in Hmr.
bbb.

unfold norm in Hs, Hmr.
injection Hs; clear Hs; intros Hs.
rewrite Hs in Hmr.
unfold map_rotate in Hmr; simpl in Hmr.
unfold Rdiv in Hmr.
repeat rewrite Rmult_1_l in Hmr.
repeat rewrite Rmult_1_r in Hmr.
repeat rewrite Rmult_0_r in Hmr.
repeat rewrite Rplus_0_r in Hmr.
revert s x y z Hs Hmr.
induction el as [| e]; intros.
 injection Hmr; clear Hmr; intros H₁ H₂ H₃ H; subst.
 apply Rmult_integral in H.
 destruct H as [H| H]; [ | lra ].
 apply Rmult_integral in H.
 destruct H as [H| H]; [ lra | ].
 revert H; apply sqrt2_neq_0.

 simpl in Hmr.
bbb.

Theorem toto : ∀ s el,
  norm s = mkF₂ (ḅ :: el)
  → ¬ map_rotate (norm s) (P 1 0 0) = P 1 0 0.
Proof.
intros s el Hs Hmr.
rewrite Hs in Hmr.
unfold norm in Hs; simpl in Hs.
injection Hs; clear Hs; intros Hs.
unfold map_rotate in Hmr; simpl in Hmr.
unfold Rdiv in Hmr.
repeat rewrite Rmult_1_l in Hmr.
repeat rewrite Rmult_1_r in Hmr.
repeat rewrite Rmult_0_r in Hmr.
repeat rewrite Rplus_0_r in Hmr.
revert s Hs.
induction el as [| e]; intros; simpl in Hmr.
  injection Hmr; lra.

bbb.
destruct e as (t, d); destruct t, d; simpl in Hmr.
 unfold Rdiv in Hmr.
 repeat rewrite Rmult_1_l in Hmr.
 repeat rewrite Rmult_0_l in Hmr.
 repeat rewrite Rmult_0_r in Hmr.
 repeat rewrite Rplus_0_l in Hmr.
 repeat rewrite Rplus_0_r in Hmr.
 rewrite fold_left_app in Hmr.
 simpl in Hmr.
 remember (fold_left rotate el (P (/ 3) (-2 * √ 2 * / 3) 0)) as u eqn:Hu.
 symmetry in Hu.
 destruct u as (x, y, z).
 simpl in Hmr.
 repeat rewrite Rmult_1_l in Hmr.
 repeat rewrite Rmult_0_l in Hmr.
 repeat rewrite Rplus_0_l in Hmr.
 repeat rewrite Rplus_0_r in Hmr.
  injection Hmr; clear Hmr; intros H₁ H₂ H₃; subst x.

bbb.


revert s Hs.
induction el as [| e] using rev_ind; intros.
 injection Hmr; clear Hmr; intros; lra.

bbb.

Theorem toto : ∀ s,
  map_rotate s (P 1 0 0) = P 1 0 0
  → s = ∅.
Proof.
intros s Hmr.
unfold empty.
unfold map_rotate in Hmr.
unfold norm; simpl.
remember (str s) as el; clear s Heqel.
induction el as [| e]; [ reflexivity | ].
simpl in Hmr; simpl.
remember (norm_list el) as el₁ eqn:Hel.
symmetry in Hel.
destruct el₁ as [| e₁].
 destruct e as (t, d).
 destruct t, d.
  simpl in Hmr.
bbb.

Theorem toto : ∀ el a b c N,
  rotate_1_0_0_param_of_list (el ++ [ḅ]) = (a, b, c, N)
  → b ≠ 0%Z.
Proof.
intros el a b c N Hr Hb.
destruct el as [| (t, d)]; [ subst b; discriminate | ].
simpl in Hr.
remember (rotate_1_0_0_param_of_list (el ++ [ḅ])) as rp eqn:Hrp.
symmetry in Hrp.
destruct rp as (((a₁, b₁), c₁), N₁).
destruct t, d.
 injection Hr; clear Hr; intros H₁ H₂ Hbc H₃; subst.
 apply -> Z.sub_move_0_r in Hbc.
 destruct el as [| (t, d)].
  simpl in Hrp; subst b₁.
  injection Hrp; clear Hrp; intros H₁ H₂ H H₄; subst.
  rewrite Z.mul_0_r in H; discriminate H.

  simpl in Hrp.
  remember (rotate_1_0_0_param_of_list (el ++ [ḅ])) as rp eqn:Hrp₁.
  symmetry in Hrp₁.
  destruct rp as (((a, b), c), N).
  destruct t, d.
   subst b₁.
   injection Hrp; clear Hrp; intros H₁ H₂ Hbc H₃; subst.
   apply -> Z.sub_move_r in Hbc.
   rewrite Z.mul_add_distr_l, <- Z.add_assoc, Z.add_diag in Hbc.
   do 2 rewrite Z.mul_assoc in Hbc; simpl in Hbc.
   symmetry in Hbc.
   apply Z.sub_move_0_r in Hbc.
   rewrite Z.add_sub_swap in Hbc.
   replace b with (1 * b)%Z in Hbc at 2 by apply Z.mul_1_l.
   rewrite <- Z.mul_sub_distr_r in Hbc; simpl in Hbc.
   revert a b c N Hrp₁ Hbc.
   induction el as [| (t, d)]; intros.
    simpl in Hrp₁.
    injection Hrp₁; clear Hrp₁; intros; subst a b c N.
    discriminate Hbc.

    simpl in Hrp₁.
    remember (rotate_1_0_0_param_of_list (el ++ [ḅ])) as rp eqn:Hrp.
    symmetry in Hrp.
    destruct rp as (((a₁, b₁), c₁), N₁).
    destruct t, d.
     injection Hrp₁; clear Hrp₁; intros; subst.
bbb.

intros el a b c N Hr Hb.
revert a b c N Hr Hb.
induction el as [| e]; intros; [ subst b; discriminate | ].
simpl in Hr.
remember (rotate_1_0_0_param_of_list (el ++ [ḅ])) as el₁ eqn:Hel.
symmetry in Hel.
destruct el₁ as (((a₁, b₁), c₁), N₁).
destruct e as (t, d).
destruct t, d.
 injection Hr; clear Hr; intros H₁ H₂ Hbc H₃; subst.
 eapply IHel; [ reflexivity | ].
 apply -> Z.sub_move_0_r in Hbc.
Print rotate_1_0_0_param_of_list.
bbb.

Theorem toto : ∀ s, s ≠ ∅ → map_rotate (norm s) (P 1 0 0) ≠ P 1 0 0.
Proof.
intros s Hs Hr; apply Hs; clear Hs.
destruct s as (el).
unfold norm in Hr; simpl in Hr.
unfold map_rotate in Hr; simpl in Hr.
unfold empty; simpl.
remember (norm_list el) as el₁ eqn:Hel; symmetry in Hel.
revert el Hel.
induction el₁ as [| e]; intros; [ reflexivity | ].
exfalso; simpl in Hr.
remember (fold_right rotate (P 1 0 0) el₁) as r₁ eqn:Hr₁.
symmetry in Hr₁.
destruct e as (t, d).
destruct t, d; simpl in Hr.
bbb.

Abort. (* à voir... *)

Theorem b_neq_0 : ∀ el a b c N,
  norm_list el ≠ []
  → rotate_1_0_0_param_of_list el = (a, b, c, N)
  → b ≠ 0%Z.
Proof.
intros el a b c N Hel Hr H; subst b.
apply Hel; clear Hel.
revert a c N Hr.
induction el as [| e]; intros; [ reflexivity | simpl in Hr; simpl ].
remember (norm_list el) as el₁ eqn:Hel.
symmetry in Hel.
destruct el₁ as [| e₁].
 clear IHel; exfalso.
 remember (rotate_1_0_0_param_of_list el) as rp eqn:Hrp.
 symmetry in Hrp.
 destruct rp as (((a₁, b₁), c₁), N₁).
 destruct e as (t, d).
 destruct t, d.
  injection Hr; clear Hr; intros H₁ H₂ H H₃; subst.
  apply -> Z.sub_move_0_r in H; subst b₁.
  revert a₁ c₁ N₁ Hrp.
  induction el as [| e]; intros.
   simpl in Hrp.
bbb. (* this theorem is false *)

revert a c N Hr.
induction el as [| e]; intros; [ discriminate Hr | simpl in Hr ].
remember (rotate_1_0_0_param_of_list (el ++ [ḅ])) as rp eqn:Hrp.
symmetry in Hrp.
destruct rp as (((a₁, b₁), c₁), N₁).
destruct e as (t, d).
destruct t, d.
 injection Hr; clear Hr; intros H₁ H₂ H₃ H₄; subst.
 apply -> Z.sub_move_0_r in H₃; subst b₁.
 destruct el as [| e].
  simpl in Hrp.
  injection Hrp; clear Hrp; intros H₁ H₂ H₃ H₄; subst.
  discriminate H₃.

  simpl in Hrp.
  revert Hrp; clear; intros.
  revert e a₁ c₁ N₁ Hrp.
  induction el as [| e₁]; intros.
   simpl in Hrp.
   destruct e as (t, d).
   destruct t, d.
    injection Hrp; clear Hrp; intros; subst; discriminate.
    injection Hrp; clear Hrp; intros; subst; discriminate.
    injection Hrp; clear Hrp; intros; subst.

bbb.

Definition map_rotate' s pt :=
  List.fold_left (λ pt e, rotate e pt) (str s) pt.

Theorem ex_map_1_0_0' : ∀ s,
  ∃ (a b c : ℤ) (N : ℕ),
  map_rotate' s (P 1 0 0) = P (IZR a/3^N) (IZR b*√2/3^N) (IZR c/3^N).
Proof.
intros (el).
induction el as [| (x, d)].
 unfold map_rotate'; simpl.
 exists 1%Z, 0%Z, 0%Z, 0; simpl.
 unfold Rdiv; rewrite Rinv_1.
 rewrite Rmult_1_l.
 do 2 rewrite Rmult_0_l.
 reflexivity.

 destruct IHel as (a, (b, (c, (N, IHel)))).
 unfold map_rotate' in IHel; simpl in IHel.
 unfold map_rotate'; simpl.
 unfold Rdiv.
 do 3 rewrite Rmult_1_l.
 do 2 rewrite Rmult_0_l.
 do 8 rewrite Rplus_0_r.
 do 3 rewrite Rplus_0_l.
 do 3 rewrite Rmult_0_r.
 do 4 rewrite Rplus_0_r.
 do 3 rewrite Rmult_1_r.
 destruct x, d.
  rewrite IHel; exists a, b, c, N; reflexivity.

  rewrite IHel; exists a, b, c, N; reflexivity.
Abort. (* to be completed, perhaps *)

(* they say... *)
Theorem toto : ∀ s a b c N,
  (a, b, c, N) = rotate_1_0_0_param (mkF₂ (str s ++ [ḅ]))
  → b ≠ 0%Z.
Proof.
intros (el) a b c N H.
unfold rotate_1_0_0_param in H.
simpl in H.
revert a b c N H.
induction el as [| e]; intros.
 simpl in H.
 injection H; intros; subst b.
 intros H₁; discriminate H₁.

 rewrite <- app_comm_cons in H; simpl in H.
 remember (rotate_1_0_0_param_of_list (el ++ [ḅ])) as rp eqn:Hrp.
 destruct rp as (((a₁, b₁), c₁), N₁).
 pose proof IHel _ _ _ _ (eq_refl _) as Hb.
 destruct e as (x, d).
 destruct x, d.
  injection H; clear H; intros; subst a b c N.
  intros H; apply Hb; clear Hb.

clear IHel.
revert a₁ b₁ c₁ N₁ Hrp H.
induction el as [| e]; intros.
 simpl in Hrp.
 injection Hrp; clear Hrp; intros; subst.
 discriminate H.

 simpl in Hrp.
 remember (rotate_1_0_0_param_of_list (el ++ [ḅ])) as rp₁ eqn:Hrp₁.
 destruct rp₁ as (((a₂, b₂), c₂), N₂).
 pose proof IHel _ _ _ _ (eq_refl _) as H₁.
 destruct e as (x, d).
 destruct x, d.
 injection Hrp; clear Hrp; intros; subst.

bbb.

Theorem toto : ∀ s a b c N,
  (a, b, c, N) = rotate_1_0_0_param (mkF₂ (ḅ :: str s))
  → b ≠ 0%Z.
Proof.
intros (el) a b c N H; simpl in H.
revert a b c N H.
induction el as [| e]; intros.
 unfold rotate_1_0_0_param in H; simpl in H.
 injection H; intros; subst b.
 intros H₁; discriminate H₁.

 unfold rotate_1_0_0_param in H.
 unfold rotate_1_0_0_param in IHel.
 remember rotate_1_0_0_param_of_list as f; simpl in IHel, H; subst f.
 remember (rotate_1_0_0_param_of_list el) as rp eqn:Hrp.
 destruct rp as (((a₁, b₁), c₁), N₁).
bbb.
 pose proof rotate_1_0_0_param_cons e el a₁ b₁ c₁ N₁ Hrp as H₁.
 remember 2%Z as two.
 remember 3%Z as three.
 remember 4%Z as four.
 remember (-2)%Z as mtwo.
 remember (-4)%Z as mfour.
 destruct e as (x, d).
 destruct x, d.
  symmetry in H₁.
  apply rotate_1_0_0_param_cons with (e := ḅ) in H₁.
  rewrite <- H in H₁.
  injection H₁; clear H₁; intros; subst b.
  subst two three; simpl.
  destruct a₁; simpl.
   destruct c₁; simpl.
    rewrite Z.sub_0_r.
    eapply IHel.
bbb.
  simpl in H₁.
  rewrite <- Hrp in H₁.
  injection H₁; clear H₁; intros H₁ H₂ H₃.


bbb.

End Rotation.
