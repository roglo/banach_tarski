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

Section Rotation.

Notation "s = '∅'" := (empty s) (at level 70).
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

Require Import Reals.

Notation "'ℝ'" := R.
Notation "'ℤ'" := Z.
Notation "'ℕ'" := nat.

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

Notation "'√'" := sqrt.

Definition rot_x := mkmat
  1 0 0
  0 (1/3) (-2*√2/3)
  0 (2*√2/3) (1/3).
Definition rot_inv_x := mkmat
  1 0 0
  0 (1/3) (2*√2/3)
  0 (-2*√2/3) (1/3).
Definition rot_z := mkmat
  (1/3) (-2*√2/3) 0
  (2*√2/3) (1/3) 0
  0 0 1.
Definition rot_inv_z := mkmat
  (1/3) (2*√2/3) 0
  (-2*√2/3) (1/3) 0
  0 0 1.

Definition rotate e pt :=
  match e with
  | E la false => mat_vec_mul rot_x pt
  | E la true => mat_vec_mul rot_inv_x pt
  | E lb false => mat_vec_mul rot_z pt
  | E lb true => mat_vec_mul rot_inv_z pt
  end.

Definition map_rotate s pt := List.fold_right rotate pt (str s).

Theorem map_1_0_0 : ∀ s,
  ∃ (a b c : ℤ) (N : ℕ),
  map_rotate s (P 1 0 0)
  = P (IZR a/3^N) (IZR b*√2/3^N) (IZR c/3^N).
Proof.
intros s.
destruct s as (el).
induction el as [| e].
 unfold map_rotate; simpl.
 exists 1%Z, 0%Z, 0%Z, 0; simpl.
 unfold Rdiv; rewrite Rinv_1.
 do 3 rewrite Rmult_1_r.
 rewrite Rmult_0_l; reflexivity.

 destruct IHel as (a, (b, (c, (N, H)))).
 unfold map_rotate; simpl.
 unfold map_rotate in H; simpl in H.
 rewrite H.
 destruct e as (x, d).
 destruct x.
Focus 2.
  destruct d.
   simpl.
   rewrite Rmult_1_l.
   do 3 rewrite Rmult_0_l.
   do 2 rewrite Rplus_0_r.
   do 2 rewrite Rplus_0_l.
   exists (a - 4 * b)%Z, (2 * a + b)%Z, (3 * c)%Z, (S N).
   f_equal.
    rewrite minus_IZR, mult_IZR; simpl.
    replace (-2 * √ 2 / 3 * (IZR b * √ 2 / 3 ^ N))%R with
    (-2 * 2 / 3 * (IZR b / 3 ^ N))%R.
     field; apply pow_nonzero.
     apply tech_Rplus; [ apply Rle_0_1 | apply Rlt_0_2 ].

     unfold Rdiv.
     do 2 rewrite <- Rmult_assoc; f_equal.
     do 4 rewrite Rmult_assoc; f_equal.
     do 3 rewrite <- Rmult_assoc.
     rewrite Rmult_shuffle0; symmetry.
     rewrite Rmult_assoc, Rmult_shuffle0.
     rewrite <- Rmult_assoc; f_equal.
     rewrite Rmult_shuffle0; f_equal.
     apply sqrt_sqrt, Rplus_le_le_0_compat; apply Rle_0_1.

    rewrite plus_IZR, mult_IZR; simpl.
    field; apply pow_nonzero.
    apply tech_Rplus; [ apply Rle_0_1 | apply Rlt_0_2 ].

    rewrite mult_IZR; simpl.
    field; apply pow_nonzero.
    apply tech_Rplus; [ apply Rle_0_1 | apply Rlt_0_2 ].

   simpl.
bbb.

End Rotation.
