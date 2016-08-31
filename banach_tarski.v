(* Banach-Tarski paradox. *)
(* Inspirations:
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)

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

Require Import Relations.

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

(* "we claim that w(1,0,0) has the form (a,b√2,c)/3^k where a,b,c are
    integers and b is not divisible by 3" *)

Theorem toto : ∀ w el el₁ d,
  w = fold_left rotate el
  → norm_list el = el
  → el = el₁ ++ [E lb d]
  → ∃ a b c k,
    w (P 1 0 0) = P (IZR a/3^k) (IZR b*√2/3^k) (IZR c/3^k) ∧
    (b mod 3 ≠ 0)%Z.
Proof.
intros w el el₁ d Hw Hn Hel.
(*
(* counter-example? *)
Compute fold_left rotate_param [ạ; ḅ] (1, 0, 0, O)%Z.
(*
     = (3%Z, 6%Z, 0%Z, 2)
     : ℤ * ℤ * ℤ * ℕ
*)
(* but perhaps we should count the division by 3^k ? *)
(* let's see with matrices... *)
remember (mat_vec_mul (fold_left mat_mul (rev (map rot_mat [ạ; ḅ])) mat_id) (P 1 0 0)) as u eqn:Hu.
simpl in Hu.
destruct u as (x, y, z).
injection Hu; clear Hu; intros Hz Hy Hx.
ring_simplify in Hx.
ring_simplify in Hy.
ring_simplify in Hz.
Check Hy.
(*
Hy
     : y = (2 * √ 2 / 3)%R
ok
*)
*)
subst w; rewrite rotate_by_mat_mul.
remember (fold_left mat_mul (rev (map rot_mat el)) mat_id) as w eqn:Hw.
revert w el₁ d Hw Hel.
induction el as [| e]; intros.
 symmetry in Hel; apply app_eq_nil in Hel; destruct Hel; discriminate.

 simpl in Hn.
 remember (norm_list el) as el₂ eqn:Hel₂.
 symmetry in Hel₂.
 destruct el₂ as [| e₂].
  injection Hn; clear Hn; intros; subst el.
  destruct el₁ as [| e₁]; [ | destruct el₁; discriminate Hel ].
  injection Hel; clear Hel; intros; subst e.
  subst w; simpl.
  progress repeat rewrite Rmult_1_l.
  progress repeat rewrite Rmult_1_r.
  progress repeat rewrite Rmult_0_l.
  progress repeat rewrite Rmult_0_r.
  progress repeat rewrite Rplus_0_l.
  progress repeat rewrite Rplus_0_r.
  unfold rot_inv_z, rot_z.
  destruct d; simpl.
   exists 1%Z, (-2)%Z, 0%Z, 1; simpl.
   progress repeat rewrite Rmult_1_r.
   split; [ f_equal; lra | intros H; discriminate H ].

   exists 1%Z, 2%Z, 0%Z, 1; simpl.
   progress repeat rewrite Rmult_1_r.
   split; [ f_equal; lra | intros H; discriminate H ].

  destruct (letter_opp_dec e e₂) as [H₁| H₁].
   destruct e as (t₁, d₁).
   destruct e₂ as (t₂, d₂).
   apply letter_opp_iff in H₁.
   destruct H₁; subst t₂ d₂; subst el₂.
   remember (negb d₁) as d₂.
   replace d₁ with (negb (negb d₁)) in Hel₂ by apply Bool.negb_involutive.
   subst d₂.
   exfalso; revert Hel₂; apply norm_list_impossible_start.

   injection Hn; clear Hn; intros; subst el.
   destruct el₁ as [| e₁]; [ discriminate Hel | simpl in Hel ].
   injection Hel; clear Hel; intros H1 H2; subst e₁.
   remember (e₂ :: el₂) as el₃ eqn:Hel₃.
   remember (fold_left mat_mul (rev (map rot_mat el₃)) mat_id) as w' eqn:Hw'.
   pose proof IHel (eq_refl _) w' el₁ d (eq_refl _) H1 as H.
   destruct H as (a', (b', (c', (k', (Hm, Hb))))).
simpl in Hm; simpl.
progress repeat rewrite Rmult_1_r in Hm.
progress repeat rewrite Rmult_0_r in Hm.
progress repeat rewrite Rplus_0_r in Hm.
progress repeat rewrite Rmult_1_r.
progress repeat rewrite Rmult_0_r.
progress repeat rewrite Rplus_0_r.
injection Hm; clear Hm; intros H2 H3 H4.
simpl in Hw.
rewrite fold_left_app, <- Hw' in Hw.
simpl in Hw; rewrite Hw; simpl.
rewrite H2, H3, H4.
destruct e as (t₁, d₁); destruct t₁, d₁; simpl.
 progress repeat rewrite Rmult_0_r.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite Rplus_0_r.
 exists a', b', c', k'.
 split; [ reflexivity | assumption ].

 progress repeat rewrite Rmult_0_r.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite Rplus_0_r.
 exists a', b', c', k'.
 split; [ reflexivity | assumption ].

 progress repeat rewrite Rmult_0_r.
 progress repeat rewrite Rplus_0_r.
 destruct e₂ as (t₂, d₂); destruct t₂, d₂; simpl.
  4: exfalso; apply H₁; constructor.

  subst w'; rewrite Hel₃; simpl; rewrite <- map_rev.
  rewrite fold_left_app; simpl.
  progress repeat rewrite Rmult_0_r, Rplus_0_l.
  rewrite Hel₃ in H2, H3, H4; simpl in H2, H3, H4.
  rewrite fold_left_app in H2, H3, H4; simpl in H2, H3, H4.
  progress repeat rewrite Rmult_0_r, Rplus_0_r, Rmult_1_r in H2, H3, H4.
  progress repeat rewrite Rmult_0_r, Rplus_0_r in H2, H3, H4.
  rewrite <- map_rev in H2, H3, H4.
  remember (fold_left mat_mul (map rot_mat (rev el₂)) mat_id) as m eqn:Hm.
bbb.
 replace (a₁₂ w') with 0%R.
Focus 2.
  subst w'; rewrite Hel₃; simpl; rewrite <- map_rev.
  rewrite fold_left_app; simpl.

bbb.

  rewrite rev_app_distr; simpl.
  destruct d.
   rewrite mat_mul_id_l.
   clear; induction el₁ as [| e₁].
    simpl.

  subst w'; rewrite H1; simpl; rewrite <- map_rev.
  rewrite rev_app_distr; simpl.
  destruct d.
   rewrite mat_mul_id_l.
   clear; induction el₁ as [| e₁].
    simpl.
bbb.
 subst el₃; rewrite Hw'.
 destruct e₂ as (t₂, d₂); destruct t₂, d₂; simpl.
  4: exfalso; apply H₁; constructor.

  rewrite fold_left_app; simpl.
  progress repeat rewrite Rmult_0_r.
  progress repeat rewrite Rplus_0_l.

bbb.

intros w el el₁ d Hw Hn Hel.
(* counter-example: *)
Compute fold_left rotate_param [ạ; ḅ] (1, 0, 0, O)%Z.
(* but perhaps we should count the division by 3^k ? *)
revert w el₁ d Hw Hel.
induction el as [| e]; intros.
 symmetry in Hel; apply app_eq_nil in Hel; destruct Hel; discriminate.

 simpl in Hn.
 remember (norm_list el) as el₂ eqn:Hel₂.
 symmetry in Hel₂.
 destruct el₂ as [| e₂].
  injection Hn; clear Hn; intros; subst el.
  destruct el₁ as [| e₁]; [ | destruct el₁; discriminate Hel ].
  injection Hel; clear Hel; intros; subst e.
  subst w; simpl.
  progress repeat rewrite Rmult_1_r.
  progress repeat rewrite Rmult_0_r.
  progress repeat rewrite Rplus_0_r.
  destruct d.
   exists 1%Z, (-2)%Z, 0%Z, 1; simpl.
   progress repeat rewrite Rmult_1_r.
   split; [ f_equal; lra | intros H; discriminate H ].

   exists 1%Z, 2%Z, 0%Z, 1; simpl.
   progress repeat rewrite Rmult_1_r.
   split; [ f_equal; lra | intros H; discriminate H ].

subst w.
rewrite rotate_by_mat_mul.

bbb.

  destruct (letter_opp_dec e e₂) as [H₁| H₁].
   destruct e as (t₁, d₁).
   destruct e₂ as (t₂, d₂).
   apply letter_opp_iff in H₁.
   destruct H₁; subst t₂ d₂; subst el₂.
   remember (negb d₁) as d₂.
   replace d₁ with (negb (negb d₁)) in Hel₂ by apply Bool.negb_involutive.
   subst d₂.
   exfalso; revert Hel₂; apply norm_list_impossible_start.

   injection Hn; clear Hn; intros; subst el.
   destruct el₁ as [| e₁]; [ discriminate Hel | simpl in Hel ].
   injection Hel; clear Hel; intros H1 H2; subst e₁.
   remember (e₂ :: el₂) as el₃ eqn:Hel₃.
   remember (fold_left rotate el₃) as w' eqn:Hw'.

pose proof IHel (eq_refl _) w' el₁ d (eq_refl _) H1 as H.
destruct H as (a', (b', (c', (k', (Hp, Hb))))).
destruct e as (t₁, d₁); destruct t₁; simpl.
 rewrite Hw; simpl; rewrite <- Hw'.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite Rmult_0_r.
 progress repeat rewrite Rplus_0_r.
 exists a', b', c', k'.
 split; [ destruct d₁; assumption | assumption ].

 rewrite Hw; simpl; rewrite <- Hw'.
 progress repeat rewrite Rmult_1_r.
 progress repeat rewrite Rmult_0_r.
 progress repeat rewrite Rplus_0_r.
 destruct d₁.
  subst w'.
  remember (fold_left rotate_param el₃ (1%Z, (-2)%Z, 0%Z, 1)) as u eqn:Hu.
  symmetry in Hu; destruct u as (((a, b), c), N).
  apply rotate_param_rotate in Hu.
  destruct Hu as (Hr, Hn); simpl in Hr.
  rewrite Rmult_1_r in Hr.
  replace (0/3)%R with 0%R in Hr by lra.
  exists a, b, c, N.
  split; [ apply Hr | ].
  subst el₃.
  destruct e₂ as (t₂, d₂); destruct t₂, d₂.
   simpl in Hr.
   progress repeat rewrite Rmult_1_l in Hr.
   progress repeat rewrite Rmult_0_r in Hr.
   progress repeat rewrite Rmult_0_l in Hr.
   progress repeat rewrite Rplus_0_r in Hr.
   progress repeat rewrite Rplus_0_l in Hr.
revert Hr; clear; intros.
bbb.

SearchAbout rotate_param.
remember (fold_left rotate_param el₂ (3, -2, 8, 2%nat)%Z) as u eqn:Hu.
symmetry in Hu; destruct u as (((a', b'), c'), N').
generalize Hu; intros Hv.
apply rotate_param_rotate in Hu; simpl in Hu.
destruct Hu as (Hu, HN).
progress repeat rewrite Rmult_1_r in Hu.
replace ((2+1)/(3*3))%R with (1/3)%R in Hu by lra.
replace (1/3*(-2*√2/3))%R with (-2*√2/(3*3))%R in Hr by lra.
replace ((2+1+1+1+1+1+1)/(3*3))%R with (-2*√2/3*(-2*√2/3))%R in Hu.
Focus 2.
unfold Rdiv; do 2 rewrite <- Rmult_assoc.
rewrite Rmult5_sqrt2_sqrt5; lra.
rewrite Hr in Hu.
injection Hu; clear Hu; intros Hc Hb Ha.


Compute fold_left rotate [] (P (1/3) (-2*√2/9) (8/9)).

revert H1 Hr; clear; intros.
revert el₁ d a b c N H1 Hr.
induction el₂ as [| e₂]; intros.
 destruct el₁ as [| e₁]; [ discriminate H1 | simpl in H1 ].
 injection H1; intros H2 H3.
 symmetry in H2; apply app_eq_nil in H2; destruct H2; discriminate.



bbb.
   subst w; simpl; rewrite <- Hw'.
   destruct e as (t₁, d₁); destruct t₁; simpl.
    progress repeat rewrite Rmult_1_r.
    progress repeat rewrite Rmult_0_r.
    progress repeat rewrite Rplus_0_r.
    destruct d₁.
     eapply IHel; [ reflexivity | reflexivity | eassumption ].
     eapply IHel; [ reflexivity | reflexivity | eassumption ].

    progress repeat rewrite Rmult_1_r.
    progress repeat rewrite Rmult_0_r.
    progress repeat rewrite Rplus_0_r.
    rewrite Hw', Hel₃; simpl.
    destruct d₁; simpl.
     destruct e₂ as (t₂, d₂); simpl.
     progress repeat rewrite Rmult_1_l.
     progress repeat rewrite Rmult_0_l.
     progress repeat rewrite Rmult_0_r.
     progress repeat rewrite Rplus_0_l.
     progress repeat rewrite Rplus_0_r.
     destruct t₂, d₂; [ | | | exfalso; apply H₁; constructor ].
      pose proof IHel (eq_refl _) w' el₁ d (eq_refl _) H1.
      destruct H as (a', (b', (c', (k', (Hp, Hb))))).
      rewrite Hw', Hel₃ in Hp; simpl in Hp.
      progress repeat rewrite Rmult_1_l in Hp.
      progress repeat rewrite Rmult_0_l in Hp.
      progress repeat rewrite Rmult_0_r in Hp.
      progress repeat rewrite Rplus_0_l in Hp.
      progress repeat rewrite Rplus_0_r in Hp.
bbb.
      remember (fold_left rotate_param el₂ (3, -2, 1, 2%nat)%Z) as u eqn:Hu.
      symmetry in Hu; destruct u as (((a, b), c), N).
      eapply rotate_param_rotate in Hu.
      destruct Hu as (Hu, HN); simpl in Hu.
      progress repeat rewrite Rmult_1_r in Hu.
      progress repeat rewrite Rmult_0_l in Hu.
      replace (0 / 3)%R with 0%R in Hu by lra.
      exists a

bbb.

Theorem toto : ∀ w el el' d,
  w = fold_left rotate el
  → norm_list el = el
  → el = E lb d :: el'
  → ∃ a b c k,
    w (P 1 0 0) = P (IZR a/3^k) (IZR b*√2/3^k) (IZR c/3^k) ∧
    (b mod 3 ≠ 0)%Z.
Proof.
intros w el el' d Hw Hn Hel.
destruct el as [| e]; [ discriminate Hel | ].
injection Hel; clear Hel; intros; subst e el'.
revert w d Hn Hw.
induction el as [| e]; intros.
 destruct d.
  exists 1%Z, (-2)%Z, 0%Z, 1.
  subst w; simpl.
  progress repeat rewrite Rmult_1_r.
  progress repeat rewrite Rmult_0_r.
  progress repeat rewrite Rplus_0_r.
  split; [ f_equal; lra | intros H; discriminate H ].

  exists 1%Z, 2%Z, 0%Z, 1.
  subst w; simpl.
  progress repeat rewrite Rmult_1_r.
  progress repeat rewrite Rmult_0_r.
  progress repeat rewrite Rplus_0_r.
  split; [ f_equal; lra | intros H; discriminate H ].

 remember (e :: el) as el' eqn:Hel.
 remember (fold_left rotate el') as w' eqn:Hw'.
 assert (Habc :
   ∃ (a b c : ℤ) (k : ℕ),
   w' (P 1 0 0) = P (IZR a / 3 ^ k) (IZR b * √ 2 / 3 ^ k) (IZR c / 3 ^ k)).
  subst w'.
  remember (fold_left rotate_param el' (1, 0, 0, O)%Z) as abc eqn:Habc.
  symmetry in Habc.
  destruct abc as (((a, b), c), N).
  exists a, b, c, N.
  apply rotate_param_rotate in Habc.
  destruct Habc as (Habc, HN).
  simpl in Habc.
  rewrite Rmult_0_l in Habc.
  unfold Rdiv in Habc.
  do 2 rewrite RMicromega.Rinv_1 in Habc.
  apply Habc.

  destruct Habc as (a', (b', (c', (k', Habc)))).
bbb.

  subst w; simpl; rewrite <- Hw'.
  progress repeat rewrite Rmult_1_r.
  progress repeat rewrite Rmult_0_r.
  progress repeat rewrite Rplus_0_r.
  destruct d.
bbb.

   rewrite Hw', Hel in Habc.
   simpl in Habc.
   destruct e as (t, d); destruct t, d.
    simpl in Habc.
    progress repeat rewrite Rmult_1_r in Habc.
    progress repeat rewrite Rmult_0_l in Habc.
    progress repeat rewrite Rmult_0_r in Habc.
    progress repeat rewrite Rplus_0_r in Habc.
    rewrite Hw', Hel; simpl.
    progress repeat rewrite Rmult_0_l.
    progress repeat rewrite Rmult_1_l.
    progress repeat rewrite Rmult_0_r.
    progress repeat rewrite Rplus_0_l.
    progress repeat rewrite Rplus_0_r.
bbb.

    exists (a'+4*b')%Z, (b'-2*a')%Z,(3*c')%Z, (S k').
bbb.
   subst w'.
split.
   revert Habc; clear; intros.
   induction el' as [| e'].
    simpl in Habc; simpl.
    injection Habc; intros H1 H2 H3.
    symmetry in H1, H2; unfold Rdiv in H1, H2, H3.
    apply Rmult_integral in H1.
    destruct H1 as [H1| H1].
Focus 2.
     exfalso; revert H1; apply Rinv_neq_0_compat, pow_nonzero; lra.

     apply Rmult_integral in H2.
     destruct H2 as [H2| H2].
Focus 2.
      exfalso; revert H2; apply Rinv_neq_0_compat, pow_nonzero; lra.

      apply Rmult_integral in H2.
      destruct H2 as [H2| H2]; [ | exfalso; revert H2; apply sqrt2_neq_0 ].
      apply Rmult_eq_compat_l with (r := (3 ^ k')%R) in H3.
      rewrite Rmult_1_r in H3.
      rewrite <- Rmult_assoc, Rmult_shuffle0 in H3.
      rewrite Rinv_r_simpl_r in H3; [ | apply pow_nonzero; lra ].
      progress repeat rewrite plus_IZR.
      progress repeat rewrite minus_IZR.
      progress repeat rewrite mult_IZR.
      rewrite H1, H2, <- H3; simpl.
      progress repeat rewrite Rmult_0_r.
      progress repeat rewrite Rplus_0_r.
      progress repeat rewrite Rminus_0_l.
      unfold Rdiv.
      f_equal; field; apply pow_nonzero; lra.

simpl in Habc; simpl.
bbb.

Theorem toto : ∀ nc x y z,
  first nc = lb
  → path nc ≠ []
  → rotate_combined nc (P 1 0 0) = P x y z
  → y ≠ 0%R.
Proof.
intros nc x y z Hf Hp Hr.
remember (uncombine nc) as el eqn:Hel.
unfold uncombine in Hel; symmetry in Hel.
rewrite Hf in Hel.
destruct el as [| e].
 remember (path nc) as bnl eqn:Hbnl.
 symmetry in Hbnl.
 destruct bnl as [| (b, n)]; [ exfalso; apply Hp; reflexivity | ].
 discriminate Hel.

 remember (path nc) as bnl eqn:Hbnl; symmetry in Hbnl.
 revert nc x y z e el Hf Hbnl Hr Hel.
 clear Hp.
 induction bnl as [| (b, n)]; intros; [ discriminate Hel | ].
 simpl in Hel.
 injection Hel; clear Hel; intros; subst e el.
 unfold rotate_combined in Hr.
 rewrite Hf, Hbnl in Hr.
 simpl in Hr.
 destruct b.
  assert (Habc : ∃ a b c, x = IZR a ∧ y = (IZR b * √2 / 3)%R ∧ z = IZR c).
   remember (rotate_param (1, 0, 0, O)%Z ḅ) as abc eqn:Habc.
   symmetry in Habc.
   simpl in Habc.

Check rotate_param_app.
bbb.

Theorem toto : ∀ nc, path nc ≠ [] → combine (uncombine nc) = nc.
Proof.
intros nc Hbnl.
unfold uncombine.
destruct nc as (f, bnl); simpl in Hbnl; simpl.
revert f.
induction bnl as [| (b, n)]; intros; [ exfalso; apply Hbnl; reflexivity | ].
clear Hbnl; simpl.
remember (repeat (E f b) n) as r eqn:Hr.
remember (r ++ uncombine_loop (other_elem f) bnl) as el eqn:Hel; subst r.
symmetry in Hel.
destruct (letter_dec f (first (combine el))) as [Hf| Hf].
 remember (path (combine el)) as bnl₁ eqn:Hbnl₁; symmetry in Hf, Hbnl₁.
 destruct bnl₁ as [| (b₁, n₁)].
  f_equal.
  destruct el as [| e].
   simpl in Hf; subst f.
   destruct n; [ | discriminate Hel ].
   simpl in Hel.
   destruct bnl as [| (b₂, n₂)]; [ reflexivity | ].
   discriminate Hel.

   simpl in Hbnl₁.
   destruct e as (t, d).
   simpl in Hf.
   destruct (letter_dec t (first (combine el))) as [H₁| H₁].
    symmetry in H₁.
    remember (path (combine el)) as bnl₂ eqn:Hbnl₂.
    symmetry in Hbnl₂.
    destruct bnl₂ as [| (b₁, n₁)]; [ discriminate Hbnl₁ | ].
    destruct (Bool.bool_dec d b₁) as [H₂| H₂]; [ subst b₁ | ].
     discriminate Hbnl₁.

     destruct n₁; [ | discriminate Hbnl₁ ].
     simpl in Hf, Hbnl₁.
     subst bnl₂ f.
     rewrite other_elem_involutive in Hel.
     destruct n.
      simpl in Hel.
      destruct bnl as [| (b₂, n₂)]; [ reflexivity | exfalso ].
      simpl in Hel.
      injection Hel; clear Hel; intros; subst b₂ el.
      assert (Hn : (d, n₂) :: bnl ≠ []) by (intros H; discriminate).
      apply IHbnl with (f := t) in Hn.
      simpl in Hn.
      rewrite H₁, Hbnl₂ in Hn.
      rewrite letter_dec_diag in Hn.
      destruct (Bool.bool_dec d b₁) as [H₃| H₃]; [ contradiction | ].
      discriminate Hn.

      exfalso.
      simpl in Hel.
      injection Hel; clear Hel; intros H₃ H₄ H₅.
      destruct t; discriminate H₅.

    discriminate Hbnl₁.
    destruct (Bool.bool_dec b b₁) as [H₁| H₁]; [ subst b₁ | ].
     f_equal.
     destruct n.
      simpl in Hel; subst el.
      destruct bnl as [| (b₂, n₂)]; [ discriminate Hbnl₁ | ].
Theorem toto : ∀ nc, path nc ≠ [] → first (combine (uncombine nc)) = first nc.
Proof.
intros (f, bnl) Hp; simpl in Hp; simpl.
unfold uncombine; simpl.
destruct bnl as [| (b, n)]; intros; [ exfalso; apply Hp; reflexivity | ].
clear Hp; simpl.
remember (repeat (E f b) n) as r eqn:Hr.
remember (r ++ uncombine_loop (other_elem f) bnl) as el eqn:Hel; subst r.
destruct (letter_dec f (first (combine el))) as [H₁| H₁]; [ | reflexivity ].
remember (path (combine el)) as bnl₁ eqn:Hbnl₁.
destruct bnl₁ as [| (b₁, n₁)]; [ reflexivity | ].
destruct (Bool.bool_dec b b₁) as [H₂| H₂]; [ reflexivity | ].
destruct n₁; [ exfalso | reflexivity ].
destruct n.
 rewrite app_nil_l in Hel.
 rewrite Hel in H₁.
 destruct bnl as [| (b₂, n₂)].
  simpl in Hel; subst el; discriminate Hbnl₁.

Theorem toto : ∀ nc, normalised_list (uncombine nc).
Proof.
intros (t, bnl).
unfold uncombine; revert t.
induction bnl as [| (b, n)]; intros; [ reflexivity | ].
simpl in IHbnl; remember uncombine_loop as f; simpl; subst f.

bbb.
  rewrite IHbnl in H₁; [ | intros H; discriminate H ].
  destruct f; discriminate H₁.

  remember (uncombine_loop (other_elem f) bnl) as bnl₂ eqn:Hbnl₂.
  subst r el; simpl in Hbnl₁.
  remember (repeat (E f b) n ++ bnl₂) as el₁ eqn:Hel₁.
  destruct (letter_dec f (first (combine el₁))) as [H₃| H₃].
   remember (path (combine el₁)) as bnl₃ eqn:Hbnl₃.
   destruct bnl₃ as [| (b₂, n₂)].
    injection Hbnl₁; intros H₄ H₅; symmetry in H₅; contradiction.

    destruct (Bool.bool_dec b b₂) as [H₄| H₄]; [ discriminate Hbnl₁ | ].
    destruct n₂.
     simpl in Hbnl₁; subst bnl₃.
     simpl in H₁.
     rewrite <- Hel₁, <- H₃ in H₁.
     rewrite letter_dec_diag in H₁.
     rewrite <- Hbnl₃ in H₁.
     destruct (Bool.bool_dec b b₂) as [H₅| H₅]; [ contradiction | ].
     destruct f; discriminate H₁.

     simpl in Hbnl₁.
     injection Hbnl₁; clear Hbnl₁; intros; subst b₂ n₂ bnl₃.
     clear H₄; simpl in H₁.
     rewrite <- Hel₁, <- H₃ in H₁.
     rewrite letter_dec_diag in H₁.
     rewrite <- Hbnl₃ in H₁.
     destruct (Bool.bool_dec b b₁) as [H₅| H₅]; [ contradiction | ].
     clear H₅ H₁.
     destruct bnl as [| (b₂, n₂)].
      simpl in Hbnl₂; subst bnl₂.
      rewrite app_nil_r in Hel₁; subst el₁.
      destruct n; [ discriminate Hbnl₃ | ].
      simpl in Hbnl₃, H₃.
      remember (combine (repeat (E f b) n)) as nc eqn:Hnc.
      destruct (letter_dec f (first nc)) as [H₁| H₁].
       remember (path nc) as bnl eqn:Hbnl.
       destruct bnl as [| (b₂, n₂)]; [ discriminate Hbnl₃ | ].
       destruct (Bool.bool_dec b b₂) as [H₄| H₄]; [ subst b₂ | ].
        simpl in Hbnl₃.
        injection Hbnl₃; intros; subst; apply H₂; reflexivity.

        destruct n₂; [ destruct f; discriminate H₃ | ].
        simpl in Hbnl₃.
        injection Hbnl₃; clear Hbnl₃; intros; subst b₂ n₂ bnl₁.

(* there is an induction somewhere... *)

bbb.
intros (f, bnl) Hp; simpl in Hp; simpl.
unfold uncombine; simpl.
destruct bnl as [| (b, n)]; [ exfalso; apply Hp; reflexivity | ].
remember combine as g; simpl; subst g.
remember (repeat (E f b) n) as r eqn:Hr.
remember (r ++ uncombine_loop (other_elem f) bnl) as el eqn:Hel.
simpl.
destruct (letter_dec f (first (combine el))) as [H₁| H₁].
 remember (path (combine el)) as bnl₁ eqn:Hbnl₁.
 destruct bnl₁ as [| (b₁, n₁)]; [ reflexivity | ].
 destruct (Bool.bool_dec b b₁) as [H₂| H₂]; [ reflexivity | ].
 destruct n₁; [ exfalso | reflexivity ].
 subst r el.
 destruct n.
  simpl in H₁.
  destruct bnl as [| (b₂, n₂)]; [ discriminate Hbnl₁ | ].
  remember combine as g; simpl in H₁; subst g.
  remember (repeat (E (other_elem f) b₂) n₂) as r eqn:Hr.
  remember (r ++ uncombine_loop (other_elem (other_elem f)) bnl) as bnl₂.
  simpl in H₁.
  destruct (letter_dec (other_elem f) (first (combine bnl₂))) as [H₃| H₃].
   destruct (path (combine bnl₂)) as [| (b₃, n₃)].
    destruct f; discriminate H₁.

    destruct (Bool.bool_dec b₂ b₃) as [H₄| H₄].
     destruct f; discriminate H₁.

     destruct n₃.
      simpl in Hbnl₁.
(* c'est parti en couille, ça, non ? *)
bbb.

rewrite fold_uncombine, toto in Hf.
simpl in Hf; destruct f; discriminate Hf.

bbb.

Theorem toto : ∀ t d el,
  normalised_list (E t d :: el)
  → first (combine (E t d :: el)) = t.
Proof.
intros t d el Hn; simpl.
destruct (letter_dec t (first (combine el))) as [H₁| H₁].
remember (path (combine el)) as bnl eqn:Hbnl.
destruct bnl as [| (b, n)]; [ reflexivity | ].
destruct (Bool.bool_dec d b) as [H₂ | H₂]; [ reflexivity | ].
destruct n; [ | reflexivity ].
bbb.

pose proof toto nc as Ht.
unfold uncombine in Ht.
rewrite Hf, <- Hel in Ht.
simpl in Ht.

bbb.

Theorem toto : ∀ nc el, el = uncombine nc → el ≠ [] → nc = combine el.
Proof.
intros nc el Hel Hu.
unfold uncombine in Hel; symmetry in Hel.
revert nc Hel Hu.
induction el as [| e]; intros; [ exfalso; apply Hu; reflexivity | clear Hu ].
simpl in Hel; simpl.
destruct e as (t, d).
destruct (letter_dec t (first (combine el))) as [H₁| H₁].
 remember (path (combine el)) as bnl eqn:Hbnl.
 symmetry in H₁, Hbnl.
 destruct bnl as [| (b, n)].
  destruct nc as (f, p).
  simpl in Hel.
bbb.

Theorem toto : ∀ el a b c N,
  fold_left rotate_param (ḅ :: el) (1, 0, 0, O)%Z = (a, b, c, N)
  → b ≠ 0%Z.
Proof.
intros el a b c N Hr.
simpl in Hr.

Theorem titi : ∀ el p q,
  fst3 p ≡₃ (1, 2, 0)%Z ∨ fst3 p ≡₃ (2, 1, 0)%Z ∨
  fst3 p ≡₃ (0, 1, 1)%Z ∨ fst3 p ≡₃ (0, 2, 2)%Z
  → fold_left rotate_param el p = q
  → fst3 q ≡₃ (1, 2, 0)%Z ∨ fst3 q ≡₃ (2, 1, 0)%Z ∨
    fst3 q ≡₃ (0, 1, 1)%Z ∨ fst3 q ≡₃ (0, 2, 2)%Z.
Proof.
intros el p q Hp Hr.
revert p q Hp Hr.
induction el as [| e]; intros; simpl in Hr; [ destruct Hr; assumption | ].
apply IHel in Hr.
 destruct Hr as [Hr| [Hr| [Hr| Hr]]].
  left; assumption.

  right; left; assumption.

  right; right; left; assumption.

  right; right; right; assumption.

 destruct p as (((a, b), c), N).
 simpl in Hp.
 destruct Hp as [Hp| [Hp| [Hp| Hp]]].
  destruct Hp as (Ha, (Hb, Hc)).
  unfold Z.modulo in Ha at 2; simpl in Ha.
  unfold Z.modulo in Hb at 2; simpl in Hb.
  unfold Z.modulo in Hc at 2; simpl in Hc.
  simpl in Hr; simpl.
  destruct e as (t, d); destruct t, d.
   simpl.
   right; right; right.
   rewrite Z.mul_mod; [ | intros H; discriminate H ].
   split; [ reflexivity | ].
   rewrite Z.add_mod; [ | intros H; discriminate H ].
   rewrite Z.mul_mod; [ | intros H; discriminate H ].
   rewrite Hb, Hc; split; [ reflexivity | ].
   rewrite Z.add_mod; [ | intros H; discriminate H ].
   rewrite Z.mul_mod; [ | intros H; discriminate H ].
   rewrite Hb, Hc.
simpl.
(* enfer et damnation ! *)

bbb.
Focus 2.
  apply IHel in Hr; [ assumption | ].
Unfocus. Focus 3.
  apply IHel in Hr; [ assumption | ].
Unfocus. Focus 4.
  apply IHel in Hr; [ assumption | ].
Unfocus.

(* counter-example *)
Compute fold_left rotate_param [ạ⁻¹] (0, 1, 1, O)%Z.

bbb.
  Hr : fold_left rotate_param el (1%Z, 2%Z, 0%Z, 1) = (a, b, c, N)
  ============================
  b ≠ 0%Z

apply titi in Hr; [ | intros H; discriminate H ].
intros H; subst b; apply Hr; reflexivity.
Qed.

bbb.

Theorem rotate_1_0_0_ending_repeat_b : ∀ n abc,
  fst3 (fold_left rotate_param (repeat ḅ (S n)) (1, 0, 0, O)%Z) ≡₃ abc
  → abc ≡₃ (1, 1, 0)%Z ∨ abc ≡₃ (2, 2, 0)%Z.
Proof.
intros n ((a, b), c) H.
rewrite <- H; clear H.
pose proof rotate_param_app [] ḅ n (0, 1, 0, O)%Z _ _ _ _ (eq_refl _) as H.
rewrite app_nil_l, Nat.add_1_r in H; rewrite H; simpl; clear H.
destruct (zerop (n mod 2)) as [H| H]; [ left; reflexivity | ].
right; simpl; split; [ reflexivity | split; reflexivity ].
Qed.

Theorem rotate_0_1_0_ending_repeat_a_and_b : ∀ el n₁ n₂ abc,
  el = repeat ạ (S n₂) ++ repeat ḅ (S n₁)
  → fst3 (fold_left rotate_param el (0, 1, 0, O)%Z) ≡₃ abc
  → abc ≡₃ (1, 1, 0)%Z ∨ abc ≡₃ (2, 2, 0)%Z.
Proof.
intros el n₁ n₂ abc Hel Hr; subst el.
remember (0, 1, 0, O)%Z as p eqn:Hp.
remember (fold_left rotate_param (repeat ạ (S n₂)) p) as abc₁ eqn:Habc₁.
symmetry in Habc₁.
destruct abc₁ as (((a₁, b₁), c₁), N₁).
pose proof rotate_param_app_bn (repeat ạ (S n₂)) n₁ p _ _ _ _ Habc₁ as Hb.
rewrite Nat.add_1_r, Hr in Hb; rewrite Hb.
remember (fold_left rotate_param [] p) as abc₂ eqn:Habc₂.
symmetry in Habc₂.
destruct abc₂ as (((a₂, b₂), c₂), N₂).
pose proof rotate_param_app_an [] n₂ p _ _ _ _ Habc₂ as Ha.
simpl in Habc₂; rewrite Hp in Habc₂.
injection Habc₂; clear Habc₂; intros; subst a₂ b₂ c₂ N₂.
rewrite app_nil_l, Nat.add_1_r  in Ha.
rewrite Habc₁ in Ha; simpl in Ha.
destruct (zerop (n₁ mod 2)) as [H₁| H₁].
 destruct (zerop (n₂ mod 2)) as [H₂| H₂].
  rewrite Z.mod_0_l in Ha; [ | intros H; discriminate H ].
  destruct Ha as (Ha₁, (Hb₁, Hc₁)).
  left.
  unfold "≡₃".
  rewrite Zdiv.Zplus_mod, Ha₁, Z.add_0_l, Hb₁.
  split; [ reflexivity | split; reflexivity ].

  rewrite Z.mod_0_l in Ha; [ | intros H; discriminate H ].
  destruct Ha as (Ha₁, (Hb₁, Hc₁)).
  right.
  unfold "≡₃".
  rewrite Zdiv.Zplus_mod, Ha₁, Z.add_0_l, Hb₁.
  split; [ reflexivity | split; reflexivity ].

 destruct (zerop (n₂ mod 2)) as [H₂| H₂].
  rewrite Z.mod_0_l in Ha; [ | intros H; discriminate H ].
  destruct Ha as (Ha₁, (Hb₁, Hc₁)).
  right.
  unfold "≡₃".
  rewrite Zdiv.Zminus_mod.
  rewrite Zdiv.Z_mod_zero_opp_full; [ | assumption ].
  rewrite Hb₁; simpl.
  split; [ reflexivity | split; reflexivity ].

  rewrite Z.mod_0_l in Ha; [ | intros H; discriminate H ].
  destruct Ha as (Ha₁, (Hb₁, Hc₁)).
  left.
  unfold "≡₃".
  rewrite Zdiv.Zminus_mod.
  rewrite Zdiv.Z_mod_zero_opp_full; [ | assumption ].
  rewrite Hb₁; simpl.
  split; [ reflexivity | split; reflexivity ].
Qed.

bbb.

Theorem titi : ∀ n a b c,
  fst3 (fold_left rotate_param (repeat ḅ (S n)) (1, 0, 0, O)%Z) ≡₃ (a, b, c)
  → b ≠ 0%Z.
Proof.
intros n a b c H.
pose proof rotate_param_app [] ḅ n (1, 0, 0, O)%Z _ _ _ _ (eq_refl _) as H₁.
rewrite app_nil_l, Nat.add_1_r in H₁; rewrite H₁ in H; clear H₁; simpl in H.
destruct (zerop (n mod 2)) as [H₁| H₁].
 destruct H as (Ha, (Hb, Hc)).
 intros H; subst b; discriminate Hb.

 destruct H as (Ha, (Hb, Hc)).
 intros H; subst b; discriminate Hb.
Qed.

Theorem tutu : ∀ x y z a b c N,
  fold_left rotate_param [] (x, y, z, 0) = (a, b, c, N)
  → fold_left rotate [] (P (IZR x) (IZR y * √ 2) (IZR z)) =
    P (IZR a) (IZR b * √ 2) (IZR c).
Proof.
intros.
simpl in H; simpl.
injection H; intros; subst; reflexivity.
Qed.

Theorem tata : ∀ p el a c,
  norm_list el ≠ []
  → p = P (IZR a) 0 (IZR c)
  → (a ^ 2 + c ^ 2 = 1)%Z
  → fold_left rotate el p ≠ p.
Proof.
intros p el a c Hn Hp Hac.
remember (fold_left rotate_param el (a, 0%Z, c, 0)) as r eqn:Hr.
symmetry in Hr.
destruct r as (((a', b'), c'), N).
generalize Hr; intros Ht.
apply rotate_param_rotate in Ht.
unfold Rdiv in Ht.
rewrite Nat.add_0_l, pow_O, Rinv_1 in Ht.
progress repeat rewrite Rmult_0_l in Ht.
progress repeat rewrite Rmult_1_r in Ht.
destruct Ht as (Ht, HN).
rewrite <- Hp in Ht.
intros Hp'; rewrite Ht in Hp'; symmetry in Hp'.
assert (Hb' : b' ≠ 0%Z).
 intros Hb'; subst b'.
induction el as [| e₁] using rev_ind; [ apply Hn; reflexivity | clear IHel ].
simpl in Hr.
destruct e₁ as (t₁, d₁); destruct t₁, d₁.
 remember (fold_left rotate_param el (a, 0%Z, c, 0)) as abcn eqn:Habcn.
 symmetry in Habcn.
 destruct abcn as (((a₁, b₁), c₁), N₁).
 apply rotate_param_app_a1n with (n := 0) in Habcn.
 simpl in Habcn.
 rewrite Hr in Habcn.
 simpl in Habcn.
 destruct Habcn as (Ha, (Hb, Hc)).
 rewrite <- Hb in Hc.
 rewrite Z.mod_0_l in Ha; [ | intros H1; discriminate H1 ].
 rewrite Z.mod_0_l in Hc; [ | intros H1; discriminate H1 ].
Check toto.
bbb.

 apply Znumtheory.Zmod_divide in Ha; [ | intros H; discriminate H ].
 apply Znumtheory.Zmod_divide in Hc; [ | intros H; discriminate H ].
 destruct Ha as (ka, Ha); subst a'.
 destruct Hc as (kc, Hc); subst c'.
 simpl in Hp'; do 2 rewrite Rmult_0_l in Hp'.
 rewrite Hp in Hp'.
 injection Hp'; clear Hp'; intros Ha Hc.

 apply IZR_eq in Hac.
 rewrite plus_IZR, Z.pow_2_r, Z.pow_2_r in Hac.
 do 2 rewrite mult_IZR in Hac.
 rewrite Ha, Hc in Hac.

bbb.

Focus 2.
 rewrite Hp in H.
 injection H; clear H; intros Hc Hb Ha.
 symmetry in Hb.
 apply Rmult_integral in Hb.
 destruct Hb as [Hb| Hb].
  apply Rmult_integral in Hb.
  destruct Hb as [Hb| Hb]; [ apply eq_IZR_R0 in Hb; contradiction | ].
  revert Hb; apply sqrt2_neq_0.

  revert Hb; apply Rinv_neq_0_compat.
  apply pow_nonzero; lra.

 intros Hb'.
 apply Hn; clear Hn.
 apply norm_nil_iff.
 subst b'; simpl in H, Hr.
 do 2 rewrite Rmult_0_l in H, Hr.
 rewrite Hp in H.
 injection H; clear H; intros Hc Ha.
 induction el as [| e] using rev_ind; [ left; reflexivity | right ].
 clear IHel.
Check rotate_param_app.
SearchAbout rotate.  
 remember (fold_left rotate_param (el ++ [e]) (a, 0%Z, c, 0)) as s eqn:Hs.
 generalize Hs; intros Ht.
 symmetry in Hs.
 Check rotate_param_app.
bbb.

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

bbb.

Theorem toto : ∀ el pt,
  rotate_norm2 (norm_combine el) pt = fold_left rotate (norm_list el) pt.
Proof.
intros el pt.
unfold rotate_norm2.
remember (norm_combine el) as pa eqn:Hpa .
symmetry in Hpa.
destruct pa as (t, bnl).
revert el pt t Hpa.
induction bnl as [| (d, n)]; intros.
 simpl.
 destruct el as [| e]; [ reflexivity |  ].
 simpl; simpl in Hpa.
 destruct e as (t₁, d₁).
 remember (path (norm_combine el)) as pa eqn:Hpa₂ .
 symmetry in Hpa₂.
 destruct pa as [| (d, n) pa]; [ discriminate Hpa |  ].
 unfold path_start in Hpa.
 rewrite Hpa₂ in Hpa.
 simpl in Hpa.
 destruct (zerop (S (length pa) mod 2)) as [H₁| H₁].
  remember (last (norm_combine el)) as lst eqn:Hlst .
  destruct (letter_dec t₁ (other_elem lst)) as [H₂| H₂].
   destruct (Bool.bool_dec d₁ d) as [H₃| H₃]; [ discriminate Hpa |  ].
   destruct n; [ injection Hpa; intros; subst; discriminate H₁ |  ].
   discriminate Hpa.

   discriminate Hpa.

  remember (last (norm_combine el)) as lst eqn:Hlst .
  destruct (letter_dec t₁ lst) as [H₂| H₂].
   destruct (Bool.bool_dec d₁ d) as [H₃| H₃]; [ discriminate Hpa |  ].
   apply neq_negb in H₃; subst d₁.
   destruct n.
    injection Hpa; clear Hpa; intros; subst.
    remember (norm_list el) as el₁ eqn:Hel .
    symmetry in Hel.
    destruct el₁ as [| e₁].
     simpl.
     apply norm_nil_iff in Hel.
     destruct Hel as [Hel| Hel]; [ subst el; discriminate Hpa₂ |  ].
     destruct Hel as (el₁, (el₂, (t₂, (d₂, (Hel, Hn))))).
     subst el.
     apply norm_nil_iff in Hn.
     destruct Hn as [Hn| Hn].
      apply app_eq_nil in Hn.
      destruct Hn; subst el₁ el₂.
      rewrite app_nil_l in Hpa₂; simpl in Hpa₂.
      unfold path_start in Hpa₂; simpl in Hpa₂.
      rewrite letter_dec_diag, bool_dec_negb_r in Hpa₂.
      discriminate Hpa₂.

      destruct Hn as (el₃, (el₄, (t₃, (d₃, (Hn₁, Hn₂))))).
      apply norm_nil_iff in Hn₂.
      destruct Hn₂ as [Hn₂| Hn₂].
       apply app_eq_nil in Hn₂.
       destruct Hn₂; subst el₃ el₄.
       rewrite app_nil_l in Hn₁.
       remember (el₁ ++ E t₂ d₂ :: E t₂ (negb d₂) :: el₂) as el₃ eqn:Hel₃ .
       remember (last (norm_combine el₃)) as t eqn:Ht .
       symmetry in Ht.
       destruct t.
        destruct d; simpl.
         exfalso.
         revert Hel₃ Hpa₂ Hn₁ Ht; clear; intros.
         revert el₁ el₂ t₂ d₂ t₃ d₃ Hel₃ Hn₁.
         induction el₃ as [| (t, d)]; intros; [ discriminate Hpa₂ |  ].
         simpl in Hpa₂, Ht.
         remember (path (norm_combine el₃)) as bnl eqn:Hbnl .
         symmetry in Hbnl.
         destruct bnl as [| (b, n)].
          simpl in Hpa₂, Ht.
          injection Hpa₂; clear Hpa₂; intros; subst d t.
          destruct el₃ as [| (t, d)].
           simpl in Hel₃.
           Focus 2.
           simpl in Hbnl; clear IHel₃.
           remember (path (norm_combine el₃)) as bnl eqn:Hbnl₁ .
           symmetry in Hbnl₁.
           destruct bnl as [| (b, n)]; [ discriminate Hbnl |  ].
           unfold path_start in Hbnl; simpl in Hbnl.
           rewrite Hbnl₁ in Hbnl; simpl in Hbnl.
           destruct (zerop (S (length bnl) mod 2)) as [H₁| H₁].
            destruct bnl as [| (b₁, n₁)]; [ discriminate H₁ |  ].
            remember (other_elem (last (norm_combine el₃))) as t₁ eqn:Ht .
            destruct (letter_dec t t₁) as [H₂| H₂]; [ subst t₁ |  ].
             destruct (Bool.bool_dec d b); [ discriminate Hbnl | ].
             destruct n; discriminate Hbnl.

             discriminate Hbnl.

            remember (last (norm_combine el₃)) as t₁ eqn:Ht₁ .
            destruct (letter_dec t t₁) as [H₂| H₂]; [ subst t₁ |  ].
             destruct (Bool.bool_dec d b) as [| H₃]; [ discriminate Hbnl |  ].
             destruct n; [ simpl in Hbnl | discriminate Hbnl ].
             subst bnl.
             apply neq_negb in H₃; subst d.
             destruct el₁ as [| e₁].
              rewrite app_nil_l in Hel₃, Hn₁; subst el₂.
              injection Hel₃; clear Hel₃; intros; subst t₂ d₂ t el₃.
              simpl in Hbnl₁, H3.
              unfold path_start in Hbnl₁; simpl in Hbnl₁.
              rewrite bool_dec_negb_r in Hbnl₁; simpl in Hbnl₁.
              rewrite letter_dec_diag in Hbnl₁. discriminate Hbnl₁.

              simpl in Hn₁.
              injection Hn₁; clear Hn₁; intros; subst e₁.
              simpl in Hel₃.
              injection Hel₃; clear Hel₃; intros; subst; simpl in H.
              destruct el₁ as [| e₁].
               rewrite app_nil_l in H, H0; subst el₂.
               injection H0; clear H0; intros; subst.
               rewrite Bool.negb_involutive in Hbnl₁.
               simpl in Hbnl₁.
               unfold path_start in Hbnl₁; simpl in Hbnl₁.
               destruct (letter_dec t₂ la) as [H₂| H₂]; [ subst t₂ |  ].
                destruct (Bool.bool_dec b false); discriminate Hbnl₁.

                discriminate Hbnl₁.

               simpl in H.
               injection H; clear H; intros; subst.
               apply app_eq_nil in H; destruct H; subst.
               simpl in H0.
               injection H0; clear H0; intros; subst.
               simpl in Hbnl₁.
               unfold path_start in Hbnl₁; simpl in Hbnl₁.
               rewrite letter_dec_diag, bool_dec_negb_r
                 in Hbnl₁.
               discriminate Hbnl₁.

             discriminate Hbnl.

           revert Hel₃; clear; intros.
           induction el₁ as [| e₁]; [ discriminate Hel₃ |  ].
           simpl in Hel₃.
           injection Hel₃; clear Hel₃; intros; subst.
           destruct el₁; discriminate H.

bbb.

SearchAbout norm_combine.
Theorem toto : ∀ el₁ el₂ t d,
  norm_combine (el₁ ++ E t d :: E t (negb d) :: el₂) =
  norm_combine (el₁ ++ el₂.
Proof.
intros.
revert el₂ t d.
induction el₁ as [| e₁]; intros.
 do 2 rewrite app_nil_l.
Theorem toto : ∀ el t d,
  path (norm_combine (E t d :: E t (negb d) :: el)) =
  path (norm_combine el.
Proof.
intros; simpl.
remember (path (norm_combine el)) as bnl eqn:Hbnl.
symmetry in Hbnl.
destruct bnl as [| (b, n)].
 simpl; unfold path_start; simpl.
 rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.

 remember (norm_combine el) as nc eqn:Hnc; symmetry in Hnc.
 destruct (letter_dec t (path_start nc)) as [H₁| H₁].
  subst t.
  destruct (Bool.bool_dec (negb d) b) as [H₁| H₁].
   subst b; simpl.
   unfold path_start; simpl.
   rewrite Hbnl; simpl.
   rewrite letter_dec_diag, bool_dec_negb_r; simpl.
   exfalso; subst nc.

* putain, c'est faux... c'est mon norm_combine qu'est pas bon ? *)
bbb.


revert el t d Hbnl.
induction bnl as [| (b, n)]; intros.
simpl.
rewrite Hbnl; simpl.
unfold path_start; simpl.
rewrite letter_dec_diag, bool_dec_negb_r; reflexivity.

unfold path_start; simpl.
rewrite Hbnl; simpl.
destruct (zerop (S (length bnl) mod 2)) as [H₁| H₁].
remember (other_elem (last (norm_combine el))) as t₁ eqn:Ht₁.
symmetry in Ht₁.
destruct (letter_dec t t₁) as [H₂| H₂]; [ subst t₁ | ].
destruct (Bool.bool_dec (negb d) b) as [H₃| H₃]; [ subst b | ].
simpl.
rewrite H₁; simpl.
rewrite <- H₂, letter_dec_diag, bool_dec_negb_r.
simpl.
clear t H₂.

bbb.

intros.
induction el as [| e].
 simpl; unfold path_start; simpl.
 rewrite letter_dec_diag, bool_dec_negb_r.
 reflexivity.

 remember (E t (negb d) :: e :: el) as el'; simpl; subst el'.
 remember (path (norm_combine (E t (negb d) :: e :: el))) as bnl eqn:Hbnl .
 symmetry in Hbnl.
 destruct bnl as [| bn].
  simpl.
  destruct e as (t₁, d₁.
  remember (path (norm_combine el)) as bnl₁ eqn:Hbnl₁ .
  symmetry in Hbnl₁.
  destruct bnl₁ as [| (b₁, n₁)].
   simpl.
   remember (E t₁ d₁ :: el) as el'; simpl in Hbnl; subst el'.
   remember (path (norm_combine (E t₁ d₁ :: el))) as bnl₂ eqn:Hbnl₂ .
   symmetry in Hbnl₂.
   destruct bnl₂ as [| (b₂, n₂)]; [ discriminate Hbnl |  ].
   remember (path_start (norm_combine (E t₁ d₁ :: el))) as t₂ eqn:Ht₂ .
   symmetry in Ht₂; simpl in Ht₂.
   rewrite Hbnl₁ in Ht₂.
   unfold path_start in Ht₂; simpl in Ht₂; subst t₂.
   destruct (letter_dec t t₁) as [H₁| H₁]; [ subst t₁ | discriminate Hbnl ].
   destruct (Bool.bool_dec (negb d) b₂) as [H₁| H₁]; [ subst b₂ |  ].
    discriminate Hbnl.

    destruct n₂; [  | discriminate Hbnl ].
    simpl in Hbnl; subst bnl₂.
    apply negb_neq in H₁; subst b₂; simpl in Hbnl₂.
    rewrite Hbnl₁ in Hbnl₂; simpl in Hbnl₂.
    rewrite Hbnl₂; reflexivity.

   remember (path_start (norm_combine el)) as t₂ eqn:Ht₂ .
   symmetry in Ht₂.
   destruct (letter_dec t₁ t₂) as [H₁| H₁]; [ subst t₂ |  ].
    simpl in Hbnl.
    rewrite Hbnl₁ in Hbnl.
    rewrite <- H₁ in Hbnl.
    rewrite letter_dec_diag in Hbnl; simpl in Hbnl.
    destruct (Bool.bool_dec d₁ b₁) as [H₂| H₂]; [ subst b₁; exfalso |  ].
     simpl in Hbnl.
     remember (mknp (last (norm_combine el)) ((d₁, S n₁) :: bnl₁)) as np
       eqn:Hnp .
     destruct (letter_dec t (path_start np)) as [H₂| H₂].
      destruct (Bool.bool_dec (negb d) d₁); discriminate Hbnl.

      discriminate Hbnl.

     destruct n₁.
      simpl.
      simpl in Hbnl.
      destruct bnl₁ as [| (b₂, n₂)].
       discriminate Hbnl.

       remember (mknp (last (norm_combine el)) ((b₂, n₂) :: bnl₁)) as np
         eqn:Hnp .
       destruct (letter_dec t (path_start np)) as [H₃| H₃].
        destruct (Bool.bool_dec (negb d) b₂) as [H₄| H₄].
         discriminate Hbnl.

         destruct n₂.
          simpl in Hbnl.
          subst bnl₁.
          apply negb_neq in H₄.
          subst b₂; reflexivity.

          apply negb_neq in H₄.
          subst b₂.
          discriminate Hbnl.

        discriminate Hbnl.

      simpl in Hbnl; simpl.
      remember (mknp (last (norm_combine el)) ((d₁, n₁) :: bnl₁)) as np
        eqn:Hnp .
      destruct (letter_dec t (path_start np)) as [H₃| H₃].
       destruct (Bool.bool_dec (negb d) d₁) as [H₄| H₄].
        discriminate Hbnl.

        destruct n₁; [  | discriminate Hbnl ].
        simpl in Hbnl; subst bnl₁.
        apply negb_neq in H₄; subst d₁; reflexivity.

       discriminate Hbnl.

    simpl.
    remember (E t₁ d₁ :: el) as el'; simpl in Hbnl; subst el'.
    remember (path (norm_combine (E t₁ d₁ :: el))) as bnl eqn:Hbnl₂ .
    symmetry in Hbnl₂.
    destruct bnl as [| (b, n)]; [ discriminate Hbnl |  ].
    remember (norm_combine (E t₁ d₁ :: el)) as nc eqn:Hnc .
    symmetry in Hnc.
    destruct (letter_dec t (path_start nc)) as [H₂| H₂].
     destruct (Bool.bool_dec (negb d) b) as [H₃| H₃].
      discriminate Hbnl.

      destruct n; [  | discriminate Hbnl ].
      simpl in Hbnl; subst bnl.
      simpl in Hnc.
      rewrite Hbnl₁ in Hnc.
      rewrite Ht₂ in Hnc.
      destruct (letter_dec t₁ t₂) as [H₄| H₄]; [ contradiction |  ].
      subst nc.
      discriminate Hbnl₂.

     discriminate Hbnl.

  destruct bn as (b, n.
  remember (norm_combine (E t (negb d) :: e :: el)) as nc eqn:Hnc .
  destruct (letter_dec t (path_start nc)) as [H₁| H₁].
   destruct (Bool.bool_dec d b) as [H₂| H₂].
    subst b.
    simpl.
    destruct e as (t₁, d₁.
    remember (path (norm_combine el)) as bnl₁ eqn:Hbnl₁ .
    destruct bnl₁ as [| bn].
     symmetry in Hbnl₁.
     subst nc.
     simpl in Hbnl.
     rewrite Hbnl₁ in Hbnl.
     simpl in Hbnl.
     unfold path_start in Hbnl.
     simpl in Hbnl.
     simpl.
     destruct (letter_dec t t₁) as [H₂| H₂]; [ subst t₁ |  ].
      destruct (Bool.bool_dec (negb d) d₁) as [H₃| H₃].
       simpl in Hbnl.
       subst d₁.
       injection Hbnl; clear Hbnl; intros.
       exfalso; revert H1; apply Bool.no_fixpoint_negb.

       discriminate Hbnl.

      simpl in Hbnl.
      injection Hbnl; clear Hbnl; intros.
      exfalso; revert H1; apply Bool.no_fixpoint_negb.

     destruct bn as (b₁, n₁.
bbb.

subst np.
unfold path_start in H₃.
simpl in H₃.

bbb.

Theorem toto : ∀ el,
  norm_list el = []
  → path (norm_combine el) = [].
Proof.
intros el Hel.
Inspect 2.
apply norm_nil_iff in 

bbb.

 simpl in Hel₁.
 remember (norm_list el) as el₁ eqn:Hel₂.
 symmetry in Hel₂.
 destruct el₁ as [| e₂].
  injection Hel₁; clear Hel₁; intros; subst e₁.
  apply H₁, letter_opp_iff; split; reflexivity.

  destruct (letter_opp_dec e₁ e₂) as [H₂| H₂].
   subst el₁.
   destruct e₁ as (t₂, d₂.
   destruct e₂ as (t₃, d₃.
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
**)
  destruct el as [| e₂]; [ discriminate Hsc | ].
  simpl in Hsc.
  destruct (letter_opp_dec e₁ e₂) as [H₂| H₂].
   injection Hsc; clear Hsc; intros; subst.
   destruct e₂ as (t₁, d₁.
   apply letter_opp_iff in H₂.
   destruct H₂; subst t₁ d₁.
   remember (E t d :: E t (negb d) :: el₂) as el₃ eqn:Hel₃.
   simpl in Hel; subst el₃.
   rewrite norm_list_cancel_start in Hel.
   split; [ reflexivity | assumption ].

   destruct el as [| e₃]; [ discriminate Hsc | simpl in Hsc ].
   destruct (letter_opp_dec e₂ e₃) as [H₃| H₃].
    injection Hsc; clear Hsc; intros; subst.
    destruct e₃ as (t₁, d₁.
    apply letter_opp_iff in H₃.
    destruct H₃; subst t₁ d₁.
    remember (E t d :: E t (negb d) :: el₂) as el₃ eqn:Hel₃.
    simpl in Hel; subst el₃.
    rewrite norm_list_cancel_start in Hel.
    split; [ reflexivity | assumption ].

bbb.

Theorem toto : ∀ el pt,
  rotate_norm2 (norm_combine el) pt = fold_left rotate el pt.
Proof.
intros el pt.
unfold rotate_norm2.
remember (norm_combine el) as pa eqn:Hpa.
symmetry in Hpa.
destruct pa as (t, bnl.
revert el pt t Hpa.
induction bnl as [| (d, n)]; intros.
 simpl.
 destruct el as [| e]; [ reflexivity | ].
 exfalso; revert Hpa; clear; intros.
 revert e t Hpa.
 induction el as [| e₁]; intros; [ destruct e; discriminate Hpa | ].

bbb.

Theorem toto : ∀ el, norm_combine el = norm_combine (norm_list el.
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
  rotate_norm2_mod_3_loop (path_start nc) (path nc.

Theorem toto : ∀ el p,
  fold_left rotate_param_mod_3 (norm_list el) p =
  rotate_norm2_mod_3 (norm_combine el) p.
Proof.
intros el p.
remember (rotate_norm2_mod_3 (norm_combine el) p) as u eqn:Hu.
symmetry in Hu.
destruct u as ((a, b), c.
Inspect 10.
pose proof rotate_param_app (norm_list el.
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
destruct p as (((x, y), z), n.
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
**)
rewrite Hs in Hr.
rewrite fold_left_app in Hr; simpl in Hr.
remember (fold_left rotate_param_mod_3 el₁ (1, 0, 0)%Z) as r₁ eqn:Hr₁.
symmetry in Hr₁; destruct r₁ as ((a₁, b₁), c₁.
simpl in Hr.
injection Hr; clear Hr; intros; subst a b c.
revert a₁ b₁ c₁ Hr₁ el Hs.
induction el₁ as [| e₁] using rev_ind; intros.
 simpl in Hr₁.
 injection Hr₁; intros; subst; intros H; discriminate H.

 rewrite fold_left_app in Hr₁; simpl in Hr₁.
 simpl in Hr₁.
 destruct e₁ as (t₁, d₁.
 destruct t₁, d₁.
  remember (fold_left rotate_param_mod_3 el₁ (1, 0, 0)%Z) as r₂ eqn:Hr₂.
  symmetry in Hr₂; destruct r₂ as ((a₂, b₂), c₂.
  simpl in Hr₁.
  injection Hr₁; clear Hr₁; intros; subst.
  rewrite Z.add_0_l, Z.mod_mod; [ | intros H; discriminate H ].

Inspect 1.
bbb.
**)
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
 symmetry in Hr₁; destruct r₁ as ((a₁, b₁), c₁.


bbb.
**)
generalize Hr; intros H.
apply rotate_param_keep_dist in H.
do 2 rewrite Nat2Z.inj_mul in H; simpl in H.
rewrite Z.mul_1_r, Z.mul_1_l in H.
rewrite Z.pow_mul_r in H; [ | apply Zle_0_pos | apply Zle_0_nat ].
replace (3 ^ 2)%Z with 9%Z in H by reflexivity.
rename H into Hd.
**)
rewrite Hs in Hr.
remember (1%Z, 0%Z, 0%Z, O) as p eqn:Hp.
remember (fold_left rotate_param el₁ p) as u eqn:Hu.
destruct u as (((a₁, b₁), c₁), N₁.
symmetry in Hu.
generalize Hu; intros H.
apply rotate_param_app_bn with (n := 0) in H.
simpl in H.
rewrite Hr in H; simpl in H.
destruct H as (Ha, (Hb, Hc.
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
 destruct v as (((a₂, b₂), c₂), N₂.
 symmetry in Hv.
 generalize Hv; intros H.
 apply rotate_param_app with (e := e₁) (n := 0) in H.
 simpl in H; rewrite Hu in H; simpl in H.
 destruct e₁ as (t₁, d₁.
 destruct t₁, d₁.
  destruct H as (Ha, (Hb, Hc.
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
**)
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
   destruct e₁ as (t₁, d₁.
   destruct t₁, d₁.
Check rotate_param_app_bn.
bbb.

**)
revert el₁ a b c N Hs Hr.
induction el as [| e]; intros.
 symmetry in Hs; apply app_eq_nil in Hs.
 destruct Hs; discriminate.

 simpl in Hs, Hr.
 remember (norm_list el) as el₂ eqn:Hel; symmetry in Hel.
 destruct el₂ as [| e₂].
  simpl in Hr.
  destruct e as (t, d.
  destruct t.
   symmetry in Hs; apply app_eq_unit in Hs.
   destruct Hs as [(_, Hs)| (_, Hs)]; discriminate.

   destruct d; injection Hr; intros; subst; intros; discriminate.

  destruct (letter_opp_dec e e₂) as [He| He].
bbb.
**)
induction el as [| e] using rev_ind; intros.
 symmetry in Hs; apply app_eq_nil in Hs.
 destruct Hs; discriminate.

 rewrite Hs in Hr.
 rewrite fold_left_app in Hr.
 simpl in Hr.

bbb.
 destruct e as (t, d.
 remember (1%Z, 0%Z, 0%Z, 0) as p eqn:Hp.
 destruct t, d.
  remember (fold_left rotate_param el p) as u eqn:Hu.
  symmetry in Hu.
  destruct u as (((a₁, b₁), c₁), N₁.
  pose proof rotate_param_app_a1n el 0 p _ _ _ _ Hu as H.
  simpl in H.
  unfold "≡₃" in H.
  rewrite Hr in H; simpl in H.
  destruct H as (Ha, (Hb, Hc.
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
destruct s as (el.
unfold empty in Hs; simpl in Hs.
unfold rotate_1_0_0_param in Hr; simpl in Hr.
unfold rotate_1_0_0_param_of_list in Hr.
bbb.

remember (1%Z, 0%Z, 0%Z, 0) as p eqn:Hp.
revert a b c N Hr.
induction el as [| e] using rev_ind; intros.
 exfalso; apply Hs; reflexivity.

 destruct e as (t, d.
 destruct t, d.
  pose proof rotate_param_app_a1 el p as H.
  unfold "≡₃" in H.
  remember (fst3 (fold_left rotate_param (el ++ [ạ⁻¹]) p)) as u eqn:Hu.
  symmetry in Hu.
  destruct u as ((a₁, b₁), c₁.
  rewrite Hr in Hu.
  simpl in Hu.
  injection Hu; clear Hu; intros; subst a₁ b₁ c₁.
SearchAbout (fold_left _ (_ ++ _.
  rewrite fold_left_app in Hr.
  simpl in Hr.
  remember (fold_left rotate_param el p) as u eqn:Hu.
  destruct u as (((a₁, b₁), c₁), N₁.
  simpl in Hr.
  injection Hr; clear Hr; intros; subst a b c N.
  pose proof H _ _ _ _ (eq_refl _) as H₁.
  destruct H₁ as (H₁, (H₂, H₃.
bbb.

End Rotation.
