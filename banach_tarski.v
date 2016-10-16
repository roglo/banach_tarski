(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8.
Require Import List.
Require Import Relations.
Require Import NPeano Wf_nat.
Import ListNotations.

(* Misc *)

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

Theorem cons_comm_app : ∀ A (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. reflexivity. Qed.

Theorem cons_to_app : ∀ A (e : A) el, e :: el = [e] ++ el.
Proof. reflexivity. Qed.

Theorem fold_right_cons : ∀ A B f (x : A) (y : B) l,
  fold_right f x (y :: l) = f y (fold_right f x l).
Proof. reflexivity. Qed.

Theorem fold_right_single : ∀ A B (f : A → B → B) x y,
  fold_right f x [y] = f y x.
Proof. reflexivity. Qed.

Theorem app_repeat_diag : ∀ A (e : A) n,
  repeat e n ++ [e] = e :: repeat e n.
Proof.
intros.
induction n; [ reflexivity | ].
simpl; rewrite IHn; reflexivity.
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

Theorem split_app_eq : ∀ A (el₁ el₂ el₃ el₄ : list A),
  el₁ ++ el₂ = el₃ ++ el₄
  → { ∃ el, el₃ = el₁ ++ el ∧ el₂ = el ++ el₄ } +
    { ∃ el, el₁ = el₃ ++ el ∧ el₄ = el ++ el₂ }.
Proof.
intros A el₁ el₂ el₃ el₄ Hel.
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

(* Type-theoretical Choice Axiom *)
Axiom TTCA : ∀ (A : Type) (R : A → A → Prop), equiv A R →
  ∃ f : A → A, (∀ x : A, R x (f x)) ∧ (∀ x y, R x y → f x = f y).

(* TTCA implies excluded middle: do you believe that? Diaconescu! *)
Theorem EM : ∀ P, P ∨ ¬P.
Proof.
intros P.
set (R (x y : bool) := x = y ∨ P).
assert (He : equiv _ R).
 split; [ intros b; left; reflexivity | ].
 split.
  intros b c d Hbc [Hcd| Hcd]; [ subst c; assumption | right; assumption ].
  intros b c [Hbc| Hbc]; [ left; symmetry | right ]; assumption.

 destruct (TTCA bool R He) as (f & Hx & Hxy).
 destruct (Bool.bool_dec (f false) (f true)) as [H| H].
  destruct (Hx true) as [Ht| Ht]; [ | left; assumption ].
  destruct (Hx false) as [Hf| Hf]; [ | left; assumption ].
  rewrite <- Ht, <- Hf in H; discriminate H.

  right; intros H₁; apply H.
  apply Hxy; unfold R.
  right; assumption.
Qed.

Record choice_function {A} (R : A → A → Prop) f := mkcf
  { cf_repr_uniqueness : ∀ x y, R x y → f x = f y;
    cf_repr_membership : ∀ x, R x (f x) }.

(* Words *)

Inductive letter := la | lb.

Inductive free_elem := FE : letter → bool → free_elem.

Notation "'ạ'" := (FE la false).
Notation "'ạ⁻¹'" := (FE la true).
Notation "'ḅ'" := (FE lb false).
Notation "'ḅ⁻¹'" := (FE lb true).

Definition negf '(FE t d) := FE t (negb d).

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

Definition letter_opp '(FE l₁ d₁) '(FE l₂ d₂) :=
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
Defined.

Theorem letter_opp_inv : ∀ x d, letter_opp (FE x d) (FE x (negb d)).
Proof.
intros.
unfold letter_opp.
rewrite letter_dec_diag, bool_dec_negb_r.
constructor.
Qed.

Theorem letter_opp_iff : ∀ x₁ d₁ x₂ d₂,
  letter_opp (FE x₁ d₁) (FE x₂ d₂)
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

Theorem negf_involutive : ∀ e, negf (negf e) = e.
Proof.
intros (t, d); simpl.
rewrite Bool.negb_involutive; reflexivity.
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

Theorem negf_eq_eq : ∀ e₁ e₂, negf e₁ = negf e₂ → e₁ = e₂.
Proof.
intros e₁ e₂ Hn.
destruct e₁ as (t₁, d₁).
destruct e₂ as (t₂, d₂).
simpl in Hn.
injection Hn; intros H₁ H₂; subst.
apply negb_eq_eq in H₁; subst d₁; reflexivity.
Qed.

(* Normalizing *)

Fixpoint norm_list el :=
  match el with
  | nil => nil
  | e₁ :: el₁ =>
      match norm_list el₁ with
      | nil => e₁ :: nil
      | e₂ :: el₂ => if letter_opp_dec e₁ e₂ then el₂ else e₁ :: e₂ :: el₂
      end
  end.

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

 remember (FE t₁ d₁ :: el) as el₁ eqn:Hel₁.
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
  { ∃ el₁ t d el₂, el = el₁ ++ FE t d :: FE t (negb d) :: el₂ }.
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

Theorem norm_list_repeat : ∀ e n, norm_list (repeat e n) = repeat e n.
Proof.
intros e n.
induction n; [ reflexivity | simpl ].
rewrite IHn.
remember (repeat e n) as el eqn:Hel.
symmetry in Hel.
destruct el as [| e₁]; [ reflexivity | ].
destruct (letter_opp_dec e e₁) as [H| H]; [ | reflexivity ].
apply letter_opp_negf in H; subst e.
exfalso.
destruct n; [ discriminate Hel | ].
injection Hel; clear Hel; intros Hel H.
revert H; apply no_fixpoint_negf.
Qed.

Theorem norm_list_is_cons : ∀ el e el₁,
  norm_list el = e :: el₁ → norm_list el₁ = el₁.
Proof.
intros * H.
destruct (norm_list_dec el₁) as [H₁| H₁]; [ assumption | ].
destruct H₁ as (el₂ & t & d & el₃ & H₁).
subst el₁.
exfalso; revert H.
replace (FE t (negb d)) with (negf (FE t d)) by reflexivity.
rewrite app_comm_cons.
apply norm_list_no_consec.
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

Theorem norm_list_is_nil_between : ∀ e el,
  norm_list (negf e :: el ++ [e]) = [] ↔ norm_list el = [].
Proof.
assert (H : ∀ e el, norm_list el = [] → norm_list (negf e :: el ++ [e]) = []).
 intros e el Hn.
 rewrite cons_to_app, <- is_normal, Hn, app_nil_l.
 remember norm_list as f; simpl; subst f.
 rewrite norm_list_cancel2; reflexivity.

 intros e el.
 split; intros Hn; [ | apply H; assumption ].
 apply H with (e := negf e) in Hn.
 rewrite negf_involutive in Hn.
 remember norm_list as f; simpl in Hn; subst f.
 rewrite norm_list_cancel in Hn.
 rewrite <- app_assoc in Hn; simpl in Hn.
 rewrite norm_list_cancel_in, app_nil_r in Hn.
 assumption.
Qed.

(* Reversing paths *)

Definition rev_path el := map negf (rev el).

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

(* Misc about Reals *)

Require Import Reals Psatz Nsatz.

Notation "'ℝ'" := R.
Notation "'ℤ'" := Z.
Notation "'ℕ'" := nat.

Notation "'√'" := sqrt.

Theorem fold_Rsqr : ∀ a, (a * a = a²)%R.
Proof. reflexivity. Qed.

Theorem Rmul_div : ∀ x y z, (x * y / z = x / z * y)%R.
Proof. intros; lra. Qed.

Theorem Req_dec : ∀ x y : ℝ, { (x = y)%R } + { (x ≠ y)%R }.
Proof.
intros x y.
destruct (Rle_dec x y) as [H₁| H₁].
 destruct (Rle_dec y x) as [H₂| H₂].
  left; apply Rle_antisym; assumption.

  right; intros H; subst y; apply H₂, Rle_refl.

 right; intros H; subst y.
 apply H₁, Rle_refl.
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

(* Matrices and Points *)

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

Theorem mat_vec_mul_id : ∀ p, mat_vec_mul mat_id p = p.
Proof.
intros (x, y, z).
unfold mat_vec_mul; simpl.
progress repeat rewrite Rmult_0_l.
progress repeat rewrite Rmult_1_l.
progress repeat rewrite Rplus_0_l.
progress repeat rewrite Rplus_0_r.
reflexivity.
Qed.

Theorem mat_vec_mul_assoc : ∀ m₁ m₂ p,
  mat_vec_mul (m₁ * m₂)%mat p = mat_vec_mul m₁ (mat_vec_mul m₂ p).
Proof.
intros m₁ m₂ (x, y, z).
unfold mat_vec_mul.
simpl; f_equal; lra.
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

Definition on_sphere_ray r '(P x y z) := (x² + y² + z² = r)%R.

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

Theorem Pdec : ∀ p₁ p₂ : point, { p₁ = p₂ } + { p₁ ≠ p₂ }.
Proof.
 intros (x₁, y₁, z₁) (x₂, y₂, z₂).
 destruct (Req_dec x₁ x₂) as [| H₁]; [ subst x₂ | right ].
  destruct (Req_dec y₁ y₂) as [| H₂]; [ subst y₂ | right ].
   destruct (Req_dec z₁ z₂) as [| H₃]; [ subst z₂; left; reflexivity | right ].
   intros H; apply H₃.
   injection H; clear H; intros; subst; reflexivity.

   intros H; apply H₂.
   injection H; clear H; intros; subst; reflexivity.

  intros H; apply H₁.
  injection H; clear H; intros; subst; reflexivity.
Qed.

(* Orbits *)

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

Definition not_in_fixpoints p :=
  ∀ el, norm_list el ≠ [] → fold_right rotate p el ≠ p.

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

Definition orbit_selector := choice_function same_orbit.

Definition sphere '(P x y z) := (x² + y² + z² <= 1)%R.

Definition orbit_has_no_fixpoint p :=
  ∀ el p₁, same_orbit p p₁
  → norm_list el ≠ [] → fold_right rotate p₁ el ≠ p₁.

Definition sphere_but_fixpoints p := sphere p ∧ orbit_has_no_fixpoint p.

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
  sphere p
  → is_rotation_matrix m
  → sphere (mat_vec_mul m p).
Proof.
intros * His Hrm.
destruct p as (x, y, z).
remember (P x y z) as p eqn:HP.
remember (x² + y² + z²)%R as r eqn:Hr; symmetry in Hr.
assert (Hos : on_sphere_ray r p) by (subst p; assumption).
pose proof on_sphere_ray_after_rotation _ _ _ Hos Hrm as H.
unfold sphere in His.
unfold on_sphere_ray in H.
unfold sphere.
subst p; simpl in *.
rewrite H, <- Hos; assumption.
Qed.

Theorem in_sphere_after_rotate : ∀ p e,
  sphere p
  → sphere (rotate e p).
Proof.
intros * His.
apply in_sphere_after_rotation; [ assumption | ].
apply rotate_is_rotation_matrix.
Qed.

Theorem same_orbit_rotate : ∀ e p₁ p₂,
  same_orbit p₁ p₂
  → same_orbit (rotate e p₁) (rotate e p₂).
Proof.
intros * Hso.
destruct Hso as (el, Hr).
exists (e :: el ++ [negf e]); simpl.
rewrite fold_right_app; simpl.
rewrite rotate_neg_rotate.
f_equal; assumption.
Qed.

Theorem no_fixpoint_after_rotate : ∀ p e,
  orbit_has_no_fixpoint p
  → orbit_has_no_fixpoint (rotate e p).
Proof.
intros * His.
unfold orbit_has_no_fixpoint in His.
intros el p₁ Hso Hel.
remember (negf e :: rev_path el ++ e :: [])  as el₁ eqn:Hel₁.
remember (norm_list el₁) as el₂ eqn:Hel₂.
symmetry in Hel₂.
destruct el₂ as [| e₂].
 exfalso; subst el₁; apply Hel.
 apply norm_list_is_nil_between in Hel₂.
 rewrite <- rev_path_norm_list in Hel₂.
 apply rev_path_is_nil in Hel₂; assumption.

 apply same_orbit_rotate with (e := negf e) in Hso.
 rewrite rotate_neg_rotate in Hso.
 assert (Hn : norm_list el₁ ≠ []) by (rewrite Hel₂; intros H; discriminate H).
 pose proof His el₁ (rotate (negf e) p₁) Hso Hn.
 intros Hr; apply H; clear H.
 rewrite <- Hr at 1.
 rewrite <- fold_right_cons, <- fold_right_app.
 rewrite Hel₁, cons_comm_app, app_comm_cons.
 rewrite <- app_assoc.
 simpl; f_equal.
 rewrite rotate_rotate_norm.
 rewrite norm_list_cancel_in.
 rewrite <- rotate_rotate_norm.
 apply app_path_rev_path.
Qed.

(* Sets as Predicates *)

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
Definition subtract {A} (E₁ E₂ : A → Prop) :=
  λ x, E₁ x ∧ ¬ E₂ x.
Definition included {A} (E₁ E₂ : A → Prop) :=
  ∀ x, E₁ x → E₂ x.
Definition nth_set {A} i (Ei : list (A → Prop)) :=
  List.nth i Ei empty_set.

Notation "a = b" := (set_eq a b) : set_scope.
Notation "'∅'" := (empty_set) : set_scope.
Notation "E₁ '⋂' E₂" := (intersection E₁ E₂) (at level 40) : set_scope.
Notation "E₁ '⋃' E₂" := (union E₁ E₂) (at level 50, left associativity)
  : set_scope.
Notation "E₁ '\' E₂" := (subtract E₁ E₂) (at level 50) : set_scope.
Notation "E₁ '⊂' E₂" := (included E₁ E₂) (at level 60) : set_scope.
Notation "'∐' Es" := (union_list Es) (at level 60) : set_scope.
Notation "E .[ i ]" := (nth_set i E) (at level 1, format "E .[ i ]")
: set_scope.

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

Theorem set_eq_equiv {A} : ∀ (s := set_equiv) (E F : A → Prop),
  (E = F)%S
  → ∀ p, E p ↔ F p.
Proof. intros s * HEF; apply HEF. Qed.

Theorem union_empty_r : ∀ A s, s = set_equiv →
  ∀ (F : A → Prop), (F ⋃ ∅ = F)%S.
Proof.
intros * Hs *.
subst s; intros x.
split; intros H; [ | left; assumption ].
destruct H as [H| H]; [ assumption | contradiction ].
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

(* Partitions *)

Definition is_partition {A} {S : set_model A} E Ep :=
  (E = ∐ Ep)%S ∧
  ∀ i j, i ≠ j → (Ep.[i] ⋂ Ep.[j] = ∅)%S.

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

Theorem is_partition_union_subtract :
  ∀ A s, s = set_equiv →
  ∀ (F : A → Prop) P₁ P₂ Pl (B : A → Prop),
  is_partition F (P₁ :: P₂ :: Pl)
  → (B ⊂ P₂)%S
  → (∀ x, Decidable.decidable (B x))
  → is_partition F (P₁ ⋃ B :: P₂ \ B :: Pl)%S.
Proof.
intros A s Hs F P₁ P₂ Pl B Hp HB HBdec.
destruct Hp as (Hu & Hi).
split.
 unfold union_list, union, subtract, set_eq in Hu |-*.
 subst s; simpl in Hu |-*.
 intros x.
 split; intros H.
  pose proof Hu x as H₁.
  destruct H₁ as (H₁ & H₂).
  pose proof H₁ H as H₃.
  destruct H₃ as [H₃| H₃]; [ left; left; assumption | ].
  destruct H₃ as [H₃| H₃]; [ | right; right; assumption ].
  destruct (HBdec x) as [H₄| H₄]; [ left; right; assumption | ].
  right; left; split; assumption.

  apply Hu.
  destruct H as [[H₁| H₁]| [H₁| H₁]]; [ left; assumption | | | ].
   right; left; apply HB; assumption.

   right; left; destruct H₁; assumption.

   right; right; assumption.

 intros i j Hij; subst s.
 destruct i.
  unfold nth_set, intersection, union, subtract, set_eq; simpl.
  intros x.
  split; [ | contradiction ].
  intros (H₁, H₂).
  destruct j; [ apply Hij; reflexivity | clear Hij ].
  destruct H₁ as [H₁| H₁].
   apply Hi with (i := O) (j := S j); [ intros H; discriminate H | ].
   unfold nth_set, intersection; simpl.
   split; [ assumption | ].
   destruct j; [ destruct H₂; assumption | assumption ].

   apply Hi with (i := 1%nat) (j := S j).
    destruct j; [ destruct H₂; contradiction | intros H; discriminate H ].

    unfold nth_set, intersection; simpl.
    split; [ apply HB; assumption | ].
    destruct j; [ destruct H₂; contradiction | assumption ].

  unfold nth_set, intersection, union, subtract, set_eq; simpl.
  intros x.
  split; [ | contradiction ].
  intros (H₁ & H₂).
  destruct j.
   destruct H₂ as [H₂| H₂].
    apply Hi with (i := O) (j := S i); [ intros H; discriminate H | ].
    unfold nth_set, intersection; simpl.
    split; [ assumption | ].
    destruct i; [ destruct H₁; assumption | assumption ].

    apply Hi with (i := 1%nat) (j := S i).
     destruct i; [ | intros H; discriminate H ].
     destruct H₁; contradiction.

     unfold nth_set, intersection; simpl.
     split; [ apply HB; assumption | ].
     destruct i; [ apply HB; assumption | assumption ].

  apply Hi with (i := S i) (j := S j).
   intros H; apply Hij; assumption.

   unfold nth_set, intersection; simpl.
   split.
    destruct i; [ destruct H₁; assumption | assumption ].

    destruct j; [ destruct H₂; assumption | assumption ].
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

(* Orbit representant *)

Class sel_model {A} := mkos
  { os_fun : A → A }.

Definition EE {os : sel_model} :=
  λ p, sphere_but_fixpoints p ∧ p = os_fun p.
Definition SS {os : sel_model} e := λ p,
  sphere_but_fixpoints p ∧
  ∃ el el₁,
  norm_list el = e :: el₁ ∧ fold_right rotate (os_fun p) el = p.

Definition on_orbit_by_seq_of e {os : sel_model} p :=
  ∃ n, fold_right rotate (os_fun p) (repeat e (S n)) = p.

Definition B {os : sel_model} := λ p,
  sphere_but_fixpoints p ∧ on_orbit_by_seq_of ạ⁻¹ p.

Definition rot e (E : point → Prop) := λ p, E (rotate (negf e) p).
Definition xtransl dx (E : point → Prop) '(P x y z) := E (P (x - dx) y z).

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

Theorem decompose_2a_contrad_case :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ p, (EE ⋃ SS ạ ⋃ B)%S p
  → rot ạ (SS ạ⁻¹ \ B)%S p
  → False.
Proof.
intros * (Hoe, Ho) * Hos * Hi Hj.
 assert (Hfr : f (rotate ạ⁻¹ p) = f p).
  apply Hoe; exists (ạ :: []); apply rotate_neg_rotate.

   destruct Hj as (Hs & Hb); simpl in Hs, Hb; apply Hb; clear Hb.
   split; [ destruct Hs; assumption | ].
   destruct Hi as [[Hi| Hi] | Hi].
    destruct Hs as (Hrnf & el & el₁ & Hn & Hr).
    destruct Hi as (Hnf & Hp); subst os; simpl in Hp.
    exists O; simpl.
    rewrite Hfr, <- Hp; reflexivity.

    eapply not_start_with_rot in Hi; try eassumption; [ contradiction | ].
    split; assumption.

    destruct Hi as (Hnf, Hoo).
    destruct Hoo as (n, Hoo).
    unfold on_orbit_by_seq_of.
    remember S as g; subst os; simpl in Hoo; simpl; subst g.
    rewrite Hfr; simpl.
    exists (S n).
    rewrite Hoo; reflexivity.
Qed.

Theorem r_decomposed_5 :
  ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints [EE; SS ạ; SS ạ⁻¹; SS ḅ; SS ḅ⁻¹].
Proof.
intros s Hs f (Hoe, Ho) os Hos; subst os s.
split.
*intros p.
 split.
 -intros Hnf.
  unfold union_list; simpl; unfold union.
  destruct (Pdec p (f p)) as [H₁| H₁]; [ left; split; assumption | ].
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
  ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints
      [(EE ⋃ SS ạ ⋃ B)%S; (SS ạ⁻¹ \ B)%S; SS ḅ; SS ḅ⁻¹].
Proof.
intros s Hs f HoeHo os Hos.
pose proof r_decomposed_5 s Hs f HoeHo os Hos as H.
destruct HoeHo as (Hoe, Ho).
eapply is_partition_group_first_2_together in H; [ | assumption ].
apply is_partition_union_subtract; [ assumption | assumption | | ].
 intros p bm; subst os.
 destruct bm as (Ha & n & Hr); remember S as g; simpl in Hr; subst g.
 split; [ assumption | ].
 exists (repeat ạ⁻¹ (S n)), (repeat ạ⁻¹ n).
 split; [ apply norm_list_repeat | assumption ].

 intros p; apply EM.
Qed.

Theorem r_decomposed_2 :
  ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ e,
    is_partition sphere_but_fixpoints [SS e; rot e (SS (negf e))].
Proof.
intros s Hs f (Hoe, Ho) os Hos e; subst os s.
split.
*intros p.
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

Add Parametric Morphism {A} : (@List.nth (A → Prop))
  with signature eq ==> eq ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as nth_set_morph.
Proof.
intros i l a b Hab.
revert i.
induction l as [| y]; intros; [ destruct i; apply Hab | ].
destruct i; simpl; [ reflexivity | apply IHl ].
Qed.

Theorem rev_path_repeat : ∀ e n, rev_path (repeat e n) = repeat (negf e) n.
Proof.
intros e n.
induction n; [ reflexivity | simpl ].
rewrite rev_path_cons, rev_path_single, IHn.
apply app_repeat_diag.
Qed.

Theorem r_decomposed_2_a :
  ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints [(EE ⋃ SS ạ ⋃ B)%S; rot ạ (SS ạ⁻¹ \ B)%S].
Proof.
intros s Hs f (Hoe, Ho) os Hos; subst s.
split.
*intros p.
 assert (Hfr : f (rotate ạ⁻¹ p) = f p).
  apply Hoe; exists (ạ :: []); apply rotate_neg_rotate.

  split.
  -intros Hnf.
   unfold union_list; simpl; unfold union.
   pose proof Ho p as H.
   apply same_orbit_sym in H.
   destruct H as (el, Hel).
   remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
   destruct el₁ as [| e₁].
    +rewrite rotate_rotate_norm, Hel₁ in Hel; simpl in Hel.
    clear el Hel₁.
    left; left; left.
    split; [ assumption | subst os; symmetry; assumption ].

    +destruct e₁ as (t, d); destruct t.
     destruct d.
      destruct (EM (B p)) as [HB| HB]; [ left; right; assumption | ].
      right; left; simpl.
      split.
       unfold SS; simpl.
       split.
        destruct Hnf as (His, Hnf).
        split; [ apply in_sphere_after_rotate; assumption | ].
        apply no_fixpoint_after_rotate; assumption.

        subst os; simpl.
        rewrite Hfr.
        exists (ạ⁻¹ :: el), (norm_list el).
        split; [ | simpl; f_equal; assumption ].
        simpl; rewrite Hel₁; reflexivity.

       simpl; intros (Haf & n & Hoo); apply HB; clear HB.
       split; [ assumption | ].
       unfold on_orbit_by_seq_of in Hoo |-*.
       remember S as g;
       subst os; simpl in Hoo |-*; subst g.
       rewrite Hfr in Hoo; simpl in Hoo.
       apply f_equal with (f := rotate (FE la false)) in Hoo.
       do 2 rewrite rotate_rotate_neg in Hoo.
       destruct n; [ | exists n; assumption ].
       simpl in Hoo.
       rewrite Hoo in Hel.
       destruct Hnf as (His & Hoh).
       unfold orbit_has_no_fixpoint in Hoh.
       exfalso; revert Hel.
       apply Hoh; [ reflexivity | ].
       rewrite Hel₁; intros H; discriminate H.

      left; left; right.
      split; [ assumption | ].
      exists el, el₁; subst os.
      split; assumption.

     right; left.
     split; simpl.
      split.
       destruct Hnf as (His & Hnf).
       split; [ apply in_sphere_after_rotate; assumption | ].
       apply no_fixpoint_after_rotate; assumption.

       subst os; simpl; rewrite Hfr.
       exists (ạ⁻¹ :: el), (norm_list el).
       split; [ | simpl; f_equal; assumption ].
       simpl; rewrite Hel₁; reflexivity.

      intros (Hnf₂, Hoo).
      subst os; simpl in Hoo.
      unfold on_orbit_by_seq_of in Hoo; simpl in Hoo.
      rewrite Hfr in Hoo.
      destruct Hoo as (n, Hr).
      apply f_equal with (f := rotate (FE la false)) in Hr.
      do 2 rewrite rotate_rotate_neg in Hr.
      destruct n.
       simpl in Hr; rewrite Hr in Hel.
       destruct Hnf as (His, Hoh).
       revert Hel; apply Hoh; [ reflexivity | ].
       rewrite Hel₁; intros H; discriminate H.

       apply rotate_rev_path in Hr.
       rewrite <- Hr, <- fold_right_app in Hel.
       destruct Hnf as (His, Hoh).
       revert Hel.
       apply Hoh; [ reflexivity | ].
       replace el with ([] ++ el) by reflexivity.
       rewrite <- app_assoc, <- is_normal, Hel₁, app_nil_l.
       rewrite rev_path_repeat.
       remember norm_list as g; remember S as h; simpl; subst g h.
       rewrite cons_to_app, app_assoc.
       intros H.
       eapply norm_list_app_is_nil in H.
        simpl in H.
        apply f_equal with (f := rev_path) in H.
        rewrite rev_path_involutive in H.
        rewrite <- app_repeat_diag in H.
        rewrite rev_path_app in H; simpl in H.
        discriminate H.

        unfold app; rewrite <- Hel₁; symmetry.
        apply norm_list_idemp.

        symmetry; apply norm_list_repeat.

 -intros HE.
  simpl in HE.
  destruct HE as [[[HE| HE]| HE]| [HE| HE]]; try (destruct HE; assumption).
  destruct HE as (((His & Hoo) & HE) & HB).
  split.
   apply in_sphere_after_rotate with (e := ạ) in His.
   rewrite rotate_rotate_neg in His; assumption.

   apply no_fixpoint_after_rotate with (e := ạ) in Hoo.
   rewrite rotate_rotate_neg in Hoo; assumption.

*intros i j Hij p.
 assert (Hfr : f (rotate ạ⁻¹ p) = f p).
  apply Hoe; exists (ạ :: []); apply rotate_neg_rotate.

  split; [ | contradiction ].
  unfold nth_set.
  intros (Hi, Hj); unfold empty_set.
  destruct i; [ simpl in Hi | ].
   destruct j; [ exfalso; apply Hij; reflexivity | clear Hij ].
   destruct j; [ simpl in Hj | destruct j; contradiction ].
   eapply decompose_2a_contrad_case; try eassumption; split; assumption.

   destruct i; [ simpl in Hi | destruct i; contradiction ].
   destruct j.
    eapply decompose_2a_contrad_case; try eassumption; split; assumption.

    destruct j; [ apply Hij; reflexivity | clear Hij ].
    destruct j; contradiction.
Qed.

Theorem r_decomposed_2_b :
  ∀ s, s = set_equiv
  → ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints [SS ḅ; rot ḅ (SS ḅ⁻¹)].
Proof.
intros.
eapply r_decomposed_2; eassumption.
Qed.

Add Parametric Morphism {A} : (@intersection A)
  with signature
    (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as intersection_morph.
Proof.
intros E E' HE F F' HF.
unfold intersection; intros p.
split; intros (H₁, H₂).
 split; [ apply HE; assumption | apply HF; assumption ].
 split; [ apply HE; assumption | apply HF; assumption ].
Qed.

Add Parametric Morphism {A} : (@intersection A)
  with signature
    (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv) ==> eq ==> iff
  as intersection_iff_morph.
Proof.
intros E E' HE F F' HF a.
unfold intersection.
split; intros (H₁, H₂).
 split; [ apply HE; assumption | apply HF; assumption ].
 split; [ apply HE; assumption | apply HF; assumption ].
Qed.

Add Parametric Morphism {A} : (@union A)
  with signature
    (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as union_morph.
Proof.
intros E E' HE F F' HF.
intros p.
split.
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
Qed.

Add Parametric Morphism {A} : (@union A)
  with signature
    (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv) ==> eq ==> iff
  as union_iff_morph.
Proof.
intros E E' HE F F' HF.
intros p.
split.
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
Qed.

(* Transformation group *)

Inductive G :=
  | Rot : free_elem → G
  | Xtransl : ℝ → G
  | Comb : G → G → G.

Fixpoint app_gr f p :=
  match f with
  | Rot e => rot e p
  | Xtransl dx => xtransl dx p
  | Comb g h => app_gr g (app_gr h p)
  end.

Fixpoint app_gr_point f p :=
  match f with
  | Rot e => rotate (negf e) p
  | Xtransl dx => match p with P x y z => P (x - dx) y z end
  | Comb g h => app_gr_point h (app_gr_point g p)
  end.

Theorem app_gr_app_gr_point : ∀ g E p, app_gr g E p → E (app_gr_point g p).
Proof.
intros * Hp.
revert E p Hp.
induction g; intros; [ assumption | destruct p; assumption | ].
simpl in Hp; simpl.
apply IHg1 in Hp.
apply IHg2 in Hp.
assumption.
Qed.

Theorem gr_subst : ∀ (s := set_equiv) g E F,
  (E = F)%S → ∀ p, app_gr g E p → app_gr g F p.
Proof.
intros s * HEF * HE.
revert E F p HEF HE.
induction g as [e| dx | g IHg h IHh]; intros.
 apply HEF, HE.

 destruct p as (x, y, z).
 apply HEF, HE.

 simpl in HE; simpl.
 eapply IHg; [ | eassumption ].
 split; intros H; [ eapply IHh; eassumption | ].
 eapply IHh; [ symmetry; eassumption | eassumption ].
Qed.

Add Parametric Morphism : app_gr
with signature eq ==> (@set_eq _ set_equiv) ==> eq ==> iff
as app_gr_morph_iff.
Proof.
intros g p q Hpq r.
split; intros H; [ eapply gr_subst; eassumption | ].
symmetry in Hpq; eapply gr_subst; eassumption.
Qed.

Add Parametric Morphism : app_gr
with signature eq ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
as app_gr_morph.
Proof.
intros g p q Hpq r.
split; intros H; [ eapply gr_subst; eassumption | ].
symmetry in Hpq; eapply gr_subst; eassumption.
Qed.

Theorem app_gr_empty_set : ∀ (s := set_equiv) f, (app_gr f ∅ = ∅)%S.
Proof.
intros s * p.
split; intros H; [ | contradiction ].
revert p H.
induction f; intros; [ contradiction | destruct p; contradiction | ].
simpl in H.
eapply gr_subst in H; [ apply IHf1 in H; contradiction | ].
split; [ apply IHf2 | intros; contradiction ].
Qed.

Theorem group_union_distr : ∀ (s := set_equiv) g E₁ E₂,
  (app_gr g (E₁ ⋃ E₂) = app_gr g E₁ ⋃ app_gr g E₂)%S.
Proof.
intros s *; subst s.
revert E₁ E₂.
induction g as [e| dx | g IHg h IHh ]; intros; simpl.
 intros p; split; intros H; assumption.

 intros (x, y, z); split; intros H; assumption.

 intros p.
 split.
  intros H; apply IHg.
  rewrite <- IHh; assumption.

  intros H; apply IHg in H.
  rewrite IHh; assumption.
Qed.

Theorem group_union_list_distr : ∀ (s := set_equiv) f PL,
  (app_gr f (∐ PL) = ∐ map (app_gr f) PL)%S.
Proof.
intros s *.
induction PL as [| P PL].
intros p; split; intros H; [ | contradiction ].
apply app_gr_empty_set in H; contradiction.
simpl in IHPL; simpl.
intros p; split; intros H.
 apply group_union_distr in H.
 destruct H as [H| H]; [ left; assumption | right; apply IHPL; assumption ].

 apply group_union_distr.
 destruct H as [H| H]; [ left; assumption | right; apply IHPL; assumption ].
Qed.

Theorem partition_group_map : ∀ (s := set_equiv) f, orbit_selector f →
  ∀ (F : point → Prop) P g,
  is_partition F P → is_partition (app_gr g F) (map (app_gr g) P).
Proof.
intros s f Ho F P * HP.
unfold is_partition in HP |-*.
destruct HP as (HF, HP).
split.
 induction g as [e| dx | g IHg h IHh ]; intros; simpl.
  intros p.
  split.
   intros Hr.
   revert F HF Hr.
   induction P as [| P PL]; intros; [ apply HF in Hr; contradiction | ].
   simpl in HF; simpl.
   generalize Hr; intros H.
   apply HF in H; simpl in H.
   destruct H as [H| H]; [ left; assumption | right ].
   eapply IHPL; [ | reflexivity | eassumption ].
   intros i j Hij.
   unfold set_eq; simpl; intros y.
   assert (HSij : S i ≠ S j).
    intros HSij; apply Hij, Nat.succ_inj; assumption.

    pose proof HP (S i) (S j) HSij y as HP; simpl in HP.
    destruct HP as (HQ, _).
    split; [ intros (HPi, HPj) | contradiction ].
    apply HQ; split; assumption.

   intros Hme.
   revert F HF.
   induction P as [| P PL]; intros; [ contradiction | ].
   simpl in HF, Hme; apply HF.
   destruct Hme as [Hme| Hme]; [ left; assumption | ].
   right; simpl.
   apply IHPL; [ | assumption | intros y; split; intros H; apply H ].
   intros i j Hij y.
   assert (HSij : S i ≠ S j).
    intros HSij; apply Hij, Nat.succ_inj; assumption.

    pose proof HP (S i) (S j) HSij y as HP; simpl in HP.
    destruct HP as (HQ, _).
    split; [ intros (HPi, HPj) | contradiction ].
    apply HQ; split; assumption.

  intros (x, y, z).
  split.
   intros Hp.
   revert F HF Hp.
   induction P as [| P PL]; intros.
    unfold set_eq in HF; simpl in HF.
    apply HF in Hp; contradiction.

    simpl in HF; simpl.
    generalize Hp; intros H.
    apply HF in H; simpl in H.
    destruct H as [H| H]; [ left; assumption | right ].
    eapply IHPL; [ | simpl; reflexivity | eassumption ].
    intros i j Hij.
    unfold set_eq; simpl; intros q.
    assert (HSij : S i ≠ S j).
     intros HSij; apply Hij, Nat.succ_inj; assumption.

     pose proof HP (S i) (S j) HSij q as HP; simpl in HP.
     destruct HP as (HQ, _).
     split; [ intros (HPi, HPj) | contradiction ].
     apply HQ; split; assumption.

   intros Hme.
   revert F HF.
   induction P as [| P PL]; intros; [ contradiction | ].
   simpl in HF, Hme; apply HF.
   destruct Hme as [Hme| Hme]; [ left; assumption | ].
   right; simpl.
   apply IHPL; [ | assumption | intros q; split; intros H; apply H ].
   intros i j Hij q.
   assert (HSij : S i ≠ S j).
    intros HSij; apply Hij, Nat.succ_inj; assumption.

    pose proof HP (S i) (S j) HSij q as HP; simpl in HP.
    destruct HP as (HQ, _).
    split; [ intros (HPi, HPj) | contradiction ].
    apply HQ; split; assumption.

  intros p.
  split.
   intros Hgh.
   revert F HF IHg IHh Hgh.
   induction P as [| P PL]; intros.
    rewrite IHh in Hgh; simpl in Hgh.
    eapply app_gr_empty_set, Hgh.

    rewrite IHh in Hgh.
    simpl in Hgh.
    apply group_union_distr in Hgh.
    destruct Hgh as [Hgh| Hgh]; [ left; assumption | right ].
    eapply IHPL.
     intros i j Hij.
     unfold set_eq; simpl; intros y.
     assert (HSij : S i ≠ S j).
      intros HSij; apply Hij, Nat.succ_inj; assumption.

      pose proof HP (S i) (S j) HSij y as HP; simpl in HP.
      destruct HP as (HQ, _).
      split; [ intros (HPi, HPj) | contradiction ].
      apply HQ; split; assumption.

     reflexivity.

     apply group_union_list_distr.

     apply group_union_list_distr.

     pose proof group_union_list_distr h PL.
     rewrite <- H in Hgh; assumption.

   intros Hgh.
   revert F HF IHg IHh Hgh.
   induction P as [| P PL]; intros; [ contradiction | ].
   destruct Hgh as [Hgh| Hgh].
    rewrite IHh; simpl.
    rewrite set_eq_equiv; [ | rewrite group_union_distr; reflexivity ].
    left; assumption.

    rewrite HF; simpl.
    rewrite set_eq_equiv; [ | rewrite group_union_distr; reflexivity ].
    rewrite set_eq_equiv; [ | rewrite group_union_distr; reflexivity ].
    right.
    rewrite group_union_list_distr.
    rewrite set_eq_equiv; [ | rewrite group_union_list_distr; reflexivity ].
    rewrite map_map; assumption.

 intros i j Hij p.
 split; intros H; [ | contradiction ].
 unfold nth_set in H.
 rewrite <- app_gr_empty_set with (f := g) in H.
 do 2 rewrite map_nth in H.
 destruct H as (Hi, Hj).
 pose proof HP i j Hij (app_gr_point g p) as Hp.
 unfold nth_set in Hp.
 destruct Hp as (Hpi, _).
 apply Hpi; clear Hpi.
 split.
  clear - Hi.
  rename P into Ql.
  revert p Ql Hi.
  induction i; intros.
   destruct Ql as [| Q Ql]; [ apply app_gr_empty_set in Hi; contradiction | ].
   simpl in Hi; simpl.
   apply app_gr_app_gr_point; assumption.

   destruct Ql as [| Q Ql]; [ apply app_gr_empty_set in Hi; contradiction | ].
   simpl in Hi; simpl.
   apply IHi; assumption.

  clear - Hj.
  rename P into Ql.
  revert p Ql Hj.
  induction j; intros.
   destruct Ql as [| Q Ql]; [ apply app_gr_empty_set in Hj; contradiction | ].
   simpl in Hj; simpl.
   apply app_gr_app_gr_point; assumption.

   destruct Ql as [| Q Ql]; [ apply app_gr_empty_set in Hj; contradiction | ].
   simpl in Hj; simpl.
   apply IHj; assumption.
Qed.

(* Banach-Tarski *)

Definition equidecomposable (s : set_model point) E₁ E₂ :=
  ∃ P₁ P₂, is_partition E₁ P₁ ∧ is_partition E₂ P₂ ∧ length P₁ = length P₂ ∧
  List.Forall2 (λ S₁ S₂, ∃ g, app_gr g S₁ = S₂) P₁ P₂.

Theorem Banach_Tarski_paradox_but_fixpoints :
  equidecomposable set_equiv sphere_but_fixpoints
    (xtransl 3 sphere_but_fixpoints ⋃ xtransl 6 sphere_but_fixpoints)%S.
Proof.
set (s := set_equiv).
pose proof TTCA _ same_orbit equiv_same_orbit as H.
destruct H as (f & Hu & Hm).
remember (mkcf _ _ f Hm Hu) as Hosf.
remember (mkos _ f) as os eqn:Hos.
clear HeqHosf.
set (A₁ := (EE ⋃ SS ạ ⋃ B)%S).
set (A₂ := (SS ạ⁻¹ \ B)%S).
set (A₃ := SS ḅ).
set (A₄ := SS ḅ⁻¹).
exists [A₁; A₂; A₃; A₄].
exists
  (map (xtransl 3) [A₁; rot ạ A₂] ++
   map (xtransl 6) [A₃; rot ḅ A₄]); simpl.
split.
 subst A₁ A₂ A₃ A₄.
 eapply r_decomposed_4; try eassumption; reflexivity.

 split.
  subst s; remember set_equiv as s eqn:Hs.
  pose proof r_decomposed_2_a s Hs f Hosf os Hos as Ha.
  pose proof r_decomposed_2_b s Hs f Hosf os Hos as Hb.
  subst s; set (s := set_equiv).
  eapply partition_group_map with (g := Xtransl 3) in Ha; try eassumption.
  eapply partition_group_map with (g := Xtransl 6) in Hb; try eassumption.
  eapply partition_union in Hb; [ | reflexivity | | apply Ha ].
   apply Hb.

   unfold intersection, set_eq; subst s; intros (x, y, z).
   split; [ intros (H₁, H₂) | contradiction ].
   simpl in H₁, H₂.
   unfold empty_set; simpl.
   destruct H₁ as (H₁, H₃).
   destruct H₂ as (H₂, H₄).
   unfold sphere in H₁, H₂.
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
   destruct (Rcase_abs (x - 3)), (Rcase_abs (x - 6)); lra.

  split; [ reflexivity | ].
  constructor; [ exists (Xtransl 3); reflexivity | ].
  constructor; [ exists (Comb (Xtransl 3) (Rot ạ)); reflexivity | ].
  constructor; [ exists (Xtransl 6); reflexivity | ].
  constructor; [ exists (Comb (Xtransl 6) (Rot ḅ)); reflexivity | ].
  constructor.
Qed.

Check Banach_Tarski_paradox_but_fixpoints.

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
  let r := √ (x² + y² + z²) in
  P (k * x / r) (k * y / r) (k * z / r).

Definition sphere_fixpoint : point → Prop :=
  λ p, ∃ el k,
  norm_list el ≠ [] ∧
  p = rotation_fixpoint (fold_right mat_mul mat_id (map mat_of_elem el)) k.

Definition orbit_has_fixpoint : point → Prop :=
  λ p, ∃ p', same_orbit p p' ∧ sphere_fixpoint p'.

Definition sphere_points_in_orbits_having_fixpoint : point → Prop :=
  λ p, sphere p ∧ orbit_has_fixpoint p.

Theorem matrix_fixpoint_ok : ∀ m p k,
  is_rotation_matrix m
  → p = rotation_fixpoint m k
  → mat_vec_mul m p = p.
Proof.
intros m p k Hrm Hn.
subst p.
unfold rotation_fixpoint.
remember (√ ((a₃₂ m - a₂₃ m)² + (a₁₃ m - a₃₁ m)² + (a₂₁ m - a₁₂ m)²)) as r.
setoid_rewrite Rmul_div.
remember (k / r)%R as kr.
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
clear Heqr Heqkr.
f_equal; nsatz.
Qed.

Theorem rotate_vec_mul : ∀ el p,
  fold_right rotate p el
  = mat_vec_mul (fold_right mat_mul mat_id (map mat_of_elem el)) p.
Proof.
intros el p.
induction el as [| e]; [ rewrite mat_vec_mul_id; reflexivity | simpl ].
rewrite IHel, mat_vec_mul_assoc; reflexivity.
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

Theorem sphere_fixpoint_prop : ∀ p el,
  norm_list el ≠ []
  → fold_right rotate p el = p
  → sphere_fixpoint p.
Proof.
intros * Hn Hr.
unfold sphere_fixpoint.
rewrite rotate_vec_mul in Hr.
exists el, 1%R.
split; [ assumption | ].
remember (fold_right mat_mul mat_id (map mat_of_elem el)) as m eqn:Hm.
generalize Hm; intros Hrm.
apply path_is_rotation in Hrm.
SearchAbout rotation_fixpoint.
bbb.

eapply matrix_fixpoint_ok with (k := 1%R) in Hrm; [ | reflexivity ].
bbb.

Theorem sphere_partition_by_fixpoints :
  let s := set_equiv in
  is_partition sphere
    [sphere_but_fixpoints;
     sphere_points_in_orbits_having_fixpoint].
Proof.
intros s.
split.
 unfold set_eq, union_list; subst s; simpl; intros p.
 split.
  intros Hs; rewrite union_empty_r; [ | reflexivity ].
  unfold sphere_but_fixpoints, sphere_points_in_orbits_having_fixpoint.
  unfold union.
  destruct (EM (orbit_has_fixpoint p)) as [Hoh| Hoh].
   right; split; assumption.

   left; split; [ assumption | ].
   unfold orbit_has_fixpoint in Hoh.
   unfold orbit_has_no_fixpoint.
   intros * Hso Hn.
   assert (H : ∀ p', not (same_orbit p p' ∧ sphere_fixpoint p')).
    intros p' H; apply Hoh.
    exists p'; assumption.

    clear Hoh; rename H into Hoh.
    pose proof Hoh p₁ as Hp.
    intros H; apply Hp; clear Hp.
    split; [ assumption | ].
    eapply sphere_fixpoint_prop; eassumption.

bbb.

    exists el, 1%R.
    split; [ assumption | ].
    remember (fold_right mat_mul mat_id (map mat_of_elem el)) as m eqn:Hm.
    unfold rotation_fixpoint.
    progress repeat rewrite Rmult_1_l.
    remember (√((a₃₂ m - a₂₃ m)² + (a₁₃ m - a₃₁ m)² + (a₂₁ m - a₁₂ m)²)) as r.
    rename Heqr into Hr.
    destruct p₁ as (x₁, y₁, z₁).
    unfold rotate in H.
    f_equal.
Inspect 1.
bbb.

Focus 2.
  intros [(H, _) | [(H, _)| H]]; [ assumption | assumption | contradiction ].


bbb.

Theorem Banach_Tarski_paradox :
  equidecomposable set_equiv sphere (xtransl 3 sphere ⋃ xtransl 6 sphere)%S.
Proof.
set (s := set_equiv).
pose proof TTCA _ same_orbit equiv_same_orbit as H.
destruct H as (f & Hu & Hm).
remember (mkcf _ _ f Hm Hu) as Hosf.
remember (mkos _ f) as os eqn:Hos.
clear HeqHosf.
set (A₁ := (EE ⋃ SS ạ ⋃ B)%S).
set (A₂ := (SS ạ⁻¹ \ B)%S).
set (A₃ := SS ḅ).
set (A₄ := SS ḅ⁻¹).
exists [A₁; A₂; A₃; A₄].
exists
  (map (xtransl 3) [A₁; rot ạ A₂] ++
   map (xtransl 6) [A₃; rot ḅ A₄]); simpl.
split.
 subst A₁ A₂ A₃ A₄.

bbb.
