(* Banach-Tarski paradox. *)
(* Coq v8.6 *)

Require Import Utf8 List Relations NPeano Wf_nat.
Import ListNotations.
Require Import Misc Words.

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
induction el as [| e₁]; intros; [ intros H; now destruct el₁ | ].
simpl; remember (norm_list el) as nl eqn:Hnl; symmetry in Hnl.
destruct nl as [| e₂].
 clear; intros H.
 destruct el₁ as [| e₂]; intros; [ easy | simpl in H ].
 injection H; clear H; intros; subst e₂.
 now destruct el₁.

 destruct (letter_opp_dec e₁ e₂) as [H₁| H₁].
  intros H; subst nl.
  pose proof IHel (e₂ :: el₁) as H₂; simpl in H₂.
  now apply H₂.

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
    now apply H₂.

    simpl; intros H.
    injection H; clear H; intros H₁ H₃.
    eapply IHel, H₁.
Qed.

Theorem norm_list_no_consec2 : ∀ e el el₁ el₂,
  norm_list el ≠ el₁ ++ negf e :: e :: el₂.
Proof.
intros e el el₁ el₂.
pose proof norm_list_no_consec (negf e) el el₁ el₂ as H.
now rewrite negf_involutive in H.
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
 simpl; now rewrite letter_dec_diag, bool_dec_negb_r.

 remember (FE t₁ d₁ :: el) as el₁ eqn:Hel₁.
 symmetry in Hel₁; simpl.
 remember (norm_list el₁) as el₂ eqn:Hel₂.
 symmetry in Hel₂; simpl.
 destruct el₂ as [| (t₂, d₂)].
  now rewrite letter_dec_diag, bool_dec_negb_r.

  subst el₁.
  destruct (letter_dec t t₂) as [H₁| H₁].
   subst t₂.
   destruct (Bool.bool_dec (negb d) d₂) as [H₁| H₁].
    subst d₂.
    now rewrite letter_dec_diag, bool_dec_negb_r.

    apply negb_neq in H₁; subst d₂.
    destruct el₂ as [| (t₂, d₂)]; [ easy | ].
    destruct (letter_dec t t₂) as [H₁| H₁]; [ | easy ].
    subst t₂.
    destruct (Bool.bool_dec d d₂) as [H₁| H₁]; [ easy | ].
    apply not_eq_sym, neq_negb in H₁; subst d₂.
    exfalso; revert Hel₂; apply norm_list_no_start.

   now rewrite letter_dec_diag, bool_dec_negb_r.
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

 simpl; now rewrite IHel₁.
Qed.

Theorem norm_list_cancel_in2 : ∀ el₁ el₂ e,
  norm_list (el₁ ++ negf e :: e :: el₂) =
  norm_list (el₁ ++ el₂).
Proof.
intros.
pose proof norm_list_cancel_in el₁ el₂ (negf e) as H.
now rewrite negf_involutive in H.
Qed.

Theorem is_normal : ∀ el₁ el₂ el₃,
  norm_list (el₁ ++ norm_list el₂ ++ el₃) =
  norm_list (el₁ ++ el₂ ++ el₃).
Proof.
intros.
revert el₁ el₃.
induction el₂ as [| e₂]; intros; [ easy | simpl ].
remember (norm_list el₂) as el eqn:Hel₂; symmetry in Hel₂.
destruct el as [| e].
 simpl in IHel₂; simpl.
 rewrite cons_comm_app, app_assoc.
 now rewrite IHel₂, <- app_assoc.

 destruct (letter_opp_dec e₂ e) as [H₁| H₁].
  apply letter_opp_negf in H₁; subst e₂.
  rewrite cons_comm_app.
  do 2 rewrite app_assoc.
  rewrite <- IHel₂.
  do 2 rewrite <- app_assoc; simpl.
  rewrite norm_list_cancel_in2.
  easy.

  rewrite cons_comm_app.
  do 2 rewrite app_assoc.
  rewrite <- IHel₂.
  do 2 rewrite <- app_assoc.
  easy.
Qed.

Theorem norm_list_normal_l : ∀ el₁ el₂,
  norm_list (el₁ ++ el₂) = norm_list (norm_list el₁ ++ el₂).
Proof.
intros.
replace el₁ with ([] ++ el₁) by easy.
rewrite <- app_assoc.
now rewrite <- is_normal.
Qed.

Theorem norm_list_normal_r : ∀ el₁ el₂,
  norm_list (el₁ ++ el₂) = norm_list (el₁ ++ norm_list el₂).
Proof.
intros.
replace el₂ with (el₂ ++ []) by apply app_nil_r.
rewrite <- is_normal.
now do 2 rewrite app_nil_r.
Qed.

Theorem norm_list_idemp : ∀ el, norm_list (norm_list el) = norm_list el.
Proof.
intros el.
pose proof is_normal [] el [] as H.
simpl in H; do 2 rewrite app_nil_r in H.
easy.
Qed.

Theorem norm_list_cons : ∀ el e,
  norm_list (e :: el) = e :: el
  → norm_list el = el.
Proof.
intros el e Hn.
revert e Hn.
induction el as [| e₁]; intros; [ easy | ].
remember (e₁ :: el) as el₁ eqn:Hel.
simpl in Hn.
remember (norm_list el₁) as el₂ eqn:Hel₁; symmetry in Hel₁.
destruct el₂ as [| e₂].
 injection Hn; clear Hn; intros; now subst.

 destruct (letter_opp_dec e e₂) as [H₁| H₁].
  apply letter_opp_negf in H₁; subst e el₂.
  exfalso; revert Hel₁; apply norm_list_no_start.

  injection Hn; clear Hn; intros; subst el₁.
  easy.
Qed.

Theorem norm_list_app_diag : ∀ el₁ el₂,
  norm_list (el₁ ++ el₂) = el₁ ++ el₂ → norm_list el₁ = el₁.
Proof.
intros el₁ el₂ Hn.
revert el₂ Hn.
induction el₁ as [| e₁]; intros; [ easy | simpl ].
generalize Hn; intros Hn₁.
rewrite <- app_comm_cons in Hn₁.
apply norm_list_cons, IHel₁ in Hn₁.
rewrite Hn₁.
destruct el₁ as [| e₂]; [ easy | ].
destruct (letter_opp_dec e₁ e₂) as [H₁| H₁]; [ exfalso | easy ].
apply letter_opp_negf in H₁; subst e₁.
revert Hn; apply norm_list_no_start2.
Qed.

Theorem norm_list_dec : ∀ el,
  { norm_list el = el } +
  { ∃ el₁ t d el₂, el = el₁ ++ FE t d :: FE t (negb d) :: el₂ }.
Proof.
intros el.
induction el as [| e]; [ now left | ].
destruct IHel as [IHel| IHel].
 simpl.
 rewrite IHel.
 destruct el as [| e₁]; [ now left | ].
 destruct (letter_opp_dec e e₁) as [H₁| H₁]; [ right | now left ].
 apply letter_opp_sym, letter_opp_negf in H₁; subst e₁.
 destruct e as (t, d).
 exists [], t, d, el.
 easy.

 right.
 destruct IHel as (el₁, (t, (d, (el₂, IHel)))).
 exists (e :: el₁), t, d, el₂; subst el.
 easy.
Qed.

Theorem norm_list_repeat : ∀ e n, norm_list (repeat e n) = repeat e n.
Proof.
intros e n.
induction n; [ easy | simpl ].
rewrite IHn.
remember (repeat e n) as el eqn:Hel.
symmetry in Hel.
destruct el as [| e₁]; [ easy | ].
destruct (letter_opp_dec e e₁) as [H| H]; [ | easy ].
apply letter_opp_negf in H; subst e.
exfalso.
destruct n; [ easy | ].
injection Hel; clear Hel; intros Hel H.
revert H; apply no_fixpoint_negf.
Qed.

Theorem norm_list_is_cons : ∀ el e el₁,
  norm_list el = e :: el₁ → norm_list el₁ = el₁.
Proof.
intros * H.
destruct (norm_list_dec el₁) as [H₁| H₁]; [ easy | ].
destruct H₁ as (el₂ & t & d & el₃ & H₁).
subst el₁.
exfalso; revert H.
replace (FE t (negb d)) with (negf (FE t d)) by easy.
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

 rewrite app_of_cons in H₂.
 apply split_app_eq in H₂.
 destruct H₂ as [(el', (H₂, H₃))| (el', (H₂, H₃))].
  subst el.
  destruct el' as [| e'].
   rewrite app_nil_r in H₁.
   rewrite app_nil_l in H₃; symmetry in H₃.
   now split.

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
   now split.
Qed.  
