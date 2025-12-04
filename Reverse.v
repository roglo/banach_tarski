(* Banach-Tarski paradox. *)

From Stdlib Require Import List Relations Arith Wf_nat Compare_dec.
Import ListNotations.
From RingLike Require Import Utf8.
From a Require Import Misc Words Normalize.

Definition rev_path el := map negf (rev el).

Theorem rev_path_cons : ∀ e el,
  rev_path (e :: el) = rev_path el ++ rev_path [e].
Proof.
intros e el.
unfold rev_path; simpl.
now rewrite map_app.
Qed.

Theorem rev_path_app : ∀ el₁ el₂,
  rev_path (el₁ ++ el₂) = rev_path el₂ ++ rev_path el₁.
Proof.
intros el₁ el₂.
revert el₁.
induction el₂ as [| (t, d)]; intros; [ now rewrite app_nil_r | ].
rewrite rev_path_cons, cons_comm_app, app_assoc, IHel₂.
rewrite <- app_assoc; f_equal; simpl.
clear el₂ IHel₂.
induction el₁ as [| e₁]; [ easy | ].
simpl; rewrite rev_path_cons; rewrite IHel₁.
simpl; f_equal; symmetry.
now rewrite rev_path_cons.
Qed.

Theorem rev_path_involutive : ∀ el, rev_path (rev_path el) = el.
Proof.
intros el.
induction el as [| (t, d)]; [ easy | simpl ].
rewrite rev_path_cons, rev_path_app.
rewrite IHel; simpl; rewrite Bool.negb_involutive.
easy.
Qed.

Theorem rev_path_single : ∀ e, rev_path [e] = [negf e].
Proof. easy. Qed.

Theorem rev_path_nil : rev_path [] = [].
Proof. easy. Qed.

Theorem rev_path_is_nil : ∀ el, rev_path el = [] → el = [].
Proof.
intros el Hr.
destruct el as [| e]; [ easy | ].
rewrite rev_path_cons, rev_path_single in Hr.
now destruct (rev_path el).
Qed.

Theorem rev_path_eq_eq : ∀ el₁ el₂,
  rev_path el₁ = rev_path el₂ ↔ el₁ = el₂.
Proof.
intros el₁ el₂.
split; [ | intros H; now subst ].
intros Hr.
revert el₂ Hr.
induction el₁ as [| e₁]; intros. {
  rewrite rev_path_nil in Hr.
  symmetry in Hr; apply rev_path_is_nil in Hr.
  now destruct Hr.
}
rewrite rev_path_cons, rev_path_single in Hr.
destruct el₂ as [| e₂]. {
  rewrite rev_path_nil in Hr.
  now destruct (rev_path el₁).
}
rewrite rev_path_cons, rev_path_single in Hr.
apply app_inj_tail in Hr.
destruct Hr as (Hr, Hn).
apply IHel₁ in Hr.
apply negf_eq_eq in Hn.
now subst el₁ e₁.
Qed.

Theorem norm_list_rev_path : ∀ el,
  norm_list el = el → norm_list (rev_path el) = rev_path el.
Proof.
intros el Hel.
induction el as [| e] using rev_ind; [ easy | ].
rewrite rev_path_app; simpl.
generalize Hel; intros Hn.
apply norm_list_app_diag in Hn.
rewrite IHel; [ | easy ].
remember (rev_path el) as el₁ eqn:Hel₁.
symmetry in Hel₁.
destruct el₁ as [| e₁]; [ easy | ].
destruct (letter_opp_dec (negf e) e₁) as [H₁| H₁]; [ | easy ].
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
destruct len. {
  apply length_zero_iff_nil in Hlen; now subst el.
}
destruct (norm_list_dec el) as [H₁| H₁]. {
  generalize H₁; intros H₂.
  apply norm_list_rev_path in H₂.
  rewrite H₁, H₂.
  easy.
}
destruct H₁ as (el₁, (t, (d, (el₂, Hs)))).
generalize Hs; intros H.
rewrite H, norm_list_cancel_in.
rewrite rev_path_app, rev_path_cons, rev_path_cons.
do 2 rewrite rev_path_single.
do 2 rewrite <- app_assoc; simpl.
rewrite Bool.negb_involutive.
rewrite norm_list_cancel_in.
rewrite <- rev_path_app.
apply IHlen with (m := length (el₁ ++ el₂)); [ | easy ].
rewrite <- Hlen, H; simpl.
do 2 rewrite length_app; simpl.
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
destruct (norm_list_dec (el₁ ++ el₂)) as [H₁| H₁]. {
  rewrite H₁ in Hn.
  apply app_eq_nil in Hn.
  destruct Hn; now subst el₁ el₂.
}
destruct H₁ as (el₃ & t & d & el₄ & H₁).
rewrite H₁, length_app, Nat.add_comm in Hlen.
destruct len; [ easy | ].
destruct len; [ easy | simpl in Hlen ].
do 2 apply -> Nat.succ_inj_wd in Hlen.
rewrite Nat.add_comm, <- length_app in Hlen.
assert (H₂ : len < S (S len)). {
  transitivity (S len); apply Nat.lt_succ_diag_r.
}
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
easy.
Qed.

Theorem rev_path_length : ∀ el, length (rev_path el) = length el.
Proof.
intros.
induction el as [| e el]; [ easy | simpl ].
rewrite rev_path_cons, rev_path_single.
rewrite length_app; simpl.
now rewrite Nat.add_1_r, IHel.
Qed.

Theorem rev_path_nth : ∀ el i,
  (i < length el)%nat
  → List.nth i (rev_path el) ạ = negf (List.nth (length el - S i) el ạ⁻¹).
Proof.
intros el i Hlen.
revert i Hlen.
induction el as [| e el]; intros; [ now simpl; rewrite match_id | ].
rewrite rev_path_cons, rev_path_single.
destruct (lt_dec i (length el)) as [Hi| Hi]. {
  rewrite app_nth1; [ | now rewrite rev_path_length ].
  rewrite IHel; simpl; [ f_equal | easy ].
  remember (length el - i)%nat as n eqn:Hn.
  symmetry in Hn.
  destruct n. {
    apply Nat.sub_0_le in Hn.
    apply Nat.lt_succ_r in Hn.
    now apply Nat.nle_gt in Hn.
  }
  f_equal; apply Nat.succ_inj.
  now rewrite <- Hn, <- Nat.sub_succ_l.
}
apply Nat.nlt_ge in Hi.
simpl in Hlen; unfold lt in Hlen.
apply Nat.succ_le_mono in Hlen.
apply Nat.le_antisymm in Hi; [ | easy ].
rewrite Hi.
rewrite app_nth2; [ simpl | now rewrite rev_path_length; unfold ge ].
now rewrite rev_path_length, <- Hi, Nat.sub_diag.
Qed.

Theorem nth_in_consec_split : ∀ A (n : nat) (l : list A) (d₁ d₂ : A),
  (S n < length l)%nat
  → ∃ l1 l2 : list A,
    l = l1 ++ List.nth n l d₁ :: List.nth (S n) l d₂ :: l2.
Proof.
intros * Hn.
revert n Hn.
induction l as [| x l]; intros; [ now apply Nat.nlt_0_r in Hn | ].
simpl in Hn.
apply Nat.succ_lt_mono in Hn.
destruct n. {
  destruct l as [| y l]; [ now apply Nat.nlt_0_r in Hn | ].
  now exists [], l.
}
apply IHl in Hn.
destruct Hn as (l1 & l2 & Hn).
now exists (x :: l1), l2; simpl; f_equal.
Qed.

Theorem rev_norm_path_eq_path : ∀ el,
  norm_list el = el
  → rev_path el = el
  → el = [].
Proof.
intros * Hn Hr.
destruct el as [| e₁ el]; [ easy | exfalso ].
destruct (zerop (length el mod 2)) as [Hel| Hel]. {
  apply Nat.Div0.mod_divides in Hel.
  destruct Hel as (c, Hc).
  assert (Hlt : (c < length (e₁ :: el))%nat). {
    simpl; rewrite Hc; simpl.
    rewrite Nat.add_0_r.
    apply Nat.lt_succ_r, Nat.le_add_r.
  }
  pose proof rev_path_nth (e₁ :: el) c Hlt as H.
  rewrite Hr in H; simpl in H.
  symmetry in H.
  replace (length el - c)%nat with c in H. {
    destruct c; [ now apply no_fixpoint_negf in H | ].
    simpl in Hlt.
    apply Nat.succ_lt_mono in Hlt.
    erewrite nth_indep in H; [ now apply no_fixpoint_negf in H | ].
    rewrite Hc; simpl; rewrite Nat.add_0_r.
    apply Nat.lt_succ_r, Nat.le_add_r.
  }
  rewrite Hc; simpl.
  now rewrite Nat.add_0_r, Nat.add_sub.
}
assert (He : (length (e₁ :: el) mod 2 = 0)%nat). {
  simpl.
  rewrite <- Nat.add_1_r.
  rewrite <- Nat.Div0.add_mod_idemp_l.
  remember (length el mod 2) as m eqn:Hm.
  destruct m; [ easy | ].
  destruct m; [ easy | ].
  assert (H : (2 ≠ 0)%nat) by easy.
  apply (Nat.mod_upper_bound (length el)) in H.
  rewrite <- Hm in H.
  do 2 apply Nat.succ_lt_mono in H.
  now apply Nat.nlt_0_r in H.
}
apply Nat.Div0.mod_divides in He.
destruct He as (c, Hc).
destruct c; [ easy | ].
assert (Hlt : (S c < length (e₁ :: el))%nat). {
  rewrite Hc; simpl; rewrite Nat.add_0_r.
  apply Nat.lt_succ_r; rewrite Nat.add_comm.
  apply Nat.le_add_r.
}
generalize Hlt; intros H.
apply rev_path_nth in H.
rewrite Hr in H.
remember (e₁ :: el) as el₂; simpl in H.
rewrite Hc in H; simpl in H.
rewrite Nat.add_0_r, Nat.add_sub in H; subst el₂.
rename H into Hlen.
pose proof nth_in_consec_split free_elem c (e₁ :: el) ạ⁻¹ ạ Hlt.
destruct H as (l₁ & l₂ & Hll).
rewrite Hlen, <- Hn in Hll.
now apply norm_list_no_consec in Hll.
Qed.

Theorem rev_path_eq_path : ∀ el,
  rev_path (norm_list el) = norm_list el
  → norm_list el = [].
Proof.
intros el Hel.
remember (norm_list el) as el₁ eqn:Hel₁.
assert (H : norm_list el₁ = el₁) by (subst el₁; apply norm_list_idemp).
clear el Hel₁.
rename el₁ into el; rename H into Hn.
now apply rev_norm_path_eq_path.
Qed.

Theorem norm_list_app_diag_is_nil : ∀ el,
  norm_list (el ++ el) = []
  → norm_list el = [].
Proof.
intros el Hel.
rewrite norm_list_normal_l in Hel.
rewrite norm_list_normal_r in Hel.
apply norm_list_app_is_nil in Hel; try now rewrite norm_list_idemp.
now apply rev_path_eq_path.
Qed.
