(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List Relations NPeano Wf_nat.
Import ListNotations.
Require Import Misc Words Normalize.

Definition rev_path el := map negf (rev el).

Theorem rev_path_cons : ∀ e el,
  rev_path (e :: el) = rev_path el ++ rev_path [e].
Proof.
intros e el.
unfold rev_path; simpl.
rewrite map_app; easy.
Qed.

Theorem rev_path_app : ∀ el₁ el₂,
  rev_path (el₁ ++ el₂) = rev_path el₂ ++ rev_path el₁.
Proof.
intros el₁ el₂.
revert el₁.
induction el₂ as [| (t, d)]; intros; [ rewrite app_nil_r; easy | ].
rewrite rev_path_cons, cons_comm_app, app_assoc, IHel₂.
rewrite <- app_assoc; f_equal; simpl.
clear el₂ IHel₂.
induction el₁ as [| e₁]; [ easy | ].
simpl; rewrite rev_path_cons; rewrite IHel₁.
simpl; f_equal; symmetry.
rewrite rev_path_cons; easy.
Qed.

Theorem rev_path_involutive : ∀ el, rev_path (rev_path el) = el.
Proof.
intros el.
induction el as [| (t, d)]; [ easy | simpl ].
rewrite rev_path_cons, rev_path_app.
rewrite IHel; simpl; rewrite Bool.negb_involutive.
easy.
Qed.

(* because of Require Import Nsatz, there is a semantic error here
Theorem rev_path_single : ∀ e, rev_path [e] = [negf e].
*)
Theorem rev_path_single : ∀ e, rev_path [e] = negf e :: [].
Proof. intros e; easy. Qed.

Theorem rev_path_nil : rev_path [] = [].
Proof. easy. Qed.

Theorem rev_path_is_nil : ∀ el, rev_path el = [] → el = [].
Proof.
intros el Hr.
destruct el as [| e]; [ easy | ].
rewrite rev_path_cons, rev_path_single in Hr.
destruct (rev_path el); easy.
Qed.

Theorem rev_path_eq_eq : ∀ el₁ el₂,
  rev_path el₁ = rev_path el₂ ↔ el₁ = el₂.
Proof.
intros el₁ el₂.
split; [ | intros H; now subst ].
intros Hr.
revert el₂ Hr.
induction el₁ as [| e₁]; intros.
 rewrite rev_path_nil in Hr.
 symmetry in Hr; apply rev_path_is_nil in Hr.
 destruct Hr; easy.

 rewrite rev_path_cons, rev_path_single in Hr.
 destruct el₂ as [| e₂].
  rewrite rev_path_nil in Hr.
  destruct (rev_path el₁); easy.

  rewrite rev_path_cons, rev_path_single in Hr.
  apply app_inj_tail in Hr.
  destruct Hr as (Hr, Hn).
  apply IHel₁ in Hr.
  apply negf_eq_eq in Hn.
  subst el₁ e₁; easy.
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
destruct len.
 apply length_zero_iff_nil in Hlen; now subst el.

 destruct (norm_list_dec el) as [H₁| H₁].
  generalize H₁; intros H₂.
  apply norm_list_rev_path in H₂.
  rewrite H₁, H₂.
  easy.

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
 destruct Hn; now subst el₁ el₂.

 destruct H₁ as (el₃ & t & d & el₄ & H₁).
 rewrite H₁, app_length, Nat.add_comm in Hlen.
 destruct len; [ easy | ].
 destruct len; [ easy | simpl in Hlen ].
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
  easy.
Qed.
