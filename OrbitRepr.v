(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List.
Import ListNotations.
Require Import Reals Nsatz.

Require Import Misc Words Normalize Reverse Matrix Pset Orbit.
Require Import Partition.

Class sel_model {A} := mkos { os_fun : A → A }.

Definition orbit_by_seq_of e {os : sel_model} :=
  mkset (λ p, ∃ n, fold_right rotate (os_fun p) (repeat e (S n)) = p).

Definition M {os : sel_model} :=
  mkset (λ p, p ∈ sphere_but_fixpoints ∧ p = os_fun p).
Definition SS {os : sel_model} e :=
  mkset
    (λ p,
     p ∈ sphere_but_fixpoints ∧
     ∃ el el₁,
       norm_list el = e :: el₁ ∧ fold_right rotate (os_fun p) el = p).
Definition B {os : sel_model} :=
  mkset (λ p, p ∈ sphere_but_fixpoints ∧ p ∈ orbit_by_seq_of ạ⁻¹).

Opaque M SS B.

Definition rot e (E : set point) :=
  mkset (λ p, rotate (negf e) p ∈ E).
Definition xtransl dx (E : set point) :=
  mkset (λ '(P x y z), (P (x - dx) y z) ∈ E).

Theorem empty_set_not_full_set : ∀ f os, os = mkos _ f →
  ∀ e p, p ∈ M → p ∈ SS e → False.
Proof.
intros f os Hos e p He Hs; subst os.
destruct He as (Hinf & He); simpl in He.
destruct Hs as (Hjnf & el & el₁ & Hn & Hs); simpl in Hs.
rewrite <- He in Hs.
unfold sphere_but_fixpoints in Hinf; simpl in Hinf.
destruct Hinf as (Hle1 & Hinf).
apply Hinf; clear Hinf.
exists el, p.
now rewrite Hn.
Qed.

Theorem start_with_same : ∀ f os, os = mkos _ f →
  ∀ e₁ e₂ p, p ∈ SS e₁ → p ∈ SS e₂ → e₁ = e₂.
Proof.
intros f os Hos (ti, di) (tj, dj) p Hsi Hsj; subst os.
destruct Hsi as (Hinf & eli & eli₁ & Hni & Hsi); simpl in Hsi.
destruct Hsj as (Hjnf & elj & elj₁ & Hnj & Hsj); simpl in Hsj.
eapply rotate_rev_path in Hsj.
destruct ti, tj.
+destruct di, dj; [ easy | exfalso | exfalso | easy ].
 *eapply not_in_fixpoints_one_path; try eassumption.
   intros el Hn.
   destruct Hinf as (Hps, Hnpd).
   intros H; apply Hnpd; clear Hnpd.
   now exists el, p.

   rewrite <- rev_path_norm_list, Hnj.
   now rewrite rev_path_cons, rev_path_single.

   easy.

 *eapply not_in_fixpoints_one_path; try eassumption.
   intros el Hn.
   destruct Hinf as (Hps, Hnpd).
   intros H; apply Hnpd.
   now exists el, p.

   rewrite <- rev_path_norm_list, Hnj.
   now rewrite rev_path_cons, rev_path_single.

   easy.

+exfalso.
 eapply not_in_fixpoints_one_path; try eassumption.
  intros el Hn.
  destruct Hinf as (Hps, Hnpd).
  intros H; apply Hnpd.
  now exists el, p.

  rewrite <- rev_path_norm_list, Hnj.
  now rewrite rev_path_cons, rev_path_single.

  easy.

+exfalso.
 eapply not_in_fixpoints_one_path; try eassumption.
  intros el Hn.
  destruct Hinf as (Hps, Hnpd).
  intros H; apply Hnpd.
  now exists el, p.

  rewrite <- rev_path_norm_list, Hnj.
  now rewrite rev_path_cons, rev_path_single.

  easy.

+destruct di, dj; [ easy | exfalso | exfalso | easy ].
 *eapply not_in_fixpoints_one_path; try eassumption.
   intros el Hn.
   destruct Hinf as (Hps, Hnpd).
   intros H; apply Hnpd.
   now exists el, p.

   rewrite <- rev_path_norm_list, Hnj.
   now rewrite rev_path_cons, rev_path_single.

   easy.

 *eapply not_in_fixpoints_one_path; try eassumption.
   intros el Hn.
   destruct Hinf as (Hps, Hnpd).
   intros H; apply Hnpd.
   now exists el, p.

   rewrite <- rev_path_norm_list, Hnj.
   now rewrite rev_path_cons, rev_path_single.

   easy.
Qed.

Theorem not_start_with_rot :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ e p, p ∈ SS e → p ∈ rot e (SS (negf e)) → False.
Proof.
intros f (Hoe, Ho) os Hos e p Hs Hr; simpl in Hr; subst os.
destruct Hs as (Hnf & el & el₁ & Hn & Hs); simpl in Hs.
destruct Hr as (Hrnf & elr & elr₁ & Hnr & Hsr); simpl in Hsr.
assert (Hr : f p = f (rotate (negf e) p)).
 apply Hoe.
 now exists (negf e :: []).

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
 destruct Hnf as (Hps, Hnpd).
 apply Hnpd.
 exists (norm_list el ++ rev_path elr₁), p.
 split; [ easy | ].
 split; [ | easy ].
 intros H.
 apply norm_list_app_is_nil in H.
  apply -> rev_path_eq_eq in H.
  rewrite H, Hn in Hnr.
  revert Hnr; apply norm_list_no_start2.

  symmetry; apply norm_list_idemp.
  rewrite <- rev_path_norm_list; eapply norm_list_is_cons in Hnr.
  now rewrite Hnr.
Qed.

Theorem decompose_2a_contrad_case :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ p, p ∈ M ∪ SS ạ ∪ B
  → p ∈ rot ạ (SS ạ⁻¹ ∖ B)
  → False.
Proof.
intros * (Hoe, Ho) * Hos * Hi Hj.
 assert (Hfr : f (rotate ạ⁻¹ p) = f p).
  apply Hoe; exists (ạ :: []); apply rotate_neg_rotate.

   destruct Hj as (Hs & Hb); simpl in Hs, Hb; apply Hb; clear Hb.
   split; [ now destruct Hs | ].
   destruct Hi as [[Hi| Hi] | Hi].
    destruct Hs as (Hrnf & el & el₁ & Hn & Hr).
    destruct Hi as (Hnf & Hp); subst os; simpl in Hp.
    exists O; simpl.
    now rewrite Hfr, <- Hp.

    eapply not_start_with_rot in Hi; try eassumption; [ easy | ].
    now split.

    destruct Hi as (Hnf, Hoo).
    destruct Hoo as (n, Hoo).
    unfold orbit_by_seq_of.
    remember S as g; subst os; simpl in Hoo; simpl; subst g.
    rewrite Hfr; simpl.
    exists (S n).
    now rewrite Hoo.
Qed.

Theorem r_decomposed_5 :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints [M; SS ạ; SS ạ⁻¹; SS ḅ; SS ḅ⁻¹].
Proof.
intros f (Hoe, Ho) os Hos; subst os.
split.
*intros p.
 split.
 -intros Hnf.
  unfold union_list; simpl; unfold union.
  destruct (eq_point_dec p (f p)) as [H₁| H₁]; [ left; now split | ].
  right.
  pose proof Ho p as H.
  destruct H as (el, Hel).
  remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
  destruct (list_nil_app_dec el₁) as [H₂| (e & el₂ & H₂)]; subst el₁.
  +now rewrite rotate_rotate_norm, H₂ in Hel.

  +destruct e as (t, d); destruct t, d.
    left; split; [ easy | ].
    exists (rev_path el), (rev_path el₂).
    split; [ | now apply rotate_rev_path ].
    now rewrite <- rev_path_norm_list, H₂, rev_path_app.

    right; left; split; [ easy | ].
    exists (rev_path el), (rev_path el₂).
    split; [ | now apply rotate_rev_path ].
    now rewrite <- rev_path_norm_list, H₂, rev_path_app.

    right; right; left; split; [ easy | ].
    exists (rev_path el), (rev_path el₂).
    split; [ | now apply rotate_rev_path ].
    now rewrite <- rev_path_norm_list, H₂, rev_path_app.

    right; right; right; left; split; [ easy | ].
    exists (rev_path el), (rev_path el₂).
    split; [ | now apply rotate_rev_path ].
    now rewrite <- rev_path_norm_list, H₂, rev_path_app.

 -intros Hul.
  unfold union_list in Hul; simpl in Hul; unfold union in Hul.
  destruct Hul as [Hul| [Hul| [Hul| [Hul| [Hul| Hul]]]]].
  +destruct Hul as (Hnf, Hul); simpl in Hul.
   now apply Hnf.

  +destruct Hul as (Hnf, Hul); simpl in Hul.
   now apply Hnf.

  +destruct Hul as (Hnf, Hul); simpl in Hul.
   now apply Hnf.

  +destruct Hul as (Hnf, Hul); simpl in Hul.
   now apply Hnf.

  +destruct Hul as (Hnf, Hul); simpl in Hul.
   now apply Hnf.

  +easy.

*intros i j Hij p.
 split; [ | easy ].
 intros (Hi, Hj).
 destruct i; [ simpl in Hi | ].
  destruct j; [ exfalso; now apply Hij | clear Hij ].
  destruct Hi as (Hinf & Hi); simpl in Hi.
  destruct j.
   eapply empty_set_not_full_set; [ easy | | eassumption ].
   now split.

   destruct j.
    eapply empty_set_not_full_set; [ easy | | eassumption ].
    now split.

    destruct j.
     eapply empty_set_not_full_set; [ easy | | eassumption ].
     now split.

     destruct j; [ | now destruct j ].
     eapply empty_set_not_full_set; [ easy | | eassumption ].
     now split.

 destruct i; [ simpl in Hi | ].
  destruct j; [ clear Hij | ].
   eapply empty_set_not_full_set; [ easy | eassumption | eassumption ].

   destruct j; [ exfalso; now apply Hij | clear Hij ].
   destruct j; [ simpl in Hj | ].
    eapply start_with_same in Hi; [ | easy | eassumption ].
    easy.

    destruct j; [ simpl in Hj | ].
     eapply start_with_same in Hi; [ | easy | eassumption ].
     easy.

     destruct j; [ simpl in Hj | now destruct j ].
     eapply start_with_same in Hi; [ | easy | eassumption ].
     easy.

  destruct i; [ simpl in Hi | ].
   destruct j; [ clear Hij | ].
    eapply empty_set_not_full_set; [ easy | | ]; eassumption.

    destruct j; [ simpl in Hj | ].
     eapply start_with_same in Hi; [ | easy | eassumption ].
     easy.

     destruct j; [ exfalso; now apply Hij | clear Hij ].
     destruct j; [ simpl in Hj | ].
      eapply start_with_same in Hi; [ | easy | eassumption ].
      easy.

      destruct j; [ simpl in Hj | now destruct j ].
      eapply start_with_same in Hi; [ | easy | eassumption ].
      easy.

   destruct i; [ simpl in Hi | ].
    destruct j; [ clear Hij | ].
     eapply empty_set_not_full_set; [ easy | | ]; eassumption.

     destruct j; [ simpl in Hj | ].
      eapply start_with_same in Hi; [ | easy | eassumption ].
      easy.

      destruct j; [ simpl in Hj | ].
       eapply start_with_same in Hi; [ | easy | eassumption ].
       easy.

       destruct j; [ exfalso; now apply Hij | clear Hij ].
       destruct j; [ simpl in Hj | now destruct j ].
       eapply start_with_same in Hi; [ | easy | eassumption ].
       easy.

    destruct i; [ simpl in Hi | ].
     destruct j; [ clear Hij | ].
      eapply empty_set_not_full_set; [ easy | | ]; eassumption.

      destruct j; [ simpl in Hj | ].
       eapply start_with_same in Hi; [ | easy | eassumption ].
       easy.

       destruct j; [ simpl in Hj | ].
        eapply start_with_same in Hi; [ | easy | eassumption ].
        easy.

        destruct j; [ simpl in Hj | ].
         eapply start_with_same in Hi; [ | easy | eassumption ].
         easy.

         destruct j; [ exfalso; now apply Hij | clear Hij ].
         now destruct j.

     now destruct i.
Qed.

Theorem r_decomposed_4 :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints
      [M ∪ SS ạ ∪ B; SS ạ⁻¹ ∖ B; SS ḅ; SS ḅ⁻¹].
Proof.
intros f HoeHo os Hos.
pose proof r_decomposed_5 f HoeHo os Hos as H.
destruct HoeHo as (Hoe, Ho).
eapply is_partition_group_first_2_together in H.
apply is_partition_union_subtract; [ easy | | ].
 intros p bm; subst os.
 destruct bm as (Ha & n & Hr); remember S as g; simpl in Hr; subst g.
 split; [ easy | ].
 exists (repeat ạ⁻¹ (S n)), (repeat ạ⁻¹ n).
 split; [ apply norm_list_repeat | easy ].

 intros p; apply EM.
Qed.

Theorem r_decomposed_2 :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ e,
    is_partition sphere_but_fixpoints [SS e; rot e (SS (negf e))].
Proof.
intros f (Hoe, Ho) os Hos e; subst os.
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
   unfold rot.
   split.
    split.
     destruct Hnf as (His, _).
     now apply in_sphere_after_rotate.

     destruct Hnf as (Hps, Hnpd).
     now apply no_fixpoint_after_rotate.

    exists (negf e :: []), [].
    split; [ easy | simpl ].
    assert (H : f p = f (rotate (negf e) p)).
     apply Hoe.
     now exists (negf e :: []).

     now rewrite <- H, Hel.

   +destruct (free_elem_dec e e₁) as [H₁| H₁]; [ subst e₁ | ].
     left; split; [ easy | ].
     exists el, el₁; now split.

     right; left.
     unfold rot.
     split.
      split.
       destruct Hnf as (His, _).
       now apply in_sphere_after_rotate.

       destruct Hnf.
       now apply no_fixpoint_after_rotate.

      assert (H : f p = f (rotate (negf e) p)).
       apply Hoe.
       now exists (negf e :: []).

       simpl; rewrite <- H.
       exists (negf e :: el), (e₁ :: el₁); simpl.
       rewrite Hel₁, Hel.
       destruct (letter_opp_dec (negf e) e₁) as [H₂| H₂].
        exfalso.
        apply letter_opp_negf in H₂.
        now apply H₁, negf_eq_eq.

        now split.

 -intros Hul.
  destruct Hul as [(H, _)| [(H, _)| Hul]]; [ easy | | easy ].
  split.
   destruct H as (His, _).
   apply in_sphere_after_rotate with (e := e) in His.
   now rewrite rotate_rotate_neg in His.

   destruct H as (Hs, Hnp).
   apply no_fixpoint_after_rotate with (e := e) in Hnp.
   now rewrite rotate_rotate_neg in Hnp.

*intros i j Hij p.
 split; [ | easy ].
 intros (Hi, Hj).
 destruct i; [ simpl in Hi | ].
  destruct j; [ exfalso; now apply Hij | clear Hij ].
  destruct j; [ | now destruct j ].
  simpl in Hj.
  eapply not_start_with_rot in Hi; try eassumption; [ | easy ].
  now split.

  destruct i; [ simpl in Hi | ].
   destruct j; [ simpl in Hj; clear Hij | ].
    eapply not_start_with_rot in Hj; try eassumption; [ | easy ].
    now split.

    destruct j; [ now apply Hij | clear Hij ].
    now destruct j.

   now destruct i.
Qed.

Add Parametric Morphism {A} : (@List.nth (set A))
  with signature eq ==> eq ==> set_eq ==> set_eq
  as nth_set_morph.
Proof.
intros i l a b Hab.
revert i.
induction l as [| y]; intros; [ destruct i; apply Hab | ].
destruct i; simpl; [ easy | apply IHl ].
Qed.

Theorem rev_path_repeat : ∀ e n, rev_path (repeat e n) = repeat (negf e) n.
Proof.
intros e n.
induction n; [ easy | simpl ].
rewrite rev_path_cons, rev_path_single, IHn.
apply app_repeat_diag.
Qed.

Theorem r_decomposed_2_a :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints [M ∪ SS ạ ∪ B; rot ạ (SS ạ⁻¹ ∖ B)].
Proof.
intros f (Hoe, Ho) os Hos.
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
    split; [ easy | subst os; now symmetry ].

    +destruct e₁ as (t, d); destruct t.
     destruct d.
      destruct (EM (p ∈ B)) as [HB| HB]; [ left; now right | ].
      right; left; simpl.
      split.
       split.
        destruct Hnf as (His, Hnf).
        split; [ now apply in_sphere_after_rotate | ].
        now apply no_fixpoint_after_rotate.

        subst os; simpl.
        rewrite Hfr.
        exists (ạ⁻¹ :: el), (norm_list el).
        split; [ | simpl; now f_equal ].
        simpl; now rewrite Hel₁.

       simpl; intros (Haf & n & Hoo); apply HB; clear HB.
       split; [ easy | ].
       unfold orbit_by_seq_of in Hoo |-*; simpl.
       remember S as g;
       subst os; simpl in Hoo |-*; subst g.
       rewrite Hfr in Hoo; simpl in Hoo.
       apply f_equal with (f := rotate (FE la false)) in Hoo.
       do 2 rewrite rotate_rotate_neg in Hoo.
       destruct n; [ | now exists n ].
       simpl in Hoo.
       rewrite Hoo in Hel.
       destruct Hnf as (His & Hoh).
       exfalso; apply Hoh.
       exists el, p.
       now rewrite Hel₁.

      left; left; right.
      split; [ easy | ].
      exists el, el₁; subst os.
      now split.

     right; left.
     split; simpl.
      split.
       destruct Hnf as (His & Hnf).
       split; [ now apply in_sphere_after_rotate | ].
       now apply no_fixpoint_after_rotate.

       subst os; simpl; rewrite Hfr.
       exists (ạ⁻¹ :: el), (norm_list el).
       split; [ | simpl; now f_equal ].
       simpl; now rewrite Hel₁.

      intros (Hnf₂, Hoo).
      subst os; simpl in Hoo.
      unfold orbit_by_seq_of in Hoo; simpl in Hoo.
      rewrite Hfr in Hoo.
      destruct Hoo as (n, Hr).
      apply f_equal with (f := rotate (FE la false)) in Hr.
      do 2 rewrite rotate_rotate_neg in Hr.
      destruct n.
       simpl in Hr; rewrite Hr in Hel.
       destruct Hnf as (His, Hoh).
       now apply Hoh; exists el, p; rewrite Hel₁.

       apply rotate_rev_path in Hr.
       rewrite <- Hr, <- fold_right_app in Hel.
       destruct Hnf as (His, Hoh).
       apply Hoh.
       exists (el ++ rev_path (repeat ạ⁻¹ (S n))), p.
       split; [ easy | ].
       split; [ | easy ].
       replace el with ([] ++ el) by easy.
       rewrite <- app_assoc, <- is_normal, Hel₁, app_nil_l.
       rewrite rev_path_repeat.
       remember norm_list as g; remember S as h; simpl; subst g h.
       rewrite app_of_cons, app_assoc.
       intros H.
       eapply norm_list_app_is_nil in H.
        simpl in H.
        apply f_equal with (f := rev_path) in H.
        rewrite rev_path_involutive in H.
        rewrite <- app_repeat_diag in H.
        now rewrite rev_path_app in H; simpl in H.

        unfold app; rewrite <- Hel₁; symmetry.
        apply norm_list_idemp.

        symmetry; apply norm_list_repeat.

 -intros HE.
  simpl in HE.
  destruct HE as [[[HE| HE]| HE]| [HE| HE]]; try now destruct HE.
  destruct HE as (((His & Hoo) & HE) & HB).
  split.
   apply in_sphere_after_rotate with (e := ạ) in His.
   now rewrite rotate_rotate_neg in His.

   apply no_fixpoint_after_rotate with (e := ạ) in Hoo.
   now rewrite rotate_rotate_neg in Hoo.

*intros i j Hij p.
 assert (Hfr : f (rotate ạ⁻¹ p) = f p).
  apply Hoe; exists (ạ :: []); apply rotate_neg_rotate.

  split; [ | easy ].
  intros (Hi, Hj).
  destruct i; [ simpl in Hi | ].
   destruct j; [ exfalso; now apply Hij | clear Hij ].
   destruct j; [ simpl in Hj | now destruct j ].
   eapply decompose_2a_contrad_case; unfold union; try eassumption.
   now split.

   destruct i; [ simpl in Hi | now destruct i ].
   destruct j.
    eapply decompose_2a_contrad_case; unfold union; try eassumption.
    now split.

    destruct j; [ now apply Hij | clear Hij ].
    now destruct j.
Qed.

Theorem r_decomposed_2_b :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints [SS ḅ; rot ḅ (SS ḅ⁻¹)].
Proof.
intros.
eapply r_decomposed_2; eassumption.
Qed.
