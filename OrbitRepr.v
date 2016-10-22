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
eapply Hinf; [ reflexivity | | eassumption ].
intros H; rewrite Hn in H; discriminate H.
Qed.

Theorem start_with_same : ∀ f os, os = mkos _ f →
  ∀ e₁ e₂ p, p ∈ SS e₁ → p ∈ SS e₂ → e₁ = e₂.
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
  → ∀ e p, p ∈ SS e → p ∈ rot e (SS (negf e)) → False.
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
  → ∀ p, p ∈ M ∪ SS ạ ∪ B
  → p ∈ rot ạ (SS ạ⁻¹ ∖ B)
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
    unfold orbit_by_seq_of.
    remember S as g; subst os; simpl in Hoo; simpl; subst g.
    rewrite Hfr; simpl.
    exists (S n).
    rewrite Hoo; reflexivity.
Qed.

Theorem r_decomposed_5 :
  ∀ (s := set_equiv) f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints [M; SS ạ; SS ạ⁻¹; SS ḅ; SS ḅ⁻¹].
Proof.
intros s f (Hoe, Ho) os Hos; subst os s.
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
 intros (Hi, Hj).
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
  ∀ (s := set_equiv) f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints
      [M ∪ SS ạ ∪ B; SS ạ⁻¹ ∖ B; SS ḅ; SS ḅ⁻¹].
Proof.
intros s f HoeHo os Hos.
pose proof r_decomposed_5 f HoeHo os Hos as H.
destruct HoeHo as (Hoe, Ho).
eapply is_partition_group_first_2_together in H.
apply is_partition_union_subtract; [ assumption | | ].
 intros p bm; subst os.
 destruct bm as (Ha & n & Hr); remember S as g; simpl in Hr; subst g.
 split; [ assumption | ].
 exists (repeat ạ⁻¹ (S n)), (repeat ạ⁻¹ n).
 split; [ apply norm_list_repeat | assumption ].

 intros p; apply EM.
Qed.

Theorem r_decomposed_2 :
  ∀ (s := set_equiv) f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ e,
    is_partition sphere_but_fixpoints [SS e; rot e (SS (negf e))].
Proof.
intros s f (Hoe, Ho) os Hos e; subst os s.
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
     unfold rot.
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
 intros (Hi, Hj).
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

Add Parametric Morphism {A} : (@List.nth (set A))
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
  ∀ (s := set_equiv) f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition sphere_but_fixpoints [M ∪ SS ạ ∪ B; rot ạ (SS ạ⁻¹ ∖ B)].
Proof.
intros s f (Hoe, Ho) os Hos; subst s.
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
      destruct (EM (p ∈ B)) as [HB| HB]; [ left; right; assumption | ].
      right; left; simpl.
      split.
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
       unfold orbit_by_seq_of in Hoo |-*; simpl.
       remember S as g;
       subst os; simpl in Hoo |-*; subst g.
       rewrite Hfr in Hoo; simpl in Hoo.
       apply f_equal with (f := rotate (FE la false)) in Hoo.
       do 2 rewrite rotate_rotate_neg in Hoo.
       destruct n; [ | exists n; assumption ].
       simpl in Hoo.
       rewrite Hoo in Hel.
       destruct Hnf as (His & Hoh).
       unfold orbit_without_fixpoint in Hoh.
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
      unfold orbit_by_seq_of in Hoo; simpl in Hoo.
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
  intros (Hi, Hj).
  destruct i; [ simpl in Hi | ].
   destruct j; [ exfalso; apply Hij; reflexivity | clear Hij ].
   destruct j; [ simpl in Hj | destruct j; contradiction ].
   eapply decompose_2a_contrad_case; unfold union; try eassumption.
   split; assumption.

   destruct i; [ simpl in Hi | destruct i; contradiction ].
   destruct j.
    eapply decompose_2a_contrad_case; unfold union; try eassumption.
    split; assumption.

    destruct j; [ apply Hij; reflexivity | clear Hij ].
    destruct j; contradiction.
Qed.

Theorem r_decomposed_2_b :
  ∀ (s := set_equiv) f, orbit_selector f
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

Add Parametric Morphism {A} : (@subtract A)
  with signature
    (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as subtract_morph.
Proof.
intros E E' HE F F' HF.
unfold subtract; intros p.
split; intros (H₁, H₂).
 split; [ apply HE; assumption | intros H; apply H₂, HF; assumption ].
 split; [ apply HE; assumption | intros H; apply H₂, HF; assumption ].
Qed.
