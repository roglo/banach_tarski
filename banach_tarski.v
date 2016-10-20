(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List Relations NPeano Wf_nat.
Import ListNotations.
Require Import Reals Psatz Nsatz.

Require Import Misc Words Normalize Reverse MiscReals Matrix Pset Orbit.
Require Import Partition OrbitRepr.

(* Transformation group *)

Inductive Gr :=
  | Rot : free_elem → Gr
  | Xtransl : ℝ → Gr
  | Comb : Gr → Gr → Gr.

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

Fixpoint app_gr_inv f :=
  match f with
  | Rot e => Rot (negf e)
  | Xtransl dx => Xtransl (-dx)
  | Comb g h => Comb (app_gr_inv h) (app_gr_inv g)
  end.

Theorem gr_subst : ∀ (s := set_equiv) g E F,
  (E = F)%S → ∀ p, p ∈ app_gr g E → p ∈ app_gr g F.
Proof.
intros s * HEF * HE.
revert E F p HEF HE.
induction g as [ e| dx | g IHg h IHh]; intros.
 apply HEF, HE.

 destruct p as (x, y, z).
 apply HEF, HE.

 simpl in HE; simpl.
 eapply IHg; [ | eassumption ].
 split; intros H; [ eapply IHh; eassumption | ].
 eapply IHh; [ symmetry; eassumption | eassumption ].
Qed.

Add Parametric Morphism {A} : (@setp A)
with signature (@set_eq _ set_equiv) ==> eq ==> iff
as setp_morph.
Proof.
intros E F HEF x.
apply HEF.
Qed.

Add Parametric Morphism : app_gr
with signature eq ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
as app_gr_morph.
Proof.
intros g p q Hpq r.
split; intros H; [ eapply gr_subst; eassumption | ].
symmetry in Hpq; eapply gr_subst; eassumption.
Qed.

Theorem app_gr_inv_l : ∀ (s := set_equiv) g E,
  (app_gr (app_gr_inv g) (app_gr g E) = E)%S.
Proof.
intros.
revert E.
induction g; intros; simpl.
 unfold rot; simpl.
 intros p.
 rewrite negf_involutive, rotate_neg_rotate.
 reflexivity.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
 reflexivity.

 intros p.
 split; intros H.
  rewrite IHg1 in H; apply IHg2; assumption.

  rewrite IHg1; apply IHg2, H.
Qed.

Theorem app_gr_app_gr_point : ∀ g E p, p ∈ app_gr g E → app_gr_point g p ∈ E.
Proof.
intros * Hp.
revert E p Hp.
induction g; intros; [ assumption | destruct p; assumption | ].
simpl in Hp; simpl.
apply IHg1 in Hp.
apply IHg2 in Hp.
assumption.
Qed.

Theorem app_gr_empty_set : ∀ (s := set_equiv) f, (app_gr f ∅ = ∅)%S.
Proof.
intros s * p.
split; intros H; [ | contradiction ].
revert p H.
induction f; intros; try contradiction; [ destruct p; contradiction | ].
simpl in H.
eapply gr_subst in H; [ apply IHf1 in H; contradiction | ].
split; [ apply IHf2 | intros; contradiction ].
Qed.

Theorem group_union_distr : ∀ (s := set_equiv) g E₁ E₂,
  (app_gr g (E₁ ∪ E₂) = app_gr g E₁ ∪ app_gr g E₂)%S.
Proof.
intros s *; subst s.
revert E₁ E₂.
induction g as [ e| dx | g IHg h IHh ]; intros; simpl.
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
  (app_gr f (⋃ PL) = ⋃ map (app_gr f) PL)%S.
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
  ∀ (F : set point) P g,
  is_partition F P → is_partition (app_gr g F) (map (app_gr g) P).
Proof.
intros s f Ho F P * HP.
unfold is_partition in HP |-*.
destruct HP as (HF, HP).
split.
 induction g as [e| dx | g IHg h IHh ]; intros; simpl.
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
 rewrite <- app_gr_empty_set with (f := g) in H.
 do 2 rewrite map_nth in H.
 destruct H as (Hi, Hj).
 pose proof HP i j Hij (app_gr_point g p) as Hp.
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
  List.Forall2 (λ S₁ S₂, ∃ g, (app_gr g S₁ = S₂)%S) P₁ P₂.

Theorem is_partition_single : ∀ A (s := @set_equiv A) E, is_partition E [E].
Proof.
intros.
split; [ symmetry; eapply union_empty_r; reflexivity | ].
intros * Hij.
destruct i.
 destruct j; [ exfalso; apply Hij; reflexivity | ].
 destruct j.
  split; [ intros (_, H); contradiction | contradiction ].
  split; [ intros (_, H); contradiction | contradiction ].

 split; [ intros (H, _) | contradiction ].
 destruct i; contradiction.
Qed.

Theorem equidec_refl : reflexive _ (equidecomposable set_equiv).
Proof.
intros E.
exists (E :: []), (E :: []).
split; [ apply is_partition_single | ].
split; [ apply is_partition_single | ].
split; [ reflexivity | ].
constructor; [ | constructor ].
exists (Xtransl 0); simpl.
unfold xtransl; intros (x, y, z).
rewrite Rminus_0_r.
reflexivity.
Qed.

Theorem Forall2_sym: ∀ A (R : A → A → Prop) l1 l2,
 symmetric _ R → Forall2 R l1 l2 → Forall2 R l2 l1.
Proof.
intros * Hs HF.
revert l2 HF.
induction l1 as [| x]; intros.
 destruct l2 as [| y]; [ constructor | ].
 apply Forall2_nil_cons in HF; contradiction.

 destruct l2 as [| y].
  apply Forall2_cons_nil in HF; contradiction.

  apply Forall2_cons_cons in HF.
  destruct HF as (HR & HF).
  constructor; [ apply Hs; assumption | ].
  apply IHl1; assumption.
Qed.

Theorem equidec_sym : symmetric _ (equidecomposable set_equiv).
Proof.
intros E F (P₁ & P₂ & HP₁ & HP₂ & Hlen & HEF).
exists P₂, P₁.
split; [ assumption | ].
split; [ assumption | ].
split; [ symmetry; assumption | ].
apply Forall2_sym; [ | assumption ].
clear -HEF.
intros E F (g & Hg).
exists (app_gr_inv g); rewrite <- Hg.
apply app_gr_inv_l.
Qed.

Definition partition_prod {A} (PL QL : list (set A)) :=
  map (λ '(p, q), intersection p q) (list_prod PL QL).

Theorem partition_prod_nil_l : ∀ A (Q : list (set A)),
  partition_prod [] Q = [].
Proof. reflexivity. Qed.

Theorem partition_prod_nil_r : ∀ A (P : list (set A)),
  partition_prod P [] = [].
Proof.
intros A P.
unfold partition_prod.
induction P as [| P PL]; [ reflexivity | apply IHPL ].
Qed.

Theorem partition_prod_cons_l : ∀ A P (PL QL : list (set A)),
  partition_prod (P :: PL) QL =
  map (intersection P) QL ++ partition_prod PL QL.
Proof.
intros A P PL QL.
unfold partition_prod; simpl.
rewrite map_app, map_map.
reflexivity.
Qed.

Theorem partition_prod_length :
  ∀ A (P Q : list (set A)),
  length (partition_prod P Q) = (length P * length Q)%nat.
Proof.
intros A P Q.
revert Q.
induction P as [| P PL]; intros; [ reflexivity | simpl ].
rewrite partition_prod_cons_l.
rewrite app_length, IHPL, map_length.
reflexivity.
Qed.

Theorem partition_prod_nth :
  ∀ A (s := set_equiv) (PL QL : list (set A)) len i,
  len = length QL
  → ((partition_prod PL QL).[i] = PL.[i / len] ∩ QL.[i mod len])%S.
Proof.
intros * Hlen.
subst len.
revert QL i.
induction PL as [| P PL]; intros.
 intros x.
 split; intros Hx; [ destruct i; contradiction | ].
 destruct Hx as (Hx, _).
 destruct (i / length QL)%nat; contradiction.

 rewrite partition_prod_cons_l.
 destruct (lt_dec i (length QL)) as [Hi| Hi].
  rewrite app_nth1; [| rewrite map_length; assumption ].
  rewrite Nat.div_small; [ simpl | assumption ].
  rewrite Nat.mod_small; [ simpl | assumption ].
  intros x; clear.
  split; intros Hx.
   revert i Hx.
   induction QL as [| Q QL]; intros; [ destruct i; contradiction | ].
   simpl in Hx; simpl.
   destruct i; [ assumption | apply IHQL; assumption ].

   revert i Hx.
   induction QL as [| Q QL]; intros.
    destruct Hx; destruct i; contradiction.

    destruct i; simpl in Hx; simpl; [ assumption | ].
    apply IHQL; assumption.

  apply Nat.nlt_ge in Hi.
  rewrite app_nth2; [| rewrite map_length; assumption ].
  rewrite map_length.
  remember (i - length QL)%nat as j eqn:Hj.
  assert (H : (i = j + length QL)%nat).
   rewrite Hj.
   rewrite Nat.sub_add; [ reflexivity | assumption ].

   subst i; clear Hi Hj.
   destruct QL as [| Q QL].
    rewrite partition_prod_nil_r; simpl.
    intros x.
    split; intros Hx; [ destruct j; contradiction | ].
    destruct Hx; destruct j; contradiction.

    rewrite nat_mod_add_once; [ | intros H; discriminate H ].
    rewrite nat_div_add_once; [ | intros H; discriminate H ].
    apply IHPL.
Qed.

Theorem partition_prod_is_partition : ∀ A (s := set_equiv) (E : set A) P Q,
  is_partition E P → is_partition E Q → is_partition E (partition_prod P Q).
Proof.
intros A s E P Q (HEP, HPij) (HEQ, HQij).
split.
 intros x.
 split; intros H.
  generalize H; intros HP; apply HEP in HP.
  generalize H; intros HQ; apply HEQ in HQ.
  clear - s HP HQ.
  induction P as [| P PL]; [ contradiction | simpl in HP ].
  destruct HP as [HP| HP].
   unfold partition_prod; simpl.
   rewrite map_app, map_map.
   pose proof union_list_app _ s eq_refl (map (intersection P) Q)
    (partition_prod PL Q) as HH.
   apply HH; clear HH.
   left; eapply union_list_intersection; assumption.

   unfold partition_prod; simpl.
   rewrite map_app, map_map.
   pose proof union_list_app _ s eq_refl (map (intersection P) Q)
    (partition_prod PL Q) as HH.
   apply HH; clear HH.
   right; apply IHPL; assumption.

  clear - HEP HEQ H.
  revert E Q HEP HEQ H.
  induction P as [| P PL]; intros; [ contradiction | ].
  unfold partition_prod in H; simpl in H.
  rewrite map_app, map_map in H.
  pose proof union_list_app _ s eq_refl (map (intersection P) Q)
    (partition_prod PL Q) as HH.
  apply HH in H; clear HH.
  apply HEP; simpl.
  destruct H as [H| H].
   left.
   clear -H.
   induction Q as [| Q QL]; [ contradiction | ].
   destruct H as [H| H]; [ destruct H; assumption | apply IHQL, H ].

   right.
   clear -s H.
   revert Q H.
   induction PL as [| P PL]; intros; [ contradiction | ].
   unfold partition_prod in H; simpl in H.
   rewrite map_app, map_map in H.
   pose proof union_list_app _ s eq_refl (map (intersection P) Q)
     (partition_prod PL Q) as HH.
   apply HH in H; clear HH.
   destruct H as [H| H].
    left.
    clear -H.
    induction Q as [| Q QL]; [ contradiction | ].
    destruct H as [H| H]; [ destruct H; assumption | apply IHQL, H ].

    right.
    eapply IHPL, H.

 intros i j Hij.
 split; [ | intros H; contradiction ].
 erewrite partition_prod_nth; [ | reflexivity ].
 erewrite partition_prod_nth; [ | reflexivity ].
 remember (length Q) as len eqn:Hlen.
 destruct Q as [| Q QL]; [ intros (_ & _ & H); subst len; contradiction | ].
 simpl in Hlen.
 intros Hx; simpl.
 destruct Hx as ((Hpi, Hqi), (Hpj, Hqj)).
 destruct (eq_nat_dec (i / len) (j / len)) as [Hd| Hd].
  destruct (eq_nat_dec (i mod len) (j mod len)) as [Hm| Hm].
   assert (Hnlen : (len ≠ 0)%nat) by (subst len; intros H; discriminate H).
   pose proof Nat.div_mod i len Hnlen as Hi.
   pose proof Nat.div_mod j len Hnlen as Hj.
   rewrite Hd, Hm, <- Hj in Hi.
   contradiction.

   eapply HQij; [ apply Hm | split; eassumption ].

  eapply HPij; [ apply Hd | split; eassumption ].
Qed.

Theorem equidec_trans : transitive _ (equidecomposable set_equiv).
Proof.
intros E F G HEF HFG.
destruct HEF as (PE & PF & HPE & HPF & Hlen1 & HEF).
destruct HFG as (P'F & P'G & HP'F & HP'G & Hlen2 & HFG).
unfold equidecomposable.
pose proof partition_prod_is_partition _ F PF P'F HPF HP'F as HFQR.
apply Forall2_Forall_combine in HEF.
remember (combine PE PF) as PEF eqn:HPEF.
set (s := set_equiv).
assert (Hgl : ∃ gl, Forall2 (λ g '(S₁, S₂), (app_gr g S₁ = S₂)%S) gl PEF).
 clear -HEF.
 induction PEF as [| PEF₁ PEF]; [ exists []; constructor | ].
 apply Forall_inv2 in HEF.
 destruct PEF₁ as (E₁, F₁).
 destruct HEF as ((g, Hg), HPEF).
 apply IHPEF in HPEF.
 destruct HPEF as (gl, HPEF).
 exists (g :: gl).
 constructor; assumption.

 destruct Hgl as (gl, Hgl).
 remember (fold_right (λ g gl, repeat g (length P'F) ++ gl) [] gl) as gll.
 rename Heqgll into Hgll.
 remember (partition_prod PF P'F) as PPF eqn:HPPF.
 remember (map (λ '(gi, PPFi), app_gr (app_gr_inv gi) PPFi) (combine gll PPF))
   as P'E eqn:HP'E.
 assert (Hleq : length gll = length PPF).
  subst gll PPF PEF.
  rewrite partition_prod_length.
  clear - PE HP'E Hlen1 Hgl.
  revert PE PF P'E P'F Hlen1 Hgl HP'E.
  induction gl as [| g gl]; intros.
   simpl in HP'E; simpl; subst P'E.
   destruct PE as [| PE₁ PE].
    symmetry in Hlen1.
    apply length_zero_iff_nil in Hlen1.
    subst PF; reflexivity.

    destruct PF as [| PF₁ PF]; [ reflexivity | ].
    simpl in Hgl; apply Forall2_nil_cons in Hgl; contradiction.

   simpl.
   rewrite app_length, repeat_length.
   destruct PE as [| PE₁ PE].
    apply Forall2_cons_nil in Hgl; contradiction.
    destruct PF as [| PF₁ PF].
     apply Forall2_cons_nil in Hgl; contradiction.

     simpl in Hlen1, Hgl; simpl; f_equal.
     apply Nat.succ_inj in Hlen1.
     apply Forall2_cons_cons in Hgl.
     destruct Hgl as (Hgl₁, Hgl).
     eapply IHgl; [ eassumption | assumption | reflexivity ].

  assert (Hophophop : is_partition E P'E).
   split.
    subst P'E.
bbb.

Add Parametric Relation : (point → Prop) (equidecomposable set_equiv)
 reflexivity proved by equidec_refl
 symmetry proved by equidec_sym
 transitivity proved by equidec_trans
 as equidec_morph.

Theorem Banach_Tarski_paradox_but_fixpoints :
  equidecomposable set_equiv sphere_but_fixpoints
    (xtransl 3 sphere_but_fixpoints ∪ xtransl 6 sphere_but_fixpoints)%S.
Proof.
set (s := set_equiv).
pose proof TTCA _ same_orbit equiv_same_orbit as H.
destruct H as (f & Hu & Hm).
remember (mkcf _ _ f Hm Hu) as Hosf.
remember (mkos _ f) as os eqn:Hos.
clear HeqHosf.
set (A₁ := (M ∪ SS ạ ∪ B)%S).
set (A₂ := (SS ạ⁻¹ ∖ B)%S).
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
(*
Definition rotation_fixpoint (m : matrix) k :=
  let x := (a₃₂ m - a₂₃ m)%R in
  let y := (a₁₃ m - a₃₁ m)%R in
  let z := (a₂₁ m - a₁₂ m)%R in
  let r := √ (x² + y² + z²) in
  P (k * x / r) (k * y / r) (k * z / r).

Definition sphere_fixpoint : point → Prop :=
  λ p, ∃ el, norm_list el ≠ [] ∧ ∃ k,
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
*)

(*
Theorem sphere_fixpoint_prop : ∀ p el,
  norm_list el ≠ []
  → fold_right rotate p el = p
  → sphere_fixpoint p.
Proof.
intros * Hn Hr.
unfold sphere_fixpoint.
rewrite rotate_vec_mul in Hr.
exists el.
split; [ assumption | ].
remember (fold_right mat_mul mat_id (map mat_of_elem el)) as m eqn:Hm.
generalize Hm; intros Hrm.
apply path_is_rotation in Hrm.
bbb.
unfold rotation_fixpoint.
remember (√ ((a₃₂ m - a₂₃ m)² + (a₁₃ m - a₃₁ m)² + (a₂₁ m - a₁₂ m)²)) as r.
destruct p as (x, y, z).
remember (√ (x² + y² + z²)) as rp eqn:Hrp.
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
   unfold orbit_without_fixpoint.
   intros * Hso Hn.
   assert (H : ∀ p', not (same_orbit p p' ∧ sphere_fixpoint p')).
    intros p' H; apply Hoh.
    exists p'; assumption.

    clear Hoh; rename H into Hoh.
    pose proof Hoh p₁ as Hp.
    intros H; apply Hp; clear Hp.
    split; [ assumption | ].
    eapply sphere_fixpoint_prop; eassumption.

  intros [(H, _)| [(H, _)| ]]; [ assumption | assumption | contradiction ].

 intros i j Hij.

bbb.
*)

Theorem Banach_Tarski_paradox :
  equidecomposable set_equiv sphere (xtransl 3 sphere ∪ xtransl 6 sphere)%S.
Proof.
set (s := set_equiv).
pose proof TTCA _ same_orbit equiv_same_orbit as H.
destruct H as (f & Hu & Hm).
remember (mkcf _ _ f Hm Hu) as Hosf.
remember (mkos _ f) as os eqn:Hos.
clear HeqHosf.
bbb.
set (A₁ := (M ∪ SS ạ ∪ B)%S).
set (A₂ := (SS ạ⁻¹ ∖ B)%S).
set (A₃ := SS ḅ).
set (A₄ := SS ḅ⁻¹).
exists [A₁; A₂; A₃; A₄].
exists
  (map (xtransl 3) [A₁; rot ạ A₂] ++
   map (xtransl 6) [A₃; rot ḅ A₄]); simpl.
split.
 subst A₁ A₂ A₃ A₄.

bbb.
