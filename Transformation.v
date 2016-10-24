(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8.
Require Import Reals Nsatz.

Require Import Words MiscReals Matrix Pset Orbit.
Require Import Partition OrbitRepr.

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

Fixpoint gr_inv f :=
  match f with
  | Rot e => Rot (negf e)
  | Xtransl dx => Xtransl (-dx)
  | Comb g h => Comb (gr_inv h) (gr_inv g)
  end.

Definition app_gr_inv g := app_gr (gr_inv g).

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

Add Parametric Morphism : app_gr_inv
with signature eq ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
as app_gr_inv_morph.
Proof.
intros g p q Hpq r.
split; intros H; [ eapply gr_subst; eassumption | ].
symmetry in Hpq; eapply gr_subst; eassumption.
Qed.

Theorem app_gr_inv_l : ∀ (s := set_equiv) g E,
  (app_gr_inv g (app_gr g E) = E)%S.
Proof.
intros.
unfold app_gr_inv.
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

Theorem app_gr_inv_r : ∀ (s := set_equiv) g E,
  (app_gr g (app_gr_inv g E) = E)%S.
Proof.
intros.
unfold app_gr_inv.
revert E.
induction g; intros; simpl.
 unfold rot; simpl.
 intros p.
 rewrite negf_involutive, rotate_rotate_neg.
 reflexivity.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
 reflexivity.

 intros p.
 split; intros H.
  rewrite IHg2 in H; apply IHg1; assumption.

  rewrite IHg2; apply IHg1, H.
Qed.

Theorem app_gr_app_gr_inv : ∀ (s := set_equiv) g E F,
  (app_gr g E = F)%S → (app_gr_inv g F = E)%S.
Proof.
intros * Ha.
rewrite <- Ha.
apply app_gr_inv_l.
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

Theorem group_intersection_distr : ∀ (s := set_equiv) g E F,
  (app_gr g (E ∩ F) = app_gr g E ∩ app_gr g F)%S.
Proof.
intros.
revert E F.
induction g; intros; [ reflexivity | intros (x, y, z); reflexivity | ].
intros p; simpl; rewrite IHg2, IHg1; reflexivity.
Qed.

Theorem group_union_distr : ∀ (s := set_equiv) g E F,
  (app_gr g (E ∪ F) = app_gr g E ∪ app_gr g F)%S.
Proof.
intros.
revert E F.
induction g; intros; [ reflexivity | intros (x, y, z); reflexivity | ].
intros p; simpl; rewrite IHg2, IHg1; reflexivity.
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
