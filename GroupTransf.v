(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8.
Require Import Reals Nsatz Psatz.

Require Import Misc Words MiscReals Matrix Pset Orbit.
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

Definition gr_ident := Xtransl 0.
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

Theorem xtransl_0 : ∀ (s := set_equiv) E, (xtransl 0 E = E)%S.
Proof.
intros; intros (x, y, z); simpl.
now unfold Rminus; rewrite Ropp_0, Rplus_0_r.
Qed.

Theorem xtransl_xtransl : ∀ (s := set_equiv) E dx dy,
  (xtransl dx (xtransl dy E) = xtransl (dx + dy) E)%S.
Proof.
intros; intros (x, y, z); simpl.
now replace (x - dx - dy)%R with (x - (dx + dy))%R by lra.
Qed.

Theorem app_gr_ident : ∀ (s := set_equiv) E, (app_gr gr_ident E = E)%S.
Proof.
intros.
unfold gr_ident; simpl.
unfold xtransl; simpl.
intros (x, y, z); simpl.
now rewrite Rminus_0_r.
Qed.

Theorem app_gr_nth : ∀ (s := set_equiv) E fl i,
  (app_gr (List.nth i fl gr_ident) E =
   List.nth i (map app_gr fl) Datatypes.id E)%S.
Proof.
intros.
revert E i.
induction fl as [| f₁ fl]; intros.
 simpl; do 2 rewrite match_id.
 apply app_gr_ident.

 destruct i; [ easy | apply IHfl ].
Qed.

Theorem app_gr_nth_inv : ∀ (s := set_equiv) E fl i,
  (app_gr (List.nth i (map gr_inv fl) gr_ident) E =
   List.nth i (map app_gr_inv fl) Datatypes.id E)%S.
Proof.
intros.
revert E i.
induction fl as [| f₁ fl]; intros.
 simpl; do 2 rewrite match_id.
 apply app_gr_ident.

 destruct i; [ easy | apply IHfl ].
Qed.

Theorem gr_inv_ident : gr_inv gr_ident = gr_ident.
Proof.
unfold gr_ident; simpl.
f_equal; apply Ropp_0.
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

Add Parametric Morphism : xtransl
  with signature eq ==> @set_eq _ set_equiv ==> @set_eq _ set_equiv
  as xtransl_morph.
Proof.
intros dx E F HEF (x, y, z); simpl; now rewrite HEF.
Qed.

Theorem fold_app_gr_inv : ∀ g, app_gr (gr_inv g) = app_gr_inv g.
Proof. easy. Qed.

Theorem app_gr_inv_l : ∀ (s := set_equiv) g E,
  (app_gr_inv g (app_gr g E) = E)%S.
Proof.
intros.
unfold app_gr_inv.
revert E.
induction g; intros; simpl.
 intros p; simpl.
 rewrite negf_involutive, rotate_neg_rotate.
 easy.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
 easy.

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
 intros p; simpl.
 rewrite negf_involutive, rotate_rotate_neg.
 easy.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
 easy.

 intros p.
 split; intros H.
  rewrite IHg2 in H; apply IHg1; assumption.

  rewrite IHg2; apply IHg1, H.
Qed.

Theorem inv_app_gr : ∀ (s := set_equiv) g E F,
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

Theorem app_gr_app_gr_inv : ∀ (s := set_equiv) E g,
  (app_gr g (app_gr_inv g E) = E)%S.
Proof.
intros.
unfold app_gr_inv.
revert E.
induction g; intros.
 intros p; simpl.
 rewrite negf_involutive.
 now rewrite rotate_rotate_neg.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 now replace (x + - r + r)%R with x by lra.

 simpl.
 rewrite IHg2.
 apply IHg1.
Qed.

Theorem app_gr_inv_app_gr : ∀ (s := set_equiv) E g,
  (app_gr_inv g (app_gr g E) = E)%S.
Proof.
intros.
unfold app_gr_inv.
revert E.
induction g; intros.
 intros p; simpl.
 rewrite negf_involutive.
 now rewrite rotate_neg_rotate.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 now replace (x + r + - r)%R with x by lra.

 simpl.
 rewrite IHg1.
 apply IHg2.
Qed.

Theorem group_intersection_distr : ∀ (s := set_equiv) g E F,
  (app_gr g (E ∩ F) = app_gr g E ∩ app_gr g F)%S.
Proof.
intros.
revert E F.
induction g; intros; [ easy | intros (x, y, z); easy | ].
intros p; simpl; rewrite IHg2, IHg1; easy.
Qed.

Theorem group_union_distr : ∀ (s := set_equiv) g E F,
  (app_gr g (E ∪ F) = app_gr g E ∪ app_gr g F)%S.
Proof.
intros.
revert E F.
induction g; intros; [ easy | intros (x, y, z); easy | ].
intros p; simpl; rewrite IHg2, IHg1; easy.
Qed.

Theorem group_union_list_distr : ∀ (s := set_equiv) f EL,
  (app_gr f (⋃ EL) = ⋃ map (app_gr f) EL)%S.
Proof.
intros.
induction EL as [| E₁ EL].
 intros x; rewrite app_gr_empty_set; split; contradiction.

 intros x; simpl.
 rewrite group_union_distr.
 split; intros Hx.
  destruct Hx as [Hx| Hx]; [ left; assumption | ].
  right; apply IHEL; assumption.

  destruct Hx as [Hx| Hx]; [ left; assumption | ].
  right; apply IHEL; assumption.
Qed.

Theorem included_group : ∀ E F g, E ⊂ F ↔ app_gr g E ⊂ app_gr g F.
Proof.
intros.
split; intros HEF.
 revert E F HEF.
 induction g as [e| dx| ]; intros.
  intros p Hp; apply HEF; assumption.

  intros (x, y, z) Hp; apply HEF; assumption.

  apply IHg1, IHg2; assumption.

 intros p Hp.
 revert p E F HEF Hp.
 induction g as [e| dx| ]; intros.
  pose proof HEF (rotate e p) as H; simpl in H.
  rewrite rotate_neg_rotate in H; apply H, Hp.

  destruct p as (x, y, z); simpl in HEF.
  pose proof HEF (P (x + dx) y z) as H; simpl in H.
  unfold Rminus in H.
  rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r in H.
  apply H, Hp.

  simpl in HEF.
  eapply IHg2; [ | eassumption ].
  intros q Hq; eapply IHg1; eassumption.
Qed.

Theorem partition_group_map : ∀ (s := set_equiv) (F : set point) P g,
  is_partition F P → is_partition (app_gr g F) (map (app_gr g) P).
Proof.
intros s F P * HP.
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
   eapply IHPL; [ | easy | eassumption ].
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
    eapply IHPL; [ | simpl; easy | eassumption ].
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

     easy.

     apply group_union_list_distr.

     apply group_union_list_distr.

     pose proof group_union_list_distr h PL.
     rewrite <- H in Hgh; assumption.

   intros Hgh.
   revert F HF IHg IHh Hgh.
   induction P as [| P PL]; intros; [ contradiction | ].
   destruct Hgh as [Hgh| Hgh].
    rewrite IHh; simpl.
    rewrite set_eq_equiv; [ | rewrite group_union_distr; easy ].
    left; assumption.

    rewrite HF; simpl.
    rewrite set_eq_equiv; [ | rewrite group_union_distr; easy ].
    rewrite set_eq_equiv; [ | rewrite group_union_distr; easy ].
    right.
    rewrite group_union_list_distr.
    rewrite set_eq_equiv; [ | rewrite group_union_list_distr; easy ].
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
