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
  | Rot : ∀ M, is_rotation_matrix M → Gr
  | Xtransl : ℝ → Gr
  | Comb : Gr → Gr → Gr.

Fixpoint app_gr f p :=
  match f with
  | Rot M Hrm => set_map (mat_vec_mul M) p
  | Xtransl dx => xtransl dx p
  | Comb g h => app_gr g (app_gr h p)
  end.

Fixpoint app_gr_vec f p :=
  match f with
  | Rot M Hrm => (mat_transp M * p)%vec
  | Xtransl dx => match p with V x y z => V (x - dx) y z end
  | Comb g h => app_gr_vec h (app_gr_vec g p)
  end.

Fixpoint gr_inv f :=
  match f with
  | Rot M Hrm => Rot (mat_transp M) (rotation_transp_is_rotation _ Hrm)
  | Xtransl dx => Xtransl (-dx)
  | Comb g h => Comb (gr_inv h) (gr_inv g)
  end.

Definition gr_ident := Xtransl 0.
Definition app_gr_inv g := app_gr (gr_inv g).

Theorem gr_subst : ∀ g E F,
  (E = F)%S → ∀ p, p ∈ app_gr g E → p ∈ app_gr g F.
Proof.
intros * HEF * HE.
revert E F p HEF HE.
induction g as [ M Hrm| dx | g IHg h IHh]; intros.
 destruct HE as (u & HuE & HMu).
 now exists u; split; [ apply HEF | ].

 destruct p as (x, y, z).
 apply HEF, HE.

 simpl in HE; simpl.
 eapply IHg; [ | eassumption ].
 split; intros H; [ eapply IHh; eassumption | ].
 eapply IHh; [ symmetry; eassumption | eassumption ].
Qed.

Theorem xtransl_0 : ∀ E, (xtransl 0 E = E)%S.
Proof.
intros; intros (x, y, z); simpl.
now unfold Rminus; rewrite Ropp_0, Rplus_0_r.
Qed.

Theorem xtransl_xtransl : ∀ E dx dy,
  (xtransl dx (xtransl dy E) = xtransl (dx + dy) E)%S.
Proof.
intros; intros (x, y, z); simpl.
now replace (x - dx - dy)%R with (x - (dx + dy))%R by lra.
Qed.

Theorem app_gr_ident : ∀ E, (app_gr gr_ident E = E)%S.
Proof.
intros.
unfold gr_ident; simpl.
unfold xtransl; simpl.
intros (x, y, z); simpl.
now rewrite Rminus_0_r.
Qed.

Theorem app_gr_nth : ∀ E fl i,
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

Theorem app_gr_nth_inv : ∀ E fl i,
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
with signature eq ==> set_eq ==> set_eq
as app_gr_morph.
Proof.
intros g p q Hpq r.
split; intros H; [ eapply gr_subst; eassumption | ].
symmetry in Hpq; eapply gr_subst; eassumption.
Qed.

Add Parametric Morphism : app_gr_inv
with signature eq ==> set_eq ==> set_eq
as app_gr_inv_morph.
Proof.
intros g p q Hpq r.
split; intros H; [ eapply gr_subst; eassumption | ].
symmetry in Hpq; eapply gr_subst; eassumption.
Qed.

Add Parametric Morphism : xtransl
  with signature eq ==> set_eq ==> set_eq
  as xtransl_morph.
Proof.
intros dx E F HEF (x, y, z); simpl; now rewrite HEF.
Qed.

Theorem fold_app_gr_inv : ∀ g, app_gr (gr_inv g) = app_gr_inv g.
Proof. easy. Qed.

Theorem set_map_mul_transp : ∀ M E,
  is_rotation_matrix M
  → (set_map (mat_vec_mul (mat_transp M)) (set_map (mat_vec_mul M) E) = E)%S.
Proof.
intros * Hrm.
intros p; simpl.
split; intros H.
 destruct H as (u & (v & Hv & Hvu) & Hu).
 rewrite <- Hvu, <- mat_vec_mul_assoc in Hu.
 rewrite rotation_mat_mul_transp_l in Hu; [ | easy ].
 rewrite mat_vec_mul_id in Hu.
 now rewrite <- Hu.

 exists (M * p)%vec.
 split; [ now exists p; split | ].
 rewrite <- mat_vec_mul_assoc.
 rewrite rotation_mat_mul_transp_l; [ | easy ].
 apply mat_vec_mul_id.
Qed.

Theorem app_gr_inv_l : ∀ g E,
  (app_gr_inv g (app_gr g E) = E)%S.
Proof.
intros.
unfold app_gr_inv.
revert E.
induction g as [ M Hrm | | ]; intros; simpl.
 now apply set_map_mul_transp.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 now rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.

 intros p.
 split; intros H.
  rewrite IHg1 in H; now apply IHg2.

  rewrite IHg1; apply IHg2, H.
Qed.

Theorem app_gr_inv_r : ∀ g E,
  (app_gr g (app_gr_inv g E) = E)%S.
Proof.
intros.
unfold app_gr_inv.
revert E.
induction g as [ M Hrm | | ]; intros; simpl.
 apply set_map_mul_transp.
 now apply rotation_transp_is_rotation.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 now rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.

 intros p.
 split; intros H.
  rewrite IHg2 in H; now apply IHg1.

  rewrite IHg2; apply IHg1, H.
Qed.

Theorem inv_app_gr : ∀ g E F,
  (app_gr g E = F)%S → (app_gr_inv g F = E)%S.
Proof.
intros * Ha.
rewrite <- Ha.
apply app_gr_inv_l.
Qed.

Theorem app_gr_app_gr_vec : ∀ g E p, p ∈ app_gr g E → app_gr_vec g p ∈ E.
Proof.
intros * Hp.
revert E p Hp.
induction g as [ M Hrm | | ]; intros.
 simpl in Hp; simpl.
 destruct Hp as (u & Hu & Hmu).
 rewrite <- Hmu, <- mat_vec_mul_assoc.
 rewrite rotation_mat_mul_transp_l; [ | easy ].
 now rewrite mat_vec_mul_id.

 now destruct p.

 simpl in Hp; simpl.
 apply IHg1 in Hp.
 now apply IHg2 in Hp.
Qed.

Theorem app_gr_empty_set : ∀ f, (app_gr f ∅ = ∅)%S.
Proof.
intros * p.
split; intros H; [ | easy ].
revert p H.
induction f as [ M Hrm | | ]; intros.
 now destruct H.

 now destruct p.

 simpl in H.
 eapply gr_subst in H; [ now apply IHf1 in H | ].
 split; [ apply IHf2 | easy ].
Qed.

Theorem app_gr_app_gr_inv : ∀ E g,
  (app_gr g (app_gr_inv g E) = E)%S.
Proof.
intros.
unfold app_gr_inv.
revert E.
induction g as [ M Hrm | | ]; intros.
 now apply set_map_mul_transp, rotation_transp_is_rotation.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 now replace (x + - r + r)%R with x by lra.

 simpl.
 rewrite IHg2.
 apply IHg1.
Qed.

Theorem app_gr_inv_app_gr : ∀ E g,
  (app_gr_inv g (app_gr g E) = E)%S.
Proof.
intros.
unfold app_gr_inv.
revert E.
induction g as [ M Hrm | | ]; intros.
 now apply set_map_mul_transp.

 intros (x, y, z); simpl.
 unfold Rminus; rewrite Ropp_involutive.
 now replace (x + r + - r)%R with x by lra.

 simpl.
 rewrite IHg1.
 apply IHg2.
Qed.

Theorem group_intersection_distr : ∀ g E F,
  (app_gr g (E ∩ F) = app_gr g E ∩ app_gr g F)%S.
Proof.
intros.
revert E F.
induction g; intros.
 apply set_map_inter_distr.
 now apply rot_mat_vec_mul_is_inj.

 now intros (x, y, z).

 intros p; simpl; now rewrite IHg2, IHg1.
Qed.

Theorem group_union_distr : ∀ g E F,
  (app_gr g (E ∪ F) = app_gr g E ∪ app_gr g F)%S.
Proof.
intros.
revert E F.
induction g; intros.
 apply set_map_union_distr.
 now intros (x, y, z).
 now intros p; simpl; rewrite IHg2, IHg1.
Qed.

Theorem group_union_list_distr : ∀ f EL,
  (app_gr f (⋃ EL) = ⋃ map (app_gr f) EL)%S.
Proof.
intros.
induction EL as [| E₁ EL].
 intros x; rewrite app_gr_empty_set; now split.

 intros x; simpl.
 rewrite group_union_distr.
 split; intros Hx.
  destruct Hx as [Hx| Hx]; [ now left | ].
  right; now apply IHEL.

  destruct Hx as [Hx| Hx]; [ now left | ].
  right; now apply IHEL.
Qed.

Theorem included_group : ∀ E F g, E ⊂ F ↔ app_gr g E ⊂ app_gr g F.
Proof.
intros.
split; intros HEF.
 revert E F HEF.
 induction g as [M Hrm| dx| ]; intros.
  intros u (v & Hv & Hm).
  now exists v; split; [ apply HEF | ].

  intros (x, y, z) Hp; now apply HEF.

  now apply IHg1, IHg2.

 intros p Hp.
 revert p E F HEF Hp.
 induction g as [M Hrm| dx| ]; intros.
  simpl in HEF.
  apply in_set_map with (f := mat_vec_mul M) in Hp.
  specialize (HEF (mat_vec_mul M p) Hp).
  apply set_map_in in HEF; [ easy | ].
  now apply rot_mat_vec_mul_is_inj.

  destruct p as (x, y, z); simpl in HEF.
  pose proof HEF (V (x + dx) y z) as H; simpl in H.
  unfold Rminus in H.
  rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r in H.
  apply H, Hp.

  simpl in HEF.
  eapply IHg2; [ | eassumption ].
  intros q Hq; eapply IHg1; eassumption.
Qed.

Theorem partition_group_map : ∀ (F : set vector) EL g,
  is_partition F EL → is_partition (app_gr g F) (map (app_gr g) EL).
Proof.
intros F EL * HP.
unfold is_partition in HP |-*.
destruct HP as (HF, HP).
split.
 induction g as [M Hrm| dx | g IHg h IHh ]; intros; simpl.
  split.
   intros Hr.
   revert F HF Hr.
   induction EL as [| E EL]; intros.
    rewrite HF in Hr.
    now destruct Hr.

    simpl in HF; simpl.
    generalize Hr; intros H.
    rewrite HF in H.
    rewrite set_map_union_distr in H.
    destruct H as [H| H]; [ now left | right ].
    eapply IHEL; [ | easy | eassumption ].
    intros i j Hij.
    unfold set_eq; simpl; intros y.
    assert (HSij : S i ≠ S j).
     intros HSij; now apply Hij, Nat.succ_inj.

     pose proof HP (S i) (S j) HSij y as HP; simpl in HP.
     destruct HP as (HQ, _).
     split; [ intros (HPi, HPj) | easy ].
     apply HQ; now split.

   intros Hme.
   revert F HF.
   induction EL as [| E EL]; intros; [ easy | ].
   simpl in Hme; rewrite HF.
   destruct Hme as [(u, Hme)| Hme].
    now exists u; split; [ left | ].

    rewrite set_map_union_list_distr; right.
    rewrite <- set_map_union_list_distr.
    apply IHEL; [ | easy | intros y; split; intros H; apply H ].
    intros i j Hij y.
    assert (HSij : S i ≠ S j).
     intros HSij; now apply Hij, Nat.succ_inj.

     pose proof HP (S i) (S j) HSij y as HP; simpl in HP.
     destruct HP as (HQ, _).
     split; [ intros (HPi, HPj) | easy ].
     apply HQ; now split.

  intros (x, y, z).
  split.
   intros Hp.
   revert F HF Hp.
   induction EL as [| E EL]; intros.
    unfold set_eq in HF; simpl in HF.
    now apply HF in Hp.

    simpl in HF; simpl.
    generalize Hp; intros H.
    apply HF in H; simpl in H.
    destruct H as [H| H]; [ now left | right ].
    eapply IHEL; [ | easy | eassumption ].
    intros i j Hij.
    unfold set_eq; simpl; intros q.
    assert (HSij : S i ≠ S j).
     intros HSij; now apply Hij, Nat.succ_inj.

     pose proof HP (S i) (S j) HSij q as HP; simpl in HP.
     destruct HP as (HQ, _).
     split; [ intros (HPi, HPj) | easy ].
     apply HQ; now split.

   intros Hme.
   revert F HF.
   induction EL as [| E EL]; intros; [ easy | ].
   simpl in HF, Hme; apply HF.
   destruct Hme as [Hme| Hme]; [ now left | ].
   right; simpl.
   apply IHEL; [ | easy | intros q; split; intros H; apply H ].
   intros i j Hij q.
   assert (HSij : S i ≠ S j).
    intros HSij; now apply Hij, Nat.succ_inj.

    pose proof HP (S i) (S j) HSij q as HP; simpl in HP.
    destruct HP as (HQ, _).
    split; [ intros (HPi, HPj) | easy ].
    apply HQ; now split.

  intros p.
  split.
   intros Hgh.
   revert F HF IHg IHh Hgh.
   induction EL as [| E EL]; intros.
    rewrite IHh in Hgh; simpl in Hgh.
    eapply app_gr_empty_set, Hgh.

    rewrite IHh in Hgh.
    simpl in Hgh.
    apply group_union_distr in Hgh.
    destruct Hgh as [Hgh| Hgh]; [ now left | right ].
    eapply IHEL; [ | easy | | | ].
     intros i j Hij.
     unfold set_eq; simpl; intros y.
     assert (HSij : S i ≠ S j).
      intros HSij; now apply Hij, Nat.succ_inj.

      pose proof HP (S i) (S j) HSij y as HP; simpl in HP.
      destruct HP as (HQ, _).
      split; [ intros (HPi, HPj) | easy ].
      apply HQ; now split.

     apply group_union_list_distr.

     apply group_union_list_distr.

     pose proof group_union_list_distr h EL.
     now rewrite <- H in Hgh.

   intros Hgh.
   revert F HF IHg IHh Hgh.
   induction EL as [| E ELl]; intros; [ easy | ].
   destruct Hgh as [Hgh| Hgh].
    rewrite IHh; simpl.
    rewrite set_eq_equiv; [ | now rewrite group_union_distr ].
    now left.

    rewrite HF; simpl.
    rewrite set_eq_equiv; [ | now rewrite group_union_distr ].
    rewrite set_eq_equiv; [ | now rewrite group_union_distr ].
    right.
    rewrite group_union_list_distr.
    rewrite set_eq_equiv; [ | now rewrite group_union_list_distr ].
    now rewrite map_map.

 intros i j Hij p.
 split; intros H; [ | easy ].
 rewrite <- app_gr_empty_set with (f := g) in H.
 do 2 rewrite map_nth in H.
 destruct H as (Hi, Hj).
 pose proof HP i j Hij (app_gr_vec g p) as Hp.
 destruct Hp as (Hpi, _).
 apply Hpi; clear Hpi.
 split.
  clear - Hi.
bbb.
  rename v into Ql.
  revert p Ql Hi.
  induction i; intros.
   destruct Ql as [| Q Ql]; [ now apply app_gr_empty_set in Hi | ].
   simpl in Hi; simpl.
   now apply app_gr_app_gr_vec.

   destruct Ql as [| Q Ql]; [ now apply app_gr_empty_set in Hi | ].
   simpl in Hi; simpl.
   now apply IHi.

  clear - Hj.
  rename v into Ql.
  revert p Ql Hj.
  induction j; intros.
   destruct Ql as [| Q Ql]; [ now apply app_gr_empty_set in Hj | ].
   simpl in Hj; simpl.
   now apply app_gr_app_gr_vec.

   destruct Ql as [| Q Ql]; [ now apply app_gr_empty_set in Hj | ].
   simpl in Hj; simpl.
   now apply IHj.
Qed.
