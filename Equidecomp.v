(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List Relations.
Import ListNotations.
Require Import Reals.

Require Import Misc Matrix Pset.
Require Import Partition OrbitRepr Transformation.

Definition equidecomposable (s : set_model point) E₁ E₂ :=
  ∃ P₁ P₂, is_partition E₁ P₁ ∧ is_partition E₂ P₂ ∧ length P₁ = length P₂ ∧
  List.Forall2 (λ S₁ S₂, ∃ g, (app_gr g S₁ = S₂)%S) P₁ P₂.

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
exists (gr_inv g); rewrite <- Hg.
apply app_gr_inv_l.
Qed.

Definition partition_prod {A} (PL QL : list (set A)) :=
  flat_map (λ p, map (intersection p) QL) PL.

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
Proof. reflexivity. Qed.

Theorem partition_prod_length :
  ∀ A (P Q : list (set A)),
  length (partition_prod P Q) = (length P * length Q)%nat.
Proof.
intros A P Q.
revert Q.
induction P as [| P PL]; intros; [ reflexivity | simpl ].
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
   rewrite partition_prod_cons_l, union_list_app; [ | reflexivity ].
   left; eapply union_list_intersection; assumption.

   rewrite partition_prod_cons_l, union_list_app; [ | reflexivity ].
   right; apply IHPL; assumption.

  clear - HEP HEQ H.
  revert E Q HEP HEQ H.
  induction P as [| P PL]; intros; [ contradiction | ].
  rewrite partition_prod_cons_l, union_list_app in H; [ | reflexivity ].
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
   rewrite partition_prod_cons_l, union_list_app in H; [ | reflexivity ].
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
 assert (HglPEF : length gl = length PEF).
  clear - Hgl.
  revert PEF Hgl.
  induction gl as [| g gl]; intros.
   destruct PEF as [| PEF₁ PEF]; [ reflexivity | ].
   apply Forall2_nil_cons in Hgl; contradiction.

   destruct PEF as [| PEF₁ PEF].
    apply Forall2_cons_nil in Hgl; contradiction.

    simpl; f_equal.
    apply Forall2_cons_cons in Hgl.
    destruct Hgl as (_, Hgl).
    apply IHgl; assumption.

  remember (partition_prod PF P'F) as PPF eqn:HPPF.
  remember
    (flat_map (λ '(p, g), map (λ q, app_gr (gr_inv g) (p ∩ q)) P'F)
       (combine PF gl)) as PPE eqn:HPPE.

  assert (Hlen3 : length gl = length PF).
   transitivity (length PEF); [ assumption | ].
   rewrite HPEF, combine_length, Hlen1, Nat.min_idempotent.
   reflexivity.

   assert (Hlen4 : length PPE = length PPF).
    subst PPE PPF.
    rewrite partition_prod_length.
    clear HPF Hlen1 HPEF HFQR Hgl HglPEF.
    revert gl Hlen3.
    induction PF as [| PF₁ PF]; intros; [ reflexivity | ].
    destruct gl as [| g gl]; [ discriminate Hlen3 | ].
    simpl in Hlen3; apply Nat.succ_inj in Hlen3.
    simpl; rewrite app_length, IHPF; [ | assumption ].
    rewrite map_length; reflexivity.

    assert (is_partition E PPE).
     split.
(**)
      subst PEF PPF.
      clear HEF G P'G HP'G Hlen2 HFG.
      move s at top.
      move P'F before PF.
      move HP'F before HPF.
      move HFQR before HP'F.
      move gl before HFQR.
      move PPE before gl.
      rename Hlen3 into Hlen2.
      clear HglPEF.
      rename Hlen4 into Hlen3.
      move Hlen2 before Hlen1.
      move Hlen3 before Hlen2.
      rewrite partition_prod_length in Hlen3.
assert (Hinc : Forall (λ Fi, Fi ⊂ F) PF).
 destruct HPF as (HPFU, HPFI).
 apply union_list_all_included; assumption.

assert
  (HFi : Forall (λ Fi, (Fi = ⋃ map (intersection Fi) P'F)%S) PF).

Theorem glop : ∀ A (s := set_equiv) (EL FL : list (set A)),
  ⋃ EL ⊂ ⋃ FL
  → (Forall (λ ELi, (ELi = ⋃ map (intersection ELi) FL)%S) EL).
Proof.
intros * HEF.
bbb.

apply glop.
destruct HPF as (HPFU, HPFI).
destruct HP'F as (HP'FU, HP'FI).
rewrite <- HPFU, <- HP'FU.
intros x Hx; assumption.
bbb.

 clear HPF HFQR Hlen1 Hlen2 Hlen3 Hgl HPPE.
 induction PF as [| PF₁ PF]; [ constructor | ].
 apply Forall_inv2 in Hinc.
 destruct Hinc as (Hinc₁, Hinc).
 constructor; [ | apply IHPF; assumption ].
 destruct HP'F as (HFU, HFI).
 clear Hinc IHPF HFI.
 revert F PF₁ HFU Hinc₁.
 induction P'F as [| P'F₁ P'F]; intros.
  rewrite HFU in Hinc₁; simpl in Hinc₁.
  split; [ apply Hinc₁ | contradiction ].

  remember set_eq as f; simpl; subst f.
  intros p.
  split; intros Hp.
bbb.
   left.
    split; [ assumption | ].

Theorem included_intersection : ∀ A (s := set_equiv) (E F G : set A),
  E ⊂ F → E ⊂ G → (E = F ∩ G)%S.
Admitted. Show.

Set Printing All. Show.
Check included_intersection.

bbb.
      revert E F PE P'F gl PPE HPE HPF HP'F HFQR Hlen1 Hlen2 Hlen3
        Hgl HPPE.
      induction PF as [| PF₁ PF]; intros.
       apply length_zero_iff_nil in Hlen1; subst PE PPE; apply HPE.

       destruct gl as [| g₁ gl]; [ discriminate Hlen2 | ].
       simpl in HPPE.
       clear Hlen1.
       revert E HPE.
       induction PE as [| PE₁ PE]; intros.
        apply Forall2_cons_nil in Hgl; contradiction.

bbb.
(*
      clear - Hlen1 Hlen3 HPE HPF Hgl HP'F.
*)
clear HEF Hlen2 HFG HPPF HFQR HglPEF HPPE.
      revert E F PE P'F gl HPE HPF HP'F Hlen1 Hlen3 Hgl.
      induction PF as [| PF₁ PF]; intros.
       apply length_zero_iff_nil in Hlen1; subst PE; apply HPE.

       destruct gl as [| g gl]; [ discriminate Hlen3 | ].
       simpl; rewrite fold_set_eq.
       destruct PE as [| PE₁ PE]; [ discriminate Hlen1 | ].
       simpl in Hlen1, Hlen3.
       apply Nat.succ_inj in Hlen1.
       apply Nat.succ_inj in Hlen3.
(*
       rewrite union_list_app; [ | reflexivity ].
       generalize HPE; intros HUI.
       destruct HUI as (HU, HI); rewrite HU.
       remember set_eq as f; simpl; subst f.
       simpl in Hgl.
       apply Forall2_cons_cons in Hgl.
       destruct Hgl as (Hg, Hgl).
       apply union_morph.
        Focus 2.
bbb.
        eapply IHPF; try eassumption.
         split; [ reflexivity | ].
         intros i j Hij.
         pose proof HI (S i) (S j) as H.
         apply H; intros HH; apply Nat.succ_inj in HH.
         contradiction.
bbb.

        rewrite fold_set_eq in Hg.
induction P'F as [| P'F₁ P'F].
remember set_eq as f; simpl; subst f.
bbb.
*)
       assert (HPM : is_partition (E ∖ PE₁) PE).
        split.
         destruct HPE as (Hu & Hi).
         intros p; rewrite Hu; simpl.
         split; intros Hp.
          destruct Hp as ([Hp| Hp], Hnp); [ contradiction | ].
          assumption.

          split; [ right; assumption | ].
          clear Hlen1.
          revert E p Hu Hp.
          induction PE as [| PE₂ PE]; intros; [ contradiction | ].
          destruct Hp as [Hp| Hp].
           pose proof Hi 0 1 (Nat.neq_succ_diag_r 0) as H.
           simpl in H; intros Hp₁; eapply H; split; eassumption.

           eapply IHPE; [ | | reflexivity | assumption ].
            intros i j Hij.
            destruct i.
             destruct j; [ exfalso; apply Hij; reflexivity | ].
             pose proof Hi 0 (S (S j)) as H.
             remember set_eq as f; simpl in H; subst f.
             apply H; intros HH; discriminate HH.

             destruct j.
              pose proof Hi (S (S i)) 0 as H.
              remember set_eq as f; simpl in H; subst f.
              apply H; intros HH; discriminate HH.

              simpl.
              pose proof Hi (S (S i)) (S (S j)) as H; simpl in H.
              apply H; intros HH.
              apply Nat.succ_inj in HH; contradiction.

            remember (PE₂ :: PE) as PE'.
            remember set_eq as f; simpl in Hgl; simpl; subst f.
            subst PE'.
            apply Forall2_cons_cons in Hgl.
            destruct Hgl as (Hg, Hgl).
            constructor; [ assumption | ].
bbb.
         intros i j Hij.
         destruct HPE as (Hu, Hi).
         pose proof Hi (S i) (S j) as H; simpl in H.
         apply H; intros HH.
         apply Nat.succ_inj in HH; contradiction.

        pose proof IHPF (E ∖ PE₁) PE gl HPM Hlen1 Hlen3 as H.
        rewrite union_list_app; [ | reflexivity ].
Theorem set_subtract_union : ∀ A (s := set_equiv) (E F G : set A),
  (∀ x, x ∈ F ∨ x ∉ F) → F ⊂ E → (E ∖ F = G)%S → (E = F ∪ G)%S.
Proof.
intros * HDF HFE HEF.
unfold included in HFE.
unfold subtract in HEF.
Transparent set_eq.
unfold set_eq in HEF.
simpl in HEF.
unfold union, set_eq; simpl.
intros x.
split; intros Hx.
 destruct (HDF x) as [HF| HnF]; [ left; assumption | ].
 right; apply HEF; split; assumption.

 destruct Hx as [Hx| Hx]; [ apply HFE; assumption | ].
 apply HEF; assumption.
Qed.

apply set_subtract_union in H.
Focus 2.

bbb.
  assert (Hophophop : is_partition E P'E).
   split.
    subst P'E.
    remember (combine gll PPF) as gpl eqn:Hgpl.
    symmetry in Hgpl.
    induction gpl as [| gp].
     intros p; split; [ intros H; simpl | contradiction ].
     destruct gll as [| gl₁ gll].
      symmetry in Hleq.
      apply length_zero_iff_nil in Hleq; subst PPF.
      destruct PF as [| PF₁ PF].
       apply length_zero_iff_nil in Hlen1; subst PE.
       apply is_partition_empty in HPE.
       rewrite HPE in H; contradiction.

       destruct PE as [| PE₁ PE]; [ discriminate Hlen1 | ].
       destruct P'F as [| P'F₁ P'F ].
        apply is_partition_empty in HP'F.
        unfold is_partition in HPF.
        destruct HPF as (HPF, HPFij).
        rewrite HP'F in HPF.
        simpl in HPF.
simpl in Hgll, HPEF.
subst PEF.
destruct gl as [| g₁ gl].
 apply Forall2_nil_cons in Hgl; contradiction.

 simpl in Hgll.
 apply Forall2_cons_cons in Hgl.
 destruct Hgl as (Hgg, Hgl).
 destruct gl as [| g₂ gl].
(*clear G P'G HP'G Hlen2 HFG Hgll Hleq Hgpl HFQR.*)
simpl in Hlen1; apply Nat.succ_inj in Hlen1.
unfold is_partition in HPE.
destruct HPE as (HE, HPE).
rewrite HE in H.
destruct H as [H| H].
 apply app_gr_app_gr_inv in Hgg.
 rewrite <- Hgg in H.
  remember (app_gr_point g₁ p) as q eqn:Hq.
pose proof HPF q as Hfq.
destruct Hfq as (_, Hfq).
destruct g₁.
Require Import Words.
simpl in Hq.
simpl in H.
rewrite negf_involutive in H.
bbb.
  apply HPF with (x := q).
bbb.

Add Parametric Relation : (point → Prop) (equidecomposable set_equiv)
 reflexivity proved by equidec_refl
 symmetry proved by equidec_sym
 transitivity proved by equidec_trans
 as equidec_morph.
