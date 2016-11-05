(* Banach-Tarski paradox. *)
(* Coq v8.6 *)

(* Equidecomposability *)

Require Import Utf8 List Relations.
Import ListNotations.
Require Import Reals.

Require Import Misc Matrix Pset.
Require Import Partition OrbitRepr GroupTransf.

Definition id {A} := @Datatypes.id A.

Definition equidecomposable (s : set_model point) E₁ E₂ :=
  ∃ P₁ P₂, is_partition E₁ P₁ ∧ is_partition E₂ P₂ ∧
  List.Forall2 (λ S₁ S₂, ∃ g, (app_gr g S₁ = S₂)%S) P₁ P₂.

Theorem equidec_refl : reflexive _ (equidecomposable set_equiv).
Proof.
intros E.
exists (E :: []), (E :: []).
split; [ apply is_partition_single | ].
split; [ apply is_partition_single | ].
constructor; [ | constructor ].
exists (Xtransl 0); unfold set_eq; simpl.
unfold xtransl; intros (x, y, z).
rewrite Rminus_0_r.
easy.
Qed.

Theorem equidec_sym : symmetric _ (equidecomposable set_equiv).
Proof.
intros E F (P₁ & P₂ & HP₁ & HP₂ & HEF).
exists P₂, P₁.
split; [ assumption | ].
split; [ assumption | ].
apply Forall2_sym; [ | assumption ].
clear -HEF.
intros E F (g & Hg).
exists (gr_inv g); rewrite <- Hg.
apply app_gr_inv_l.
Qed.

Definition partition_combine {A B} (fl : list (set A → set B)) PE PF :=
  flat_map (λ '(fi, Ei), map (λ Fj, Ei ∩ fi Fj) PF) (combine fl PE).

Definition partition_combine_swi {A B} (fl : list (set A → set B)) PE PF :=
  flat_map (λ Fj, map (λ '(fi, Ei), Ei ∩ fi Fj) (combine fl PE)) PF.

Theorem partition_combine_nth :
  ∀ A (s := set_equiv) fl (PE : list (set A)) PF i len,
  len = length PF
  → length fl = length PE
  → (∀ f, List.In f fl → (f ∅ = ∅)%S)
  → ((partition_combine fl PE PF).[i] =
     PE.[i / len] ∩ nth (i / len) fl id PF.[i mod len])%S.
Proof.
intros * Hlen HlfP Hf.
subst len.
unfold partition_combine; simpl.
revert fl PF i HlfP Hf.
induction PE as [| E₁ PE]; intros.
 destruct fl as [| f₁ fl]; [ | discriminate HlfP ].
 intros x.
 split; intros Hx; [ destruct i; contradiction | ].
 destruct Hx as (Hx, _).
 destruct (i / length PF)%nat; contradiction.

 destruct fl as [| f₁ fl]; [ discriminate HlfP | ].
 simpl in HlfP; apply Nat.succ_inj in HlfP; simpl.
 destruct (lt_dec i (length PF)) as [Hi| Hi].
  rewrite app_nth1; [| rewrite map_length; assumption ].
  rewrite Nat.div_small; [ simpl | assumption ].
  rewrite Nat.mod_small; [ simpl | assumption ].
  intros x; clear - HlfP Hf.
  split; intros Hx.
   revert i Hx.
   induction PF as [| F₁ PF]; intros; [ destruct i; contradiction | ].
   simpl in Hx; simpl.
   destruct i; [ assumption | apply IHPF; assumption ].

   revert i Hx.
   induction PF as [| F₁ PF]; intros.
    destruct Hx as (_, Hx).
    destruct i; simpl in Hx; simpl.
     rewrite Hf in Hx; [ contradiction | left; easy ].
     rewrite Hf in Hx; [ contradiction | left; easy ].

    destruct i; simpl in Hx; simpl; [ assumption | ].
    apply IHPF; assumption.

  apply Nat.nlt_ge in Hi.
  rewrite app_nth2; [| rewrite map_length; assumption ].
  rewrite map_length.
  remember (i - length PF)%nat as j eqn:Hj.
  assert (H : (i = j + length PF)%nat).
   rewrite Hj.
   rewrite Nat.sub_add; [ easy | assumption ].

   subst i; clear Hi Hj.
   destruct PF as [| F₁ PF].
    simpl.
    intros x.
    split; intros Hx.
     destruct j; simpl in Hx.
      induction (combine fl PE) as [| (y, z) l]; [ contradiction | ].
      apply IHl, Hx.

      induction (combine fl PE) as [| (y, z) l]; [ contradiction | ].
      apply IHl, Hx.

     rewrite Hf in Hx; [ | left; easy ].
     rewrite intersection_empty_r in Hx.
     contradiction.

    rewrite nat_mod_add_once; [ | intros H; discriminate H ].
    rewrite nat_div_add_once; [ | intros H; discriminate H ].
    apply IHPE; [ assumption | ].
    intros f Hfi.
    apply Hf; right; assumption.
Qed.

Theorem partition_combine_swi_nth :
  ∀ A (s := set_equiv) fl (PE : list (set A)) PF i len,
  len = length PE
  → length fl = length PE
  → (∀ f, List.In f fl → (f ∅ = ∅)%S)
  → ((partition_combine_swi fl PE PF).[i] =
     PE.[i mod len] ∩ nth (i mod len) fl id PF.[i / len])%S.
Proof.
intros * Hlen HlfP Hf.
subst len.
unfold partition_combine_swi; simpl.
revert fl PE i HlfP Hf.
induction PF as [| F₁ PF]; intros.
 simpl; do 2 rewrite match_id.
 clear -Hf.
 remember (i mod length PE) as j eqn:Hj; clear Hj.
 assert (Hj : ∀ j, (nth j fl id ∅ = ∅)%S).
  clear -Hf.
  induction fl as [| f₁ fl]; intros; [ simpl; now rewrite match_id | ].
  destruct j; [ now apply Hf; left | simpl ].
  apply IHfl.
  intros f₂ Hf₂; now apply Hf; right.

  now rewrite Hj, intersection_empty_r.

 simpl.
 destruct (lt_dec i (length fl)) as [Hi| Hi].
  rewrite app_nth1.
   rewrite HlfP in Hi.
   rewrite Nat.mod_small; [ | easy ].
   rewrite Nat.div_small; [ | easy ].
   intros x; clear - HlfP Hf.
   split; intros Hx.
    revert i fl Hx HlfP Hf.
    induction PE as [| E₁ PE]; intros.
     apply length_zero_iff_nil in HlfP; subst fl.
     simpl in Hx; now rewrite match_id in Hx.

     destruct fl as [| f₁ fl]; [ easy | ].
     simpl in HlfP; apply Nat.succ_inj in HlfP.
     destruct i; [ easy | ].
     simpl in Hx; simpl.
     apply IHPE; [ easy | easy | ].
     intros f Hfi.
     now apply Hf; right.

    destruct Hx as (Hx, Hxn).
    revert x i fl HlfP Hf Hx Hxn.
    induction PE as [| E₁ PE]; intros.
     now simpl in Hx; rewrite match_id in Hx.

     destruct fl as [| f₁ fl]; [ easy | ].
     simpl in HlfP; apply Nat.succ_inj in HlfP.
     simpl in Hx; simpl.
     destruct i; [ now split | ].
     apply IHPE; [ easy | | easy | easy ].
     intros f Hfi.
     now apply Hf; right.

   rewrite map_length, combine_length, Nat.min_l; [ easy | ].
   now rewrite HlfP.

  apply Nat.nlt_ge in Hi.
  rewrite app_nth2.
   rewrite IHPF; [ | easy | easy ].
   rewrite map_length, combine_length, Nat.min_l; [ | now rewrite HlfP ].
   rewrite HlfP in Hi.
   remember (length PE) as len eqn:Hlen; symmetry in Hlen.
   destruct (eq_nat_dec len 0) as [Hzl| Hnzl].
    move Hzl at top; subst len.
    apply length_zero_iff_nil in Hlen.
    apply length_zero_iff_nil in HlfP.
    subst PE fl; simpl.
    now do 2 rewrite intersection_empty_l.

    subst len.
    generalize Hi; intros H.
    apply Nat.div_le_mono with (c := length PE) in H; [ | easy ].
    rewrite Nat.div_same in H; [ | easy ].
    remember (i / length PE) as j eqn:Hj; symmetry in Hj.
    destruct j; [ now apply Nat.le_0_r in H | ].
    rewrite HlfP.
    remember (i - length PE) as k eqn:Hk.
    assert (i = k + length PE) by (now subst k; rewrite Nat.sub_add).
    subst i; clear Hk.
    rewrite nat_mod_add_once; [ | easy ].
    rewrite nat_div_add_once in Hj; [ | easy ].
    apply Nat.succ_inj in Hj.
    now rewrite Hj.

   rewrite map_length, combine_length, Nat.min_l; [ easy | ].
   now rewrite HlfP.
Qed.

Theorem partition_combine_is_partition :
  ∀ (s := set_equiv) E F PE PF P'F gl,
  is_partition E PE
  → is_partition F PF
  → length PE = length PF
  → length gl = length PE
  → is_partition F P'F
  → (∀ i : nat, (app_gr (nth i gl gr_ident) PE.[i] = PF.[i])%S)
  → ∀ fl, fl = map app_gr_inv gl
  → is_partition E (partition_combine fl PE P'F).
Proof.
intros * HPE HPF Hlen1 Hlen3 HP'F Hgl * Hfl.
split.
 destruct HPE as (HPEU, _).
 destruct HPF as (HPFU, _).
 destruct HP'F as (HP'FU, _).
 assert (HUP'F : F ⊂ ⋃ P'F) by (rewrite HP'FU; intros x H; assumption).
 clear HP'FU.
 unfold partition_combine.
 subst fl.
 revert E F gl PF P'F HPEU HPFU HUP'F Hlen1 Hlen3 Hgl.
 induction PE as [| E₁ PE]; intros.
  apply length_zero_iff_nil in Hlen3; subst gl; assumption.

  destruct gl as [| g₁ gl]; [ discriminate Hlen3 | ].
  rewrite HPEU; simpl.
  rewrite union_list_app; [ | easy ].
  simpl in Hlen3; apply Nat.succ_inj in Hlen3.
  apply union_morph.
   pose proof union_intersection_self point E₁ (map (app_gr_inv g₁) P'F).
   rewrite map_map in H.
   apply H.
   assert (HEF : E₁ ⊂ app_gr_inv g₁ F).
    rewrite HPFU.
    apply included_group with g₁.
    rewrite app_gr_inv_r.
    intros p Hp.
    pose proof Hgl 0 p as Hgl₁; simpl in Hgl₁.
    apply Hgl₁ in Hp.
    destruct PF as [| P₁ PF]; [ contradiction | simpl in Hp ].
    left; assumption.

    apply included_group with (g := gr_inv g₁) in HUP'F.
    rewrite group_union_list_distr in HUP'F.
    rewrite fold_app_gr_inv in HUP'F.
    eapply included_trans; eassumption.

   destruct PF as [| F₁ PF]; [ discriminate Hlen1 |  ].
   simpl in Hlen1; apply Nat.succ_inj in Hlen1.
   eapply IHPE; [ | | | eassumption | assumption | ]; try easy.
    rewrite HPFU in HUP'F.
    intros p Hp; apply HUP'F.
    right; assumption.

    intros i.
    pose proof (Hgl (S i)) as H; simpl in H.
    assumption.

 intros i j Hij.
 erewrite partition_combine_nth; [ | easy | | ].
  erewrite partition_combine_nth; [ | easy | | ].
   remember (length P'F) as len eqn:Hlen.
   destruct len.
    symmetry in Hlen.
    apply length_zero_iff_nil in Hlen; subst P'F; simpl.
    subst fl.
    destruct gl as [| g₁ gl].
     simpl; unfold id, Datatypes.id at 2; simpl.
     do 2 rewrite intersection_empty_r; easy.

     simpl; unfold app_gr_inv, Nat.div; rewrite app_gr_empty_set.
     do 2 rewrite intersection_empty_r; easy.

    destruct HPE as (HPEU, HPEI).
    destruct HP'F as (HP'FU, HP'FI).
    destruct (eq_nat_dec (i / S len) (j / S len)) as [Hd| Hd].
     destruct (eq_nat_dec (i mod S len) (j mod S len)) as [Hm| Hm].
      assert (Hnlen : (S len ≠ 0)%nat) by (intros H; discriminate H).
      pose proof Nat.div_mod i (S len) Hnlen as Hi.
      pose proof Nat.div_mod j (S len) Hnlen as Hj.
      rewrite Hd, Hm, <- Hj in Hi;  contradiction.

      subst fl; rewrite <- Hd; simpl.
      pose proof map_nth app_gr_inv gl gr_ident (i / S len) as Hi.
      destruct (lt_dec (i / S len) (length gl)) as [Hil| Hil].
       rewrite nth_indep with (d' := id) in Hi.
        rewrite Hi, intersection_shuffle0.
        rewrite intersection_assoc, <- intersection_assoc.
        unfold app_gr_inv; rewrite <- group_intersection_distr.
        apply not_eq_sym in Hm.
        rewrite HP'FI; [ | assumption ].
        rewrite app_gr_empty_set.
        apply intersection_empty_r.

        rewrite map_length; assumption.

       apply Nat.nlt_ge in Hil.
       rewrite Hlen3 in Hil.
       rewrite nth_overflow; [ | assumption ].
       do 2 rewrite intersection_empty_l; easy.

     rewrite intersection_shuffle0, intersection_assoc.
     rewrite HPEI; [ | assumption ].
     do 2 rewrite intersection_empty_l; easy.

   subst fl; rewrite map_length; assumption.

   subst fl.
   intros f Hf.
   apply in_map_iff in Hf.
   destruct Hf as (g & Hg & Hix).
   subst f; apply app_gr_empty_set.

  subst fl; rewrite map_length; assumption.

  subst fl.
  intros f Hf.
  apply in_map_iff in Hf.
  destruct Hf as (g & Hg & Hix).
  subst f; apply app_gr_empty_set.
Qed.

Require Import Permutation.

Theorem partition_combine_swi_is_permutation :
  ∀ A (fl : list (set A → set A)) PE P'F,
  Permutation (partition_combine_swi fl PE P'F) (partition_combine fl PE P'F).
Proof.
intros.
unfold partition_combine, partition_combine_swi.
rewrite Permutation_flat_map_map.
induction (combine fl PE) as [| a la]; intros; [ easy | ].
simpl; rewrite IHla; destruct a; easy.
Qed.

Theorem permuted_partition_is_partition :
  ∀ A (s := set_equiv) (E : set A) PE P'E,
  Permutation PE P'E
  → is_partition E PE
  → is_partition E P'E.
Proof.
intros * Hpe Hpa.
destruct Hpa as (Hpau, Hpai).
split.
 rewrite Hpau; clear -Hpe.
 induction Hpe; [ easy | | | ].
  simpl; rewrite IHHpe; easy.

  simpl; rewrite union_comm, <- union_assoc.
  apply union_morph; [ easy | apply union_comm ].

  etransitivity; eassumption.

 intros i j Hij x.
 split; [ intros Hx; simpl | contradiction ].
 apply Permutation_nth_error in Hpe.
 destruct Hpe as (Hlen & f & Hfi & Hn).
 unfold FinFun.Injective in Hfi.
 assert (Hfij : f i ≠ f j) by (intros H; now apply Hfi in H).
 assert (HP'P : ∀ i, P'E.[i] = PE.[f i]).
  intros k.
  pose proof Hn k as Hk.
  remember (nth_error P'E k) as p'k eqn:H'k.
  symmetry in Hk, H'k.
  destruct p'k as [v | ].
   apply nth_error_split in Hk.
   apply nth_error_split in H'k.
   destruct Hk as (l1 & l2 & HPE & Hlen1).
   destruct H'k as (l'1 & l'2 & HP'E & Hlen'1).
   rewrite HPE, HP'E, <- Hlen1, <- Hlen'1.
   rewrite app_nth2; [ | now unfold ge ].
   rewrite app_nth2; [ | now unfold ge ].
   now do 2 rewrite Nat.sub_diag.

   apply nth_error_None in Hk.
   apply nth_error_None in H'k.
   rewrite nth_overflow; [ | easy ].
   now rewrite nth_overflow.

  do 2 rewrite HP'P in Hx.
  now rewrite Hpai in Hx.
Qed.

Theorem partition_combine_partition_combine_swi :
  ∀ A (s := set_equiv) E (fl : list (set A → set A)) PE P'F,
  is_partition E (partition_combine fl PE P'F)
  → is_partition E (partition_combine_swi fl PE P'F).
Proof.
intros * HP.
eapply permuted_partition_is_partition; [ | eassumption ].
symmetry.
apply partition_combine_swi_is_permutation.
Qed.

Theorem partition_combine_swi_is_partition :
  ∀ (s := set_equiv) E F PE PF P'F gl,
  is_partition E PE
  → is_partition F PF
  → length PE = length PF
  → length gl = length PE
  → is_partition F P'F
  → (∀ i : nat, (app_gr (nth i gl gr_ident) PE.[i] = PF.[i])%S)
  → ∀ fl, fl = map app_gr_inv gl
  → is_partition E (partition_combine_swi fl PE P'F).
Proof.
intros * HPE HPF Hlen1 Hlen3 HP'F Hgl * Hfl.
apply partition_combine_partition_combine_swi.
eapply partition_combine_is_partition with (F := F) (PF := PF); eassumption.
Qed.

Theorem partition_combine_length :
  ∀ A fl (PE PF : list (set A)),
  length fl = length PE
  → length (partition_combine fl PE PF) = (length PE * length PF)%nat.
Proof.
intros * Hlen.
unfold partition_combine; simpl.
revert fl PF Hlen.
induction PE as [| E₁ PE]; intros; [ destruct fl; easy | simpl ].
destruct fl as [| f₁ fl]; [ discriminate Hlen | ].
destruct PF as [| F₁ FL].
 unfold partition_combine; simpl.
 rewrite Nat.mul_0_r.
 induction (combine fl PE) as [| (x, y) l]; [ easy | apply IHl ].

 simpl in Hlen; simpl; f_equal.
 rewrite app_length, map_length.
 apply Nat.succ_inj in Hlen.
 apply IHPE with (PF := F₁ :: FL) in Hlen.
 simpl in Hlen; rewrite Hlen; easy.
Qed.

Theorem partition_combine_swi_length :
  ∀ A fl (PE PF : list (set A)),
  length fl = length PE
  → length (partition_combine_swi fl PE PF) = (length PE * length PF)%nat.
Proof.
intros * Hlen.
pose proof partition_combine_swi_is_permutation _ fl PE PF as H.
apply Permutation_length in H.
now rewrite H; apply partition_combine_length.
Qed.

Require Import Setoid.
Add Parametric Morphism :
  (λ n fl, @nth (set point → set point) n (map app_gr_inv fl) id)
  with signature eq ==> eq ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as nth_map_app_gr_inv_morph.
Proof.
intros n fl E F HEF x.
split; intros Hx.
 revert n Hx.
 induction fl as [| f₁ fl]; intros.
  simpl in Hx; simpl; rewrite match_id in Hx |-*; now apply HEF.

  simpl in Hx; simpl.
  now destruct n; [ rewrite <- HEF | apply IHfl ].

 revert n Hx.
 induction fl as [| f₁ fl]; intros.
  simpl in Hx; simpl; rewrite match_id in Hx |-*; now apply HEF.

  simpl in Hx; simpl.
  now destruct n; [ rewrite HEF | apply IHfl ].
Qed.

Theorem equidec_trans : transitive _ (equidecomposable set_equiv).
Proof.
intros E F G HEF HFG.
unfold equidecomposable.
destruct HEF as (PE & P₁F & HPE & HP₁F & HEF).
destruct HFG as (P₂F & PG & HP₂F & HPG & HFG).
set (s := set_equiv).
assert
  (Hgl : ∃ gl, length gl = length PE ∧
   ∀ i, (app_gr (nth i gl gr_ident) (nth i PE ∅) = nth i P₁F ∅)%S).
 apply Forall2_Forall_combine in HEF.
 destruct HEF as (HEF, Hlen1).
 clear HPE HP₁F.
 revert P₁F Hlen1 HEF.
 induction PE as [| E₁ PE]; intros.
  exists []; split; [ easy | ].
  symmetry in Hlen1; apply length_zero_iff_nil in Hlen1; subst P₁F.
  intros i; simpl.
  do 2 rewrite match_id; simpl.
  intros (x, y, z); split; contradiction.

  destruct P₁F as [| F₁ P₁F]; [ discriminate Hlen1 | ].
  simpl in Hlen1; apply Nat.succ_inj in Hlen1.
  simpl in HEF; apply Forall_inv2 in HEF.
  destruct HEF as ((g₁, HgEF), HEF).
  apply IHPE in HEF; [ | assumption ].
  destruct HEF as (gl & Hlen3 & HEF).
  exists (g₁ :: gl).
  split; [ simpl; rewrite Hlen3; easy | ].
  intros i; simpl.
  destruct i; [ assumption | apply HEF ].

 assert
   (Hhl : ∃ hl, length hl = length PG ∧
    ∀ i, (app_gr (nth i hl gr_ident) (nth i PG ∅) = nth i P₂F ∅)%S).
  apply Forall2_Forall_combine in HFG.
  destruct HFG as (HFG, Hlen2).
  clear HPG HP₂F.
  revert P₂F Hlen2 HFG.
  induction PG as [| G₁ PG]; intros.
   exists []; split; [ easy | ].
   apply length_zero_iff_nil in Hlen2; subst P₂F.
   intros i; simpl.
   do 2 rewrite match_id; simpl.
   intros (x, y, z); split; contradiction.

   destruct P₂F as [| F₁ P₂F]; [ discriminate Hlen2 | ].
   simpl in Hlen2; apply Nat.succ_inj in Hlen2.
   simpl in HFG; apply Forall_inv2 in HFG.
   destruct HFG as ((h₁, HhFG), HFG).
   apply IHPG in HFG; [ | assumption ].
   destruct HFG as (hl & Hlen3 & HFG).
   exists (gr_inv h₁ :: hl).
   split; [ simpl; rewrite Hlen3; easy | ].
   intros i; simpl.
   destruct i; [ | apply HFG ].
   rewrite <- HhFG, fold_app_gr_inv.
   rewrite app_gr_inv_l; easy.

  destruct Hgl as (gl & Hlen3 & Hgl).
  destruct Hhl as (hl & Hlen4 & Hhl).
  apply Forall2_Forall_combine in HEF.
  destruct HEF as (HEF, Hlen1).
  apply Forall2_Forall_combine in HFG.
  destruct HFG as (HFG, Hlen2).
  remember (map app_gr_inv gl) as g'l eqn:Hg'l.
  assert (Hpcf : is_partition E (partition_combine g'l PE P₂F)).
   eapply partition_combine_is_partition with (PF := P₁F); eassumption.

   exists (partition_combine g'l PE P₂F).
   remember (map app_gr_inv hl) as h'l eqn:Hh'l.
   assert (Hpcg : is_partition G (partition_combine_swi h'l PG P₁F)).
    symmetry in Hlen2.
    eapply partition_combine_swi_is_partition with (PF := P₂F); eassumption.

    exists (partition_combine_swi h'l PG P₁F).
    split; [ assumption | ].
    split; [ assumption | ].
    apply Forall2_Forall_combine.
    split.
     apply Forall_forall.
     intros (U, V) HUV.
     apply In_nth with (d := (∅, ∅)) in HUV.
     rewrite combine_length in HUV.
     rewrite partition_combine_length in HUV.
      rewrite partition_combine_swi_length in HUV.
       rewrite <- Hlen1, Hlen2, Nat.mul_comm in HUV.
       rewrite Nat.min_l in HUV; [ | easy ].
       destruct HUV as (i & Hi & HUV).
       rewrite combine_nth in HUV.
        injection HUV; clear HUV; intros HV HU.
        apply eq_set_eq in HU.
        apply eq_set_eq in HV.
        remember (partition_combine g'l PE P₂F) as PE' eqn:HPE'.
        remember (partition_combine_swi h'l PG P₁F) as PG' eqn:HPG'.
        subst g'l h'l.
        destruct Hpcf as (HpcfU, HpcfI).
        destruct Hpcg as (HpcgU, HpcgI).
        remember (nth (i / length PG) gl gr_ident) as gi.
        remember (nth (i mod length PG) (map gr_inv hl) gr_ident) as hj.
        exists (Comb hj gi); subst gi hj; simpl.
        rewrite <- HU, <- HV; clear HU HV.
        rewrite HPE', HPG'.
        rewrite partition_combine_nth; [ | easy | | ].
         rewrite partition_combine_swi_nth; [ | easy | | ].
          do 2 rewrite group_intersection_distr.
          rewrite Hlen2, Hgl.
          rewrite intersection_comm.
          apply intersection_morph.
           rewrite app_gr_nth.
           replace Datatypes.id with (@id (set point)) by easy.
           rewrite map_map.
           (* does not work, I don't know why
           rewrite <- Hhl.
           *)
           (* using transitivity instead *)
           etransitivity.
            apply nth_map_app_gr_inv_morph_Proper; [ easy | easy | ].
            apply app_gr_morph_Proper; [ easy | ].
            apply nth_map_app_gr_inv_morph_Proper; [ easy | easy | ].
            symmetry; apply Hhl.

            do 2 rewrite Nat.add_0_r.
            do 2 rewrite <- app_gr_nth_inv.
            assert (HPGnz : length PG ≠ 0).
             intros H; rewrite H in Hi.
             now apply Nat.nlt_0_r in Hi.

             setoid_rewrite nth_indep with (d' := gr_inv gr_ident).
              do 2 rewrite map_nth.
              rewrite gr_inv_ident.
              remember (nth (i / length PG) gl gr_ident) as x.
              do 2 rewrite fold_app_gr_inv.
              rewrite app_gr_app_gr_inv.
              now rewrite app_gr_inv_app_gr.

              rewrite map_length, Hlen4.
              now apply Nat.mod_upper_bound.

              now rewrite Hlen3; apply Nat.div_lt_upper_bound.

              rewrite map_length, Hlen3.
              now apply Nat.div_lt_upper_bound.

              rewrite Hlen4.
              now apply Nat.mod_upper_bound.

           rewrite app_gr_nth.
           replace Datatypes.id with (@id (set point)) by easy.
           now rewrite map_map.

          now rewrite map_length.

          intros f Hif.
          clear -Hif.
          induction hl as [| h₁ hl]; [ easy | ].
          destruct Hif; [ subst f; apply app_gr_empty_set | now apply IHhl ].

         now rewrite map_length.

         intros f Hif.
         clear -Hif.
         induction gl as [| g₁ gl]; [ easy | ].
         destruct Hif; [ subst f; apply app_gr_empty_set | now apply IHgl ].

        rewrite partition_combine_length.
         rewrite partition_combine_swi_length.
          rewrite Hlen1, Hlen2.
          apply Nat.mul_comm.

          now subst h'l; rewrite map_length.

         now subst g'l; rewrite map_length.

       now rewrite Hh'l, map_length.

      now rewrite Hg'l, map_length.

     rewrite partition_combine_length.
      rewrite partition_combine_swi_length.
       rewrite Hlen1, Hlen2.
       apply Nat.mul_comm.

       now subst h'l; rewrite map_length.

       now subst g'l; rewrite map_length.
Qed.

Add Parametric Relation : (set point) (equidecomposable set_equiv)
 reflexivity proved by equidec_refl
 symmetry proved by equidec_sym
 transitivity proved by equidec_trans
 as equidec_morph.
