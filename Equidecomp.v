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
reflexivity.
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

Definition partition_prod {A} (PE PF : list (set A)) :=
  flat_map (λ p, map (intersection p) PF) PE.

Definition partition_prod2 {A} (PE PF : list (set A)) :=
  partition_combine (map (λ _ E, E) PE) PE PF.

Theorem equiv_partition_prod_prod2 : ∀ A (PE PF : list (set A)),
  partition_prod PE PF = partition_prod2 PE PF.
Proof.
intros.
unfold partition_prod, partition_prod2.
unfold partition_combine.
induction PE as [| E₁ PE]; intros; [ destruct PF; reflexivity | simpl ].
f_equal; apply IHPE.
Qed.

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
     rewrite Hf in Hx; [ contradiction | left; reflexivity ].
     rewrite Hf in Hx; [ contradiction | left; reflexivity ].

    destruct i; simpl in Hx; simpl; [ assumption | ].
    apply IHPF; assumption.

  apply Nat.nlt_ge in Hi.
  rewrite app_nth2; [| rewrite map_length; assumption ].
  rewrite map_length.
  remember (i - length PF)%nat as j eqn:Hj.
  assert (H : (i = j + length PF)%nat).
   rewrite Hj.
   rewrite Nat.sub_add; [ reflexivity | assumption ].

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

     rewrite Hf in Hx; [ | left; reflexivity ].
     rewrite intersection_empty_r in Hx.
     contradiction.

    rewrite nat_mod_add_once; [ | intros H; discriminate H ].
    rewrite nat_div_add_once; [ | intros H; discriminate H ].
    apply IHPE; [ assumption | ].
    intros f Hfi.
    apply Hf; right; assumption.
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
  rewrite union_list_app; [ | reflexivity ].
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
   eapply IHPE; [ | | | eassumption | assumption | ]; try reflexivity.
    rewrite HPFU in HUP'F.
    intros p Hp; apply HUP'F.
    right; assumption.

    intros i.
    pose proof (Hgl (S i)) as H; simpl in H.
    assumption.

 intros i j Hij.
 erewrite partition_combine_nth; [ | reflexivity | | ].
  erewrite partition_combine_nth; [ | reflexivity | | ].
   remember (length P'F) as len eqn:Hlen.
   destruct len.
    symmetry in Hlen.
    apply length_zero_iff_nil in Hlen; subst P'F; simpl.
    subst fl.
    destruct gl as [| g₁ gl].
     simpl; unfold id, Datatypes.id at 2; simpl.
     do 2 rewrite intersection_empty_r; reflexivity.

     simpl; unfold app_gr_inv, Nat.div; rewrite app_gr_empty_set.
     do 2 rewrite intersection_empty_r; reflexivity.

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
       do 2 rewrite intersection_empty_l; reflexivity.

     rewrite intersection_shuffle0, intersection_assoc.
     rewrite HPEI; [ | assumption ].
     do 2 rewrite intersection_empty_l; reflexivity.

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

Theorem old_partition_combine_is_partition :
  ∀ A (s := set_equiv) (fl : list (set A → set A)) E F PE PF,
  is_partition E PE
  → is_partition F PF
  → length fl = length PE
  → (∀ i, PE.[i] ⊂ ⋃ map (nth i fl id) PF)
  → (∀ i j k, j ≠ k → (nth i fl id PF.[j] ∩ nth i fl id PF.[k] = ∅)%S)
  → (∀ i, (nth i fl id ∅ = ∅)%S)
  → is_partition E (partition_combine fl PE PF).
Proof.
intros * HPE HPF Hlen3 Hfl Hfli Hfle.
split.
 destruct HPE as (HPEU, _).
 destruct HPF as (HPFU, _).
 assert (HUPF : F ⊂ ⋃ PF) by (rewrite HPFU; intros x H; assumption).
 clear HPFU Hfli Hfle.
 unfold partition_combine.
 revert E F fl PF HPEU HUPF Hlen3 Hfl.
 induction PE as [| E₁ PE]; intros.
  destruct fl as [| f₁ fl]; [ assumption | discriminate Hlen3 ].

  destruct fl as [| f₁ fl]; [ discriminate Hlen3 | ].
  rewrite HPEU; simpl.
  rewrite union_list_app; [ | reflexivity ].
  simpl in Hlen3; apply Nat.succ_inj in Hlen3.
  apply union_morph.
   pose proof union_intersection_self A E₁ (map f₁ PF).
   rewrite map_map in H.
   apply H.
   pose proof Hfl 0 as Hf; simpl in Hf.
   apply Hf.

   eapply IHPE; try eassumption; [ reflexivity | ].
   intros i; apply (Hfl (S i)).

 intros i j Hij.
 unfold partition_combine; simpl.
 revert i j E F fl PF HPE HPF Hlen3 Hfl Hfli Hfle Hij.
 induction PE as [| E₁ PE]; intros.
  destruct fl; simpl; do 2 rewrite match_id; apply intersection_empty_l.

  destruct fl as [| f₁ fl].
   simpl; do 2 rewrite match_id; apply intersection_empty_l.

   simpl.
   destruct (lt_dec i (length PF)) as [Hi| Hi].
    rewrite app_nth1; [ | rewrite map_length; assumption ].
    pose proof Hfle 0 as H; simpl in H.
    pose proof map_nth (λ Fj, E₁ ∩ f₁ Fj) PF ∅ i as Him; simpl in Him.
    apply eq_set_eq in Him.
    rewrite H, intersection_empty_r in Him; rewrite Him.
    destruct (lt_dec j (length PF)) as [Hj| Hj].
     rewrite app_nth1; [ | rewrite map_length; assumption ].
     pose proof Hfli 0 i j Hij as Hjk; simpl in Hjk.
     pose proof map_nth (λ Fj, E₁ ∩ f₁ Fj) PF ∅ j as Hjm; simpl in Hjm.
     apply eq_set_eq in Hjm.
     rewrite H, intersection_empty_r in Hjm; rewrite Hjm.
     rewrite intersection_shuffle0.
     do 2 rewrite <- intersection_assoc.
     rewrite intersection_comm in Hjk; rewrite Hjk.
     do 2 rewrite intersection_empty_r.
     reflexivity.

     apply Nat.nlt_ge in Hj.
     rewrite app_nth2; [ | rewrite map_length; assumption ].
     rewrite map_length.
Abort. (* à voir si on peut continuer quand même *)
(*
bbb.
     assert (∃ k l, (PE.[k] ∩ nth k fl id PF.[l] = (flat_map (λ '(fi, Ei), map (λ Fj, Ei ∩ fi Fj) PF) (combine fl PE)).[j - length PF])%S).
Focus 2.
destruct H0 as (k & l & Hkl).
rewrite <- Hkl.
pose proof Hfli 0 ...
bbb.
*)

Theorem partition_prod_is_partition2 : ∀ A (s := set_equiv) (E : set A) P Q,
  is_partition E P → is_partition E Q → is_partition E (partition_prod P Q).
Proof.
intros A s E P Q HPE HQE.
rewrite equiv_partition_prod_prod2.
unfold partition_prod2.
assert (Hi : ∀ i, nth i (map (λ _ E : set A, E) P) id = λ E, E).
 clear; intros i; revert i.
 induction P as [| E EL]; intros; [ simpl; apply match_id | simpl ].
 destruct i; [ reflexivity | apply IHEL ].

Abort. (* tant que partition_prod_is_partition n'est pas fait...
 eapply partition_combine_is_partition; try eassumption.
  rewrite map_length; reflexivity.

  intros i; rewrite Hi.
  assert (HQ : map id Q = Q).
   clear.
   induction Q as [| E EL]; [ reflexivity | simpl ].
   f_equal; apply IHEL.

   rewrite HQ.
   destruct HQE as (HQEU, _); rewrite <- HQEU.
   destruct HPE as (HPEU, _); rewrite HPEU.
   clear.
   revert i.
   induction P as [| E EL]; intros.
    simpl; rewrite match_id.
    intros x Hx; assumption.

    simpl.
    destruct i; [ left; assumption | right; eapply IHEL; eassumption ].

 intros i j k Hjk.
 rewrite Hi.
 destruct HQE as (HQEU, HQEI).
 apply HQEI; assumption.
Qed.
*)

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

Theorem partition_combine_length :
  ∀ A fl (PE PF : list (set A)),
  length fl = length PE
  → length (partition_combine fl PE PF) = (length PE * length PF)%nat.
Proof.
intros * Hlen.
unfold partition_combine; simpl.
revert fl PF Hlen.
induction PE as [| E₁ PE]; intros; [ destruct fl; reflexivity | simpl ].
destruct fl as [| f₁ fl]; [ discriminate Hlen | ].
destruct PF as [| F₁ FL].
 unfold partition_combine; simpl.
 rewrite Nat.mul_0_r.
 induction (combine fl PE) as [| (x, y) l]; [ reflexivity | apply IHl ].

 simpl in Hlen; simpl; f_equal.
 rewrite app_length, map_length.
 apply Nat.succ_inj in Hlen.
 apply IHPE with (PF := F₁ :: FL) in Hlen.
 simpl in Hlen; rewrite Hlen; reflexivity.
Qed.

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
(* see if I could reuse partition_combine_nth; but, perhaps the present
   theorem is going to be removed later, if no more used *)
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
  exists []; split; [ reflexivity | ].
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
  split; [ simpl; rewrite Hlen3; reflexivity | ].
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
   exists []; split; [ reflexivity | ].
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
   split; [ simpl; rewrite Hlen3; reflexivity | ].
   intros i; simpl.
   destruct i; [ | apply HFG ].
   rewrite <- HhFG, fold_app_gr_inv.
   rewrite app_gr_inv_l; reflexivity.

  destruct Hgl as (gl & Hlen3 & Hgl).
  destruct Hhl as (hl & Hlen4 & Hhl).
  apply Forall2_Forall_combine in HEF.
  destruct HEF as (HEF, Hlen1).
  apply Forall2_Forall_combine in HFG.
  destruct HFG as (HFG, Hlen2).
  remember (map app_gr_inv gl) as fl eqn:Hfl.
  assert (Hpcf : is_partition E (partition_combine fl PE P₂F)).
   eapply partition_combine_is_partition with (PF := P₁F); eassumption.

   exists (partition_combine fl PE P₂F).
   remember (map app_gr_inv hl) as f'l eqn:Hf'l.
   assert (Hpcg : is_partition G (partition_combine f'l PG P₁F)).
    symmetry in Hlen2.
    eapply partition_combine_is_partition with (PF := P₂F); eassumption.

    exists (partition_combine f'l PG P₁F).
    split; [ assumption | ].
    split; [ assumption | ].
    apply Forall2_Forall_combine.
    split.
     apply Forall_forall.
     intros (U, V) HU.
     generalize HU; intros HV.
     apply in_combine_l in HU.
     apply in_combine_r in HV.
     apply In_nth with (d := ∅) in HU.
     apply In_nth with (d := ∅) in HV.
     destruct HU as (i & Hi & HU).
     destruct HV as (j & Hj & HV).
     subst fl f'l.
     rewrite partition_combine_length in Hi; [ | rewrite map_length; easy ].
     rewrite partition_combine_length in Hj; [ | rewrite map_length; easy ].
(*
     remember (map app_gr_inv gl) as fl eqn:Hfl.
     remember (map app_gr_inv hl) as f'l eqn:Hf'l.
*)
     rewrite Hlen2 in Hi.
     rewrite <- Hlen1, Nat.mul_comm in Hj.
     apply eq_set_eq in HU.
     apply eq_set_eq in HV.
remember (partition_combine (map app_gr_inv gl) PE P₂F) as PE' eqn:HPE'.
remember (partition_combine (map app_gr_inv hl) PG P₁F) as PG' eqn:HPG'.
destruct Hpcf as (HpcfU, HpcfI).
destruct Hpcg as (HpcgU, HpcgI).
(**)
     remember (nth (i / length P₂F) gl gr_ident) as gi.
     remember (gr_inv (nth (j mod length P₁F) hl gr_ident)) as hj.
     exists (Comb hj gi); subst gi hj; simpl.
(*
remember gr_ident as toto in |-*.
exists toto.
*)
rewrite <- HU, <- HV; clear HU HV.
rewrite HPE', partition_combine_nth; [ | reflexivity | | ].
rewrite HPG', partition_combine_nth; [ | reflexivity | | ].
rewrite group_intersection_distr.
rewrite group_intersection_distr.
rewrite Hgl.

(**)
Require Export Setoid.
Add Parametric Morphism : (λ n l, @nth _ n (map app_gr_inv l) id)
  with signature eq ==> eq ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as nth_set_morph2.
Proof.
intros n l E F HEF x.
split; intros Hx.
 revert n x Hx.
 induction l as [| y l]; intros.
  simpl in Hx; rewrite match_id in Hx.
  simpl; rewrite match_id.
  apply HEF; assumption.

  simpl in Hx; simpl.
  destruct n; [ rewrite <- HEF; assumption | ].
  apply IHl; assumption.

 revert n x Hx.
 induction l as [| y l]; intros.
  simpl in Hx; rewrite match_id in Hx.
  simpl; rewrite match_id.
  apply HEF; assumption.

  simpl in Hx; simpl.
  destruct n; [ rewrite HEF; assumption | ].
  apply IHl; assumption.
Qed.
(*
Focus 1.
clear - s Hhl.
subst s.

rewrite <- Hhl.
replace (P₂F.[i mod length P₂F]) with ((app_gr (nth (i mod length P₂F) hl gr_ident) PG.[i mod length P₂F])).
Focus 2.

Require Import Relations OrdersFacts.
Print Instances Proper.
(*
Typeclasses eauto := debug.
Fail rewrite <- Hhl. (* fails *)
Print Instances Proper.
*)
*)
(* this works *)
etransitivity.
apply intersection_morph_Proper; [ reflexivity | ].
apply app_gr_morph_Proper; [ reflexivity | ].
apply app_gr_morph_Proper; [ reflexivity | ].
(*
Typeclasses eauto := debug.
Fail rewrite <- Hhl.
*)
apply nth_set_morph2_Proper; [ reflexivity | reflexivity | ].
rewrite <- Hhl.
reflexivity.
bbb.

assert (toto:
(
  app_gr (gr_inv (nth (j mod length P₁F) hl gr_ident))
     (P₁F.[i / length P₂F]
      ∩ app_gr (nth (i / length P₂F) gl gr_ident)
          (nth (i / length P₂F) (map app_gr_inv gl) id
             P₂F.[i mod length P₂F]))
=
  app_gr (gr_inv (nth (j mod length P₁F) hl gr_ident))
     (P₁F.[i / length P₂F]
      ∩ app_gr (nth (i / length P₂F) gl gr_ident)
          (nth (i / length P₂F) (map app_gr_inv gl) id
             (app_gr (nth (i mod length P₂F) hl gr_ident) PG.[i mod length P₂F])))
)%S
).
apply app_gr_morph; [ reflexivity | ].
apply intersection_morph; [ reflexivity | ].
apply app_gr_morph; [ reflexivity | ].
apply nth_set_morph2; try reflexivity.
rewrite <- Hhl; reflexivity. (* does not fail! *)
bbb.

Check nth_set_morph2.
rewrite toto.
bbb.

(*
apply nth_set_morph2; try reflexivity.
*)
rewrite <- Hhl.
reflexivity.
bbb.

Definition gr_eq_list (gl₁ gl₂ : list Gr) := gl₁ = gl₂.
Add Parametric Morphism : (map app_gr_inv)
  with signature gr_eq_list ==> eq
  as map_app_gr_inv_morph.
Proof.
intros.
Admitted. Show.
rewrite <- Hhl.
bbb.
Add Parametric Morphism : (@nth (set point → set point))
  with signature eq ==> eq ==> eq ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as nth_set_morph2.
Proof.
Admitted. Show.
rewrite <- Hhl.
bbb.

intros n l d E F HEF x.
split; intros Hx.
 unfold set_eq in HEF.
 simpl in HEF.
 revert n d E F x HEF Hx.
 induction l as [| y l]; intros.
  simpl in Hx; rewrite match_id in Hx.
  simpl; rewrite match_id.

bbb.


rewrite <- Hhl.
rewrite group_intersection_distr.

bbb.

pose proof Hhl (i mod length P₂F) as H.

bbb.
     rewrite partition_combine_nth in HU; [ | reflexivity | | ].
      rewrite partition_combine_nth in HV; [ | reflexivity | | ].
       rewrite <- HU, <- HV; clear HU HV.
       rewrite group_intersection_distr.
bbb.
       rewrite Hgl.
       rewrite group_intersection_distr.
       destruct (eq_nat_dec (i / length P₂F) (j / length P₁F)) as [Hidj| Hidj].
        rewrite <- Hidj.

bbb.

Focus 2.
     subst fl f'l.
     rewrite partition_combine_length; [ | now rewrite map_length ].
     rewrite partition_combine_length; [ | now rewrite map_length ].
     rewrite Hlen1, Hlen2; apply Nat.mul_comm.

bbb.

Add Parametric Relation : (point → Prop) (equidecomposable set_equiv)
 reflexivity proved by equidec_refl
 symmetry proved by equidec_sym
 transitivity proved by equidec_trans
 as equidec_morph.
