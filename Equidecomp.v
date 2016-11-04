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

Definition partition_combine_swi {A B} (fl : list (set A → set B)) PE PF :=
  flat_map (λ Fj, map (λ '(fi, Ei), Ei ∩ fi Fj) (combine fl PE)) PF.

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

Theorem partition_combine_swi_nth_from_combine :
  ∀ A (s := set_equiv) fl (PE PF : list (set A)) i lenE lenF,
  lenE = length PE
  → lenF = length PF
  → length fl = length PE
  → (∀ f, List.In f fl → (f ∅ = ∅)%S)
  → ((partition_combine_swi fl PE PF).[i] =
     (partition_combine fl PE PF).[(i mod lenE) * lenF + i / lenE])%S.
Proof.
intros * HlenE HlenF Hflp Hf.
rewrite partition_combine_nth; try eassumption.
destruct (eq_nat_dec lenE 0) as [HEz| HEnz].
 subst lenE.
 apply length_zero_iff_nil in HEz; subst PE.
 apply length_zero_iff_nil in Hflp; subst fl.
 simpl; do 2 rewrite match_id.
 unfold partition_combine_swi; simpl.
 rewrite flat_map_nil_fun; simpl.
  rewrite match_id; now rewrite intersection_empty_l.

  clear; induction PF; now constructor; easy.

 destruct (eq_nat_dec lenF 0) as [HFz| HFnz].
  subst lenF.
  apply length_zero_iff_nil in HFz; subst PF.
  simpl; rewrite match_id.
  rewrite Nat.mul_0_r, Nat.add_0_l.
  assert (Hj : ∀ j, (nth j fl id ∅ = ∅)%S).
   clear -Hf.
   induction fl as [| f₁ fl]; intros; [ simpl; now rewrite match_id | simpl ].
   destruct j.
    rewrite Hf; [ easy | now left ].

    apply IHfl.
    intros f Hfi.
    apply Hf; now right.

   now rewrite Hj, intersection_empty_r.

  rewrite Nat.div_add_l; [ | easy ].
  setoid_rewrite Nat.add_comm.
  rewrite Nat.mod_add; [ | easy ].
  rewrite Nat.div_div; [ | easy | easy ].
  destruct (lt_dec i (lenE * lenF)) as [Hi| Hi].
   rewrite Nat.div_small; [ | easy ].
   rewrite Nat.add_0_l.
   replace ((i / lenE) mod lenF) with (i / lenE).
 Focus 2.
 rewrite Nat.mod_small; [ easy | ].
 now apply Nat.div_lt_upper_bound.
Abort.

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
   2: rewrite map_length, combine_length, Nat.min_l; [ easy | ].
   2: now rewrite HlfP.

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

(*
Theorem glop : ∀ A (l l' : list A) d s,
  Permutation l l'
  → ∃ σ, Permutation (seq s (length l)) σ ∧
    ∀ i, i < length l → nth i l d = nth (nth i σ 0 - s) l' d.
Proof.
intros * HP.
remember (length l) as len eqn:Hlen.
symmetry in Hlen.
revert l l' d s HP Hlen.
induction len; intros.
 exists [].
 split; [ easy | intros i Hi; now apply Nat.nlt_0_r in Hi ].

 destruct l as [| x l]; [ easy | ].
 simpl in Hlen; apply Nat.succ_inj in Hlen.
 assert (HP' : ∃ l₁ l₂, l' = l₁ ++ x :: l₂).
  eapply Permutation_cons_exist; eassumption.

  destruct HP' as (l₁ & l₂ & Hl'); subst l'.
  apply Permutation_app_inv with (l1 := []) in HP; simpl in HP.
  generalize HP; intros H.
  apply IHlen with (d := d) (s := s) in H; [ | easy ].
  destruct H as (σ & Hs & Hσ).
(**)
exists (s + length l₁ :: firstn (length l₁) σ ++ []).
split. Focus 2.
intros i Hilen.
 simpl.
 destruct i.
  rewrite Nat.add_comm, Nat.add_sub.
  rewrite app_nth2; [ | unfold ge; easy ].
  now rewrite Nat.sub_diag.

  apply Nat.succ_lt_mono in Hilen.
  pose proof Hσ i Hilen as H.
  destruct (lt_dec i (length l₁)) as [H₁| H₁].
   assert (Hnn : nth i (firstn (length l₁) σ ++ []) 0 = nth i σ 0).
    rewrite app_nth1; [ now rewrite nth_firstn | ].
    rewrite firstn_length_le; [ easy | ].
    apply Permutation_length in Hs.
    rewrite seq_length in Hs; rewrite <- Hs.
    apply Permutation_length in HP.
    rewrite <- Hlen, HP, app_length.
    apply Nat.le_add_r.

    rewrite Hnn, H.
    rewrite app_nth1.
     rewrite app_nth1; [ easy | ].

bbb.
SearchAbout firstn.
     rewrite firstn_all2.


2: rewrite firstn_length_le; [ easy | ].


bbb.
remember (map S σ) as σ' eqn:Hσ'.
exists (firstn (length l₁) σ' ++ [s] ++ skipn (length l₁) σ').
subst σ'.
split.
 simpl.
 apply Permutation.Permutation_cons_app.
 rewrite firstn_skipn.
 clear -HP.
 revert s σ HP.
 induction len; intros; simpl in HP; simpl.
  destruct σ as [| σ₁ σ]; [ easy | now apply Permutation_nil_cons in HP ].

  generalize HP; intros H.
  apply Permutation_cons_app in H.
  destruct H as (l₁ & l₂ & Hσ); subst σ.
  rewrite map_app; simpl.
  apply Permutation.Permutation_cons_app.
  rewrite <- map_app.
  apply IHlen.
  eapply Permutation_cons_app_inv; eassumption.

intros i Hilen.
bbb.

destruct i; simpl.
 destruct l₁ as [| x₁ l₁]; [ simpl; now rewrite Nat.sub_diag | simpl ].
 destruct σ as [| σ₁ σ].
simpl.
rewrite Nat.sub_diag.
simpl in Hσ.
destruct len; [ | now apply Permutation_cons_nil in HP ].
clear Hσ Hilen.
simpl in HP.

bbb. (* ah putain, ça commence à me gonfler, putain *)

split. Focus 2.
intros i Hilen.
destruct (lt_dec i (length l₁)) as [H₁| H₁].
assert (nth i (firstn (length l₁) σ ++ []) 0 = nth i σ 0).
rewrite app_nth1.
2: rewrite firstn_length.



bbb.

  exists
bbb.

  clear -HP Hlen.
  revert x l l' HP Hlen.
  induction len; intros.
   apply length_zero_iff_nil in Hlen; subst l.
   exists [], [].
   now apply Permutation_length_1_inv in HP.

   destruct l as [| y l]; [ easy | simpl in Hlen ].
   apply Nat.succ_inj in Hlen.
   destruct l' as [| x' l']; [ now apply Permutation_cons_nil in HP | ].
bbb.

  revert x l len HP Hlen.
  induction l' as [| x']; intros.
   apply Permutation_cons_nil in HP; easy.

   inversion HP; subst; [ exists [], l'; easy | exists [x'], l0; easy | ].
   rename l'0 into l''; rename H0 into H''.

bbb.
intros * HP.
revert s l' HP.
induction l as [| x l]; intros.
 destruct l' as [| x' l']; [ | apply Permutation_nil_cons in HP; easy ].
 exists []; split; [ reflexivity | ].
 intros i Hi; apply Nat.nlt_0_r in Hi; easy.

 destruct l' as [| x' l']; [ apply Permutation_cons_nil in HP; easy | ].
 induction HP.
  exists []; split; [ reflexivity | ].
  intros i Hi; apply Nat.nlt_0_r in Hi; easy.

bbb.
intros * HP.
induction HP.
 exists []; simpl.
 split; [ constructor | ].
 intros i Hi; exfalso; revert Hi; apply Nat.nlt_0_r.

 destruct IHHP as (l'' & HPl & Hl'').
 exists (l'' ++ [length l + s]).
 simpl; split.
  clear - HPl.
  revert s l HPl.
  induction l'' as [| x'']; intros.
   destruct l as [| x]; [ constructor; constructor | ].
   apply Permutation_sym, Permutation_nil_cons in HPl.
   contradiction.

   simpl.
   destruct l as [| x l].
    simpl in HPl; apply Permutation_nil_cons in HPl.
    contradiction.

    simpl in HPl; simpl.
    destruct (eq_nat_dec s x'') as [Hs| Hx].
     subst x''; constructor.
     apply Permutation_cons_inv in HPl.
     rewrite <- Nat.add_succ_r.
     apply IHl''; assumption.

     inversion HPl; [ contradiction | | ].
      subst y x0 l''.
      destruct l as [| y l]; [ discriminate H1 | simpl in H1 ].
      injection H1; clear H1; intros; subst x'' l0.
      simpl in HPl; simpl.
rewrite cons_comm_app.
SearchAbout (Permutation (_ :: _)).
bbb.

Theorem gogo : ∀ A (x y : A) l l',
  Permutation l l'
  → Permutation (x :: y :: l) (y :: x :: l').
Proof.
intros * HP.
induction HP; [ constructor | | | ].


 inversion IHHP; subst.
  constructor; constructor; constructor; assumption.

  inversion IHHP; subst.
   constructor; constructor; constructor; assumption.
bbb.

apply gogo.
simpl.

bbb.
*)

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
 induction Hpe; [ reflexivity | | | ].
  simpl; rewrite IHHpe; reflexivity.

  simpl; rewrite union_comm, <- union_assoc.
  apply union_morph; [ reflexivity | apply union_comm ].

  etransitivity; eassumption.

(**)
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
     intros (U, V) HU.
     generalize HU; intros HV.
     apply in_combine_l in HU.
     apply in_combine_r in HV.
     apply In_nth with (d := ∅) in HU.
     apply In_nth with (d := ∅) in HV.
     destruct HU as (i & Hi & HU).
     destruct HV as (j & Hj & HV).
     subst g'l h'l.
     rewrite partition_combine_length in Hi; [ | now rewrite map_length ].
     rewrite partition_combine_swi_length in Hj; [ | now rewrite map_length ].
(*
     remember (map app_gr_inv gl) as fl eqn:Hfl.
     remember (map app_gr_inv hl) as f'l eqn:Hf'l.
*)
     rewrite Hlen2 in Hi.
     rewrite <- Hlen1, Nat.mul_comm in Hj.
     apply eq_set_eq in HU.
     apply eq_set_eq in HV.
remember (partition_combine (map app_gr_inv gl) PE P₂F) as PE' eqn:HPE'.
remember (partition_combine_swi (map app_gr_inv hl) PG P₁F) as PG' eqn:HPG'.
destruct Hpcf as (HpcfU, HpcfI).
destruct Hpcg as (HpcgU, HpcgI).
     remember (nth (i / length PG) gl gr_ident) as gi.
     remember (nth (j / length PE) (map gr_inv hl) gr_ident) as hj.
     exists (Comb hj gi); subst gi hj; simpl.
(*
remember gr_ident as toto in |-*.
exists toto.
*)
(*
remember (length PG) as lenPG eqn:HlenPG.
symmetry in HlenPG.
destruct lenPG; [ rewrite Nat.mul_0_r in Hi; now apply Nat.nlt_0_r in Hi | ].
*)
rewrite <- HU, <- HV; clear HU HV.
rewrite HPE', HPG'.
rewrite partition_combine_nth; [ | easy | | ].
 rewrite partition_combine_swi_nth; [ | easy | | ].
  do 2 rewrite group_intersection_distr.
rewrite Hlen2.
(*
  rewrite <- Hlen1, Hlen2.
*)

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

Show.
(* works: *)
etransitivity.
apply intersection_morph_Proper; [ reflexivity | ].
apply app_gr_morph_Proper; [ reflexivity | ].
apply app_gr_morph_Proper; [ reflexivity | ].
apply nth_map_app_gr_inv_morph; [ easy | easy | ].
symmetry; apply Hhl.
(* doesn't work:
rewrite <- Hhl.
*)
rewrite Nat.add_0_r.
symmetry.
etransitivity.
apply intersection_morph_Proper; [ reflexivity | ].
apply nth_map_app_gr_inv_morph; [ easy | easy | ].
symmetry; apply Hgl.
rewrite Nat.add_0_r.
rewrite intersection_comm.
(**)
apply intersection_morph.
Check app_gr_nth.

bbb.
rewrite app_gr_nth.


apply app_gr_morph_Proper; [ reflexivity | ].
apply app_gr_morph_Proper; [ reflexivity | ].
apply nth_map_app_gr_inv_morph; [ easy | easy | ].
symmetry; apply Hhl.


rewrite app_gr_nth.
replace Datatypes.id with (@id (set point)) by easy.
rewrite intersection_comm.
apply intersection_morph.
Focus 2.

bbb.
rewrite app_gr_nth.

bbb.

(*
Typeclasses eauto := debug.
Fail rewrite <- Hhl.
*)
apply nth_set_morph2_Proper; [ reflexivity | reflexivity | ].
rewrite <- Hhl.
reflexivity.
remember (i mod length P₂F) as III.
remember (j / length P₁F) as JJJ.

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
