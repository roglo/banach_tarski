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
 remember (map (λ '(gi, PPFi), app_gr (gr_inv gi) PPFi) (combine gll PPF))
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
    remember (combine gll PPF) as gpl eqn:Hgpl.
    symmetry in Hgpl.
    induction gpl as [| gp].
     intros p; split; [ intros H; simpl | contradiction ].
bbb.
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
clear G P'G HP'G Hlen2 HFG Hgll Hleq Hgpl HFQR.
simpl in Hlen1; apply Nat.succ_inj in Hlen1.
unfold is_partition in HPE.
destruct HPE as (HE, HPE).
rewrite HE in H.
destruct H as [H| H].
 apply app_gr_app_gr_inv in Hgg.
 rewrite <- Hgg in H.

bbb.
  remember (app_gr_point g₁ p) as q eqn:Hq.
  apply HPF with (x := q).
bbb.

Add Parametric Relation : (point → Prop) (equidecomposable set_equiv)
 reflexivity proved by equidec_refl
 symmetry proved by equidec_sym
 transitivity proved by equidec_trans
 as equidec_morph.
