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
exists (Xtransl 0); unfold set_eq; simpl.
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
pose proof partition_prod_is_partition _ F PF P'F HPF HP'F as HPFF'.
apply Forall2_Forall_combine in HEF.
remember (combine PE PF) as PEF eqn:HPEF.
set (s := set_equiv).
assert
  (Hgl : ∃ gl, length gl = length PE ∧
   ∀ i, (app_gr (nth i gl gr_ident) (nth i PE ∅) = nth i PF ∅)%S).
 subst PEF.
 clear HPE HPF HPFF'.
 revert PF Hlen1 HEF.
 induction PE as [| E₁ PE]; intros.
  exists []; split; [ reflexivity | ].
  symmetry in Hlen1; apply length_zero_iff_nil in Hlen1; subst PF.
  intros i; simpl.
  do 2 rewrite match_id; simpl.
  intros (x, y, z); split; contradiction.

  destruct PF as [| F₁ PF]; [ discriminate Hlen1 | ].
  simpl in Hlen1; apply Nat.succ_inj in Hlen1.
  remember set_eq as f; simpl in HEF; apply Forall_inv2 in HEF; subst f.
  destruct HEF as ((g₁, HgEF), HEF).
  apply IHPE in HEF; [ | assumption ].
  destruct HEF as (gl & Hlen3 & HEF).
  exists (g₁ :: gl).
  split; [ simpl; rewrite Hlen3; reflexivity | ].
  intros i.
  remember set_eq as f; simpl; subst f.
  destruct i; [ assumption | apply HEF ].

 destruct Hgl as (gl & Hlen3 & Hgl).
 move P'F before PF; move P'G before P'F.
 move gl before P'G.
 move Hlen2 before Hlen1.
 move Hlen3 before Hlen2.
 remember
   (flat_map (λ '(gi, Ei), map (λ F'j, Ei ∩ app_gr_inv gi F'j) P'F)
      (combine gl PE)) as PPE eqn:HPPE.
 assert (is_partition E PPE).
  split.
   subst PPE PEF.
   clear HEF HPFF' HFG G P'G HP'G Hlen2.
   destruct HPE as (HPEU, _).
   destruct HPF as (HPFU, _).
   destruct HP'F as (HP'FU, _).
   assert (HUP'F : F ⊂ ⋃ P'F) by (rewrite HP'FU; intros x H; assumption).
   clear HP'FU.
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

      destruct PF as [| F₁ PF ]; [ discriminate Hlen1 | ].
      simpl in Hlen1; apply Nat.succ_inj in Hlen1.
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
   remember (length P'F) as len eqn:Hlen.
   assert
     ((PPE.[i] =
      PE.[i/len] ∩ app_gr_inv (nth (i/len) gl gr_ident) P'F.[i mod len])%S).
    subst PPE.
    clear - Hlen3 Hlen.
    revert i gl Hlen3.
    induction PE as [| E₁ PE]; intros.
     apply length_zero_iff_nil in Hlen3; subst gl; simpl.
     do 3 rewrite match_id.
     rewrite intersection_empty_l; reflexivity.

     destruct gl as [| g₁ gl]; [ discriminate Hlen3 | ].
     simpl in Hlen3; simpl.
     apply Nat.succ_inj in Hlen3.
     destruct (zerop (i / len)) as [Hil| Hil].
      rewrite Hil; simpl.
      remember ((λ '(gi, Ei),
        map (λ F'j : set point, Ei ∩ app_gr_inv gi F'j) P'F)) as ff.
      set (gg := λ F'j : set point, E₁ ∩ app_gr_inv g₁ F'j).
      destruct (lt_dec i len) as [Hi| Hi].
       rewrite app_nth1; [ | rewrite map_length; subst len; assumption ].
       pose proof map_nth gg P'F ∅ i as H.
subst len.
clear - Hi.
revert P'F Hi.
induction i; intros.
 destruct P'F as [| F'₁ P'F].
  exfalso; revert Hi; apply Nat.nlt_0_r.

  rewrite Nat.mod_0_l; [ simpl | intros HH; discriminate HH ].
  reflexivity.

 destruct P'F as [| F'₁ P'F].
  exfalso; revert Hi; apply Nat.nlt_0_r.

Arguments Nat.modulo : simpl never.
  simpl.

SearchAbout (nth (S _)).

bbb.
       assert (Hgg : (gg ∅ = ∅)%S).
        subst gg; unfold app_gr_inv; rewrite app_gr_empty_set.
        apply intersection_empty_r.

        rewrite Hgg in H.
bbb.
   destruct (eq_nat_dec (i / len) (j / len)) as [Hil| Hil].
bbb.

Add Parametric Relation : (point → Prop) (equidecomposable set_equiv)
 reflexivity proved by equidec_refl
 symmetry proved by equidec_sym
 transitivity proved by equidec_trans
 as equidec_morph.
