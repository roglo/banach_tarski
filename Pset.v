(* Sets as A → Prop *)

Require Import Utf8 List Relations NPeano Compare_dec Setoid.
Require Import Misc.

Record set A := mkset { setp : A → Prop }.
Arguments mkset [A] _.
Arguments setp [A] _ _.

Definition empty_set {A} := mkset (λ _ : A, False).

Notation "x '∈' E" := (setp E x) (at level 60).
Notation "x '∉' E" := (¬ setp E x) (at level 60).
Notation "'∅'" := (empty_set).

Definition intersection {A} (E₁ E₂ : set A) :=
  mkset (λ x, x ∈ E₁ ∧ x ∈ E₂).
Definition union {A} (E₁ E₂ : set A) :=
  mkset (λ x, x ∈ E₁ ∨ x ∈ E₂).
Definition union_list {A} (Ei : list (set A)) :=
  fold_right union ∅ Ei.
Definition subtract {A} (E₁ E₂ : set A) :=
  mkset (λ x, x ∈ E₁ ∧ x ∉ E₂).
Definition included {A} (E₁ E₂ : set A) :=
  ∀ x, x ∈ E₁ → x ∈ E₂.

Arguments intersection : simpl never.
Arguments union : simpl never.
Arguments subtract : simpl never.
Arguments included : simpl never.

Delimit Scope set_scope with S.

Definition set_eq {A} (E₁ E₂ : set A) := ∀ x, x ∈ E₁ ↔ x ∈ E₂.

Notation "E₁ = E₂" := (set_eq E₁ E₂) : set_scope.
Notation "E₁ ≠ E₂" := (¬ set_eq E₁ E₂) : set_scope.
Notation "E₁ '∩' E₂" := (intersection E₁ E₂) (at level 40).
Notation "E₁ '∪' E₂" := (union E₁ E₂) (at level 50).
Notation "E₁ '∖' E₂" := (subtract E₁ E₂) (at level 50).
Notation "E₁ '⊂' E₂" := (included E₁ E₂) (at level 60).
Notation "'⋃' Es" := (union_list Es) (at level 55).
Notation "E .[ i ]" := (List.nth i E ∅)
  (at level 1, format "'[' E '[' .[ i ] ']' ']'").

Definition set_map {A B} (f : A → B) s := mkset (λ v, ∃ u, u ∈ s ∧ f u = v).

Add Parametric Morphism {A B f} : (@set_map A B f)
  with signature set_eq ==> set_eq
  as set_map_morph.
Proof.
intros E F HEF b.
split; intros H.
 destruct H as (a & Ha & Hf).
 now exists a; split; [ apply HEF in Ha | ].

 destruct H as (a & Ha & Hf).
 now exists a; split; [ apply HEF in Ha | ].
Qed.

Theorem set_map_inter_distr : ∀ A B E F (f : A → B),
  FinFun.Injective f
  → (set_map f (E ∩ F) = set_map f E ∩ set_map f F)%S.
Proof.
intros * Hinj b.
split; intros H.
 destruct H as (a & (HaE & HaF) & Hf); simpl.
 split; exists a; easy.

 simpl in H; simpl.
 destruct H as ((ae & HE & Hae) & (af & HF & Haf)).
 rewrite <- Haf in Hae.
 specialize (Hinj _ _ Hae); subst af.
 now exists ae.
Qed.

Theorem set_map_union_distr : ∀ A B E F (f : A → B),
  (set_map f (E ∪ F) = set_map f E ∪ set_map f F)%S.
Proof.
intros; intros b.
split; intros H.
 now destruct H as (a & [Hae| Haf] & Hf); [ left | right ]; exists a.

 destruct H as [(a & Hae & Hf)| (a & Haf & Hf)].
  now exists a; split; [ left | ].
  now exists a; split; [ right | ].
Qed.

Theorem set_map_empty : ∀ A B (f : A → B), (set_map f ∅ = ∅)%S.
Proof.
intros; intros b.
now split; intros H; destruct H.
Qed.

Theorem in_set_map : ∀ A B x E (f : A → B),
  x ∈ E → f x ∈ set_map f E.
Proof. now intros * Hx; exists x. Qed.

Theorem set_map_in : ∀ A B x E (f : A → B),
  FinFun.Injective f
  → f x ∈ set_map f E
  → x ∈ E.
Proof.
intros * Hinj Hx.
destruct Hx as (a & Ha & Hfa).
now apply Hinj in Hfa; subst a.
Qed.

Theorem set_eq_refl A : reflexive (set A) set_eq.
Proof. now intros P x; split. Qed.

Theorem set_eq_sym A : symmetric (set A) set_eq.
Proof.
intros P₁ P₂ HPP x.
destruct (HPP x) as (H₁, H₂).
split; intros H; [ apply H₂, H | apply H₁, H ].
Qed.

Theorem set_eq_trans A : transitive (set A) set_eq.
Proof.
intros P₁ P₂ P₃ H₁₂ H₂₃ x.
destruct (H₁₂ x) as (H₁, H₂).
destruct (H₂₃ x) as (H₃, H₄).
split; intros H; [ apply H₃, H₁, H | apply H₂, H₄, H ].
Qed.

Add Parametric Relation A : (set A) (@set_eq A)
 reflexivity proved by (set_eq_refl A)
 symmetry proved by (set_eq_sym A)
 transitivity proved by (set_eq_trans A)
 as set_eq_rel.

Theorem eq_set_eq : ∀ A (x y : set A), x = y → (x = y)%S.
Proof. intros; now subst x. Qed.

Theorem included_trans A : transitive _ (@included A).
Proof.
intros E F G HEF HFG x Hx.
apply HFG, HEF, Hx.
Qed.

Theorem included_in_empty : ∀ A (E : set A),
  E ⊂ ∅
  → (E = ∅)%S.
Proof.
intros * HE.
intros x.
split; intros Hx; [ | easy ].
now apply HE in Hx.
Qed.

Add Parametric Morphism {A} : (@intersection A)
  with signature set_eq ==> set_eq ==> set_eq
  as intersection_morph.
Proof.
intros E E' HE F F' HF.
unfold intersection; intros p.
split; intros (H₁, H₂).
 now split; [ apply HE | apply HF ].
 now split; [ apply HE | apply HF ].
Qed.

Add Parametric Morphism {A} : (@union A)
  with signature set_eq ==> set_eq ==> set_eq
  as union_morph.
Proof.
intros E E' HE F F' HF.
intros p.
split.
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
Qed.

Add Parametric Morphism {A} : (@subtract A)
  with signature set_eq ==> set_eq ==> set_eq
  as subtract_morph.
Proof.
intros E E' HE F F' HF.
unfold subtract; intros p.
split; intros (H₁, H₂).
 split; [ now apply HE | intros H; now apply H₂, HF ].
 split; [ now apply HE | intros H; now apply H₂, HF ].
Qed.

Add Parametric Morphism {A} : (@included A)
  with signature set_eq ==> set_eq ==> iff
  as included_morph.
Proof.
intros E F HEF E' F' HE'F'.
split; intros HEE' x HF; apply HE'F', HEE', HEF, HF.
Qed.

Theorem set_eq_equiv {A} : ∀ (E F : set A),
  (E = F)%S
  → ∀ p, p ∈ E ↔ p ∈ F.
Proof. intros s * HEF; apply HEF. Qed.

Theorem union_empty_r : ∀ A (F : set A),
  (F ∪ ∅ = F)%S.
Proof.
intros * x.
split; intros H; [ | now left ].
now destruct H.
Qed.

Theorem intersection_empty_l : ∀ A (F : set A),
  (∅ ∩ F = ∅)%S.
Proof.
intros * x.
split; intros H; [ now destruct H as (H, _) | easy ].
Qed.

Theorem intersection_empty_r : ∀ A (F : set A),
  (F ∩ ∅ = ∅)%S.
Proof.
intros * x.
split; intros H; [ now destruct H as (_, H) | easy ].
Qed.

Theorem intersection_comm : ∀ A (E F : set A),
  (E ∩ F = F ∩ E)%S.
Proof.
intros; intros x.
split; intros H; destruct H as (HE & HF); now split.
Qed.

Theorem union_comm : ∀ A (E F : set A),
  (E ∪ F = F ∪ E)%S.
Proof.
intros; intros x.
now split; intros [HE| HF]; [ right | left | right | left ] .
Qed.

Theorem intersection_assoc : ∀ A (E F G : set A),
  (E ∩ (F ∩ G) = (E ∩ F) ∩ G)%S.
Proof.
intros; intros x.
split; intros H.
 destruct H as (HE & (HF & HG)).
 split; [ now split | easy ].

 destruct H as ((HE & HF) & HG).
 split; [ easy | now split ].
Qed.

Theorem union_assoc : ∀ A (E F G : set A),
  (E ∪ (F ∪ G) = (E ∪ F) ∪ G)%S.
Proof.
intros; intros x.
split; intros H.
 destruct H as [H| [H| H]].
  left; now left.
  left; now right.
  now right.

 destruct H as [[H| H]| H].
  now left.
  right; now left.
  right; now right.
Qed.

Theorem in_intersection : ∀ A (E F : set A) x, x ∈ E ∩ F ↔ x ∈ E ∧ x ∈ F.
Proof. intros; split; intros H; easy. Qed.

Theorem intersection_shuffle0 : ∀ A (E F G : set A),
  (E ∩ F ∩ G = E ∩ G ∩ F)%S.
Proof.
intros; intros x.
split; intros H.
 destruct H as ((HE & HF) & HG).
 split; [ now split | easy ].

 destruct H as ((HE & HF) & HG).
 split; [ now split | easy ].
Qed.

Theorem union_is_empty : ∀ A (E F : set A),
  (E ∪ F = ∅)%S → (E = ∅)%S ∧ (F = ∅)%S.
Proof.
intros * HEF.
split; intros x.
 split; [ intros Hx; apply HEF; now left | easy ].
 split; [ intros Hx; apply HEF; now right | easy ].
Qed.

Theorem union_list_is_empty_iff : ∀ A (EL : list (set A)),
  (⋃ EL = ∅)%S ↔ Forall (λ E, (E = ∅)%S) EL.
Proof.
intros *.
split; intros HEL.
 apply Forall_forall; intros E HE.
 revert E HE.
 induction EL as [| E₁ EL]; intros; [ easy | ].
 simpl in HEL, HE.
 apply union_is_empty in HEL.
 destruct HEL as (HE₁, HEL).
 destruct HE as [HE| HE]; [ now subst E₁ | ].
 apply IHEL, HE; apply HEL.

 rewrite Forall_forall in HEL.
 split; [ intros Hx; simpl | easy ].
 revert x Hx.
 induction EL as [| E₁ EL]; intros; [ easy | ].
 simpl in Hx.
 destruct Hx as [Hx| Hx].
  apply HEL in Hx; [ easy | now left ].

  eapply IHEL; [ | eassumption ].
  intros E HE; apply HEL; now right.
Qed.

Theorem union_list_app : ∀ A (P₁ P₂ : list (set A)),
  (⋃ (P₁ ++ P₂) = (⋃ P₁) ∪ (⋃ P₂))%S.
Proof.
intros.
revert P₁.
induction P₂ as [| Q]; intros.
 rewrite app_nil_r; simpl.
 now rewrite union_empty_r.

 rewrite cons_comm_app, app_assoc; simpl.
 rewrite IHP₂.
 unfold union_list; simpl; rewrite union_assoc.
 intros x.
 split; intros H.
  destruct H as [H| H]; [ left | now right ].
  unfold union_list in H.
  rewrite fold_right_app in H.
  simpl in H.
  clear - H.
  induction P₁ as [| R P₁].
   simpl in H; simpl.
   destruct H as [H| H]; [ now right | easy ].

   simpl in H.
   destruct H as [H| H]; [ simpl; left; now left | ].
   apply IHP₁ in H.
   destruct H as [H| H]; [ simpl; left; now right | ].
   now right.

  destruct H as [H| H]; [ left | now right ].
  unfold union_list.
  rewrite fold_right_app; simpl.
  clear - H.
  induction P₁ as [| R P₁].
   simpl in H; simpl; left.
   now destruct H.

   simpl in H; simpl.
   destruct H.
    destruct H; [ now left | right ].
    now apply IHP₁; left.

    now right; apply IHP₁; right.
Qed.

Theorem nth_set_union_list : ∀ A (P : list (set A)) i x,
  i < length P → x ∈ P.[i] → x ∈ ⋃ P.
Proof.
intros A P i x Hi H.
revert P H Hi.
induction i; intros P H Hi.
 destruct P as [| E P]; [ easy | now left ].

 destruct P as [| E P]; [ easy | simpl in Hi ].
 apply Nat.succ_lt_mono in Hi.
 right; now apply IHi.
Qed.

Theorem nth_set_app : ∀ A (P₁ P₂ : list (set A)) i,
  (P₁ ++ P₂).[i] =
  if lt_dec i (length P₁) then P₁.[i] else P₂.[i-length P₁].
Proof.
intros.
unfold union, set_eq; simpl; intros.
destruct (lt_dec i (length P₁)) as [H₁| H₁].
 now rewrite app_nth1.

 rewrite app_nth2; [ easy | now apply Nat.nlt_ge ].
Qed.

Theorem union_list_intersection : ∀ A (S : set A) SL x,
  x ∈ S
  → x ∈ ⋃ SL
  → x ∈ ⋃ map (intersection S) SL.
Proof.
intros A P QL * HP HQL.
induction QL as [| Q QL]; intros; [ easy | simpl ].
destruct HQL as [HQ| HQL]; [ left; now split | right ].
apply IHQL, HQL.
Qed.

Theorem union_list_all_included : ∀ A (E : set A) EL,
  (E = ⋃ EL)%S → Forall (λ Ei, Ei ⊂ E) EL.
Proof.
intros * HE.
apply Forall_forall.
intros F HF.
rewrite HE.
clear - HF.
revert F HF.
induction EL as [| E EL]; intros; [ easy | ].
destruct HF as [HF| HF]; [ left; now subst E | ].
right; eapply IHEL; eassumption.
Qed.

Theorem union_intersection_self : ∀ A (E : set A) EL,
  E ⊂ ⋃ EL
  → (E = ⋃ map (intersection E) EL)%S.
Proof.
intros * HEL x.
split; intros Hx.
 generalize Hx; intros Hxl.
 apply HEL in Hxl.
 clear -Hx Hxl.
 induction EL as [| E₁ EL]; intros; [ easy | ].
 destruct Hxl as [Hxl| Hxl]; [ left; now split | ].
 right; now apply IHEL.

 clear -Hx.
 induction EL as [| E₁ EL]; intros; [ easy | ].
 destruct Hx as [(Hx, _)| Hx]; [ easy | ].
 apply IHEL, Hx.
Qed. 

Theorem intersection_union_distr_r : ∀ A (E F G : set A),
  ((E ∪ F) ∩ G = (E ∩ G) ∪ (F ∩ G))%S.
Proof.
intros * x.
split; intros H.
 now destruct H as ([HE| HF] & HG); [ left | right ].

 destruct H as [(HE, HG)| (HF, HG)].
  now split; [ left | ].

  now split; [ right | ].
Qed.

Add Parametric Morphism {A} : (@setp A)
with signature set_eq ==> eq ==> iff
as setp_morph.
Proof.
intros E F HEF x.
apply HEF.
Qed.

Theorem set_map_union_list_distr : ∀ A B EL (f : A → B),
  (set_map f (⋃ EL) = ⋃ (map (set_map f) EL))%S.
Proof.
intros.
induction EL as [| E EL]; [ apply set_map_empty | simpl ].
now rewrite set_map_union_distr, IHEL.
Qed.
