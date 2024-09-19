(* Sets as A → Prop *)

Require Import Utf8 List Relations Arith Compare_dec Setoid.
Require Import Misc.

Record set A := mkset { setp : A → Prop }.
Arguments mkset [A] _.
Arguments setp [A] _ _.

Definition empty_set {A} := mkset (λ _ : A, False).

Notation "x ∈ S" := (setp S x) (at level 60).
Notation "x ∉ S" := (¬ setp S x) (at level 60).
Notation "∅" := (empty_set).

Definition set_inter {A} (S₁ S₂ : set A) :=
  mkset (λ x, x ∈ S₁ ∧ x ∈ S₂).
Definition set_union {A} (S₁ S₂ : set A) :=
  mkset (λ x, x ∈ S₁ ∨ x ∈ S₂).
Definition set_union_list {A} (Si : list (set A)) :=
  fold_right set_union ∅ Si.
Definition set_sub {A} (S₁ S₂ : set A) :=
  mkset (λ x, x ∈ S₁ ∧ x ∉ S₂).
Definition set_incl {A} (S₁ S₂ : set A) :=
  ∀ x, x ∈ S₁ → x ∈ S₂.

Arguments set_inter : simpl never.
Arguments set_union : simpl never.
Arguments set_sub : simpl never.
Arguments set_incl : simpl never.

Declare Scope set_scope.
Delimit Scope set_scope with S.

Definition set_eq {A} (S₁ S₂ : set A) := ∀ x, x ∈ S₁ ↔ x ∈ S₂.

Notation "E₁ = E₂" := (set_eq E₁ E₂) : set_scope.
Notation "E₁ ≠ E₂" := (¬ set_eq E₁ E₂) : set_scope.
Notation "E₁ '∩' E₂" := (set_inter E₁ E₂) (at level 40).
Notation "E₁ '∪' E₂" := (set_union E₁ E₂) (at level 50).
Notation "E₁ '∖' E₂" := (set_sub E₁ E₂) (at level 50).
Notation "E₁ '⊂' E₂" := (set_incl E₁ E₂) (at level 60).
Notation "'⋃' Es" := (set_union_list Es) (at level 55).
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

Theorem included_trans A : transitive _ (@set_incl A).
Proof.
intros E F G HEF HFG x Hx.
apply HFG, HEF, Hx.
Qed.

Add Parametric Morphism {A} : (@set_inter A)
  with signature set_eq ==> set_eq ==> set_eq
  as set_inter_morph.
Proof.
intros E E' HE F F' HF.
unfold set_inter; intros p.
split; intros (H₁, H₂).
 now split; [ apply HE | apply HF ].
 now split; [ apply HE | apply HF ].
Qed.

Add Parametric Morphism {A} : (@set_union A)
  with signature set_eq ==> set_eq ==> set_eq
  as set_union_morph.
Proof.
intros E E' HE F F' HF.
intros p.
split.
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
Qed.

Add Parametric Morphism {A} : (@set_sub A)
  with signature set_eq ==> set_eq ==> set_eq
  as set_sub_morph.
Proof.
intros E E' HE F F' HF.
unfold set_sub; intros p.
split; intros (H₁, H₂).
 split; [ now apply HE | intros H; now apply H₂, HF ].
 split; [ now apply HE | intros H; now apply H₂, HF ].
Qed.

Add Parametric Morphism {A} : (@set_incl A)
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

Theorem set_union_empty_r : ∀ A (F : set A),
  (F ∪ ∅ = F)%S.
Proof.
intros * x.
split; intros H; [ | now left ].
now destruct H.
Qed.

Theorem set_inter_empty_l : ∀ A (F : set A),
  (∅ ∩ F = ∅)%S.
Proof.
intros * x.
split; intros H; [ now destruct H as (H, _) | easy ].
Qed.

Theorem set_inter_empty_r : ∀ A (F : set A),
  (F ∩ ∅ = ∅)%S.
Proof.
intros * x.
split; intros H; [ now destruct H as (_, H) | easy ].
Qed.

Theorem set_inter_comm : ∀ A (E F : set A),
  (E ∩ F = F ∩ E)%S.
Proof.
intros; intros x.
split; intros H; destruct H as (HE & HF); now split.
Qed.

Theorem set_union_comm : ∀ A (E F : set A),
  (E ∪ F = F ∪ E)%S.
Proof.
intros; intros x.
now split; intros [HE| HF]; [ right | left | right | left ] .
Qed.

Theorem set_inter_assoc : ∀ A (E F G : set A),
  (E ∩ (F ∩ G) = (E ∩ F) ∩ G)%S.
Proof.
intros; intros x.
split; intros H.
 destruct H as (HE & (HF & HG)).
 split; [ now split | easy ].

 destruct H as ((HE & HF) & HG).
 split; [ easy | now split ].
Qed.

Theorem set_union_assoc : ∀ A (E F G : set A),
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

Theorem set_inter_shuffle0 : ∀ A (E F G : set A),
  (E ∩ F ∩ G = E ∩ G ∩ F)%S.
Proof.
intros; intros x.
split; intros H.
 destruct H as ((HE & HF) & HG).
 split; [ now split | easy ].

 destruct H as ((HE & HF) & HG).
 split; [ now split | easy ].
Qed.

Theorem set_union_list_app : ∀ A (P₁ P₂ : list (set A)),
  (⋃ (P₁ ++ P₂) = (⋃ P₁) ∪ (⋃ P₂))%S.
Proof.
intros.
revert P₁.
induction P₂ as [| Q]; intros.
 rewrite app_nil_r; simpl.
 now rewrite set_union_empty_r.

 rewrite cons_comm_app, app_assoc; simpl.
 rewrite IHP₂.
 unfold set_union_list; simpl; rewrite set_union_assoc.
 intros x.
 split; intros H.
  destruct H as [H| H]; [ left | now right ].
  unfold set_union_list in H.
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
  unfold set_union_list.
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
unfold set_union, set_eq; simpl; intros.
destruct (lt_dec i (length P₁)) as [H₁| H₁].
 now rewrite app_nth1.

 rewrite app_nth2; [ easy | now apply Nat.nlt_ge ].
Qed.

Theorem set_union_inter_self : ∀ A (E : set A) EL,
  E ⊂ ⋃ EL
  → (E = ⋃ map (set_inter E) EL)%S.
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

Theorem set_inter_union_distr_r : ∀ A (E F G : set A),
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

Theorem  set_sub_empty_l : ∀ A (E : set A), (∅ ∖ E = ∅)%S.
Proof.
intros; intros a; now simpl; split; intros H.
Qed.

Theorem set_sub_sub_swap : ∀ A (E F G : set A),
  (E ∖ F ∖ G = E ∖ G ∖ F)%S.
Proof.
intros; intros x; split; intros Hx.
 now destruct Hx as ((HE & HF) & HG).
 now destruct Hx as ((HE & HF) & HG).
Qed.
