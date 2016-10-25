(* Sets as A → Prop *)

Require Import Utf8 List Relations NPeano Compare_dec Setoid.
Require Import Misc.

Record set A := mkset { setp : A → Prop }.
Arguments mkset [A] _.
Arguments setp [A] _ _.

Class set_model A := mksm { set_eq : set A → set A → Prop }.
Arguments set_eq : simpl never.

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

Delimit Scope set_scope with S.

Notation "a = b" := (set_eq a b) : set_scope.
Notation "E₁ '∩' E₂" := (intersection E₁ E₂)
  (at level 40, left associativity).
Notation "E₁ '∪' E₂" := (union E₁ E₂)
  (at level 50, left associativity).
Notation "E₁ '∖' E₂" := (subtract E₁ E₂) (at level 50).
Notation "E₁ '⊂' E₂" := (included E₁ E₂) (at level 60).
Notation "'⋃' Es" := (union_list Es) (at level 55).
Notation "E .[ i ]" := (List.nth i E ∅)
  (at level 1, format "'[' E '[' .[ i ] ']' ']'").

Definition set_equiv {A} := mksm A (λ (E₁ E₂ : set A), ∀ x, x ∈ E₁ ↔ x ∈ E₂).

Theorem set_eq_refl A : reflexive _ (@set_eq A set_equiv).
Proof. intros P x; split; intros; assumption. Qed.

Theorem set_eq_sym A : symmetric _ (@set_eq A set_equiv).
Proof.
intros P₁ P₂ HPP x.
destruct (HPP x) as (H₁, H₂).
split; intros H; [ apply H₂, H | apply H₁, H ].
Qed.

Theorem set_eq_trans A : transitive _ (@set_eq A set_equiv).
Proof.
intros P₁ P₂ P₃ H₁₂ H₂₃ x.
destruct (H₁₂ x) as (H₁, H₂).
destruct (H₂₃ x) as (H₃, H₄).
split; intros H; [ apply H₃, H₁, H | apply H₂, H₄, H ].
Qed.

Add Parametric Relation A : (set A) (@set_eq A set_equiv)
 reflexivity proved by (set_eq_refl A)
 symmetry proved by (set_eq_sym A)
 transitivity proved by (set_eq_trans A)
 as set_eq_rel.

Theorem included_trans A : transitive _ (@included A).
Proof.
intros E F G HEF HFG x Hx.
apply HFG, HEF, Hx.
Qed.

Add Parametric Morphism {A} : (@intersection A)
  with signature
    (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as intersection_morph.
Proof.
intros E E' HE F F' HF.
unfold intersection; intros p.
split; intros (H₁, H₂).
 split; [ apply HE; assumption | apply HF; assumption ].
 split; [ apply HE; assumption | apply HF; assumption ].
Qed.

Add Parametric Morphism {A} : (@union A)
  with signature
    (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as union_morph.
Proof.
intros E E' HE F F' HF.
intros p.
split.
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
 intros [H₁| H₂]; [ left; apply HE, H₁ | right; apply HF, H₂ ].
Qed.

Add Parametric Morphism {A} : (@subtract A)
  with signature
    (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv)
  as subtract_morph.
Proof.
intros E E' HE F F' HF.
unfold subtract; intros p.
split; intros (H₁, H₂).
 split; [ apply HE; assumption | intros H; apply H₂, HF; assumption ].
 split; [ apply HE; assumption | intros H; apply H₂, HF; assumption ].
Qed.

Add Parametric Morphism {A} : (@included A)
  with signature (@set_eq _ set_equiv) ==> (@set_eq _ set_equiv) ==> iff
  as included_morph.
Proof.
intros E F HEF E' F' HE'F'.
split; intros HEE' x HF; apply HE'F', HEE', HEF, HF.
Qed.

Theorem fold_set_eq : ∀ A (s := set_equiv) (P Q : set A),
  (∀ x, x ∈ P ↔ x ∈ Q) = (P = Q)%S.
Proof. intros; reflexivity. Qed.

Theorem set_eq_equiv {A} : ∀ (s := set_equiv) (E F : set A),
  (E = F)%S
  → ∀ p, p ∈ E ↔ p ∈ F.
Proof. intros s * HEF; apply HEF. Qed.

Theorem union_empty_r : ∀ A (s := set_equiv) (F : set A),
  (F ∪ ∅ = F)%S.
Proof.
intros.
subst s; intros x.
split; intros H; [ | left; assumption ].
destruct H as [H| H]; [ assumption | contradiction ].
Qed.

Theorem intersection_empty_l : ∀ A (s := set_equiv) (F : set A),
  (∅ ∩ F = ∅)%S.
Proof.
intros.
subst s; intros x.
split; intros H; [ destruct H as (H, _); contradiction | contradiction ].
Qed.

Theorem intersection_empty_r : ∀ A (s := set_equiv) (F : set A),
  (F ∩ ∅ = ∅)%S.
Proof.
intros.
subst s; intros x.
split; intros H; [ destruct H as (_, H); contradiction | contradiction ].
Qed.

Theorem union_assoc : ∀ A s, s = set_equiv → ∀ (E F G : set A),
  (E ∪ (F ∪ G) = (E ∪ F) ∪ G)%S.
Proof.
intros * Hs E *.
unfold set_eq, union; subst s; intros x.
split; intros H.
 destruct H as [H| [H| H]].
  left; left; assumption.
  left; right; assumption.
  right; assumption.

 destruct H as [[H| H]| H].
  left; assumption.
  right; left; assumption.
  right; right; assumption.
Qed.

Theorem union_list_app : ∀ A s, s = set_equiv → ∀ (P₁ P₂ : list (set A)),
  (⋃ (P₁ ++ P₂) = (⋃ P₁) ∪ (⋃ P₂))%S.
Proof.
intros * Hs *.
revert P₁.
induction P₂ as [| Q]; intros.
 rewrite app_nil_r; simpl; subst s.
 rewrite union_empty_r; reflexivity.

 rewrite cons_comm_app, app_assoc; simpl; subst s.
 rewrite IHP₂, union_assoc; [ | reflexivity ].
 intros x.
 split; intros H.
  destruct H as [H| H]; [ left | right; assumption ].
  unfold union_list in H.
  rewrite fold_right_app in H.
  simpl in H.
  clear - H.
  induction P₁ as [| R P₁].
   simpl in H; simpl.
   destruct H as [H| H]; [ right; assumption | contradiction ].

   simpl in H.
   destruct H as [H| H]; [ simpl; left; left; assumption | ].
   apply IHP₁ in H.
   destruct H as [H| H]; [ simpl; left; right; assumption | ].
   right; assumption.

  destruct H as [H| H]; [ left | right; assumption ].
  unfold union_list.
  rewrite fold_right_app; simpl.
  clear - H.
  induction P₁ as [| R P₁].
   simpl in H; simpl; left.
   destruct H; [ contradiction | assumption ].

   simpl in H; simpl.
   destruct H.
    destruct H; [ left; assumption | right ].
    apply IHP₁; left; assumption.

    right; apply IHP₁; right; assumption.
Qed.

Theorem nth_set_union_list : ∀ A (P : list (set A)) i x,
  i < length P → x ∈ P.[i] → x ∈ ⋃ P.
Proof.
intros A P i x Hi H.
revert P H Hi.
induction i; intros P H Hi.
 destruct P as [| E P]; [ contradiction | left; assumption ].

 destruct P as [| E P]; [ contradiction | simpl in Hi ].
 apply Nat.succ_lt_mono in Hi.
 right; apply IHi; assumption.
Qed.

Theorem nth_set_app : ∀ A (P₁ P₂ : list (set A)) i,
  (P₁ ++ P₂).[i] =
  if lt_dec i (length P₁) then P₁.[i] else P₂.[i-length P₁].
Proof.
intros.
unfold union, set_eq; simpl; intros.
destruct (lt_dec i (length P₁)) as [H₁| H₁].
 rewrite app_nth1; [ reflexivity | assumption ].

 rewrite app_nth2; [ reflexivity | apply Nat.nlt_ge; assumption ].
Qed.

Theorem union_list_intersection : ∀ A (S : set A) SL x,
  x ∈ S
  → x ∈ ⋃ SL
  → x ∈ ⋃ map (intersection S) SL.
Proof.
intros A P QL * HP HQL.
induction QL as [| Q QL]; intros; [ contradiction | simpl ].
destruct HQL as [HQ| HQL]; [ left; split; assumption | right ].
apply IHQL, HQL.
Qed.

Theorem union_list_all_included : ∀ A (s := set_equiv) (E : set A) EL,
  (E = ⋃ EL)%S → Forall (λ Ei, Ei ⊂ E) EL.
Proof.
intros * HE.
apply Forall_forall.
intros F HF.
rewrite HE.
clear - HF.
revert F HF.
induction EL as [| E EL]; intros; [ contradiction | ].
destruct HF as [HF| HF]; [ left; subst E; assumption | ].
right; eapply IHEL; eassumption.
Qed.

Theorem union_intersection_self : ∀ A (s:=set_equiv) (E : set A) EL,
  E ⊂ ⋃ EL
  → (E = ⋃ map (intersection E) EL)%S.
Proof.
intros * HEL x.
split; intros Hx.
 generalize Hx; intros Hxl.
 apply HEL in Hxl.
 clear -Hx Hxl.
 induction EL as [| E₁ EL]; intros; [ contradiction | ].
 destruct Hxl as [Hxl| Hxl]; [ left; split; assumption | ].
 right; apply IHEL; assumption.

 clear -Hx.
 induction EL as [| E₁ EL]; intros; [ contradiction | ].
 destruct Hx as [(Hx, _)| Hx]; [ assumption | ].
 apply IHEL, Hx.
Qed. 

Add Parametric Morphism {A} : (@setp A)
with signature (@set_eq _ set_equiv) ==> eq ==> iff
as setp_morph.
Proof.
intros E F HEF x.
apply HEF.
Qed.
