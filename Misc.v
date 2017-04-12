(* Banach-Tarski paradox. *)
(* Coq v8.6 *)

Require Import Utf8 List Relations NPeano PArith Compare_dec.
Import ListNotations.

Arguments Nat.div : simpl never.
Arguments Nat.modulo : simpl never.

Theorem match_id : ∀ A a (b : A), match a with O => b | S _ => b end = b.
Proof. intros A a b; now destruct a. Qed.

Theorem nat_add_diag_mul_2 : ∀ n, (n + n = 2 * n)%nat.
Proof.
intros.
destruct n; [ easy | now simpl; rewrite Nat.add_0_r ].
Qed.

Theorem nat_div_add_once : ∀ a b, b ≠ 0 → (a + b) / b = S (a / b).
Proof.
intros a b Hb.
replace b with (1 * b) at 1 by apply Nat.mul_1_l.
rewrite Nat.div_add; [ apply Nat.add_1_r | easy ].
Qed.

Theorem nat_mod_add_once : ∀ a b, b ≠ 0 → (a + b) mod b = a mod b.
Proof.
intros a b Hb.
replace b with (1 * b) at 1 by apply Nat.mul_1_l.
now apply Nat.mod_add.
Qed.

Theorem neq_negb : ∀ x y, x ≠ y → x = negb y.
Proof.
intros.
destruct x, y; try easy; exfalso; now apply H.
Qed.

Theorem negb_neq : ∀ b₁ b₂, negb b₁ ≠ b₂ → b₁ = b₂.
Proof.
intros b₁ b₂ H.
destruct b₁, b₂; try easy; exfalso; now apply H.
Qed.

Theorem negb_eq_eq : ∀ b₁ b₂, negb b₁ = negb b₂ → b₁ = b₂.
Proof.
intros b₁ b₂ Hn.
now destruct b₁, b₂.
Qed.

Theorem cons_comm_app : ∀ A (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. easy. Qed.

Theorem app_of_cons : ∀ A (e : A) el, e :: el = [e] ++ el.
Proof. easy. Qed.

Theorem fold_right_single : ∀ A B (f : A → B → B) x y,
  fold_right f x [y] = f y x.
Proof. easy. Qed.

Theorem combine_map : ∀ A B C D (f : A → B) (g : C → D) l l',
  combine (map f l) (map g l') = map (λ '(x, y), (f x, g y)) (combine l l').
Proof.
intros.
revert l'.
induction l as [| x l]; intros; [ easy | simpl ].
destruct l' as [| x' l']; [ easy | simpl; f_equal; apply IHl ].
Qed.

Theorem Forall_inv2 : ∀ A (P : A → Prop) a l,
  List.Forall P (a :: l) → P a ∧ List.Forall P l.
Proof.
intros A P a l H.
inversion H; now split.
Qed.

Theorem Forall2_cons_nil : ∀ A B (R : A → B → Prop) x l,
  ¬Forall2 R (x :: l) [].
Proof.
intros A B * H.
inversion H.
Qed.

Theorem Forall2_cons_cons : ∀ A B (R : A → B → Prop) x y l l',
  Forall2 R (x :: l) (y :: l')
  → R x y ∧ Forall2 R l l'.
Proof.
intros A B * H.
inversion H; subst.
now split.
Qed.

Theorem forall_Forall2 : ∀ A B (R : A → B → Prop) l l' d d',
  length l = length l'
  → (∀ i, (i < length l)%nat → R (List.nth i l d) (List.nth i l' d'))
  → Forall2 R l l'.
Proof.
intros * Hlen Hfa.
revert l' Hlen Hfa.
induction l as [| x l]; intros.
 destruct l' as [| x' l']; [ constructor | easy ].

 destruct l' as [| x' l']; [ easy | constructor ].
  now specialize (Hfa O (Nat.lt_0_succ (length l))); simpl in Hfa.

  simpl in Hlen; apply Nat.succ_inj in Hlen.
  apply IHl; [ easy | ].
  intros i Hilen.
  assert (S i < length (x :: l))%nat as H.
   now simpl; apply -> Nat.succ_lt_mono.

   now specialize (Hfa (S i) H); simpl in Hfa.
Qed.

Theorem Forall2_Forall_combine : ∀ A B f (l1 : list A) (l2 : list B),
  Forall2 f l1 l2
  ↔ Forall (λ '(x, y), f x y) (combine l1 l2) ∧ length l1 = length l2.
Proof.
intros; revert l2.
induction l1, l2.
all: split; [ intros HF | intros (HF, H) ]; simpl.
 1-6: easy.

 apply Forall2_cons_cons in HF.
 split; [ | now f_equal; apply IHl1 ].
 constructor; [ easy | now apply IHl1 ].

 simpl in HF; apply Forall_inv2 in HF.
 constructor; [ easy | ].
 simpl in H; apply Nat.succ_inj in H.
 now apply IHl1; split.
Qed.

Theorem flat_map_nil_fun : ∀ A B (f : A → list B) l,
 Forall (λ x, f x = []) l
 → flat_map f l = [].
Proof.
intros * HF.
induction l as [| x l]; [ easy | simpl ].
apply Forall_inv2 in HF.
destruct HF as (Hx, HF).
rewrite IHl; [ now rewrite Hx | easy ].
Qed.

Theorem app_repeat_diag : ∀ A (e : A) n,
  repeat e n ++ [e] = e :: repeat e n.
Proof.
intros.
induction n; [ easy | ].
simpl; now rewrite IHn.
Qed.

Theorem list_nil_app_dec {A} : ∀ (l : list A),
  {l = []} + {∃ x l', l = l' ++ [x]}.
Proof.
intros l.
destruct l as [| x]; [ now left | right ].
revert x.
induction l as [| y] using rev_ind; intros; [ now exists x, [] | ].
now exists y, (x :: l).
Qed.

Theorem split_app_eq : ∀ A (el₁ el₂ el₃ el₄ : list A),
  el₁ ++ el₂ = el₃ ++ el₄
  → { ∃ el, el₃ = el₁ ++ el ∧ el₂ = el ++ el₄ } +
    { ∃ el, el₁ = el₃ ++ el ∧ el₄ = el ++ el₂ }.
Proof.
intros A el₁ el₂ el₃ el₄ Hel.
revert el₂ el₃ el₄ Hel.
induction el₁ as [| e₁]; intros.
 left; exists el₃.
 now split.

 destruct el₃ as [| e₃].
  right; exists (e₁ :: el₁).
  now split.

  simpl in Hel.
  injection Hel; clear Hel; intros; subst e₃.
  apply IHel₁ in H.
  destruct H as [H| H].
   left; destruct H as (el, (H₁, H₂)); subst el₂ el₃.
   exists el; now split.

   right; destruct H as (el, (H₁, H₂)); subst el₁ el₄.
   exists el; now split.
Qed.

Definition false_neq_negb_false : false ≠ negb false :=
  λ p, False_ind False
    (eq_ind false (λ e : bool, if e then False else True) I true p).

Definition true_neq_negb_true : true ≠ negb true :=
  λ p, False_ind False
   (eq_ind true (λ e : bool, if e then True else False) I false p).

Definition negb_true_neq_true : negb true ≠ true := false_neq_negb_false.
Definition negb_false_neq_false : negb false ≠ false := true_neq_negb_true.

Theorem bool_dec_negb_l : ∀ b,
  Bool.bool_dec (negb b) b =
  right (if b return _ then negb_true_neq_true else negb_false_neq_false).
Proof. intros b; now destruct b. Qed.

Theorem bool_dec_negb_r : ∀ b,
  Bool.bool_dec b (negb b) =
  right (if b return _ then true_neq_negb_true else false_neq_negb_false).
Proof. intros b; now destruct b. Qed.

Theorem Forall2_sym : ∀ A (R : A → A → Prop) l1 l2,
 symmetric _ R → Forall2 R l1 l2 → Forall2 R l2 l1.
Proof.
intros * Hs HF; revert l2 HF.
induction l1; intros; [ now destruct l2 | ].
destruct l2; [ now apply Forall2_cons_nil in HF | ].
apply Forall2_cons_cons in HF.
now constructor; [ apply Hs | apply IHl1 ].
Qed.

(* Type-theoretical Choice Axiom *)
Axiom TTCA : ∀ (A : Type) (R : A → A → Prop), equiv A R →
  ∃ f : A → A, (∀ x : A, R x (f x)) ∧ (∀ x y, R x y → f x = f y).

Theorem EM : ∀ P, P ∨ ¬P.
Proof.
intros P.
set (R (x y : bool) := x = y ∨ P).
assert (He : equiv _ R).
 split; [ intros b; now left | ].
 split.
  now intros b c d Hbc [Hcd| Hcd]; [ subst c | right ].
  now intros b c [Hbc| Hbc]; [ left; symmetry | right ].

 destruct (TTCA bool R He) as (f & Hx & Hxy).
 subst R; simpl in Hx, Hxy.
 destruct (Bool.bool_dec (f false) (f true)) as [H| H].
  destruct (Hx true) as [Ht| Ht]; [ | now left ].
  destruct (Hx false) as [Hf| Hf]; [ | now left ].
  now rewrite <- Ht, <- Hf in H.

  right; intros H₁; apply H.
  now apply Hxy; right.
Qed.

Record choice_function {A} (R : A → A → Prop) f := mkcf
  { cf_repr_uniqueness : ∀ x y, R x y → f x = f y;
    cf_repr_membership : ∀ x, R x (f x) }.

Require Import Permutation.

Theorem Permutation_flat_map_map : ∀ A B C (f : A → B → C) la lb,
  Permutation
    (flat_map (λ a, map (λ b, f a b) lb) la)
    (flat_map (λ b, map (λ a, f a b) la) lb).
Proof.
intros.
revert lb.
induction la as [| a la]; intros.
 simpl; rewrite flat_map_nil_fun; [ easy | ].
 induction lb; now constructor.

 simpl.
 rewrite IHla; clear IHla.
 revert a la.
 induction lb as [| b lb]; intros; [ easy | ].
 simpl; constructor; rewrite <- IHlb.
 do 2 rewrite app_assoc.
 apply Permutation_app_tail.
 apply Permutation_app_comm.
Qed.

Fixpoint map2 {A B C} (f : A → B → C) l1 l2 :=
  match l1 with
  | [] => []
  | a :: t =>
      match l2 with
      | [] => []
      | b :: u => f a b :: map2 f t u
      end
  end.
