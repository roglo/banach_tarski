(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List Relations NPeano.
Import ListNotations.

Arguments Nat.div : simpl never.
Arguments Nat.modulo : simpl never.

Theorem match_id : ∀ A a (b : A), match a with O => b | S _ => b end = b.
Proof. intros A a b; destruct a; reflexivity. Qed.

Theorem nat_div_add_once : ∀ a b, b ≠ 0 → (a + b) / b = S (a / b).
Proof.
intros a b Hb.
replace b with (1 * b) at 1 by apply Nat.mul_1_l.
rewrite Nat.div_add; [ apply Nat.add_1_r | assumption ].
Qed.

Theorem nat_mod_add_once : ∀ a b, b ≠ 0 → (a + b) mod b = a mod b.
Proof.
intros a b Hb.
replace b with (1 * b) at 1 by apply Nat.mul_1_l.
apply Nat.mod_add; assumption.
Qed.

Theorem neq_negb : ∀ x y, x ≠ y → x = negb y.
Proof.
intros.
destruct x, y; try reflexivity; exfalso; apply H; reflexivity.
Qed.

Theorem negb_neq : ∀ b₁ b₂, negb b₁ ≠ b₂ → b₁ = b₂.
Proof.
intros b₁ b₂ H.
destruct b₁, b₂; try reflexivity; exfalso; apply H; reflexivity.
Qed.

Theorem negb_eq_eq : ∀ b₁ b₂, negb b₁ = negb b₂ → b₁ = b₂.
Proof.
intros b₁ b₂ Hn.
destruct b₁, b₂; [ reflexivity | | | reflexivity ]; discriminate Hn.
Qed.

Theorem cons_comm_app : ∀ A (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. reflexivity. Qed.

Theorem cons_to_app : ∀ A (e : A) el, e :: el = [e] ++ el.
Proof. reflexivity. Qed.

Theorem fold_right_cons : ∀ A B f (x : A) (y : B) l,
  fold_right f x (y :: l) = f y (fold_right f x l).
Proof. reflexivity. Qed.

Theorem fold_right_single : ∀ A B (f : A → B → B) x y,
  fold_right f x [y] = f y x.
Proof. reflexivity. Qed.

Theorem list_prod_nil_r : ∀ A B (l : list A),
  list_prod l ([] : list B) = [].
Proof.
intros A B l.
induction l as [| x]; [ reflexivity | assumption ].
Qed.

Theorem list_prod_map_l : ∀ A B C (f : A → B) l (l' : list C),
  list_prod (map f l) l' =
  map (λ '(x, x'), (f x, x')) (list_prod l l').
Proof.
intros A B *.
revert l'.
induction l as [| x l]; intros; [ reflexivity | simpl ].
rewrite map_app.
f_equal; [ rewrite map_map; reflexivity | apply IHl ].
Qed.

Theorem Forall_inv2 : ∀ A (P : A → Prop) a l,
  List.Forall P (a :: l) → P a ∧ List.Forall P l.
Proof.
intros A P a l H.
inversion H; split; assumption.
Qed.

Theorem Forall2_nil_cons : ∀ A B (R : A → B → Prop) x l,
  ¬Forall2 R [] (x :: l).
Proof.
intros A B * H.
inversion H.
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
split; assumption.
Qed.

Theorem Forall2_Forall_combine : ∀ A B f (l1 : list A) (l2 : list B),
  Forall2 f l1 l2
  → Forall (λ '(x, y), f x y) (combine l1 l2).
Proof.
intros * HF.
revert l2 HF.
induction l1 as [| x1 l1]; intros; [ constructor | ].
destruct l2 as [| x2 l2]; [ constructor | ].
apply Forall2_cons_cons in HF.
destruct HF as (Hf, HF).
simpl; constructor; [ assumption | ].
apply IHl1; assumption.
Qed.

Theorem app_repeat_diag : ∀ A (e : A) n,
  repeat e n ++ [e] = e :: repeat e n.
Proof.
intros.
induction n; [ reflexivity | ].
simpl; rewrite IHn; reflexivity.
Qed.

Theorem list_nil_app_dec {A} : ∀ (l : list A),
  {l = []} + {∃ x l', l = l' ++ [x]}.
Proof.
intros l.
destruct l as [| x]; [ left; reflexivity | right ].
revert x.
induction l as [| y] using rev_ind; intros; [ exists x, []; reflexivity | ].
exists y, (x :: l); reflexivity.
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
 split; [ reflexivity | assumption ].

 destruct el₃ as [| e₃].
  right; exists (e₁ :: el₁).
  split; [ reflexivity | symmetry; assumption ].

  simpl in Hel.
  injection Hel; clear Hel; intros; subst e₃.
  apply IHel₁ in H.
  destruct H as [H| H].
   left; destruct H as (el, (H₁, H₂)); subst el₂ el₃.
   exists el; split; reflexivity.

   right; destruct H as (el, (H₁, H₂)); subst el₁ el₄.
   exists el; split; reflexivity.
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
Proof. intros b; destruct b; reflexivity. Qed.

Theorem bool_dec_negb_r : ∀ b,
  Bool.bool_dec b (negb b) =
  right (if b return _ then true_neq_negb_true else false_neq_negb_false).
Proof. intros b; destruct b; reflexivity. Qed.

Theorem Forall2_sym: ∀ A (R : A → A → Prop) l1 l2,
 symmetric _ R → Forall2 R l1 l2 → Forall2 R l2 l1.
Proof.
intros * Hs HF.
revert l2 HF.
induction l1 as [| x]; intros.
 destruct l2 as [| y]; [ constructor | ].
 apply Forall2_nil_cons in HF; contradiction.

 destruct l2 as [| y].
  apply Forall2_cons_nil in HF; contradiction.

  apply Forall2_cons_cons in HF.
  destruct HF as (HR & HF).
  constructor; [ apply Hs; assumption | ].
  apply IHl1; assumption.
Qed.

(* Type-theoretical Choice Axiom *)
Axiom TTCA : ∀ (A : Type) (R : A → A → Prop), equiv A R →
  ∃ f : A → A, (∀ x : A, R x (f x)) ∧ (∀ x y, R x y → f x = f y).

(* TTCA implies excluded middle: do you believe that? Diaconescu! *)
Theorem EM : ∀ P, P ∨ ¬P.
Proof.
intros P.
set (R (x y : bool) := x = y ∨ P).
assert (He : equiv _ R).
 split; [ intros b; left; reflexivity | ].
 split.
  intros b c d Hbc [Hcd| Hcd]; [ subst c; assumption | right; assumption ].
  intros b c [Hbc| Hbc]; [ left; symmetry | right ]; assumption.

 destruct (TTCA bool R He) as (f & Hx & Hxy).
 destruct (Bool.bool_dec (f false) (f true)) as [H| H].
  destruct (Hx true) as [Ht| Ht]; [ | left; assumption ].
  destruct (Hx false) as [Hf| Hf]; [ | left; assumption ].
  rewrite <- Ht, <- Hf in H; discriminate H.

  right; intros H₁; apply H.
  apply Hxy; unfold R.
  right; assumption.
Qed.

Record choice_function {A} (R : A → A → Prop) f := mkcf
  { cf_repr_uniqueness : ∀ x y, R x y → f x = f y;
    cf_repr_membership : ∀ x, R x (f x) }.
