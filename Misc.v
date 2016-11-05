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
Proof. intros A a b; destruct a; easy. Qed.

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
apply Nat.mod_add; easy.
Qed.

Theorem neq_negb : ∀ x y, x ≠ y → x = negb y.
Proof.
intros.
destruct x, y; try easy; exfalso; apply H; easy.
Qed.

Theorem negb_neq : ∀ b₁ b₂, negb b₁ ≠ b₂ → b₁ = b₂.
Proof.
intros b₁ b₂ H.
destruct b₁, b₂; try easy; exfalso; apply H; easy.
Qed.

Theorem negb_eq_eq : ∀ b₁ b₂, negb b₁ = negb b₂ → b₁ = b₂.
Proof.
intros b₁ b₂ Hn.
destruct b₁, b₂; [ easy | | | easy ]; discriminate Hn.
Qed.

Theorem cons_comm_app : ∀ A (x : A) l l', l ++ x :: l' = l ++ [x] ++ l'.
Proof. easy. Qed.

Theorem cons_to_app : ∀ A (e : A) el, e :: el = [e] ++ el.
Proof. easy. Qed.

Theorem fold_right_cons : ∀ A B f (x : A) (y : B) l,
  fold_right f x (y :: l) = f y (fold_right f x l).
Proof. easy. Qed.

Theorem fold_right_single : ∀ A B (f : A → B → B) x y,
  fold_right f x [y] = f y x.
Proof. easy. Qed.

Theorem list_prod_nil_r : ∀ A B (l : list A),
  list_prod l ([] : list B) = [].
Proof.
intros A B l.
now induction l.
Qed.

Theorem list_prod_map : ∀ A B C D (f : A → B) (g : C → D) l l',
  list_prod (map f l) (map g l') =
  map (λ '(x, x'), (f x, g x')) (list_prod l l').
Proof.
intros.
revert l'.
induction l as [| x l]; intros; [ easy | simpl ].
rewrite map_app.
f_equal; [ | apply IHl ].
rewrite map_map.
induction l' as [| x' l']; [ easy | now simpl; rewrite IHl' ].
Qed.

Theorem list_prod_map_l : ∀ A B C (f : A → B) l (l' : list C),
  list_prod (map f l) l' =
  map (λ '(x, x'), (f x, x')) (list_prod l l').
Proof.
intros.
revert l'.
induction l as [| x l]; intros; [ easy | simpl; rewrite map_app ].
f_equal; [ now rewrite map_map | apply IHl ].
Qed.

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
inversion H; split; easy.
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
now split.
Qed.

Theorem Forall2_Forall_combine : ∀ A B f (l1 : list A) (l2 : list B),
  Forall2 f l1 l2
  ↔ Forall (λ '(x, y), f x y) (combine l1 l2) ∧ length l1 = length l2.
Proof.
intros.
split; intros HF.
 revert l2 HF.
 induction l1 as [| x1 l1]; intros.
  destruct l2 as [| x2 l2]; [ | now apply Forall2_nil_cons in HF ].
  split; [ constructor | easy ].

  destruct l2 as [| x2 l2]; [ now apply Forall2_cons_nil in HF | simpl ].
  apply Forall2_cons_cons in HF.
  destruct HF as (Hf, HF).
  split.
   constructor; [ easy | now apply IHl1 ].

   f_equal.
   clear -HF.
   revert l2 HF.
   induction l1 as [| x1 l1]; intros.
    destruct l2 as [| x2 l2]; [ easy | ].
    apply Forall2_nil_cons in HF; contradiction.

    destruct l2 as [| x2 l2].
     apply Forall2_cons_nil in HF; contradiction.

     apply Forall2_cons_cons in HF.
     destruct HF as (Hf, HF).
     simpl; f_equal; now apply IHl1.

 destruct HF as (HF, Hlen).
 revert l2 HF Hlen.
 induction l1 as [| x1 l1]; intros.
  destruct l2 as [| x2 l2]; [ constructor | easy ].

  destruct l2 as [| x2 l2]; [ easy | ].
  simpl in Hlen; apply Nat.succ_inj in Hlen.
  simpl in HF.
  apply Forall_inv2 in HF.
  destruct HF as (Hf, HF).
  constructor; [ easy | ].
  apply IHl1; easy.
Qed.

Theorem flat_map_nil_fun : ∀ A B (f : A → list B) l,
 Forall (λ x, f x = []) l
 → flat_map f l = [].
Proof.
intros * HF.
induction l as [| x l]; [ easy | simpl ].
apply Forall_inv2 in HF.
destruct HF as (Hx, HF).
rewrite IHl; [ rewrite Hx; easy | easy ].
Qed.

Theorem app_repeat_diag : ∀ A (e : A) n,
  repeat e n ++ [e] = e :: repeat e n.
Proof.
intros.
induction n; [ easy | ].
simpl; rewrite IHn; easy.
Qed.

Theorem list_nil_app_dec {A} : ∀ (l : list A),
  {l = []} + {∃ x l', l = l' ++ [x]}.
Proof.
intros l.
destruct l as [| x]; [ left; easy | right ].
revert x.
induction l as [| y] using rev_ind; intros; [ exists x, []; easy | ].
exists y, (x :: l); easy.
Qed.

Theorem nth_firstn : ∀ A (l : list A) i n d,
  i < n
  → nth i (firstn n l) d =  nth i l d.
Proof.
intros * Hin.
revert i n Hin.
induction l as [| x l]; intros; [ destruct n, i; easy | simpl ].
destruct n, i; try easy.
apply Nat.succ_lt_mono in Hin; simpl.
now apply IHl.
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
   exists el; split; easy.

   right; destruct H as (el, (H₁, H₂)); subst el₁ el₄.
   exists el; split; easy.
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
Proof. intros b; destruct b; easy. Qed.

Theorem bool_dec_negb_r : ∀ b,
  Bool.bool_dec b (negb b) =
  right (if b return _ then true_neq_negb_true else false_neq_negb_false).
Proof. intros b; destruct b; easy. Qed.

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
  constructor; [ apply Hs; easy | ].
  apply IHl1; easy.
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
 split; [ intros b; left; easy | ].
 split.
  intros b c d Hbc [Hcd| Hcd]; [ subst c; easy | right; easy ].
  intros b c [Hbc| Hbc]; [ left; symmetry | right ]; easy.

 destruct (TTCA bool R He) as (f & Hx & Hxy).
 destruct (Bool.bool_dec (f false) (f true)) as [H| H].
  destruct (Hx true) as [Ht| Ht]; [ | left; easy ].
  destruct (Hx false) as [Hf| Hf]; [ | left; easy ].
  rewrite <- Ht, <- Hf in H; discriminate H.

  right; intros H₁; apply H.
  apply Hxy; unfold R.
  now right.
Qed.

Record choice_function {A} (R : A → A → Prop) f := mkcf
  { cf_repr_uniqueness : ∀ x y, R x y → f x = f y;
    cf_repr_membership : ∀ x, R x (f x) }.

Require Import Permutation.

Theorem Permutation_cons_nil : ∀ A l (x : A),
  ¬ Permutation (x :: l) [].
Proof.
intros * H.
apply Permutation_sym, Permutation_nil_cons in H; easy.
Qed.

Theorem Permutation_cons_exist : ∀ A (x : A) l l',
  Permutation (x :: l) l'
  → ∃ l₁ l₂ : list A, l' = l₁ ++ x :: l₂.
Proof.
intros * HP.
apply Permutation_in with (x := x) in HP; [ now apply in_split | left; easy ].
Qed.

Theorem Permutation_flat_map_map : ∀ A B C (f : A → B → C) la lb,
  Permutation
    (flat_map (λ a, map (λ b, f a b) lb) la)
    (flat_map (λ b, map (λ a, f a b) la) lb).
Proof.
intros.
revert lb.
induction la as [| a la]; intros.
 simpl; rewrite flat_map_nil_fun; [ easy | ].
 induction lb; constructor; easy.

 simpl.
 rewrite IHla; clear IHla.
 revert a la.
 induction lb as [| b lb]; intros; [ easy | ].
 simpl; constructor; rewrite <- IHlb.
 do 2 rewrite app_assoc.
 apply Permutation_app_tail.
 apply Permutation_app_comm.
Qed.
