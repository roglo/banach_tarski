(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List Relations NPeano Wf_nat.
Import ListNotations.
Require Import Reals Psatz Nsatz.

Require Import Misc Words Normalize Reverse MiscReals Matrix Pset Orbit.
Require Import Partition OrbitRepr GroupTransf Equidecomp.
Require Import Countable QCountable RnCountable NotEmptyPath.

Theorem Rno_intersect_balls_x3_x6 : ∀ x y z,
  ((x - 3)² + y² + z² <= 1)%R
  → ((x - 6)² + y² + z² <= 1)%R
  → False.
Proof.
intros x y z H3 H6.
apply Rplus_le_reg_pos_r in H3; [ | apply Rle_0_sqr ].
apply Rplus_le_reg_pos_r in H3; [ | apply Rle_0_sqr ].
apply Rplus_le_reg_pos_r in H6; [ | apply Rle_0_sqr ].
apply Rplus_le_reg_pos_r in H6; [ | apply Rle_0_sqr ].
clear - H3 H6.
rewrite <- Rsqr_1 in H3 at 4.
rewrite <- Rsqr_1 in H6 at 6.
apply Rsqr_le_abs_0 in H3.
apply Rsqr_le_abs_0 in H6.
rewrite Rabs_R1 in H3, H6.
unfold Rabs in H3, H6.
destruct (Rcase_abs (x - 3)), (Rcase_abs (x - 6)); lra.
Qed.

Theorem Banach_Tarski_paradox_but_fixpoints :
  equidecomposable ball_but_fixpoints
    (xtransl 3 ball_but_fixpoints ∪ xtransl 6 ball_but_fixpoints)%S.
Proof.
pose proof TTCA _ same_orbit equiv_same_orbit as H.
destruct H as (f & Hu & Hm).
remember (mkcf _ _ f Hm Hu) as Hosf.
remember (mkos _ f) as os eqn:Hos.
clear HeqHosf.
set (A₁ := (M ∪ SS ạ ∪ B)%S).
set (A₂ := (SS ạ⁻¹ ∖ B)%S).
set (A₃ := SS ḅ).
set (A₄ := SS ḅ⁻¹).
exists [A₁; A₂; A₃; A₄].
exists
  (map (xtransl 3) [A₁; rot ạ A₂] ++
   map (xtransl 6) [A₃; rot ḅ A₄]); simpl.
split.
 subst A₁ A₂ A₃ A₄.
 eapply r_decomposed_4; now try eassumption.

 split.
  pose proof r_decomposed_2_a f Hosf os Hos as Ha.
  pose proof r_decomposed_2_b f Hosf os Hos as Hb.
  eapply partition_group_map with (g := Xtransl 3) in Ha; try eassumption.
  eapply partition_group_map with (g := Xtransl 6) in Hb; try eassumption.
  eapply partition_union in Hb; [ | | apply Ha ].
   apply Hb.

   unfold intersection, set_eq; intros (x, y, z).
   split; [ intros (H₁, H₂) | easy ].
   simpl in H₁, H₂.
   unfold empty_set; simpl.
   destruct H₁ as (H₁, H₃).
   destruct H₂ as (H₂, H₄).
   unfold ball in H₁, H₂.
   now apply (Rno_intersect_balls_x3_x6 x y z).

  constructor; [ now exists (Xtransl 3) | ].
  constructor; [ now exists (Comb (Xtransl 3) (Rot ạ)) | ].
  constructor; [ now exists (Xtransl 6) | ].
  constructor; [ now exists (Comb (Xtransl 6) (Rot ḅ)) | ].
  constructor.
Qed.

Check Banach_Tarski_paradox_but_fixpoints.

Theorem equidec_union : ∀ E₁ E₂ F₁ F₂,
  (E₁ ∩ F₁ = ∅)%S
  → (E₂ ∩ F₂ = ∅)%S
  → equidecomposable E₁ E₂
  → equidecomposable F₁ F₂
  → equidecomposable (E₁ ∪ F₁) (E₂ ∪ F₂).
Proof.
intros * HEF₁ HEF₂ HE HF.
destruct HE as (PE₁ & PE₂ & HE₁ & HE₂ & HE).
destruct HF as (PF₁ & PF₂ & HF₁ & HF₂ & HF).
unfold equidecomposable.
exists (PE₁ ++ PF₁), (PE₂ ++ PF₂).
split; [ now apply partition_union | ].
split; [ now apply partition_union | ].
now apply Forall2_app.
Qed.

Theorem equidec_transl : ∀ dx E F,
  equidecomposable E F
  → equidecomposable (xtransl dx E) (xtransl dx F).
Proof.
intros * HEF.
destruct HEF as (PE & PF & HPE & HPF & HEF).
unfold equidecomposable.
exists (map (xtransl dx) PE), (map (xtransl dx) PF).
split; [ apply (partition_group_map E PE (Xtransl dx) HPE) | ].
split; [ apply (partition_group_map F PF (Xtransl dx) HPF) | ].
apply Forall2_Forall_combine in HEF.
destruct HEF as (HEF, Hlen).
apply Forall2_Forall_combine.
do 2 rewrite map_length.
split; [ | easy ].
rewrite Forall_forall in HEF.
apply Forall_forall; intros (E₁, F₁) HEF₁.
rewrite combine_map in HEF₁.
apply in_map_iff in HEF₁.
destruct HEF₁ as ((E₂ & F₂) & Hp & HEF₁).
injection Hp; clear Hp; intros; subst E₁ F₁.
apply HEF in HEF₁.
destruct HEF₁ as (g, HEF₁).
exists (Comb (Xtransl dx) (Comb g (Xtransl (-dx)))); simpl.
rewrite xtransl_xtransl, Rplus_opp_l.
now rewrite xtransl_0, HEF₁.
Qed.

Theorem separated_balls_without_fixpoints :
  (xtransl 3 ball_but_fixpoints ∩ xtransl 6 ball_but_fixpoints = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6); simpl | easy ].
unfold ball_but_fixpoints in H3, H6.
simpl in H3, H6.
destruct H3 as (H3, _).
destruct H6 as (H6, _).
now apply (Rno_intersect_balls_x3_x6 x y z).
Qed.

Theorem separated_balls :
  (xtransl 3 ball ∩ xtransl 6 ball = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6) | easy ].
unfold ball in H3, H6.
simpl in H3, H6.
now apply (Rno_intersect_balls_x3_x6 x y z).
Qed.

Definition nat_of_free_elem e : nat :=
  match e with
  | ạ => 0
  | ạ⁻¹ => 1
  | ḅ => 2
  | ḅ⁻¹ => 3
  end.

Definition free_elem_of_nat n :=
  match n with
  | 0 => ạ
  | 1 => ạ⁻¹
  | 2 => ḅ
  | _ => ḅ⁻¹
  end.

Fixpoint path_of_nat_aux it (n : nat) :=
  match it with
  | O => []
  | S it' =>
      free_elem_of_nat (n mod 4) ::
      match (n / 4)%nat with
      | O => []
      | S n' => path_of_nat_aux it' n'
      end
  end.

Definition path_of_nat n :=
  match n with
  | O => []
  | S n' => path_of_nat_aux n n'
  end.

Theorem free_elem_of_nat_nat_of_free_elem_mod_4 : ∀ e,
  free_elem_of_nat (nat_of_free_elem e mod 4) = e.
Proof. intros (t, d); now destruct t, d. Qed.

Theorem nat_of_free_elem_div_4 : ∀ e, (nat_of_free_elem e / 4 = 0)%nat.
Proof. intros (t, d); now destruct t, d. Qed.

Theorem path_of_nat_aux_enough_iter : ∀ m n p,
  m < n
 → m < p
  → path_of_nat_aux n m = path_of_nat_aux p m.
Proof.
intros * Hmn Hmp.
revert m p Hmn Hmp.
induction n; intros; [ easy | ].
destruct p; [ easy | ].
simpl; f_equal.
remember (m / 4) as q eqn:Hq; symmetry in Hq.
destruct q; [ easy | ].
destruct m; [ easy | ].
apply Nat.succ_lt_mono in Hmn.
apply Nat.succ_lt_mono in Hmp.
destruct (lt_dec q n) as [Hqn| Hqn].
 destruct (lt_dec q p) as [Hqp| Hqp]; [ apply IHn; easy | ].
 apply Nat.nlt_ge in Hqp.
 apply Nat.succ_le_mono in Hqp.
 rewrite <- Hq in Hqp.
 apply Nat.succ_lt_mono in Hmp.
 assert (H : S m < S m / 4) by (eapply Nat.lt_le_trans; eassumption).
 apply Nat.nle_gt in H.
 exfalso; apply H; clear.
 remember (S m) as n; clear m Heqn.
 apply Nat.div_le_upper_bound; [ easy | ].
 induction n; [ easy | ].
 rewrite Nat.mul_comm; simpl.
 apply -> Nat.succ_le_mono.
 eapply Nat.le_trans; [ eassumption | ].
 rewrite Nat.mul_comm.
 eapply Nat.le_trans; [ | eapply Nat.le_succ_diag_r ].
 eapply Nat.le_trans; eapply Nat.le_succ_diag_r.

 apply Nat.nlt_ge in Hqn.
 apply Nat.succ_le_mono in Hqn.
 rewrite <- Hq in Hqn.
 assert (H : m < S m / 4).
  eapply lt_trans; [ eapply Hmn | assumption ].

  exfalso; clear - H.
  apply Nat.nle_gt in H.
  exfalso; apply H; clear.
  destruct m; [ easy | ].
  apply Nat.div_le_upper_bound; [ easy | simpl ].
  rewrite <- Nat.add_succ_comm; simpl.
  do 2 apply -> Nat.succ_le_mono.
  apply Nat.le_add_r.
Qed.

Theorem path_of_nat_aux_cons : ∀ e p q, (q < p)%nat →
  ∃ m n : ℕ, n < m ∧ path_of_nat_aux m n = e :: path_of_nat_aux p q.
Proof.
intros * Hqp.
remember (nat_of_free_elem e) as r eqn:Hr.
exists (S (r + S q * 4)), (r + S q * 4)%nat.
split; [ apply Nat.lt_succ_diag_r | ].
remember (S q) as sq; simpl; subst sq.
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.div_add; [ | easy ].
rewrite <- Nat.add_succ_comm.
remember (S q * 4)%nat as qq; simpl; subst qq.
rewrite Hr, free_elem_of_nat_nat_of_free_elem_mod_4.
f_equal.
rewrite nat_of_free_elem_div_4, Nat.add_0_l.
apply path_of_nat_aux_enough_iter; [ | easy ].
eapply Nat.lt_trans; [ apply Nat.lt_succ_diag_r | ].
rewrite Nat.mul_comm, Nat.add_comm; simpl.
do 4 rewrite <- Nat.add_succ_l.
rewrite <- Nat.add_assoc.
apply Nat.lt_add_pos_r, Nat.lt_0_succ.
Qed.

Theorem path_of_nat_aux_is_cons : ∀ e el,
  ∃ m n, (n < m)%nat ∧ path_of_nat_aux m n = e :: el.
Proof.
intros.
revert e.
induction el as [| e₁]; intros.
 remember (nat_of_free_elem e) as m eqn:Hm.
 exists (S m), m.
 split; [ now apply Nat.lt_succ_r | ].
 now subst m; destruct e as (t, d); destruct t, d.

 pose proof IHel e₁ as He₁.
 destruct He₁ as (p & q & Hpq & He₁).
 rewrite <- He₁.
 clear - Hpq.
 now apply path_of_nat_aux_cons.
Qed.

Theorem paths_are_countable : is_countable (list free_elem).
Proof.
unfold is_countable; simpl.
exists path_of_nat.
intros el.
destruct el as [| e el]; [ now exists O | ].
enough (Hn : ∃ n, path_of_nat (S n) = e :: el).
 destruct Hn as (n, Hn).
 now exists (S n).

 pose proof path_of_nat_aux_is_cons e el.
 destruct H as (m & n & Hmn & H).
 exists n; unfold path_of_nat.
 rewrite path_of_nat_aux_enough_iter with (p := m); try easy.
 apply Nat.lt_succ_diag_r.
Qed.

Definition unit_interv := mkset (λ x, (0 <= x < 1)%R).

Definition ter_bin_of_point r '(P x y z) := ter_bin_of_frac_part (x / r).

Theorem ter_bin_of_ball_surj : ∀ r, (0 < r)%R → ∀ (u : ℕ → bool),
  ∃ p : point, p ∈ sphere r ∧ (∀ n, ter_bin_of_point r p n = u n).
Proof.
intros * Hr *.
specialize (ter_bin_of_frac_part_surj u); intros (s & Hs & Hn).
exists (P (s * r) (r * √ (1 - s²)) 0); simpl.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_r; [ | lra ].
rewrite Rmult_1_r.
split; [ | easy ].
do 2 rewrite Rsqr_mult.
rewrite Rsqr_sqrt; [ do 3 rewrite Rsqr_pow2; lra | ].
rewrite Rsqr_pow2.
apply Rplus_le_reg_r with (r := (s ^ 2)%R).
unfold Rminus; rewrite Rplus_assoc, Rplus_opp_l.
rewrite Rplus_0_l, Rplus_0_r.
replace 1%R with (1 ^ 2)%R by lra.
apply pow_incr; lra.
Qed.

Theorem in_sphere_in_ball : ∀ r p, (0 ≤ r ≤ 1)%R →
  p ∈ sphere r
  → p ∈ ball.
Proof.
intros r (x, y, z) Hr Hs; simpl in Hs; simpl; rewrite Hs.
replace 1%R with (1²)%R by apply Rsqr_1.
apply Rsqr_incr_1; [ easy | easy | lra ].
Qed.

Theorem ball_not_countable : ¬ (is_countable {p : point | p ∈ ball}).
Proof.
intros H.
unfold is_countable in H.
destruct H as (f, Hf).
enough (Hcontr : ∃ a, a ∈ ball ∧ ∀ n, proj1_sig (f n) ≠ a).
 destruct Hcontr as (a & Ha & Hnn).
 specialize (Hf (exist _ a Ha)).
 destruct Hf as (n, Hn).
 specialize (Hnn n).
 now rewrite Hn in Hnn; apply Hnn.

 specialize
  (Cantor_gen ℕ ℕ point (setp (sphere 1)) id (ter_bin_of_point 1) id_nat
     (ter_bin_of_ball_surj 1 Rlt_0_1)).
 intros H.
 specialize (H (λ n, proj1_sig (f n))) as (p, H).
 exists p.
 split.
  specialize (H O) as (Hs, _).
  apply in_sphere_in_ball with (r := 1); [ | easy ].
  split; [ apply Rle_0_1 | apply Rle_refl ].

  intros n Hn.
  specialize (H n).
  destruct H.
  now symmetry in Hn.
Qed.

Theorem ball_set_not_countable : ∀ r, (0 < r)%R →
  ∀ f : ℕ → point, ∃ p : point, p ∈ sphere r ∧ ∀ n : ℕ, f n ≠ p.
Proof.
intros * Hr *.
specialize
 (Cantor_gen ℕ ℕ point (setp (sphere r)) id (ter_bin_of_point r) id_nat
    (ter_bin_of_ball_surj r Hr) f) as (p, Hp).
exists p.
split; [ apply (Hp O) | ].
intros n.
apply not_eq_sym, Hp.
Qed.

Require Import QArith.
Notation "'ℚ'" := Q.

Definition mkqmat := @mkmat ℚ.

Definition qmat_id := mkqmat 1 0 0 0 1 0 0 0 1.

Definition qmat_mul m₁ m₂ :=
  mkqmat
    (a₁₁ m₁ * a₁₁ m₂ + a₁₂ m₁ * a₂₁ m₂ + a₁₃ m₁ * a₃₁ m₂)
    (a₁₁ m₁ * a₁₂ m₂ + a₁₂ m₁ * a₂₂ m₂ + a₁₃ m₁ * a₃₂ m₂)
    (a₁₁ m₁ * a₁₃ m₂ + a₁₂ m₁ * a₂₃ m₂ + a₁₃ m₁ * a₃₃ m₂)
    (a₂₁ m₁ * a₁₁ m₂ + a₂₂ m₁ * a₂₁ m₂ + a₂₃ m₁ * a₃₁ m₂)
    (a₂₁ m₁ * a₁₂ m₂ + a₂₂ m₁ * a₂₂ m₂ + a₂₃ m₁ * a₃₂ m₂)
    (a₂₁ m₁ * a₁₃ m₂ + a₂₂ m₁ * a₂₃ m₂ + a₂₃ m₁ * a₃₃ m₂)
    (a₃₁ m₁ * a₁₁ m₂ + a₃₂ m₁ * a₂₁ m₂ + a₃₃ m₁ * a₃₁ m₂)
    (a₃₁ m₁ * a₁₂ m₂ + a₃₂ m₁ * a₂₂ m₂ + a₃₃ m₁ * a₃₂ m₂)
    (a₃₁ m₁ * a₁₃ m₂ + a₃₂ m₁ * a₂₃ m₂ + a₃₃ m₁ * a₃₃ m₂).

Delimit Scope qmat_scope with qmat.
Notation "m₁ * m₂" := (qmat_mul m₁ m₂) : qmat_scope.

Definition Trv i j a :=
  match i with
  | 1%nat =>
      match j with
      | 1%nat => qmat_id
      | 2 => mkqmat 1 a 0 0 1 0 0 0 1
      | _ => mkqmat 1 0 a 0 1 0 0 0 1
      end
  | 2%nat =>
      match j with
      | 1%nat => mkqmat 1 0 0 a 1 0 0 0 1
      | 2 => qmat_id
      | _ => mkqmat 1 0 0 0 1 a 0 0 1
      end
  | _ =>
      match j with
      | 1%nat => mkqmat 1 0 0 0 1 0 a 0 1
      | 2 => mkqmat 1 0 0 0 1 0 0 a 1
      | _ => qmat_id
      end
  end.

Definition Dil i a :=
  match i with
  | 1%nat => mkqmat a 0 0 0 1 0 0 0 1
  | 2 => mkqmat 1 0 0 0 a 0 0 0 1
  | _ => mkqmat 1 0 0 0 1 0 0 0 a
  end.

Definition mat_swap i j :=
  match i with
  | 1%nat =>
      match j with
      | 1%nat => qmat_id
      | 2 => (Dil 2 (-1 # 1) * Trv 1 2 1 * Trv 2 1 (-1 # 1) * Trv 1 2 1)%qmat
      | _ => (Dil 3 (-1 # 1) * Trv 1 3 1 * Trv 3 1 (-1 # 1) * Trv 1 3 1)%qmat
      end
  | 2 =>
      match j with
      | 1%nat =>
          (Dil 1 (-1 # 1) * Trv 2 1 1 * Trv 1 2 (-1 # 1) * Trv 2 1 1)%qmat
      | 2 =>
          qmat_id
      | _ =>
          (Dil 3 (-1 # 1) * Trv 2 3 1 * Trv 3 2 (-1 # 1) * Trv 2 3 1)%qmat
      end
  | _ =>
      match j with
      | 1%nat =>
          (Dil 1 (-1 # 1) * Trv 1 3 1 * Trv 3 1 (-1 # 1) * Trv 1 3 1)%qmat
      | 2 =>
          (Dil 3 (-1 # 1) * Trv 2 3 1 * Trv 3 2 (-1 # 1) * Trv 2 3 1)%qmat
      | _ =>
          qmat_id
      end
  end.

Definition Qabs q := if Qlt_le_dec q 0 then Qopp q else q.

Fixpoint argmax_loop it m i k :=
  match it with
  | O => O
  | S it' =>
      let i_max := if eq_nat_dec i 3 then 3 else argmax_loop it' m (S i) k in
      if Qlt_le_dec (Qabs (mt i k m)) (Qabs (mt i_max k m)) then i_max else i
  end.

Definition argmax m k := argmax_loop 3 m k k.

Fixpoint cancel_but_loop four_minus_i k m :=
  match four_minus_i with
  | O => m
  | S fmi =>
      let i := (4 - four_minus_i)%nat in
      let m :=
        if eq_nat_dec i k then m else (Trv i k (- mt i k m) * m)%qmat
      in
      cancel_but_loop fmi k m
  end.

Definition cancel_but := cancel_but_loop 3.

Fixpoint gauss_jordan_loop four_minus_k m :=
  match four_minus_k with
  | O => m
  | S fmk =>
      let k := (4 - four_minus_k)%nat in
      let i_max := argmax m k in
      if Qeq_dec (mt i_max k m) 0 then m
      else
        let m := (mat_swap k i_max * m)%qmat in
        let m := (Dil k (/ mt k k m) * m)%qmat in
        let m := cancel_but k m in
        let m := mat_map Qred m in
        gauss_jordan_loop fmk m
  end.

Definition gauss_jordan := gauss_jordan_loop 3.

Definition mat_ex :=
  mkqmat 1 (2#1) (3#1) (4#1) (5#1) (6#1) (7#1) (8#1) (9#1).
Definition mat_ex2 :=
  mkqmat (2#1) (-1#1) 0 (-1#1) (2#1) (-1#1) 0 (-1#1) (2#1).
Definition mat_ex3 :=
  mkqmat (1#1) (3#1) (1#1) (1#1) (1#1) (-1#1) (3#1) (11#1) (5#1).
Definition mat_ex4 :=
  mkqmat (2#1) (1#1) (-1#1) (-3#1) (-1#1) (2#1) (-2#1) (1#1) (2#1).

(*
Compute (mat_swap 1 2 * mat_ex)%qmat.
Compute (mat_swap 2 3 * mat_ex)%qmat.
Compute (mat_swap 3 1 * mat_ex)%qmat.
*)

(*
Compute (gauss_jordan mat_ex).
Compute (gauss_jordan mat_ex2).
Compute (gauss_jordan mat_ex3).
Compute (gauss_jordan mat_ex4).
*)

Definition rotation_unit_eigenvec (m : matrix ℝ) :=
  let x := (a₂₃ m - a₃₂ m)%R in
  let y := (a₃₁ m - a₁₃ m)%R in
  let z := (a₁₂ m - a₂₁ m)%R in
  let r := vec_norm (P x y z) in
  P (x / r) (y / r) (z / r).

Definition rotation_fixpoint (m : matrix ℝ) k :=
  vec_const_mul k (rotation_unit_eigenvec m).

Definition mat_of_path el :=
  List.fold_right mat_mul mat_id (map mat_of_elem el).

Definition fixpoint_of_path r el :=
  rotation_fixpoint (mat_of_path el) r.

Definition fixpoint_of_nat r n :=
  fixpoint_of_path r (path_of_nat n).

Theorem rotation_fixpoint_on_sphere : ∀ r m,
  m ≠ mat_transp m
  → rotation_fixpoint m r ∈ sphere r.
Proof.
intros * Hm.
unfold rotation_fixpoint; simpl.
remember (a₂₃ m - a₃₂ m)%R as x eqn:Hx.
remember (a₃₁ m - a₁₃ m)%R as y eqn:Hy.
remember (a₁₂ m - a₂₁ m)%R as z eqn:Hz.
remember (√ (x² + y² + z²)) as r₁ eqn:Hr₁.
do 3 rewrite Rsqr_mult.
do 2 rewrite <- Rmult_plus_distr_l.
assert (Hrnz : (r₁ ≠ 0)%R).
 intros H; apply Hm; clear Hm; subst r₁.
 apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in H.
 unfold mat_transp.
 destruct m; simpl in *; simpl.
 unfold mkrmat; f_equal; lra.

 rewrite Rsqr_div; [ | easy ].
 rewrite Rsqr_div; [ | easy ].
 rewrite Rsqr_div; [ | easy ].
 unfold Rdiv.
 do 2 rewrite <- Rmult_plus_distr_r; subst r₁.
 rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
 rewrite Rinv_r; [ apply Rmult_1_r | ].
 intros H; apply Hrnz; clear Hrnz; rewrite H.
 apply sqrt_0.
Qed.

Theorem matrix_all_fixpoints_ok : ∀ m p k,
  is_rotation_matrix m
  → p = rotation_fixpoint m k
  → mat_vec_mul m p = p.
Proof.
intros * Hrm Hn.
subst p.
unfold rotation_fixpoint.
remember (rotation_unit_eigenvec m) as ev eqn:Hev.
unfold rotation_unit_eigenvec in Hev.
remember (√ ((a₃₂ m - a₂₃ m)² + (a₁₃ m - a₃₁ m)² + (a₂₁ m - a₁₂ m)²)) as r.
rename Heqr into Hr.
destruct ev as (x, y, z).
injection Hev; clear Hev; intros Hz Hy Hx.
move Hx after Hy; move Hz after Hy.
unfold is_rotation_matrix in Hrm.
destruct Hrm as (Ht & Hd).
unfold mat_det in Hd.
unfold mat_mul, mat_transp, mat_id in Ht; simpl in Ht.
injection Ht; clear Ht; intros H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ H₉.
simpl.
setoid_rewrite fold_Rsqr in H₁.
setoid_rewrite fold_Rsqr in H₅.
setoid_rewrite fold_Rsqr in H₉.
move H₉ after H₁; move H₅ after H₁.
move H₄ before H₂; move H₇ before H₃; move H₈ before H₆.
clear H₄ H₇ H₈; move H₆ after H₂.
move Hd before H₉.
rename H₆ into H₁₁; rename H₂ into H₂₁; rename H₃ into H₃₁.
rename H₁ into H₃; rename H₅ into H₂; rename H₉ into H₁.
replace (k * x)%R with (x * k)%R by apply Rmult_comm.
replace (k * y)%R with (y * k)%R by apply Rmult_comm.
replace (k * z)%R with (z * k)%R by apply Rmult_comm.
subst x y z.
progress repeat rewrite <- Rmult_div.
unfold Rdiv.
progress repeat rewrite Rmult_assoc.
remember (k * / r)%R as kr.
clear Hr Heqkr.
f_equal; nsatz.
Qed.

(* https://en.wikipedia.org/wiki/Rotation_matrix#Determining_the_angle *)
Definition mat_trace M := (a₁₁ M + a₂₂ M + a₃₃ M)%R.
Definition cos_rot_angle M := ((mat_trace M - 1) / 2)%R.

Theorem rotate_vec_mul : ∀ el p,
  fold_right rotate p el
  = mat_vec_mul (fold_right mat_mul mat_id (map mat_of_elem el)) p.
Proof.
intros el p.
induction el as [| e]; [ rewrite mat_vec_mul_id; reflexivity | simpl ].
rewrite IHel, mat_vec_mul_assoc; reflexivity.
Qed.

Theorem matrix_of_non_empty_path_is_not_identity : ∀ el,
  norm_list el ≠ []
  → mat_of_path el ≠ mat_id.
Proof.
intros * Hn.
apply rotate_non_empty_path_is_not_identity in Hn.
destruct Hn as (p, Hp).
intros H; apply Hp; clear Hp.
rewrite rotate_vec_mul.
fold (mat_of_path el); rewrite H.
apply mat_vec_mul_id.
Qed.

Theorem mat_of_path_is_rotation_matrix : ∀ el,
 is_rotation_matrix (mat_of_path el).
Proof.
intros.
induction el as [| e el].
 unfold mat_of_path; simpl.
 apply mat_id_is_rotation_matrix.

 unfold mat_of_path; simpl; fold (mat_of_path el).
 apply mat_mul_is_rotation_matrix; [ apply rotate_is_rotation_matrix | easy ].
Qed.

Theorem D_of_nat_prop : ∀ r n nf no p p₁ el el₁,
  (nf, no) = prod_nat_of_nat n
  → el₁ = path_of_nat nf
  → p₁ = rotation_fixpoint (mat_of_path el₁) r
  → el = path_of_nat no
  → p = fold_right rotate p₁ el
  → same_orbit p p₁ ∧ fold_right rotate p₁ el₁ = p₁.
Proof.
intros * Hnfo Hel₁ Hp₁ Hel Hp.
split.
 exists (rev_path el).
 symmetry in Hp; apply rotate_rev_path in Hp; apply Hp.

 apply matrix_all_fixpoints_ok in Hp₁.
  unfold mat_of_path in Hp₁.
  rewrite <- rotate_vec_mul in Hp₁; apply Hp₁.

  apply mat_of_path_is_rotation_matrix.
Qed.

Definition D_of_prod_nat r '(nf, no) :=
  let p₁ := fixpoint_of_nat r nf in
  let el := path_of_nat no in
  fold_right rotate p₁ el.

Definition D_of_nat r n :=
  D_of_prod_nat r (prod_nat_of_nat n).

Theorem D_of_nat_nat_in_D : ∀ r nf no,
  norm_list (path_of_nat nf) ≠ []
  → D_of_prod_nat r (nf, no) ∈ D.
Proof.
intros * Hnl; simpl.
remember (fixpoint_of_nat r nf) as p₁ eqn:Hp₁.
remember (path_of_nat no) as el eqn:Hel.
remember (fold_right rotate p₁ el) as p eqn:Hp.
remember (path_of_nat nf) as el₁ eqn:Hel₁.
exists el₁, p₁.
remember (nat_of_prod_nat (nf, no)) as n eqn:Hn.
assert (Hnfo : (nf, no) = prod_nat_of_nat n).
 now rewrite Hn, prod_nat_of_nat_inv.

 unfold fixpoint_of_nat in Hp₁.
 unfold fixpoint_of_path in Hp₁.
 rewrite <- Hel₁ in Hp₁.
 now eapply D_of_nat_prop in Hnfo; try eassumption.
Defined.

Theorem D_of_prod_nat_in_D : ∀ r nn,
  norm_list (path_of_nat (fst nn)) ≠ []
  → D_of_prod_nat r nn ∈ D.
Proof.
intros r (nf, no) Hnl.
now apply D_of_nat_nat_in_D.
Defined.

Theorem D_of_nat_in_D : ∀ r n, 
  norm_list (path_of_nat (Nat.sqrt n - (n - Nat.sqrt n ^ 2))) ≠ []
  → D_of_nat r n ∈ D.
Proof.
intros * Hnl.
now apply D_of_nat_nat_in_D.
Defined.

Fixpoint nat_of_path_aux el :=
  match el with
  | e :: el' => S (nat_of_path_aux el' * 4 + nat_of_free_elem e)
  | [] => O
  end.

Definition nat_of_path el :=
  match el with
  | e :: el' => nat_of_path_aux el
  | [] => O
  end.

Theorem path_of_nat_inv : ∀ el, path_of_nat (nat_of_path el) = el.
Proof.
intros el.
unfold path_of_nat, nat_of_path.
induction el as [| e₁ el]; [ easy | simpl ].
rewrite Nat.add_comm.
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.div_add; [ | easy ].
rewrite nat_of_free_elem_div_4, Nat.add_0_l.
f_equal; [ now destruct e₁ as (t, d); destruct t, d | ].
destruct el as [| e₂ el]; [ easy | ].
simpl in IHel.
rewrite Nat.add_comm in IHel.
rewrite Nat.mod_add in IHel; [ | easy ].
rewrite Nat.div_add in IHel; [ | easy ].
rewrite nat_of_free_elem_div_4, Nat.add_0_l in IHel.
injection IHel; clear IHel; intros Hel He₂.
simpl; rewrite <- Nat.add_succ_comm; simpl.
rewrite Nat.add_comm.
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.div_add; [ | easy ].
rewrite nat_of_free_elem_div_4, Nat.add_0_l.
rewrite He₂; f_equal.
remember (nat_of_path_aux el) as n eqn:Hn; symmetry in Hn.
destruct n; [ easy | ].
rewrite <- Hel.
apply path_of_nat_aux_enough_iter.
 apply Nat.lt_lt_add_l.
 do 3 apply Nat.lt_lt_succ_r.
 rewrite Nat.mul_add_distr_r.
 apply Nat.lt_lt_add_l.
 remember 4 as four; simpl; subst four.
 rewrite Nat.mul_add_distr_r.
 destruct n; [ apply Nat.lt_0_succ | ].
 apply Nat.lt_lt_add_l.
 remember 4 as four; simpl; subst four.
 rewrite Nat.mul_add_distr_r.
 rewrite <- Nat.mul_assoc.
 apply Nat.lt_le_trans with (m := (4 * 4 + n)%nat).
  simpl; apply -> Nat.succ_lt_mono.
  do 14 apply Nat.lt_lt_succ_r.
  apply Nat.lt_succ_diag_r.

  apply Nat.add_le_mono; [ easy | ].
  rewrite Nat.mul_comm; simpl.
  apply Nat.le_add_r.

 apply Nat.lt_lt_add_l.
 rewrite Nat.mul_comm; simpl.
 rewrite <- Nat.add_succ_l.
 apply Nat.lt_lt_add_r, Nat.lt_succ_diag_r.
Qed.

(*
Compute (path_of_nat (nat_of_path [])).
Compute (path_of_nat (nat_of_path [ạ])).
Compute (path_of_nat (nat_of_path [ạ⁻¹])).
Compute (path_of_nat (nat_of_path [ḅ])).
Compute (path_of_nat (nat_of_path [ḅ⁻¹])).
Compute (path_of_nat (nat_of_path [ạ; ạ])).
Compute (path_of_nat (nat_of_path [ạ; ạ⁻¹])).
Compute (path_of_nat (nat_of_path [ạ; ḅ])).
Compute (path_of_nat (nat_of_path [ạ; ḅ⁻¹])).

Compute (nat_of_path (path_of_nat 0)).
Compute (nat_of_path (path_of_nat 1)).
Compute (nat_of_path (path_of_nat 2)).
Compute (nat_of_path (path_of_nat 3)).
Compute (nat_of_path (path_of_nat 4)).
Compute (nat_of_path (path_of_nat 5)).
Compute (nat_of_path (path_of_nat 6)).
Compute (nat_of_path (path_of_nat 7)).
Compute (nat_of_path (path_of_nat 8)).
Compute (nat_of_path (path_of_nat 9)).
Compute (nat_of_path (path_of_nat 10)).
Compute (nat_of_path (path_of_nat 11)).
Compute (nat_of_path (path_of_nat 12)).
Compute (nat_of_path (path_of_nat 13)).
*)

Theorem surj_prod_nat_surj_nat : ∀ A P,
  (∃ g : ℕ * ℕ -> A, ∀ a : A, P a → ∃ nn : ℕ * ℕ, g nn = a)
  → ∃ f : ℕ → A, ∀ a : A, P a → ∃ n : ℕ, f n = a.
Proof.
intros * (g & Hg).
exists (λ n, g (prod_nat_of_nat n)).
intros a Ha.
specialize (Hg a Ha) as (nfo & Hg); subst a.
exists (nat_of_prod_nat nfo); destruct nfo.
now rewrite prod_nat_of_nat_inv.
Qed.

Definition prod_4_nat_of_nat n :=
  let '(n₁, n₂) := prod_nat_of_nat n in
  let '(n₃, n₄) := prod_nat_of_nat n₁ in
  let '(n₅, n₆) := prod_nat_of_nat n₂ in
  (n₃, n₄, n₅, n₆).

Theorem surj_prod_4_nat_surj_nat : ∀ A P,
  (∃ g : ℕ * ℕ * ℕ * ℕ -> A, ∀ a : A, P a → ∃ nn, g nn = a)
  → ∃ f : ℕ → A, ∀ a : A, P a → ∃ n : ℕ, f n = a.
Proof.
intros * (g & Hg).
exists (λ n, g (prod_4_nat_of_nat n)).
intros a Ha.
specialize (Hg a Ha) as ((((n₁, n₂), n₃), n₄) & Hg); subst a.
exists (nat_of_prod_nat (nat_of_prod_nat (n₁, n₂), nat_of_prod_nat (n₃, n₄))).
unfold prod_4_nat_of_nat.
now do 3 rewrite prod_nat_of_nat_inv.
Qed.

Definition bool_prod_nat_of_prod_nat '(n₁, n₂) : bool * ℕ * ℕ :=
  (if n₁ mod 2 then false else true, (n₁ / 2)%nat, n₂).

Definition prod_nat_of_bool_prod_nat '(b, n₁, n₂) : ℕ * ℕ :=
  ((2 * n₁ + Nat.b2n b)%nat, n₂).

Theorem bool_prod_nat_of_prod_nat_inv : ∀ bnn,
  bool_prod_nat_of_prod_nat (prod_nat_of_bool_prod_nat bnn) = bnn.
Proof.
intros ((b & n₁) & n₂); simpl; f_equal.
rewrite Nat.add_0_r.
rewrite nat_add_diag_mul_2.
rewrite Nat.add_comm, Nat.mul_comm.
rewrite Nat.mod_add; [ | easy ].
rewrite Nat.div_add; [ | easy ].
now destruct b.
Qed.

Theorem surj_bool_prod_nat_surj_prod_nat : ∀ A P,
  (∃ g : bool * ℕ * ℕ -> A, ∀ a, P a → ∃ bnn, g bnn = a)
  → ∃ f : ℕ * ℕ → A, ∀ a, P a → ∃ nn, f nn = a.
Proof.
intros * (g & Hg).
exists (λ nn, g (bool_prod_nat_of_prod_nat nn)).
intros a Ha.
specialize (Hg a Ha) as (bnn, Hg).
exists (prod_nat_of_bool_prod_nat bnn).
now rewrite bool_prod_nat_of_prod_nat_inv.
Qed.

Theorem surjective_prod_nat_surjective_nat : ∀ A,
  (∃ g : ℕ * ℕ → A, FinFun.Surjective g)
  → ∃ f : ℕ → A, FinFun.Surjective f.
Proof.
intros * (g & Hg).
exists (λ n, g (prod_nat_of_nat n)).
intros p.
specialize (Hg p) as (nfo & Hg).
subst p.
exists (nat_of_prod_nat nfo); destruct nfo.
now rewrite prod_nat_of_nat_inv.
Qed.

Definition fixpoint_of_bool_prod_nat r '(b, nf, no) :=
  let p := rotation_fixpoint (mat_of_path (path_of_nat nf)) r in
  let p₁ :=
    if is_neg_point p then if (b : bool) then p else neg_point p
    else if b then neg_point p else p
  in
  fold_right rotate p₁ (path_of_nat no).

Lemma mat_of_path_app : ∀ el₁ el₂,
  mat_of_path (el₁ ++ el₂) = (mat_of_path el₁ * mat_of_path el₂)%mat.
Proof.
intros.
revert el₁.
induction el₂ as [| e₂ el₂]; intros.
 unfold mat_of_path at 3; simpl.
 rewrite app_nil_r.
 now rewrite mat_mul_id_r.

 rewrite cons_comm_app, app_assoc, IHel₂.
 unfold mat_of_path; simpl.
 rewrite map_app, fold_right_app; simpl.
 rewrite mat_mul_assoc; f_equal.
 rewrite mat_mul_id_r; clear.
 induction el₁ as [| e₁]; [ now rewrite mat_mul_id_l | ].
 now simpl; rewrite IHel₁, mat_mul_assoc.
Qed.

Theorem rev_path_length : ∀ el, length (rev_path el) = length el.
Proof.
intros.
induction el as [| e el]; [ easy | simpl ].
rewrite rev_path_cons, rev_path_single.
rewrite app_length; simpl.
now rewrite Nat.add_1_r, IHel.
Qed.

Theorem rev_path_nth : ∀ el i,
  (i < length el)%nat
  → List.nth i (rev_path el) ạ = negf (List.nth (length el - S i) el ạ⁻¹).
Proof.
intros el i Hlen.
revert i Hlen.
induction el as [| e el]; intros; [ now simpl; rewrite match_id | ].
rewrite rev_path_cons, rev_path_single.
destruct (lt_dec i (length el)) as [Hi| Hi].
 rewrite app_nth1; [ | now rewrite rev_path_length ].
 rewrite IHel; simpl; [ f_equal | easy ].
 remember (length el - i)%nat as n eqn:Hn.
 symmetry in Hn.
 destruct n.
  apply Nat.sub_0_le in Hn.
  apply Nat.lt_succ_r in Hn.
  now apply Nat.nle_gt in Hn.

  f_equal; apply Nat.succ_inj.
  now rewrite <- Hn, <- Nat.sub_succ_l.

 apply Nat.nlt_ge in Hi.
 simpl in Hlen; unfold lt in Hlen.
 apply Nat.succ_le_mono in Hlen.
 apply Nat.le_antisymm in Hi; [ | easy ].
 rewrite Hi.
 rewrite app_nth2; [ simpl | now rewrite rev_path_length; unfold ge ].
 now rewrite rev_path_length, <- Hi, Nat.sub_diag.
Qed.

Theorem nth_in_split : ∀ A (n : ℕ) (l : list A) (d : A),
  (n < length l)%nat
  → ∃ l1 l2 : list A, l = l1 ++ List.nth n l d :: l2.
Proof.
intros * Hn.
now apply in_split, nth_In.
Qed.

Theorem nth_in_consec_split : ∀ A (n : ℕ) (l : list A) (d₁ d₂ : A),
  (S n < length l)%nat
  → ∃ l1 l2 : list A,
    l = l1 ++ List.nth n l d₁ :: List.nth (S n) l d₂ :: l2.
Proof.
intros * Hn.
revert n Hn.
induction l as [| x l]; intros; [ now apply Nat.nlt_0_r in Hn | ].
simpl in Hn.
apply Nat.succ_lt_mono in Hn.
destruct n.
 destruct l as [| y l]; [ now apply Nat.nlt_0_r in Hn | ].
 now exists [], l.

 apply IHl in Hn.
 destruct Hn as (l1 & l2 & Hn).
 now exists (x :: l1), l2; simpl; f_equal.
Qed.

Theorem rev_norm_path_eq_path : ∀ el,
  norm_list el = el
  → rev_path el = el
  → el = [].
Proof.
intros * Hn Hr.
destruct el as [| e₁ el]; [ easy | exfalso ].
destruct (zerop (length el mod 2)) as [Hel| Hel].
 apply Nat.mod_divides in Hel; [ | easy ].
 destruct Hel as (c, Hc).
  assert (Hlt : (c < length (e₁ :: el))%nat).
   simpl; rewrite Hc; simpl.
   rewrite Nat.add_0_r.
   apply Nat.lt_succ_r, Nat.le_add_r.

   pose proof rev_path_nth (e₁ :: el) c Hlt as H.
   rewrite Hr in H; simpl in H.
   symmetry in H.
   replace (length el - c)%nat with c in H.
    destruct c; [ now apply no_fixpoint_negf in H | ].
    simpl in Hlt.
    apply Nat.succ_lt_mono in Hlt.
    erewrite nth_indep in H; [ now apply no_fixpoint_negf in H | ].
    rewrite Hc; simpl; rewrite Nat.add_0_r.
    apply Nat.lt_succ_r, Nat.le_add_r.

    rewrite Hc; simpl.
    now rewrite Nat.add_0_r, Nat.add_sub.

 assert (He : (length (e₁ :: el) mod 2 = 0)%nat).
  simpl.
  rewrite <- Nat.add_1_r.
  rewrite <- Nat.add_mod_idemp_l; [ | easy ].
  remember (length el mod 2) as m eqn:Hm.
  destruct m; [ easy | ].
  destruct m; [ easy | ].
  assert (H : (2 ≠ 0)%nat) by easy.
  apply (Nat.mod_upper_bound (length el)) in H.
  rewrite <- Hm in H.
  do 2 apply Nat.succ_lt_mono in H.
  now apply Nat.nlt_0_r in H.

  apply Nat.mod_divides in He; [ | easy ].
  destruct He as (c, Hc).
  destruct c; [ easy | ].
  assert (Hlt : (S c < length (e₁ :: el))%nat).
   rewrite Hc; simpl; rewrite Nat.add_0_r.
   apply Nat.lt_succ_r; rewrite Nat.add_comm.
   apply Nat.le_add_r.

   generalize Hlt; intros H.
   apply rev_path_nth in H.
   rewrite Hr in H.
   remember (e₁ :: el) as el₂; simpl in H.
   rewrite Hc in H; simpl in H.
   rewrite Nat.add_0_r, Nat.add_sub in H; subst el₂.
   rename H into Hlen.
   pose proof nth_in_consec_split free_elem c (e₁ :: el) ạ⁻¹ ạ Hlt.
   destruct H as (l₁ & l₂ & Hll).
   rewrite Hlen, <- Hn in Hll.
   now apply norm_list_no_consec in Hll.
Qed.

Theorem rev_path_eq_path : ∀ el,
  rev_path (norm_list el) = norm_list el
  → norm_list el = [].
Proof.
intros el Hel.
remember (norm_list el) as el₁ eqn:Hel₁.
assert (H : norm_list el₁ = el₁) by (subst el₁; apply norm_list_idemp).
clear el Hel₁.
rename el₁ into el; rename H into Hn.
now apply rev_norm_path_eq_path.
Qed.

Theorem norm_list_app_diag_is_nil : ∀ el,
  norm_list (el ++ el) = []
  → norm_list el = [].
Proof.
intros el Hel.
rewrite norm_list_normal_l in Hel.
rewrite norm_list_normal_r in Hel.
apply norm_list_app_is_nil in Hel; try now rewrite norm_list_idemp.
now apply rev_path_eq_path.
Qed.

Theorem mat_vec_mul_cross_distr : ∀ M U V,
  is_rotation_matrix M
  → mat_vec_mul M (U × V) = mat_vec_mul M U × mat_vec_mul M V.
Proof.
intros M (u₁, u₂, u₃) (v₁, v₂, v₃) (Ht, Hd); simpl.
unfold mat_mul, mat_id in Ht; simpl in Ht.
injection Ht; clear Ht; intros H₁ H₂ H₃ H₄ H₅ H₆ H₇ H₈ H₉.
unfold mat_det in Hd.
destruct M; simpl in *.
f_equal.
 clear H₁ H₂ H₃ H₄ H₅ H₆; nsatz.
 clear H₁ H₂ H₃ H₇ H₈ H₉; nsatz.
 clear H₄ H₅ H₆ H₇ H₈ H₉; nsatz.
Qed.

Theorem mat_eigenvec_mul_const : ∀ M V,
  mat_vec_mul M V = V
  → ∀ k, mat_vec_mul M (vec_const_mul k V) = vec_const_mul k V.
Proof.
intros * HV k.
rewrite <- mat_const_vec_mul.
rewrite mat_vec_mat_const_mul.
now rewrite HV.
Qed.

Theorem vec_cross_mul_eq_0 : ∀ U V,
  U ≠ 0%vec
  → V ≠ 0%vec
  → U × V = 0%vec
  → ∃ a b, a ≠ 0%R ∧ b ≠ 0%R ∧ (a ⁎ U + b ⁎ V = 0)%vec.
Proof.
intros * HU HV HUV.
destruct U as (u₁, u₂, u₃).
destruct V as (v₁, v₂, v₃).
simpl in HUV; simpl.
injection HUV; clear HUV; intros H₃ H₂ H₁.
move H₁ after H₂; move H₃ after H₂.
apply Rminus_diag_uniq in H₁.
apply Rminus_diag_uniq in H₂.
apply Rminus_diag_uniq in H₃.
destruct (Req_dec u₁ 0) as [Hu₁| Hu₁].
 subst u₁; rewrite Rmult_0_l in H₃; symmetry in H₃.
 apply Rmult_integral in H₃.
 destruct H₃ as [H₃| H₃]; [ subst u₂ | subst v₁ ].
  rewrite Rmult_0_l in H₁; symmetry in H₁.
  apply Rmult_integral in H₁.
  destruct H₁ as [H₁| H₁]; [ now exfalso; subst u₃; apply HU | subst v₂ ].
  rewrite Rmult_0_l in H₂.
  apply Rmult_integral in H₂.
  destruct H₂ as [H₂| H₂]; [ now exfalso; subst u₃; apply HU | subst v₁ ].
  exists v₃, (- u₃)%R.
  split; [ now intros H; apply HV; f_equal | ].
  split; [ now apply Ropp_neq_0_compat; intros H; apply HU; f_equal | ].
  f_equal; lra.

  destruct (Req_dec u₂ 0) as [Hu₂| Hu₂].
   subst u₂; rewrite Rmult_0_l in H₁; symmetry in H₁.
   apply Rmult_integral in H₁.
   destruct H₁ as [H₁| H₁]; [ now exfalso; subst u₃; apply HU | subst v₂ ].
   exists v₃, (- u₃)%R.
   split; [ now intros H; apply HV; f_equal | ].
   split; [ now apply Ropp_neq_0_compat; intros H; apply HU; f_equal | ].
   f_equal; lra.

   destruct (Req_dec u₃ 0) as [Hu₃| Hu₃].
    subst u₃; rewrite Rmult_0_l in H₁.
    apply Rmult_integral in H₁.
    destruct H₁ as [H₁| H₁]; [ easy | subst v₃ ].
    exists v₂, (-u₂)%R.
    split; [ now intros H; apply HV; f_equal | ].
    split; [ now apply Ropp_neq_0_compat; intros H; apply HU; f_equal | ].
    f_equal; lra.

    destruct (Req_dec v₂ 0) as [Hv₂| Hv₂].
     subst v₂; rewrite Rmult_0_r in H₁.
     apply Rmult_integral in H₁.
     destruct H₁ as [H₁| H₁]; [ easy | now exfalso; subst v₃; apply HV ].

     exists v₂, (- u₂)%R.
     split; [ easy | ].
     split; [ now apply Ropp_neq_0_compat | ].
     f_equal; [ lra | lra | ].
     rewrite Rmult_comm, <- H₁; lra.

 destruct (Req_dec v₁ 0) as [Hv₁| Hv₁].
  subst v₁; rewrite Rmult_0_r in H₃.
  apply Rmult_integral in H₃.
  destruct H₃ as [H₃| H₃]; [ easy | subst v₂ ].
  rewrite Rmult_0_r in H₂; symmetry in H₂.
  apply Rmult_integral in H₂.
  destruct H₂ as [H₂| H₂]; [ easy | now exfalso; subst v₃; apply HV ].

  exists v₁, (- u₁)%R.
  split; [ easy | ].
  split; [ now apply Ropp_neq_0_compat | ].
  f_equal; lra.
Qed.

Theorem free_family_diff_norm_vec : ∀ U V,
  ∥U∥ = ∥V∥
  → U ≠ V
  → is_neg_point U = is_neg_point V
  → U ≠ 0%vec
  → V ≠ 0%vec
  → ∀ a b : ℝ, (a ⁎ U + b ⁎ V)%vec = 0%vec → a = 0%R ∧ b = 0%R.
Proof.
intros * Hvn Hvv Hn Hv₁ Hv₂ * Hab.
destruct U as (x₁, y₁, z₁).
destruct V as (x₂, y₂, z₂).
simpl in Hab.
injection Hab; clear Hab; intros Hz Hy Hx.
move Hx after Hy; move Hz after Hy.
simpl in Hvn.
destruct (Req_dec a 0) as [Ha| Ha].
 subst a; split; [ easy | ].
 rewrite Rmult_0_l, Rplus_0_l in Hx, Hy, Hz.
 apply Rmult_integral in Hx; destruct Hx as [Hx| Hx]; [ easy | ].
 apply Rmult_integral in Hy; destruct Hy as [Hy| Hy]; [ easy | ].
 apply Rmult_integral in Hz; destruct Hz as [Hz| Hz]; [ easy | ].
 now exfalso; subst; apply Hv₂.

 destruct (Req_dec b 0) as [Hb| Hb].
  subst b; split; [ | easy ].
  rewrite Rmult_0_l, Rplus_0_r in Hx, Hy, Hz.
  apply Rmult_integral in Hx; destruct Hx as [Hx| Hx]; [ easy | ].
  apply Rmult_integral in Hy; destruct Hy as [Hy| Hy]; [ easy | ].
  apply Rmult_integral in Hz; destruct Hz as [Hz| Hz]; [ easy | ].
  now exfalso; subst; apply Hv₁.

  exfalso.
  apply Rplus_opp_r_uniq in Hx.
  apply Rplus_opp_r_uniq in Hy.
  apply Rplus_opp_r_uniq in Hz.
  apply Rmult_eq_compat_r with (r := (/ b)%R) in Hx.
  apply Rmult_eq_compat_r with (r := (/ b)%R) in Hy.
  apply Rmult_eq_compat_r with (r := (/ b)%R) in Hz.
  rewrite Rmult_shuffle0, Rinv_r in Hx; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r in Hy; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r in Hz; [ | easy ].
  rewrite Rmult_1_l, fold_Rdiv in Hx, Hy, Hz.
  rewrite Ropp_mult_distr_l in Hx, Hy, Hz.
  rewrite Rmult_div in Hx, Hy, Hz.
  subst x₂ y₂ z₂.
  do 3 rewrite Rsqr_mult in Hvn.
  do 2 rewrite <- Rmult_plus_distr_l in Hvn.
  rewrite sqrt_mult_alt in Hvn; [ | apply Rle_0_sqr ].
  rewrite <- Rmult_1_l in Hvn at 1.
  apply Rmult_eq_reg_r in Hvn.
   symmetry in Hvn.
   rewrite sqrt_Rsqr_abs in Hvn.
   apply Rabs_or in Hvn.
   destruct Hvn as [ Hvn | Hvn ].
    rewrite Hvn in Hvv.
    now do 3 rewrite Rmult_1_l in Hvv; apply Hvv.

    rewrite Hvn in Hn.
    do 3 rewrite <- Ropp_mult_distr_l in Hn.
    do 3 rewrite Rmult_1_l in Hn.
    fold (neg_point (P x₁ y₁ z₁)) in Hn.
    rewrite is_neg_point_neg_point in Hn; [ | easy ].
    now symmetry in Hn; apply no_fixpoint_negb in Hn.

   intros H; apply Hv₁.
   apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
   apply sqr_vec_norm_eq_0 in H.
   now destruct H as (Hx & Hy & Hz); subst.
Qed.

Theorem nonzero_cross_mul : ∀ U V,
  ∥U∥ = ∥V∥
  → is_neg_point U = is_neg_point V
  → U ≠ 0%vec
  → V ≠ 0%vec
  → U ≠ V
  → U × V ≠ 0%vec.
Proof.
intros * Hvn Hn Hv₁ Hv₂ Hvv Hvvz.
destruct U as (x₁, y₁, z₁).
destruct V as (x₂, y₂, z₂).
simpl in Hvvz.
injection Hvvz; clear Hvvz; intros Hz Hy Hx.
move Hx after Hy; move Hz after Hy.
apply Rminus_diag_uniq in Hx.
apply Rminus_diag_uniq in Hy.
apply Rminus_diag_uniq in Hz.
simpl in Hn.
destruct (Rlt_dec x₁ 0) as [Hx₁| Hx₁].
 destruct (Rlt_dec x₂ 0) as [Hx₂| Hx₂]; [ clear Hn |  ].
  apply Rmult_eq_compat_r with (r := (/ x₂)%R) in Hz.
  symmetry in Hz.
  rewrite Rmult_assoc in Hz.
  rewrite Rinv_r in Hz; [  | lra ].
  rewrite Rmult_1_r in Hz.
  rewrite Rmult_shuffle0, fold_Rdiv in Hz.
  apply Rmult_eq_compat_r with (r := (/ x₂)%R) in Hy.
  rewrite Rmult_assoc in Hy.
  rewrite Rinv_r in Hy; [  | lra ].
  rewrite Rmult_1_r in Hy.
  rewrite Rmult_shuffle0, fold_Rdiv in Hy.
  subst y₁ z₁; clear Hx.
  replace x₁ with (x₁ / x₂ * x₂)%R in Hvn at 1.
   replace x₁ with (x₁ / x₂ * x₂)%R in Hvv at 1.
    remember (x₁ / x₂)%R as k eqn:Hk .
    rewrite vec_mul_diag in Hvn, Hvv.
    simpl in Hvn.
    do 3 rewrite Rsqr_mult in Hvn.
    do 2 rewrite <- Rmult_plus_distr_l in Hvn.
    rewrite sqrt_mult in Hvn.
     rewrite <- Rmult_1_l in Hvn.
     apply Rmult_eq_reg_r in Hvn.
      rewrite sqrt_Rsqr_abs in Hvn.
      apply Rabs_or in Hvn.
      destruct Hvn as [Hvn| Hvn]; subst k.
       rewrite Hvn in Hvv.
       rewrite vec_const_mul_1_l in Hvv.
       now apply Hvv.

       apply Rmult_eq_compat_r with (r := x₂) in Hvn.
       unfold Rdiv in Hvn.
       rewrite Rmult_assoc in Hvn.
       rewrite Rinv_l in Hvn; [  | lra ].
       rewrite <- Ropp_mult_distr_l in Hvn.
       rewrite Rmult_1_r, Rmult_1_l in Hvn.
       subst x₁; lra.

      intros H.
      apply sqrt_eq_0 in H.
       apply sqr_vec_norm_eq_0 in H; lra.

       apply nonneg_sqr_vec_norm.

     apply Rle_0_sqr.

     apply nonneg_sqr_vec_norm.

    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite Rinv_l; [  | lra ].
    now (rewrite Rmult_1_r).

   unfold Rdiv.
   rewrite Rmult_assoc.
   rewrite Rinv_l; [  | lra ].
   now (rewrite Rmult_1_r).

  destruct (Rgt_dec x₂ 0) as [Hgx₂| Hgx₂]; [ easy |  ].
  apply Rnot_lt_le in Hx₂.
  apply Rnot_lt_le in Hgx₂.
  apply Rle_antisym in Hx₂; [ subst x₂ | easy ].
  rewrite Rmult_0_r in Hy, Hz; symmetry in Hy.
  apply Rmult_integral in Hy.
  apply Rmult_integral in Hz.
  destruct Hy as [| Hy]; [ lra |  ].
  destruct Hz as [| Hz]; [ lra |  ].
  now subst y₂ z₂; apply Hv₂.

 destruct (Rgt_dec x₁ 0) as [Hgx₁| Hgx₁].
  destruct (Rlt_dec x₂ 0) as [Hlx₂| Hlx₂]; [ easy |  ].
  destruct (Rgt_dec x₂ 0) as [Hgx₂| Hgx₂]; [ clear Hn |  ].
   apply Rmult_eq_compat_r with (r := (/ x₂)%R) in Hz.
   symmetry in Hz.
   rewrite Rmult_assoc in Hz.
   rewrite Rinv_r in Hz; [  | lra ].
   rewrite Rmult_1_r in Hz.
   rewrite Rmult_shuffle0, fold_Rdiv in Hz.
   apply Rmult_eq_compat_r with (r := (/ x₂)%R) in Hy.
   rewrite Rmult_assoc in Hy.
   rewrite Rinv_r in Hy; [  | lra ].
   rewrite Rmult_1_r in Hy.
   rewrite Rmult_shuffle0, fold_Rdiv in Hy.
   subst y₁ z₁; clear Hx.
   replace x₁ with (x₁ / x₂ * x₂)%R in Hvn at 1.
    replace x₁ with (x₁ / x₂ * x₂)%R in Hvv at 1.
     remember (x₁ / x₂)%R as k eqn:Hk .
     rewrite vec_mul_diag in Hvn, Hvv.
     simpl in Hvn.
     do 3 rewrite Rsqr_mult in Hvn.
     do 2 rewrite <- Rmult_plus_distr_l in Hvn.
     rewrite sqrt_mult in Hvn.
      rewrite <- Rmult_1_l in Hvn.
      apply Rmult_eq_reg_r in Hvn.
       rewrite sqrt_Rsqr_abs in Hvn.
       apply Rabs_or in Hvn.
       destruct Hvn as [Hvn| Hvn]; subst k.
        rewrite Hvn in Hvv.
        rewrite vec_const_mul_1_l in Hvv.
        now (apply Hvv).

        apply Rmult_eq_compat_r with (r := x₂) in Hvn.
        unfold Rdiv in Hvn.
        rewrite Rmult_assoc in Hvn.
        rewrite Rinv_l in Hvn; [  | lra ].
        rewrite <- Ropp_mult_distr_l in Hvn.
        rewrite Rmult_1_r, Rmult_1_l in Hvn.
        subst x₁; lra.

       intros H.
       apply sqrt_eq_0 in H.
        apply sqr_vec_norm_eq_0 in H; lra.

        apply nonneg_sqr_vec_norm.

      apply Rle_0_sqr.

      apply nonneg_sqr_vec_norm.

     unfold Rdiv.
     rewrite Rmult_assoc.
     rewrite Rinv_l; [  | lra ].
     now rewrite Rmult_1_r.

    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite Rinv_l; [  | lra ].
    now rewrite Rmult_1_r.

   apply Rnot_lt_le in Hlx₂.
   apply Rnot_gt_le in Hgx₂.
   apply Rle_antisym in Hlx₂; [ subst x₂ | easy ].
   rewrite Rmult_0_r in Hy; symmetry in Hy.
   rewrite Rmult_0_r in Hz.
   apply Rmult_integral in Hy.
   apply Rmult_integral in Hz.
   destruct Hy; [ lra | subst z₂ ].
   destruct Hz; [ lra | subst y₂ ].
   now apply Hv₂.

  apply Rnot_lt_le in Hx₁.
  apply Rnot_gt_le in Hgx₁.
  apply Rle_antisym in Hx₁; [ subst x₁ | easy ].
  rewrite Rmult_0_l in Hy.
  rewrite Rmult_0_l in Hz; symmetry in Hz.
  apply Rmult_integral in Hy.
  apply Rmult_integral in Hz.
  destruct (Rlt_dec x₂ 0) as [Hlx₂| Hlx₂].
   destruct Hy; [ subst z₁ | lra ].
   destruct Hz; [ subst y₁ | lra ].
   now apply Hv₁.

   destruct (Rgt_dec x₂ 0) as [Hgx₂| Hgx₂].
    destruct Hy; [ subst z₁ | lra ].
    destruct Hz; [ subst y₁ | lra ].
    now apply Hv₁.

    apply Rnot_lt_le in Hlx₂.
    apply Rnot_gt_le in Hgx₂.
    apply Rle_antisym in Hlx₂; [ subst x₂ | easy ].
    clear Hy Hz.
    destruct (Rlt_dec y₁ 0) as [Hly₁| Hly₁].
     destruct (Rgt_dec y₁ 0) as [Hgy₁| Hgy₁]; [ lra |  ].
     apply Rmult_eq_compat_l with (r := (/ y₁)%R) in Hx.
     do 2 rewrite <- Rmult_assoc in Hx.
     rewrite Rinv_l in Hx; [  | lra ].
     rewrite Rmult_1_l, Rmult_comm, <- Rmult_assoc in Hx.
     rewrite fold_Rdiv in Hx.
     subst z₂.
     replace y₂ with (y₂ / y₁ * y₁)%R in Hvn at 1.
      replace y₂ with (y₂ / y₁ * y₁)%R in Hvv at 1.
       replace 0%R with (y₂ / y₁ * 0)%R in Hvn at 2 by lra.
       replace 0%R with (y₂ / y₁ * 0)%R in Hvv at 2 by lra.
       remember (y₂ / y₁)%R as k eqn:Hk .
       rewrite vec_mul_diag in Hvn, Hvv.
       simpl in Hvn.
       do 3 rewrite Rsqr_mult in Hvn.
       do 2 rewrite <- Rmult_plus_distr_l in Hvn.
       rewrite sqrt_mult in Hvn.
        symmetry in Hvn.
        rewrite <- Rmult_1_l in Hvn.
        apply Rmult_eq_reg_r in Hvn.
         rewrite sqrt_Rsqr_abs in Hvn.
         apply Rabs_or in Hvn.
         destruct Hvn as [Hvn| Hvn]; subst k.
          rewrite Hvn in Hvv.
          rewrite vec_const_mul_1_l in Hvv.
          now apply Hvv.

          apply Rmult_eq_compat_r with (r := y₁) in Hvn.
          unfold Rdiv in Hvn.
          rewrite Rmult_assoc in Hvn.
          rewrite Rinv_l in Hvn; [  | lra ].
          rewrite <- Ropp_mult_distr_l in Hvn.
          rewrite Rmult_1_r, Rmult_1_l in Hvn.
          subst y₂.
          destruct (Rlt_dec (- y₁) 0) as [Hly₂| Hly₂]; [ lra |  ].
          destruct (Rgt_dec (- y₁) 0) as [Hgy₂| Hgy₂]; [ easy | lra ].

         intros H.
         apply sqrt_eq_0 in H.
          apply sqr_vec_norm_eq_0 in H; lra.

          apply nonneg_sqr_vec_norm.

        apply Rle_0_sqr.

        apply nonneg_sqr_vec_norm.

       unfold Rdiv.
       rewrite Rmult_assoc.
       rewrite Rinv_l; [  | lra ].
       now rewrite Rmult_1_r.

      unfold Rdiv.
      rewrite Rmult_assoc.
      rewrite Rinv_l; [  | lra ].
      now rewrite Rmult_1_r.

  destruct (Rgt_dec y₁ 0) as [Hgy₁| Hgy₁].
   apply Rmult_eq_compat_l with (r := (/ y₁)%R) in Hx.
   do 2 rewrite <- Rmult_assoc in Hx.
   rewrite Rinv_l in Hx; [  | lra ].
   rewrite Rmult_1_l, Rmult_comm, <- Rmult_assoc in Hx.
   rewrite fold_Rdiv in Hx.
   subst z₂.
   replace y₂ with (y₂ / y₁ * y₁)%R in Hvn at 1.
    replace y₂ with (y₂ / y₁ * y₁)%R in Hvv at 1.
     replace 0%R with (y₂ / y₁ * 0)%R in Hvn at 2 by lra.
     replace 0%R with (y₂ / y₁ * 0)%R in Hvv at 2 by lra.
     remember (y₂ / y₁)%R as k eqn:Hk .
     rewrite vec_mul_diag in Hvn, Hvv.
     simpl in Hvn.
     do 3 rewrite Rsqr_mult in Hvn.
     do 2 rewrite <- Rmult_plus_distr_l in Hvn.
     rewrite sqrt_mult in Hvn.
      symmetry in Hvn.
      rewrite <- Rmult_1_l in Hvn.
      apply Rmult_eq_reg_r in Hvn.
       rewrite sqrt_Rsqr_abs in Hvn.
       apply Rabs_or in Hvn.
       destruct Hvn as [Hvn| Hvn]; subst k.
        rewrite Hvn in Hvv.
        rewrite vec_const_mul_1_l in Hvv.
        now apply Hvv.

        apply Rmult_eq_compat_r with (r := y₁) in Hvn.
        unfold Rdiv in Hvn.
        rewrite Rmult_assoc in Hvn.
        rewrite Rinv_l in Hvn; [  | lra ].
        rewrite <- Ropp_mult_distr_l in Hvn.
        rewrite Rmult_1_r, Rmult_1_l in Hvn.
        subst y₂.
        destruct (Rlt_dec (- y₁) 0) as [Hly₂| Hly₂]; [ easy | lra ].

       intros H.
       apply sqrt_eq_0 in H.
        apply sqr_vec_norm_eq_0 in H; lra.

        apply nonneg_sqr_vec_norm.

      apply Rle_0_sqr.

      apply nonneg_sqr_vec_norm.

     unfold Rdiv.
     rewrite Rmult_assoc.
     rewrite Rinv_l; [  | lra ].
     now rewrite Rmult_1_r.

    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite Rinv_l; [  | lra ].
    now rewrite Rmult_1_r.

   apply Rnot_lt_le in Hly₁.
   apply Rnot_gt_le in Hgy₁.
   apply Rle_antisym in Hly₁; [ subst y₁ | easy ].
   rewrite Rmult_0_l in Hx; symmetry in Hx.
   apply Rmult_integral in Hx.
   destruct Hx as [Hx| Hx]; [ now subst z₁; apply Hv₁ | subst y₂ ].
   destruct (Rlt_dec 0 0) as [H| H]; [ lra | clear H ].
   destruct (Rgt_dec 0 0) as [H| H]; [ lra | clear H ].
   destruct (Rlt_dec z₁ 0) as [Hlz₁| Hlz₁].
    destruct (Rlt_dec z₂ 0) as [Hlz₂| Hlz₂]; [ clear Hn | ].
     simpl in Hvn.
     rewrite Rsqr_0 in Hvn.
     do 3 rewrite Rplus_0_l in Hvn.
     do 2 rewrite sqrt_Rsqr_abs in Hvn.
     apply Rabs_eq_Rabs in Hvn.
     destruct Hvn; subst z₁; [ now apply Hvv | lra ].

     destruct (Rgt_dec z₂ 0) as [Hgz₂| Hgz₂]; [ easy | ].
     apply Rnot_lt_le in Hlz₂.
     apply Rnot_gt_le in Hgz₂.
     apply Rle_antisym in Hlz₂; [ subst z₂ | easy ].
     now apply Hv₂.

    destruct (Rgt_dec z₁ 0) as [Hgz₁| Hgz₁].
     destruct (Rlt_dec z₂ 0) as [Hlz₂| Hlz₂]; [ easy | ].
     destruct (Rgt_dec z₂ 0) as [Hgz₂| Hgz₂]; [ | easy ].
     simpl in Hvn.
     rewrite Rsqr_0 in Hvn.
     do 3 rewrite Rplus_0_l in Hvn.
     do 2 rewrite sqrt_Rsqr_abs in Hvn.
     apply Rabs_eq_Rabs in Hvn.
     destruct Hvn; subst z₁; [ now apply Hvv | lra ].

     apply Rnot_lt_le in Hlz₁.
     apply Rnot_gt_le in Hgz₁.
     apply Rle_antisym in Hlz₁; [ subst z₁ | easy ].
     now apply Hv₁.
Qed.

Theorem vec_cross_mul_are_free_family : ∀ U V,
  ∥U∥ = ∥V∥
  → is_neg_point U = is_neg_point V
  → U ≠ 0%vec
  → V ≠ 0%vec
  → U ≠ V
  → ∀ a b c : ℝ,
    (a ⁎ U + b ⁎ V + c ⁎ (U × V))%vec = 0%vec
    → a = 0%R ∧ b = 0%R ∧ c = 0%R.
Proof.
intros * Hvn Hn HU HV HUV * Hab.
generalize Hab; intros H.
apply (f_equal (vec_dot_mul (U × V))) in H.
rewrite vec_dot_mul_0_r in H.
do 2 rewrite vec_dot_mul_add_distr_l in H.
do 2 rewrite <- Rmult_vec_dot_mul_distr_r in H.
rewrite vec_cross_dot_mul, Rmult_0_r, Rplus_0_l in H.
rewrite vec_cross_mul_anticomm in H.
rewrite <- vec_opp_dot_mul_distr_l in H.
rewrite vec_cross_dot_mul, Ropp_0, Rmult_0_r, Rplus_0_l in H.
rewrite <- Rmult_vec_dot_mul_distr_r in H.
rewrite <- vec_opp_dot_mul_distr_l in H.
rewrite <- vec_opp_dot_mul_distr_r in H.
rewrite Ropp_involutive in H.
rewrite vec_dot_mul_diag in H.
apply Rmult_integral in H.
destruct H as [| H]; [ subst c | ].
 rewrite vec_const_mul_0_l, vec_add_0_r in Hab.
 now apply free_family_diff_norm_vec in Hab.

 apply Rsqr_eq_0 in H.
 apply vec_norm_eq_0 in H.
 apply nonzero_cross_mul in H; try easy.
 now intros H₁; apply HUV.
Qed.

Theorem vec_dot_sqr_cros_mul : ∀ U V,
  ((U × V) · (U × V) = (U · U) * (V · V) - (U · V)²)%R.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃); simpl.
rewrite Rsqr_pow2; ring.
Qed.

Theorem vec_couple_and_cross_formula : ∀ U V X,
  (U × V · U × V) ⁎ X =
   (((X · U) * (V · V) - (X · V) * (U · V)) ⁎ U +
    ((X · V) * (U · U) - (X · U) * (U · V)) ⁎ V +
    (X · (U × V)) ⁎ (U × V))%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (x₁, x₂, x₃).
simpl; f_equal; ring.
Qed.

Theorem vec_couple_and_cross_is_base : ∀ U V X,
  (U × V · U × V) ≠ 0%R
  → ∃ a b c, X = (a ⁎ U + b ⁎ V + c ⁎ (U × V))%vec.
Proof.
intros * HUV.
remember (U × V · U × V) as r eqn:Hr.
exists (((X · U) * (V · V) - (X · V) * (U · V)) / r)%R.
exists (((X · V) * (U · U) - (X · U) * (U · V)) / r)%R.
exists ((X · (U × V)) / r)%R.
apply (vec_const_mul_eq_reg_l r); [ | easy ].
do 2 rewrite vec_const_mul_add_distr_l.
do 3 rewrite vec_const_mul_assoc.
setoid_rewrite Rmult_comm.
unfold Rdiv.
do 3 rewrite Rmult_assoc.
rewrite Rinv_l; [ | easy ].
do 3 rewrite Rmult_1_r; subst r.
apply vec_couple_and_cross_formula.
Qed.

Theorem fixpoint_unicity : ∀ M U V,
  is_rotation_matrix M
  → M ≠ mat_id
  → ∥U∥ = ∥V∥
  → is_neg_point U = is_neg_point V
  → (M * U)%vec = U
  → (M * V)%vec = V
  → U = V.
Proof.
intros * Hm Hnid Hvn Hn Hp₁ Hp₂.
destruct (eq_point_dec U (P 0 0 0)) as [Hv₁| Hv₁].
 rewrite Hv₁ in Hvn.
 unfold vec_norm in Hvn at 1.
 rewrite Rsqr_0, Rplus_0_r, Rplus_0_r in Hvn.
 rewrite sqrt_0 in Hvn.
 symmetry in Hvn.
 apply vec_norm_eq_0 in Hvn.
 now rewrite Hvn, Hv₁.

 destruct (eq_point_dec V (P 0 0 0)) as [Hv₂| Hv₂].
  rewrite Hv₂ in Hvn.
  unfold vec_norm in Hvn at 2.
  rewrite Rsqr_0, Rplus_0_r, Rplus_0_r in Hvn.
  rewrite sqrt_0 in Hvn.
  now apply vec_norm_eq_0 in Hvn.

  destruct (eq_point_dec U V) as [Hvv| Hvv]; [ easy | exfalso ].
  remember (vec_const_mul (∥U∥ / ∥(U × V)∥)%R (U × V)) as W eqn:HW.
  move W before V.
  assert (Hp₃ : (M * (U × V) = U × V)%vec).
   apply mat_vec_mul_cross_distr with (U := U) (V := V) in Hm.
   now rewrite Hp₁, Hp₂ in Hm.

   move Hp₃ before Hp₂.
   assert (HVV : ∥(U × V)∥ ≠ 0%R).
    intros H; apply vec_norm_eq_0 in H.
    apply vec_cross_mul_eq_0 in H; [ | easy | easy ].
    destruct H as (a & b & Ha & Hb & Hab).
    remember (vec_const_mul a U) as aU eqn:HaU; symmetry in HaU.
    remember (vec_const_mul b V) as bV eqn:HbV; symmetry in HbV.
    destruct aU as (ax₁, ay₁, az₁).
    destruct bV as (bx₂, by₂, bz₂).
    simpl in Hab.
    injection Hab; clear Hab; intros Hz Hy Hx.
    move Hx after Hy; move Hz after Hy.
    apply Rplus_opp_r_uniq in Hx.
    apply Rplus_opp_r_uniq in Hy.
    apply Rplus_opp_r_uniq in Hz.
    rewrite Hx, Hy, Hz in HbV.
    replace (- ax₁)%R with (-1 * ax₁)%R in HbV by lra.
    replace (- ay₁)%R with (-1 * ay₁)%R in HbV by lra.
    replace (- az₁)%R with (-1 * az₁)%R in HbV by lra.
    fold (vec_const_mul (-1) (P ax₁ ay₁ az₁)) in HbV.
    rewrite <- HaU in HbV.
    rewrite vec_const_mul_assoc in HbV.
    replace (-1 * a)%R with (-a)%R in HbV by lra.
    apply vec_const_mul_div in HbV; [ | easy ].
    rewrite HbV in Hvn.
    rewrite vec_norm_vec_const_mul in Hvn.
    replace (∥U∥) with (1 * ∥U∥)%R in Hvn at 1 by lra.
    apply Rmult_eq_reg_r in Hvn; [ | now intros H; apply Hv₁, vec_norm_eq_0 ].
    symmetry in Hvn.
    apply Rabs_or in Hvn.
    destruct Hvn as [Hvn| Hvn]; rewrite Hvn in HbV.
     now rewrite vec_const_mul_1_l in HbV; symmetry in HbV.

     destruct U as (x, y, z); simpl in HbV.
     do 3 rewrite <- Ropp_mult_distr_l in HbV.
     do 3 rewrite Rmult_1_l in HbV.
     fold (neg_point (P x y z)) in HbV.
     rewrite HbV in Hn.
     rewrite is_neg_point_neg_point in Hn; [ | easy ].
     now symmetry in Hn; apply no_fixpoint_negb in Hn.

    move HVV before Hvn.
    assert (HMX : ∀ X, (M * X)%vec = X).
     assert (HUV : U × V · U × V ≠ 0%R).
      rewrite vec_dot_mul_diag.
      intros HUV; apply HVV.
      now apply Rsqr_eq_0 in HUV.

      intros X.
      specialize (vec_couple_and_cross_is_base U V X HUV).
      intros (a & b & c & HX).
      subst X.
      do 2 rewrite mat_vec_mul_add_distr_l.
      do 3 rewrite mat_vec_mul_const_distr.
      now rewrite Hp₁, Hp₂, Hp₃.

     move HMX before Hp₃.
     pose proof HMX (P 1 0 0) as H1; simpl in H1.
     pose proof HMX (P 0 1 0) as H2; simpl in H2.
     pose proof HMX (P 0 0 1) as H3; simpl in H3.
     do 6 rewrite Rmult_0_r, Rplus_0_r in H1.
     do 6 rewrite Rmult_0_r in H2, H3.
     do 3 rewrite Rplus_0_l, Rplus_0_r in H2.
     do 4 rewrite Rplus_0_l in H3.
     do 3 rewrite Rmult_1_r in H1, H2, H3.
     injection H1; clear H1; intros H31 H21 H11.
     injection H2; clear H2; intros H32 H22 H12.
     injection H3; clear H3; intros H33 H23 H13.
     destruct M; simpl in *; subst.
     now apply Hnid.
Qed.

Theorem D_set_is_countable : ∀ r,
  ∃ f : ℕ → point, ∀ p : point,
  p ∈ D ∩ sphere r → ∃ n : ℕ, f n = p.
Proof.
intros r.
apply surj_prod_nat_surj_nat.
apply surj_bool_prod_nat_surj_prod_nat.
exists (fixpoint_of_bool_prod_nat r).
intros p (Hp & Hsr).
destruct Hp as (el₁ & p₁ & (el & Hs) & Hnl & Hr).
rewrite rotate_vec_mul in Hr.
remember (if is_neg_point p₁ then true else false) as b eqn:Hb.
remember (nat_of_path el₁) as nf eqn:Hnf.
remember (nat_of_path (rev_path el)) as no eqn:Hno.
fold (mat_of_path el₁) in Hr.
pose proof mat_of_path_is_rotation_matrix el as H.
generalize Hsr; intros Hsr₁.
eapply on_sphere_after_rotation in Hsr₁; [ clear H | apply H ].
unfold mat_of_path in Hsr₁.
rewrite <- rotate_vec_mul, Hs in Hsr₁.
apply rotate_rev_path in Hs.
remember (mat_of_path el₁) as m eqn:Hm.
remember (rotation_fixpoint m r) as p₂ eqn:Hp₂.
assert (Hrm : is_rotation_matrix m).
 rewrite Hm; apply mat_of_path_is_rotation_matrix.

 destruct (rmat_eq_dec m (mat_transp m)) as [Hmt| Hmt].
  assert (Hmm : (m * m = mat_id)%mat) by (rewrite Hmt at 2; apply Hrm).
  rewrite Hm in Hmm.
  rewrite <- mat_of_path_app in Hmm.
  exfalso; revert Hmm.
  apply matrix_of_non_empty_path_is_not_identity.
  intros H; apply Hnl.
  now apply norm_list_app_diag_is_nil.

  pose proof rotation_fixpoint_on_sphere r m Hmt as Hsr₂.
  rewrite <- Hp₂ in Hsr₂.
  move p₁ before p; move p₂ before p₁.
  move Hsr₁ before Hsr; move Hsr₂ before Hsr₁.
  exists (b, nf, no).
  unfold fixpoint_of_bool_prod_nat.
  rewrite Hno, path_of_nat_inv.
  rewrite Hnf, path_of_nat_inv.
  rewrite <- Hm, <- Hp₂.
  rewrite <- Hr in Hs.
  remember (is_neg_point p₂) as b₁.
  rename Heqb₁ into Hb₁.
  move Hb before Hb₁.
  symmetry in Hb, Hb₁.
  symmetry; rewrite <- Hs; f_equal.
  apply matrix_all_fixpoints_ok in Hp₂; [ | easy ].
  move Hp₂ at bottom; move Hr before Hp₂.
  rewrite Hr.
  remember (is_neg_point p₁) as b₂ eqn:Hb₂.
  symmetry in Hb₂.
  move Hb₂ before Hb₁.
  destruct b₁, b.
   destruct b₂; [ | easy ].
   rewrite <- Hb₁ in Hb₂.
   eapply fixpoint_unicity; try eassumption.
    intros H; rewrite Hm in H.
    now apply matrix_of_non_empty_path_is_not_identity in Hnl.

    destruct p₁ as (x₁, y₁, z₁).
    destruct p₂ as (x₂, y₂, z₂).
    simpl in Hsr₁, Hsr₂; simpl.
    now rewrite Hsr₁, Hsr₂.

   destruct b₂; [ easy | ].
   replace false with (negb true) in Hb₂ by easy.
   rewrite <- Hb₁ in Hb₂.
   eapply fixpoint_unicity; try eassumption.
    intros H; rewrite Hm in H.
    now apply matrix_of_non_empty_path_is_not_identity in Hnl.

    destruct p₁ as (x₁, y₁, z₁).
    destruct p₂ as (x₂, y₂, z₂).
    simpl in Hsr₁, Hsr₂; simpl.
    do 3 rewrite <- Rsqr_neg.
    now rewrite Hsr₁, Hsr₂.

    rewrite Hb₂.
    rewrite is_neg_point_neg_point; [ easy | ].
    intros H; subst p₂; simpl in Hb₂.
    destruct (Rlt_dec 0 0) as [H1| H1]; [ now lra | clear H1 ].
    destruct (Rgt_dec 0 0) as [H1| H1]; [ now lra | clear H1 ].
    simpl in Hsr₂.
    rewrite Rsqr_0 in Hsr₂; symmetry in Hsr₂.
    do 2 rewrite Rplus_0_l in Hsr₂.
    apply Rsqr_eq_0 in Hsr₂; subst r.
    simpl in Hsr₁; rewrite Rsqr_0 in Hsr₁.
    destruct p₁ as (x, y, z).
    apply sqr_vec_norm_eq_0 in Hsr₁.
    destruct Hsr₁ as (H1 & H2 & H3); subst x y z.
    now rewrite Hb₁ in Hb₂.

    destruct p₂ as (x, y, z).
    simpl in Hp₂; simpl.
    do 9 rewrite <- Ropp_mult_distr_r.
    do 6 rewrite <- Ropp_plus_distr.
    injection Hp₂; clear Hp₂; intros Hz Hy Hx.
    now rewrite Hx, Hy, Hz.

   destruct b₂; [ | easy ].
   replace true with (negb false) in Hb₂ by easy.
   rewrite <- Hb₁ in Hb₂.
   eapply fixpoint_unicity; try eassumption.
    intros H; rewrite Hm in H.
    now apply matrix_of_non_empty_path_is_not_identity in Hnl.

    destruct p₁ as (x₁, y₁, z₁).
    destruct p₂ as (x₂, y₂, z₂).
    simpl in Hsr₁, Hsr₂; simpl.
    do 3 rewrite <- Rsqr_neg.
    now rewrite Hsr₁, Hsr₂.

    rewrite Hb₂.
    rewrite is_neg_point_neg_point; [ easy | ].
    intros H; subst p₂; simpl in Hb₁.
    destruct (Rlt_dec 0 0) as [H1| H1]; [ now lra | clear H1 ].
    destruct (Rgt_dec 0 0) as [H1| H1]; [ now lra | easy ].

    destruct p₂ as (x, y, z).
    simpl in Hp₂; simpl.
    do 9 rewrite <- Ropp_mult_distr_r.
    do 6 rewrite <- Ropp_plus_distr.
    injection Hp₂; clear Hp₂; intros Hz Hy Hx.
    now rewrite Hx, Hy, Hz.

   destruct b₂; [ easy | ].
   rewrite <- Hb₁ in Hb₂.
   eapply fixpoint_unicity; try eassumption.
    intros H; rewrite Hm in H.
    now apply matrix_of_non_empty_path_is_not_identity in Hnl.

    destruct p₁ as (x₁, y₁, z₁).
    destruct p₂ as (x₂, y₂, z₂).
    simpl in Hsr₁, Hsr₂; simpl.
    now rewrite Hsr₁, Hsr₂.
Qed.

Definition sphere_sym S := mkset (λ p, neg_point p ∈ S).

Theorem sphere_sym_neg_point : ∀ p, p ∈ sphere_sym D → neg_point p ∈ D.
Proof.
intros (x, y, z) (el₁ & p₁ & Hso & Hn & Hr).
now exists el₁, p₁.
Qed.

Theorem neg_point_in_sphere : ∀ r p, p ∈ sphere r → neg_point p ∈ sphere r.
Proof.
intros r (x, y, z) Hp; simpl.
now do 3 rewrite <- Rsqr_neg.
Qed.

Theorem neg_point_in_ball : ∀ p, p ∈ ball → neg_point p ∈ ball.
Proof.
intros (x, y, z) Hp; simpl.
now do 3 rewrite <- Rsqr_neg.
Qed.

Theorem D_set_symmetry_is_countable : ∀ r,
  ∃ f : ℕ → point, ∀ p : point,
  p ∈ sphere_sym D ∩ sphere r → ∃ n : ℕ, f n = p.
Proof.
intros r.
specialize (D_set_is_countable r) as (f, Hf).
exists (λ n, neg_point (f n)).
intros p Hp.
enough (Hn : neg_point p ∈ D ∩ sphere r).
 specialize (Hf (neg_point p) Hn) as (n & Hf).
 exists n; rewrite Hf.
 apply neg_point_involutive.

 destruct Hp as (Hss, Hs).
 split; [ now apply sphere_sym_neg_point | ].
 now apply neg_point_in_sphere.
Qed.

Theorem countable_union : ∀ A (E F : set A),
  (∃ f : ℕ → A, ∀ a : A, a ∈ E → ∃ n, f n = a)
  → (∃ g : ℕ → A, ∀ a : A, a ∈ F → ∃ n, g n = a)
  → (∃ h : ℕ → A, ∀ a : A, a ∈ E ∪ F → ∃ n, h n = a).
Proof.
intros * (f & Hf) (g & Hg).
exists
  (λ n, if bool_dec (even n) true then f (Nat.div2 n) else g (Nat.div2 n)).
intros a [Ha| Ha].
 specialize (Hf a Ha) as (n & Hn).
 exists (2 * n)%nat.
 rewrite Nat.even_mul, orb_true_l.
 now rewrite Nat.div2_double.

 specialize (Hg a Ha) as (n & Hn).
 exists (2 * n + 1)%nat.
 rewrite Nat.even_add.
 rewrite Nat.even_mul, orb_true_l, Nat.even_1.
 remember (2 * n + 1)%nat as m; simpl; subst m.
 now rewrite Nat.add_1_r, Nat.div2_succ_double.
Qed.

Theorem D_set_and_its_symmetric_are_countable : ∀ r,
  ∃ f : ℕ → point, ∀ p : point,
  p ∈ (D ∪ sphere_sym D) ∩ sphere r → ∃ n : ℕ, f n = p.
Proof.
intros r.
enough
  (∃ f, ∀ p,
   p ∈ (D ∩ sphere r) ∪ (sphere_sym D ∩ sphere r) → ∃ n : ℕ, f n = p).
 destruct H as (f, Hf).
 exists f; intros p Hp; apply Hf.
 now rewrite intersection_union_distr_r in Hp.

 apply countable_union; [ apply D_set_is_countable | ].
 apply D_set_symmetry_is_countable.
Qed.

Definition rotation_around p :=
  mkset (λ R, is_rotation_matrix R ∧ (R * p = p)%vec).

(* We know, from theory of linear algebra, that tr(M) = 1 + 2 cos θ.
   Therefore, when θ varies from 0 to 2π, tr(M) varies between -1 and 3.
   Then (tr(M)+1)/4 varies from 0 to 1. *)
Definition ter_bin_of_rotation M :=
  ter_bin_of_frac_part ((mat_trace M + 1) / 4).

Definition matrix_of_axis_cos_sin_angle '(P x y z) c s :=
  let r := (√ (x² + y² + z²))%R in
  let ux := (x / r)%R in
  let uy := (y / r)%R in
  let uz := (z / r)%R in
  mkrmat
    (ux²*(1-c)+c) (ux*uy*(1-c)-uz*s) (ux*uz*(1-c)+uy*s)
    (ux*uy*(1-c)+uz*s) (uy²*(1-c)+c) (uy*uz*(1-c)-ux*s)
    (ux*uz*(1-c)-uy*s) (uy*uz*(1-c)+ux*s) (uz²*(1-c)+c).

Theorem z_of_xy : ∀ x y z r,
  r = (√ (x² + y² + z²)%R)
  → r ≠ 0%R
  → ((z / r) ^ 2 = 1 - (x / r) ^ 2 - (y / r) ^ 2)%R.
Proof.
intros * Hr Hrnz.
assert (H : (r ^ 2 ≠ 0 ∧ r ^ 2 - x ^ 2 - y ^ 2 = z ^ 2)%R).
 split.
  rewrite <- Rsqr_pow2.
  intros H; apply Hrnz.
  now apply Rsqr_eq_0 in H.

  rewrite Hr, <- Rsqr_pow2.
  rewrite Rsqr_sqrt; [ do 3 rewrite Rsqr_pow2; ring | ].
  apply nonneg_sqr_vec_norm.

 destruct H as (Hr2nz & Hrxyz).
 remember (x / r)%R as xr eqn:Hxr.
 remember (y / r)%R as yr eqn:Hyr.
 remember (z / r)%R as zr eqn:Hzr.
 subst xr yr zr.
 unfold Rdiv.
 do 3 rewrite Rpow_mult_distr.
 rewrite <- Hrxyz; ring_simplify.
 rewrite <- Rinv_pow; [ | easy ].
 rewrite Rinv_r; [ ring | easy ].
Qed.

Theorem matrix_of_axis_angle_is_rotation_matrix : ∀ p cosθ sinθ,
  p ≠ 0%vec
  → (sinθ² + cosθ² = 1)%R
  → is_rotation_matrix (matrix_of_axis_cos_sin_angle p cosθ sinθ).
Proof.
intros * Hp Hsc.
rename Hsc into Hsc1.
assert (Hsc : (sinθ² = 1 - cosθ²)%R) by lra; clear Hsc1.
destruct p as (xp, yp, zp).
remember ((√ (xp² + yp² + zp²))%R) as r eqn:Hr.
assert (Hrnz : (r ≠ 0)%R).
 intros H; rewrite Hr in H.
 apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in H.
 destruct H as (Hx & Hy & Hz); subst xp yp zp.
 now apply Hp.

 remember (xp / r)%R as x eqn:Hx.
 remember (yp / r)%R as y eqn:Hy.
 remember (zp / r)%R as z eqn:Hz.
 assert (Hrxyz2 : (1 - x ^ 2 - y ^ 2 = z ^ 2)%R).
  subst x y z.
  now symmetry; apply z_of_xy.

  unfold matrix_of_axis_cos_sin_angle.
  rewrite <- Hr, <- Hx, <- Hy, <- Hz.
  split.
   unfold mat_transp, mat_mul, mat_id; simpl.
   f_equal;
    ring_simplify;
    do 2 rewrite Rsqr_pow2 in Hsc; rewrite Hsc;
    repeat rewrite Rsqr_pow2;
    rewrite <- Hrxyz2; ring.

  unfold mat_det; simpl.
  ring_simplify.
  do 2 rewrite Rsqr_pow2 in Hsc; rewrite Hsc.
  repeat rewrite Rsqr_pow2.
  rewrite <- Hrxyz2; ring.
Qed.

Theorem axis_of_matrix_is_eigen_vec : ∀ p cosθ sinθ,
  (sinθ² + cosθ² = 1)%R
  → (matrix_of_axis_cos_sin_angle p cosθ sinθ * p)%vec = p.
Proof.
intros (xp, yp, zp) * Hsc.
remember ((√ (xp² + yp² + zp²))%R) as r eqn:Hr.
destruct (Req_dec r 0) as [Hrz| Hrnz].
 rewrite Hr in Hrz.
 apply sqrt_eq_0 in Hrz; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in Hrz.
 destruct Hrz as (Hx & Hy & Hz); subst xp yp zp.
 now rewrite mat_vec_mul_0_r.

 unfold matrix_of_axis_cos_sin_angle; simpl.
 rewrite <- Hr.
 specialize (z_of_xy xp yp zp r Hr Hrnz) as Hz.
 f_equal; ring_simplify.
  replace (yp / r * sinθ * zp)%R with (zp / r * sinθ * yp)%R by lra.
  replace (xp / r * (zp / r) * zp)%R with (xp * (zp / r) ^ 2)%R by lra.
  replace (cosθ * (xp / r) * (zp / r) * zp)%R
  with (cosθ * xp * (zp / r) ^ 2)%R by lra.
  rewrite Rsqr_pow2, Hz; lra.

  replace (xp / r * sinθ * zp)%R with (zp / r * sinθ * xp)%R by lra.
  replace (yp / r * cosθ * (zp / r) * zp)%R with (yp * cosθ * (zp / r) ^ 2)%R
    by lra.
  replace (yp / r * (zp / r) * zp)%R with (yp * (zp / r) ^ 2)%R by lra.
  rewrite Rsqr_pow2, Hz; lra.

  rewrite Rsqr_pow2, Hz; lra.
Qed.

Theorem ter_bin_of_rotation_surj : ∀ p, p ≠ 0%vec → ∀ (u : ℕ → bool),
  ∃ M, M ∈ rotation_around p ∧ (∀ n : ℕ, ter_bin_of_rotation M n = u n).
Proof.
intros * Hp *.
specialize (ter_bin_of_frac_part_surj u); intros (s & Hs & Hn).
remember (2 * s - 1)%R as cosθ eqn:Hcosθ.
remember (√ (1 - cosθ²))%R as sinθ eqn:Hsinθ.
assert(Hsc : (sinθ² = (1 - cosθ²))%R).
 rewrite Hsinθ, Rsqr_sqrt; [ easy | ].
 rewrite Hcosθ, Rsqr_pow2.
 eapply Rplus_le_reg_r; unfold Rminus.
 rewrite Rplus_assoc, Rplus_opp_l.
 rewrite Rplus_0_l, Rplus_0_r.
 replace 1%R with (1 ^ 2)%R at 4 by lra.
 apply pow_maj_Rabs, Rabs_le; lra.

 exists (matrix_of_axis_cos_sin_angle p cosθ sinθ).
 split.
  split.
   apply matrix_of_axis_angle_is_rotation_matrix; [ easy | lra ].

   apply axis_of_matrix_is_eigen_vec; lra.

  intros n.
  destruct p as (x, y, z); simpl.
  unfold ter_bin_of_rotation.
  unfold mat_trace; simpl.
  remember (√ (x² + y² + z²))%R as r eqn:Hr.
  rewrite <- Hn.
  f_equal.
  apply Rmult_eq_reg_r with (r := 4%R); [ | lra ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l; [ | lra ].
  rewrite Rmult_1_r.
  do 3 rewrite fold_Rdiv.
  rename cosθ into c.
  do 2 rewrite <- Rplus_assoc.
  remember ((x / r)² * (1 - c))%R as xc.
  remember ((y / r)² * (1 - c))%R as yc.
  remember ((z / r)² * (1 - c))%R as zc.
  replace (xc + c + yc + c + zc + c)%R with (xc + yc + zc + 3 * c)%R by ring.
  subst xc yc zc.
  do 2 rewrite <- Rmult_plus_distr_r.
  replace ((x / r)² + (y / r)² + (z / r)²)%R with 1%R.
   ring_simplify; subst c; lra.

   assert (Hrnz : (r ≠ 0)%R).
    intros H; rewrite Hr in H.
    apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
    apply sqr_vec_norm_eq_0 in H.
    destruct H as (Hx & Hy & Hz); subst x y z.
    now apply Hp.

    symmetry.
    rewrite Rsqr_div; [ | easy ].
    rewrite Rsqr_div; [ | easy ].
    rewrite Rsqr_div; [ | easy ].
    unfold Rdiv.
    do 2 rewrite <- Rmult_plus_distr_r.
    rewrite Hr.
    rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
    rewrite Rinv_r; [ easy | ].
    intros H; rewrite H in Hr.
    now rewrite sqrt_0 in Hr.
Qed.

Theorem rotation_around_not_countable : ∀ p, p ≠ 0%vec →
  ∀ f : ℕ → _, ∃ M, M ∈ rotation_around p ∧ ∀ n, f n ≠ M.
Proof.
intros * Hp f.
specialize
 (Cantor_gen ℕ ℕ (matrix ℝ) (setp (rotation_around p)) id
    ter_bin_of_rotation id_nat
    (ter_bin_of_rotation_surj p Hp) f) as (M, HM).
exists M.
split; [ apply (HM O) | ].
intros n.
apply not_eq_sym, HM.
Qed.

(* J = set of rotations mapping a point of D to some point of D. *)
Definition J p₁ :=
  mkset
    (λ R₁, R₁ ∈ rotation_around p₁ ∧
     ∃ p p' n, p ∈ D ∧ p' ∈ D ∧ ((R₁ ^ n)%mat * p)%vec = p').

Definition J_of_nats (p₁ : point) '(nf, no, nf', no'(*, n*)) : matrix ℝ :=
  let r := ∥p₁∥ in
  let p₂ := fixpoint_of_nat r nf in
  let p := fold_right rotate p₂ (path_of_nat no) in
  let p₃ := fixpoint_of_nat r nf' in
  let p' := fold_right rotate p₃ (path_of_nat no') in
  let cosθ := ((p · p') / r)%R in
  let sinθ := √ (1 - cosθ²) in
  let px := p × p' in
  if eq_point_dec p p' then mat_id
  else if eq_point_dec p₁ px then
    matrix_of_axis_cos_sin_angle px cosθ sinθ
  else if eq_point_dec p₁ (neg_point px) then
    matrix_of_axis_cos_sin_angle px cosθ (- sinθ)
  else mat_id.

Theorem J_is_countable : ∀ p₁,
  ∃ f : ℕ → matrix ℝ, ∀ M : matrix ℝ,
  M ∈ J p₁ → ∃ n : ℕ, f n = M.
Proof.
intros.
apply surj_prod_4_nat_surj_nat.
exists (J_of_nats p₁).
intros M HM.
destruct HM as (Hrm & p & p' & n & Hp & Hp' & HM).
destruct Hp as (el & p₂ & Hso₂ & Hn₂ & Hr₂).
destruct Hp' as (el' & p₃ & Hso₃ & Hn₃& Hr₃).
destruct Hso₂ as (el₂ & Hso₂).
destruct Hso₃ as (el₃ & Hso₃).
apply rotate_rev_path in Hso₂.
apply rotate_rev_path in Hso₃.
remember (nat_of_path el) as nf eqn:Hnf.
remember (nat_of_path (rev_path el₂)) as no eqn:Hno.
remember (nat_of_path el') as nf' eqn:Hnf'.
remember (nat_of_path (rev_path el₃)) as no' eqn:Hno'.
exists (nf, no, nf', no'); simpl.
remember ∥p₁∥ as r eqn:Hr.
remember (fixpoint_of_nat r nf) as q₂ eqn:Hq₂.
remember (fold_right rotate q₂ (path_of_nat no)) as q eqn:Hq.
remember (fixpoint_of_nat r nf') as q₃ eqn:Hq₃.
remember (fold_right rotate q₃ (path_of_nat no')) as q' eqn:Hq'.
symmetry.
subst nf no nf' no'.
unfold fixpoint_of_nat, fixpoint_of_path in Hq₂, Hq₃.
rewrite path_of_nat_inv in Hq₂, Hq₃, Hq, Hq'.
generalize Hq₂; intros Hs₂.
apply matrix_all_fixpoints_ok in Hs₂.
 2: apply mat_of_path_is_rotation_matrix.
 unfold mat_of_path in Hs₂.
 rewrite <- rotate_vec_mul in Hs₂.

 generalize Hq₃; intros Hs₃.
 apply matrix_all_fixpoints_ok in Hs₃.
  2: apply mat_of_path_is_rotation_matrix.
  unfold mat_of_path in Hs₃.
  rewrite <- rotate_vec_mul in Hs₃.
  move Hn₂ at bottom.
  move Hr₂ at bottom.
  move Hs₂ at bottom.
  move Hr₃ at bottom.
  move Hs₃ at bottom.

Theorem glop : ∀ p₁ p₂ el,
  ∥p₁∥ = ∥p₂∥
  → norm_list el ≠ []
  → fold_right rotate p₁ el = p₁
  → fold_right rotate p₂ el = p₂
  → p₁ = p₂ ∨ p₁ = (- p₂)%vec.
Proof.
intros * Hpp Hn Hr₁ Hr₂.
rewrite rotate_vec_mul in Hr₁, Hr₂.
fold (mat_of_path el) in Hr₁, Hr₂.
remember (mat_of_path el) as M eqn:HM.
assert (H : is_rotation_matrix M ∧ M ≠ mat_id).
 split; [ subst M; apply mat_of_path_is_rotation_matrix | ].
 now rewrite HM; apply matrix_of_non_empty_path_is_not_identity.

 destruct H as (Hrm & Hni).
 destruct (Bool.bool_dec (is_neg_point p₁) (is_neg_point p₂)) as [Hnn| Hnn].
  destruct (eq_point_dec p₁ p₂) as [| Hneq ]; [ now left | exfalso ].

   now specialize (fixpoint_unicity M p₁ p₂ Hrm Hni Hpp Hnn Hr₁ Hr₂).

  destruct (eq_point_dec p₁ (- p₂)%vec) as [| Hneq ]; [ now right | exfalso ].
  specialize (fixpoint_unicity M p₁ (- p₂)%vec Hrm Hni).

bbb.

revert p₁ p₂ Hpp Hn Hr₁ Hr₂.
induction el as [| e₁ el]; intros; [ easy | ].
simpl in Hr₁, Hr₂.
destruct e₁ as (t, d); destruct t, d.

bbb.

destruct (eq_point_dec q q') as [Heqq| Hneqq].
 subst nf no nf' no'.
 unfold fixpoint_of_nat, fixpoint_of_path in Hq₂, Hq₃.
 rewrite path_of_nat_inv in Hq₂, Hq₃, Hq, Hq'.
 rewrite Hq, Hq' in Heqq.
 rewrite Hq₂, Hq₃ in Heqq.
SearchAbout (rotation_fixpoint (mat_of_path _)).
Check matrix_all_fixpoints_ok.

Print J.

bbb.
assert (p₂ = q₂).
 subst nf no nf' no'.
 unfold fixpoint_of_nat, fixpoint_of_path in Hq₂.
 rewrite path_of_nat_inv in Hq₂, Hq, Hq'.
 generalize Hq₂; intros H.
 apply matrix_all_fixpoints_ok in H.
  2: apply mat_of_path_is_rotation_matrix.
  unfold mat_of_path in H.
  rewrite <- rotate_vec_mul in H.
  move Hn₂ at bottom.
  move Hr₂ at bottom.
  move H at bottom.
bbb.

unfold rotation_fixpoint in Hq₂.
unfold mat_of_path in Hq₂.
Print rotation_unit_eigenvec.
rewrite <- rotate_vec_mul in Hq₂.
bbb.

SearchAbout rotation_fixpoint.
 apply D_of_nat_prop with
   (nf := nf) (no := no) (el := rev_path el₂) (n := nat_of_prod_nat (nf, no))
   (p := q) in Hq₂.
  subst nf no nf' no'.
  rewrite path_of_nat_inv in Hq₂, Hq, Hq'.
  destruct Hq₂ as (Hsoq₂ & Hrq₂).
  move Hn₂ at bottom.
  move Hr₂ at bottom.
  move Hrq₂ at bottom.
Print rotation_fixpoint.
SearchAbout (fold_right rotate).
bbb.
  clear - Hn₂ Hr₂ Hrq₂.
bbb.

subst nf no nf' no'.
unfold fixpoint_of_nat in Hq₂, Hq₃.
rewrite path_of_nat_inv in Hq₂, Hq, Hq₃, Hq'.
unfold fixpoint_of_path in Hq₂.
bbb.

Theorem equidec_ball_with_and_without_fixpoints :
  equidecomposable ball ball_but_fixpoints.
Proof.
intros.
assert (H : ∃ p₁, p₁ ∈ ball ∖ D ∧ neg_point p₁ ∈ ball ∖ D).
 unfold "∈", "∖".
 specialize (D_set_and_its_symmetric_are_countable 1) as (f, Hdnc).
 specialize (ball_set_not_countable 1 Rlt_0_1 f) as (p & Hps & Hp).
 exists p.
 split.
  split.
   apply in_sphere_in_ball in Hps; [ easy | ].
   split; [ apply Rle_0_1 | apply Rle_refl ].

   intros HD.
   assert (H : p ∈ (D ∪ sphere_sym D) ∩ sphere 1).
    now rewrite intersection_union_distr_r; left.

    specialize (Hdnc p H) as (n, Hdnc).
    revert Hdnc; apply Hp.

  split.
   apply neg_point_in_ball.
   apply in_sphere_in_ball in Hps; [ easy | ].
   split; [ apply Rle_0_1 | apply Rle_refl ].

   intros HD.
   assert (H : p ∈ (D ∪ sphere_sym D) ∩ sphere 1).
    now rewrite intersection_union_distr_r; right.

    specialize (Hdnc p H) as (n, Hdnc).
    revert Hdnc; apply Hp.

 destruct H as (p₁ & (Hpb & Hpnd) & (Hqb & Hqnd)).
 assert
   (H : ∃ R₁, R₁ ∈ rotation_around p₁
    ∧ ∀ n p p', p ∈ D → p' ∈ D
    → ((R₁ ^ n)%mat * p ≠ p')%vec).
  assert (Hp₁nz : p₁ ≠ 0%vec).
   intros H; apply Hpnd; subst p₁; simpl.
   exists (ạ :: []), 0%vec.
   split; [ apply same_orbit_refl | ].
   split; [ easy | simpl; f_equal; lra ].

   specialize (J_is_countable p₁) as (f, Hdnc).
   specialize (rotation_around_not_countable p₁ Hp₁nz f) as (R₁ & HR₁ & Hn).
   exists R₁.
   split; [ easy | ].
   intros * Hp Hp' HRnp.
   assert (H : R₁ ∈ J p₁).
    split; [ easy | ].
    now exists n, p, p'.

    specialize (Hdnc R₁ H) as (m, Hdnc).
    revert Hdnc; apply Hn.

  destruct H as (R₁ & HR₁ & HR₁nkeep).
bbb.

Theorem Banach_Tarski_paradox :
  equidecomposable ball (xtransl 3 ball ∪ xtransl 6 ball)%S.
Proof.
transitivity ball_but_fixpoints.
 apply equidec_ball_with_and_without_fixpoints.

 etransitivity.
  apply Banach_Tarski_paradox_but_fixpoints.

  apply equidec_union.
   apply separated_balls_without_fixpoints.

   apply separated_balls.

   apply equidec_transl; symmetry.
   apply equidec_ball_with_and_without_fixpoints.

   apply equidec_transl; symmetry.
   apply equidec_ball_with_and_without_fixpoints.
Qed.

Check Banach_Tarski_paradox.
