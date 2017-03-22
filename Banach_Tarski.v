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

Notation "r ³" := (Rpow_def.pow r 3) (at level 1, format "r ³") : R_scope.
Notation "r ⁴" := (Rpow_def.pow r 4) (at level 1, format "r ⁴") : R_scope.

Theorem Rno_intersect_balls_x3_x6 : ∀ x y z,
  (x - 3)² + y² + z² <= 1
  → (x - 6)² + y² + z² <= 1
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

Definition rot_elem e := Rot (mat_of_elem e) (rotate_is_rotation_matrix e).

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
  constructor.
   now exists (Comb (Xtransl 3) (rot_elem ạ)); rewrite rot_set_map_mul.

   constructor; [ now exists (Xtransl 6) | ].
   constructor; [ | constructor ].
   now exists (Comb (Xtransl 6) (rot_elem ḅ)); rewrite rot_set_map_mul.
Qed.

Check Banach_Tarski_paradox_but_fixpoints.

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
  (m < n)%nat
  → (m < p)%nat
  → path_of_nat_aux n m = path_of_nat_aux p m.
Proof.
intros * Hmn Hmp.
revert m p Hmn Hmp.
induction n; intros; [ easy | ].
destruct p; [ easy | ].
simpl; f_equal.
remember (m / 4)%nat as q eqn:Hq; symmetry in Hq.
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
 assert (H : (S m < S m / 4)%nat) by (eapply Nat.lt_le_trans; eassumption).
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
 assert (H : (m < S m / 4)%nat).
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
  ∃ m n : ℕ, (n < m)%nat ∧ path_of_nat_aux m n = e :: path_of_nat_aux p q.
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

Definition unit_interv := mkset (λ x, 0 <= x < 1).

Definition ter_bin_of_vec r '(V x y z) := ter_bin_of_frac_part (x / r).

Theorem ter_bin_of_ball_surj : ∀ r, 0 < r → ∀ (u : ℕ → bool),
  ∃ p : vector, p ∈ sphere r ∧ (∀ n, ter_bin_of_vec r p n = u n).
Proof.
intros * Hr *.
specialize (ter_bin_of_frac_part_surj u); intros (s & Hs & Hn).
exists (V (s * r) (r * √ (1 - s²)) 0); simpl.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_r; [ | lra ].
rewrite Rmult_1_r.
split; [ | easy ].
do 2 rewrite Rsqr_mult.
rewrite Rsqr_sqrt; [ do 3 rewrite Rsqr_pow2; lra | ].
rewrite Rsqr_pow2.
apply Rplus_le_reg_r with (r := s ^ 2).
unfold Rminus; rewrite Rplus_assoc, Rplus_opp_l.
rewrite Rplus_0_l, Rplus_0_r.
replace 1 with (1 ^ 2) by lra.
apply pow_incr; lra.
Qed.

Theorem on_sphere_in_ball : ∀ r p, 0 ≤ r ≤ 1 →
  p ∈ sphere r
  → p ∈ ball.
Proof.
intros r (x, y, z) Hr Hs; simpl in Hs; simpl; rewrite Hs.
replace 1 with 1² by apply Rsqr_1.
apply Rsqr_incr_1; [ easy | easy | lra ].
Qed.

Theorem ball_not_countable : ¬ (is_countable {p : vector | p ∈ ball}).
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
  (Cantor_gen ℕ ℕ vector (setp (sphere 1)) id (ter_bin_of_vec 1) id_nat
     (ter_bin_of_ball_surj 1 Rlt_0_1)).
 intros H.
 specialize (H (λ n, proj1_sig (f n))) as (p, H).
 exists p.
 split.
  specialize (H O) as (Hs, _).
  apply on_sphere_in_ball with (r := 1); [ | easy ].
  split; [ apply Rle_0_1 | apply Rle_refl ].

  intros n Hn.
  specialize (H n).
  destruct H.
  now symmetry in Hn.
Qed.

Theorem ball_set_not_countable : ∀ r, 0 < r →
  ∀ f : ℕ → vector, ∃ p : vector, p ∈ sphere r ∧ ∀ n : ℕ, f n ≠ p.
Proof.
intros * Hr *.
specialize
 (Cantor_gen ℕ ℕ vector (setp (sphere r)) id (ter_bin_of_vec r) id_nat
    (ter_bin_of_ball_surj r Hr) f) as (p, Hp).
exists p.
split; [ apply (Hp O) | ].
intros n.
apply not_eq_sym, Hp.
Qed.

Definition and_dec {A B C D} P Q := Sumbool.sumbool_and A B C D P Q.

Definition fixpoint_of_path r el :=
  rotation_fixpoint (mat_of_path el) r.

Definition fixpoint_of_nat r n :=
  fixpoint_of_path r (path_of_nat n).

Theorem ortho_matrix_sqr_coeff_le_1 : ∀ M,
  (M * mat_transp M)%mat = mat_id
  → ((a₁₁ M)² ≤ 1 ∧ (a₁₂ M)² ≤ 1 ∧ (a₁₃ M)² ≤ 1) ∧
     ((a₂₁ M)² ≤ 1 ∧ (a₂₂ M)² ≤ 1 ∧ (a₂₃ M)² ≤ 1) ∧
     ((a₃₁ M)² ≤ 1 ∧ (a₃₂ M)² ≤ 1 ∧ (a₃₃ M)² ≤ 1).
Proof.
intros * Hrm.
injection Hrm; clear Hrm.
destruct M; simpl.
intros H33 H32 H31 H23 H22 H21 H13 H12 H11.
ring_simplify in H11; ring_simplify in H12; ring_simplify in H13.
ring_simplify in H21; ring_simplify in H22; ring_simplify in H23.
ring_simplify in H31; ring_simplify in H32; ring_simplify in H33.
clear H21 H31 H32.
do 3 rewrite <- Rsqr_pow2 in H11, H22, H33.
split; [ | split ].
 rewrite <- H11.
 split; [ | split ].
  rewrite Rplus_assoc.
  replace a₁₁² with (a₁₁² + 0) at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_shuffle0, Rplus_comm.
  replace a₁₂² with (a₁₂² + 0) at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_comm.
  replace a₁₃² with (a₁₃² + 0) at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

 rewrite <- H22.
 split; [ | split ].
  rewrite Rplus_assoc.
  replace a₂₁² with (a₂₁² + 0) at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_shuffle0, Rplus_comm.
  replace a₂₂² with (a₂₂² + 0) at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_comm.
  replace a₂₃² with (a₂₃² + 0) at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

 rewrite <- H33.
 split; [ | split ].
  rewrite Rplus_assoc.
  replace a₃₁² with (a₃₁² + 0) at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_shuffle0, Rplus_comm.
  replace a₃₂² with (a₃₂² + 0) at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_comm.
  replace a₃₃² with (a₃₃² + 0) at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.
Qed.

Theorem Rsqr_le_1_interv : ∀ x, x² ≤ 1 → -1 ≤ x ≤ 1.
Proof.
intros * Hx.
replace 1 with (1 ^ 2) in Hx by lra.
rewrite <- Rsqr_pow2 in Hx.
split; [ apply Rsqr_neg_pos_le_0; lra | ].
apply Rsqr_incr_0_var; lra.
Qed.

Theorem ortho_matrix_coeff_interv : ∀ M,
  (M * mat_transp M)%mat = mat_id
  → (-1 ≤ a₁₁ M ≤ 1 ∧ -1 ≤ a₁₂ M ≤ 1 ∧ -1 ≤ a₁₃ M ≤ 1) ∧
     (-1 ≤ a₂₁ M ≤ 1 ∧ -1 ≤ a₂₂ M ≤ 1 ∧ -1 ≤ a₂₃ M ≤ 1) ∧
     (-1 ≤ a₃₁ M ≤ 1 ∧ -1 ≤ a₃₂ M ≤ 1 ∧ -1 ≤ a₃₃ M ≤ 1).
Proof.
intros * Hrm.
specialize (ortho_matrix_sqr_coeff_le_1 _ Hrm) as Ha.
destruct Ha as (Ha₁ & Ha₂ & Ha₃).
destruct Ha₁ as (Ha₁₁ & Ha₁₂ & Ha₁₃).
destruct Ha₂ as (Ha₂₁ & Ha₂₂ & Ha₂₃).
destruct Ha₃ as (Ha₃₁ & Ha₃₂ & Ha₃₃).
apply Rsqr_le_1_interv in Ha₁₁.
apply Rsqr_le_1_interv in Ha₁₂.
apply Rsqr_le_1_interv in Ha₁₃.
apply Rsqr_le_1_interv in Ha₂₁.
apply Rsqr_le_1_interv in Ha₂₂.
apply Rsqr_le_1_interv in Ha₂₃.
apply Rsqr_le_1_interv in Ha₃₁.
apply Rsqr_le_1_interv in Ha₃₂.
apply Rsqr_le_1_interv in Ha₃₃.
easy.
Qed.

Theorem mat_trace_large_interv : ∀ M,
  is_rotation_matrix M
  → -3 ≤ mat_trace M ≤ 3.
Proof.
intros * (Hrm & Hdet).
specialize (ortho_matrix_coeff_interv _ Hrm) as Ha.
destruct Ha as (Ha₁ & Ha₂ & Ha₃).
destruct Ha₁ as (Ha₁₁ & Ha₁₂ & Ha₁₃).
destruct Ha₂ as (Ha₂₁ & Ha₂₂ & Ha₂₃).
destruct Ha₃ as (Ha₃₁ & Ha₃₂ & Ha₃₃).
unfold mat_trace.
split; lra.
Qed.

(* We know, from theory of linear algebra, that tr(M) = 1 + 2 cos θ.
   Therefore, when θ varies from 0 to 2π, tr(M) varies between -1 and 3.
   Then (tr(M)+1)/4 varies from 0 to 1. *)
Definition ter_bin_of_rotation M :=
  ter_bin_of_frac_part ((mat_trace M + 1) / 4).

Theorem mat_pow_0 : ∀ M, (M ^ 0)%mat = mat_id.
Proof. intros; easy. Qed.

Theorem mat_sin_cos_0 : ∀ p, matrix_of_axis_angle (p, 0, 1) = mat_id.
Proof.
intros (x, y, z); simpl.
rewrite Rminus_diag_eq; [ | easy ].
progress repeat rewrite Rmult_0_r.
unfold mat_id, mkrmat.
f_equal; lra.
Qed.

Theorem mat_of_axis_angle_trace_interv : ∀ a s c,
  a ≠ 0%vec
  → s² + c² = 1
  → -1 ≤ mat_trace (matrix_of_axis_angle (a, s, c)) ≤ 3.
Proof.
intros * Ha Hsc.
rewrite mat_trace_eq; [ | easy ].
assert (Hc : c² ≤ 1).
 rewrite <- Hsc.
 apply Rplus_le_reg_r with (r := - c²).
 rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
 apply Rle_0_sqr.

 split.
  enough (-1 ≤ c) by lra.
  replace 1 with 1² in Hc by apply Rsqr_1.
  apply Rsqr_neg_pos_le_0 in Hc; [ easy | lra ].

  enough (c ≤ 1) by lra.
  replace 1 with 1² in Hc by apply Rsqr_1.
  apply Rsqr_incr_0_var in Hc; [ easy | lra ].
Qed.

Theorem z_of_xy : ∀ x y z r,
  r = √ (x² + y² + z²)
  → r ≠ 0
  → (z / r) ^ 2 = 1 - (x / r) ^ 2 - (y / r) ^ 2.
Proof.
intros * Hr Hrnz.
assert (H : r ^ 2 ≠ 0 ∧ r ^ 2 - x ^ 2 - y ^ 2 = z ^ 2).
 split.
  rewrite <- Rsqr_pow2.
  intros H; apply Hrnz.
  now apply Rsqr_eq_0 in H.

  rewrite Hr, <- Rsqr_pow2.
  rewrite Rsqr_sqrt; [ do 3 rewrite Rsqr_pow2; ring | ].
  apply nonneg_sqr_vec_norm.

 destruct H as (Hr2nz & Hrxyz).
 remember (x / r) as xr eqn:Hxr.
 remember (y / r) as yr eqn:Hyr.
 remember (z / r) as zr eqn:Hzr.
 subst xr yr zr.
 unfold Rdiv.
 do 3 rewrite Rpow_mult_distr.
 rewrite <- Hrxyz; ring_simplify.
 rewrite <- Rinv_pow; [ | easy ].
 rewrite Rinv_r; [ ring | easy ].
Qed.

Theorem matrix_of_axis_angle_is_rotation_matrix : ∀ p cosθ sinθ,
  p ≠ 0%vec
  → sinθ² + cosθ² = 1
  → is_rotation_matrix (matrix_of_axis_angle (p, sinθ, cosθ)).
Proof.
intros * Hp Hsc.
rename Hsc into Hsc1.
assert (Hsc : sinθ² = 1 - cosθ²) by lra; clear Hsc1.
destruct p as (xp, yp, zp).
remember (√ (xp² + yp² + zp²)) as r eqn:Hr.
assert (Hrnz : r ≠ 0).
 intros H; rewrite Hr in H.
 apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in H.
 destruct H as (Hx & Hy & Hz); subst xp yp zp.
 now apply Hp.

 remember (xp / r) as x eqn:Hx.
 remember (yp / r) as y eqn:Hy.
 remember (zp / r) as z eqn:Hz.
 assert (Hrxyz2 : 1 - x ^ 2 - y ^ 2 = z ^ 2).
  subst x y z.
  now symmetry; apply z_of_xy.

  unfold matrix_of_axis_angle.
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

(* complicated... perhaps it works with patience...
   I hope I don't need it...
Theorem rotation_matrix_has_axis_angle : ∀ M,
  is_rotation_matrix M
  → M ≠ mat_transp M
  → ∃ a s c, M = matrix_of_axis_angle (a, s, c) ∧ s² + c² = 1.
Proof.
intros * (Htr, Hdet) Hmt.
remember (axis_angle_of_matrix M) as asc eqn:Hasc.
symmetry in Hasc.
destruct asc as ((a, s), c).
exists a, s, c.
unfold axis_angle_of_matrix in Hasc.
(* Hmm... not sure that sin is correct: what about its sign? *)
injection Hasc; clear Hasc; intros Hc Hs Ha.
rewrite Hc in Hs.
split.
 rewrite <- Hs; simpl.
 destruct a as (x, y, z).
 remember (√ (x² + y² + z²)) as r eqn:Hr.
 unfold rotation_unit_axis in Ha.
 simpl in Ha.
 remember (√ ((a₃₂ M - a₂₃ M)² + (a₁₃ M - a₃₁ M)² + (a₂₁ M - a₁₂ M)²)) as r'
   eqn:Hr'.
 injection Ha; clear Ha; intros Hz Hy Hx.
 rewrite <- Hx, <- Hy, <- Hz in Hr.
 do 3 rewrite Rsqr_mult in Hr.
 do 2 rewrite <- Rmult_plus_distr_l in Hr.
 rewrite sqrt_mult in Hr.
 rewrite <- Hr' in Hr.
 rewrite sqrt_Rsqr in Hr.
 rewrite Rinv_l in Hr.
 subst r.
 do 3 rewrite Rdiv_1_r.
 rename r' into r.
 unfold mat_transp, mat_mul, mat_id, mkrmat in Htr.
 unfold mat_det in Hdet.
 unfold mat_transp, mkrmat in Hmt.
 unfold mat_trace in Hc.
 unfold mkrmat.
 destruct M; simpl in *.
 f_equal.
  injection Htr; clear Htr; intros H33 H32 H31 H23 H22 H21 H13 H12 H11.
  rewrite <- Hx.
  rewrite Rsqr_mult.
  apply Rmult_eq_reg_l with (r := r²).
  rewrite Rmult_plus_distr_l.
  do 2 rewrite <- Rmult_assoc.
  rewrite Rsqr_inv.
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  rewrite Hr'.
  rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
  assert (Hc' : a₁₁ + a₂₂ + a₃₃ - 1 = 2 * c) by lra.
  clear - Hdet Hc' H11 H12 H13 H22 H23 H33.
bbb.
(* very long, but works *)
  Time nsatz.
(*
Finished transaction in 145.255 secs (145.267u,0.004s) (successful)
*)
bbb.

Theorem mat_trace_interv : ∀ M,
  is_rotation_matrix M
  → -1 ≤ mat_trace M ≤ 3.
Proof.
intros * Hrm.

bbb.

intros * (Hrm & Hdet).
specialize (ortho_matrix_coeff_interv _ Hrm) as Ha.
destruct Ha as (Ha₁ & Ha₂ & Ha₃).
destruct Ha₁ as (Ha₁₁ & Ha₁₂ & Ha₁₃).
destruct Ha₂ as (Ha₂₁ & Ha₂₂ & Ha₂₃).
destruct Ha₃ as (Ha₃₁ & Ha₃₂ & Ha₃₃).
unfold mat_trace.
split; [ | lra ].
bbb.

unfold mat_det in Hdet.
destruct M; simpl in *.
unfold mat_mul, mat_transp, mat_id, mkrmat in Hrm; simpl in Hrm.
injection Hrm; clear Hrm.
intros H33 H32 H31 H23 H22 H21 H13 H12 H11.
ring_simplify in H11; ring_simplify in H12; ring_simplify in H13.
ring_simplify in H21; ring_simplify in H22; ring_simplify in H23.
ring_simplify in H31; ring_simplify in H32; ring_simplify in H33.
clear H21 H31 H32.
progress repeat rewrite <- Rsqr_pow2 in *.
rewrite Rplus_assoc in Hdet.
remember (a₁₂ * (a₂₃ * a₃₁ - a₃₃ * a₂₁)) as u eqn:Hu.
remember (a₁₃ * (a₂₁ * a₃₂ - a₃₁ * a₂₂)) as v eqn:Hv.
remember (u + v) as w eqn:Hw; subst u v.
apply Rplus_eq_compat_r with (r := - w) in Hdet.
rewrite Rplus_assoc, fold_Rminus in Hdet.
replace (w - w) with 0 in Hdet by lra.
rewrite Rplus_0_r, fold_Rminus in Hdet.
destruct (Req_dec w 1) as [Hw1| Hw1].
 move Hw1 at top; subst w.
 replace (1 - 1) with 0 in Hdet by lra.
 symmetry in Hw.
 apply Rmult_integral in Hdet.
 destruct Hdet as [Hdet| Hdet].
  subst a₁₁; clear Ha₁₁.
  rewrite Rsqr_0, Rplus_0_l in H11.
  rewrite Rmult_0_l, Rplus_0_l in H12, H13.
  rewrite Rplus_0_l.
  remember (a₁₃ * (a₂₁ * a₃₂ - a₃₁ * a₂₂)) as v eqn:Hv.
  apply Rplus_eq_compat_r with (r := - v) in Hw.
  rewrite Rplus_assoc, fold_Rminus in Hw.
  replace (v - v) with 0 in Hw by lra.
  rewrite Rplus_0_r, fold_Rminus in Hw.
  destruct (Req_dec v 1) as [Hv1| Hv1].
   move Hv1 at top; subst v.
   replace (1 - 1) with 0 in Hw by lra.
   symmetry in Hv.
   apply Rmult_integral in Hw.
   destruct Hw as [Hw| Hw].
    subst a₁₂.
    rewrite Rsqr_0, Rplus_0_l in H11.
    rewrite Rmult_0_l, Rplus_0_l in H12, H13.
    apply Rmult_integral in H12.
    destruct H12 as [H12| H12]; [ rewrite H12, Rsqr_0 in H11; lra | ].
    subst a₂₃.
    apply Rmult_integral in H13.
    destruct H13 as [H13| H13]; [ rewrite H13, Rsqr_0 in H11; lra | ].
    subst a₃₃; lra.

    apply Rminus_diag_uniq in Hw.
    destruct (Rlt_dec a₂₂ 0) as [Ha22| Ha22]; [ | lra ].
    destruct (Rlt_dec a₃₃ 0) as [Ha33| Ha33]; [ | lra ].
    apply Rmult_eq_compat_r with (r := / a₃₃) in Hw.
    symmetry in Hw; rewrite Rmult_shuffle0 in Hw.
    rewrite Rinv_r in Hw; [ rewrite Rmult_1_l in Hw | lra ].
    subst a₂₁.
    replace (a₂₃ * a₃₁ * / a₃₃ * a₃₂ - a₃₁ * a₂₂)
    with (a₃₁ * (a₂₃ * / a₃₃ * a₃₂ - a₂₂)) in Hv by lra.
    rewrite <- Rmult_assoc in Hv.
    ring_simplify in H23.
    apply Rmult_eq_compat_r with (r := a₃₃) in H23.
    do 2 rewrite Rmult_plus_distr_r in H23.
    rewrite Rmult_assoc in H23.
    rewrite Rinv_l in H23; [ rewrite Rmult_1_r in H23 | lra ].
    ring_simplify in H23.
    rewrite <- Rmult_plus_distr_l in H23.
    do 2 rewrite <- Rsqr_pow2 in H23.
    apply Rmult_eq_compat_r with (r := a₃₃) in Hv.
    rewrite Rmult_assoc in Hv.
    replace ((a₂₃ * / a₃₃ * a₃₂ - a₂₂) * a₃₃)
    with (a₂₃ * a₃₂ * (/ a₃₃ * a₃₃) - a₂₂ * a₃₃) in Hv by lra.
    rewrite Rinv_l in Hv; [ | lra ].
    rewrite Rmult_1_r, Rmult_1_l in Hv.
    rewrite Rsqr_mult in H22.
    apply Rmult_eq_compat_r with (r := a₃₃²) in H22.
    rewrite Rplus_assoc in H22.
    rewrite Rmult_plus_distr_r in H22.
    rewrite Rmult_assoc in H22.
    rewrite <- Rsqr_mult in H22.
    rewrite Rinv_l in H22; [ | lra ].
    rewrite Rsqr_1 in H22.
    rewrite Rmult_1_r, Rmult_1_l in H22.
    assert (H : (a₂₃ * a₃₁)² = a₃₃² * (1 - (a₂₂² + a₂₃²))) by lra.
    clear H22; rename H into H22; move H22 before H11.
    destruct (Req_dec (a₂₂² + a₂₃²) 1) as [Haa| Haa].
     rewrite Haa in H22.
     rewrite Rminus_diag_eq in H22; [ | easy ].
     rewrite Rmult_0_r in H22.
     apply Rsqr_eq_0 in H22.
     apply Rmult_integral in H22.
     destruct H22 as [H22| H22].
      subst a₂₃; clear Ha₂₁ Ha₂₃.
      rewrite Rmult_0_l, Rplus_0_l in H23.
      apply Rmult_integral in H23.
      destruct H23 as [H23| H23].
       apply Rmult_integral in H23.
       destruct H23; lra.

       subst a₃₂.
       rewrite Rmult_0_r, Rplus_0_l in H13.
       apply Rmult_integral in H13.
       destruct H13; [ | lra ].
       subst a₁₃.
       do 2 rewrite Rmult_0_l in Hv; lra.

      subst a₃₁.
      rewrite Rmult_0_r, Rmult_0_l in Hv; lra.

     idtac.
Abort.
(* chais pas...
let truc est vrai, pourtant, mais chais pas comment le démontrer.

bbb.
 ring_simplify in Hdet.
 assert (Hdet' :
   a₁₁ * a₂₂ * a₃₃ + a₃₂ * a₂₁ * a₁₃ + a₂₃ * a₁₂ * a₃₁ =
    a₁₁ * a₃₂ * a₂₃ + a₂₂ * a₃₁ * a₁₃ + a₃₃ * a₁₂ * a₂₁ + 1) by lra.
 clear Hdet; rename Hdet' into Hdet.
bbb.
*)
*)

Theorem matrix_axis_ok : ∀ M p k,
  is_rotation_matrix M
  → M ≠ mat_transp M
  → p = k ⁎ rotation_axis M
  → mat_vec_mul M p = p.
Proof.
intros * Hrm Hm Hn.
subst p.
remember (rotation_axis M) as ev eqn:Hev.
unfold rotation_axis in Hev.
unfold "_-_", sub_notation in Hev.
remember (a₃₂ M - a₂₃ M) as x eqn:Hx.
remember (a₁₃ M - a₃₁ M) as y eqn:Hy.
remember (a₂₁ M - a₁₂ M) as z eqn:Hz.
destruct (vec_zerop ev) as [Hvz| Hvnz].
 subst ev.
 injection Hvz; clear Hvz; intros H1 H2 H3.
 move H1 at top; move H2 at top; move H3 at top; subst x y z.
 symmetry in Hx, Hy, Hz.
 apply Rminus_diag_uniq in Hx.
 apply Rminus_diag_uniq in Hy.
 apply Rminus_diag_uniq in Hz.
 exfalso; apply Hm; clear Hm.
 unfold mat_transp, mkrmat.
 destruct M; simpl in Hx, Hy, Hz |-*.
 now subst; f_equal.

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
 subst ev; simpl.
 replace (k * x) with (x * k) by apply Rmult_comm.
 replace (k * y) with (y * k) by apply Rmult_comm.
 replace (k * z) with (z * k) by apply Rmult_comm.
 subst x y z.
 clear Hm Hvnz.
 f_equal; nsatz.
Qed.

Theorem normalized_axis : ∀ M k v,
  (M * (k ⁎ v) = k ⁎ v)%vec
  → (M * (k ⁎ vec_normalize v) = k ⁎ vec_normalize v)%vec.
Proof.
intros M k (x, y, z) Hv.
unfold vec_normalize.
remember ‖(V x y z)‖ as r eqn:Hr.
rewrite vec_const_mul_assoc.
setoid_rewrite Rmult_comm.
rewrite <- vec_const_mul_assoc.
rewrite mat_vec_mul_const_distr.
now rewrite Hv.
Qed.

Theorem matrix_all_fixpoints_ok : ∀ M p k,
  is_rotation_matrix M
  → M ≠ mat_transp M
  → p = rotation_fixpoint M k
  → mat_vec_mul M p = p.
Proof.
intros * Hrm Hm Hn.
unfold rotation_fixpoint in Hn.
unfold rotation_unit_axis in Hn.
subst p.
apply normalized_axis.
now apply matrix_axis_ok with (k := k).
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

Theorem mat_of_path_app : ∀ el₁ el₂,
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

Theorem mat_of_path_cons : ∀ e el,
   mat_of_path (e :: el) = (mat_of_elem e * mat_of_path el)%mat.
Proof. easy. Qed.

Theorem mat_of_elem_negf_mul_l : ∀ e,
  (mat_of_elem (negf e) * mat_of_elem e)%mat = mat_id.
Proof.
intros (t, d); simpl.
destruct t, d; simpl.
 apply rot_rot_inv_x.
 apply rot_inv_rot_x.
 apply rot_rot_inv_z.
 apply rot_inv_rot_z.
Qed.

Theorem mat_of_path_norm : ∀ el,
  mat_of_path (norm_list el) = mat_of_path el.
Proof.
intros.
induction el as [| e el]; [ easy | simpl ].
remember (norm_list el) as nel eqn:Hnel.
symmetry in Hnel.
destruct nel as [| e₁ nel].
 unfold mat_of_path in IHel at 1.
 simpl in IHel; symmetry.
 rewrite mat_of_path_cons.
 now rewrite <- IHel.

 destruct (letter_opp_dec e e₁) as [He| He].
  apply letter_opp_negf in He; subst e.
  rewrite mat_of_path_cons.
  rewrite <- IHel.
  rewrite mat_of_path_cons.
  rewrite mat_mul_assoc.
  now rewrite mat_of_elem_negf_mul_l, mat_mul_id_l.

  rewrite mat_of_path_cons; symmetry.
  rewrite mat_of_path_cons; symmetry.
  now rewrite IHel.
Qed.

Definition is_a_rotation_π M := M = mat_transp M ∧ M ≠ mat_id.

Theorem mat_of_path_is_not_rotation_π : ∀ el,
  ¬ is_a_rotation_π (mat_of_path el).
Proof.
intros el H.
unfold is_a_rotation_π in H.
destruct H as (Hmt, Hid).
remember (mat_of_path el) as M eqn:HM.
apply Hid; clear Hid.
assert (Hr : is_rotation_matrix M).
 subst M.
 apply mat_of_path_is_rotation_matrix.

 assert (HMI : (M * M = mat_id)%mat).
  rewrite Hmt at 2.
  now destruct Hr.

  rewrite <- mat_of_path_norm in HM.
  remember (norm_list el) as nel eqn:Hnel.
  symmetry in Hnel.
  destruct nel as [| e nel]; [ easy | ].
  rewrite HM in HMI.
  rewrite <- mat_of_path_app in HMI.
  exfalso; revert HMI.
  apply matrix_of_non_empty_path_is_not_identity.
  rewrite <- Hnel.
  intros H.
  apply norm_list_app_is_nil in H.
   symmetry in H; apply rev_path_eq_path in H.
   now rewrite Hnel in H.

   now rewrite norm_list_idemp.

   now rewrite norm_list_idemp.
Qed.

Theorem rotation_fixpoint_of_path : ∀ el p k,
  p = rotation_fixpoint (mat_of_path el) k
  → (mat_of_path el * p)%vec = p.
Proof.
intros * Hp.
remember (mat_of_path el) as M eqn:HM.
destruct (mat_eq_dec M mat_id) as [Hid| Hid].
 now rewrite Hid, mat_vec_mul_id.

 subst M.
 apply matrix_all_fixpoints_ok in Hp; [ easy | | ].
  apply mat_of_path_is_rotation_matrix.

  specialize (mat_of_path_is_not_rotation_π el) as Hmt.
  now intros H; apply Hmt.
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

 eapply rotation_fixpoint_of_path in Hp₁.
 rewrite <- rotate_vec_mul in Hp₁; apply Hp₁.
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
 remember 4%nat as four; simpl; subst four.
 rewrite Nat.mul_add_distr_r.
 destruct n; [ apply Nat.lt_0_succ | ].
 apply Nat.lt_lt_add_l.
 remember 4%nat as four; simpl; subst four.
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

Theorem surj_prod_nat_surj_nat : ∀ A V,
  (∃ g : ℕ * ℕ -> A, ∀ a : A, V a → ∃ nn : ℕ * ℕ, g nn = a)
  → ∃ f : ℕ → A, ∀ a : A, V a → ∃ n : ℕ, f n = a.
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

Theorem surj_prod_4_nat_surj_nat : ∀ A V,
  (∃ g : ℕ * ℕ * ℕ * ℕ -> A, ∀ a : A, V a
   → ∃ n₁ n₂ n₃ n₄, g (n₁, n₂, n₃, n₄) = a)
  → ∃ f : ℕ → A, ∀ a : A, V a → ∃ n : ℕ, f n = a.
Proof.
intros * (g & Hg).
exists (λ n, g (prod_4_nat_of_nat n)).
intros a Ha.
specialize (Hg a Ha) as (n₃ & n₄ & n₅ & n₆ & Hg); subst a.
remember (nat_of_prod_nat (n₅, n₆)) as n₂.
remember (nat_of_prod_nat (n₃, n₄)) as n₁.
remember (nat_of_prod_nat (n₁, n₂)) as n.
exists n; subst.
unfold prod_4_nat_of_nat.
now do 3 rewrite prod_nat_of_nat_inv.
Qed.

Definition prod_6_nat_of_nat n :=
  let '(n₁, n₂) := prod_nat_of_nat n in
  let '(n₃, n₄) := prod_nat_of_nat n₁ in
  let '(n₅, n₆) := prod_nat_of_nat n₂ in
  let '(n₇, n₈) := prod_nat_of_nat n₃ in
  let '(n₉, n₁₀) := prod_nat_of_nat n₄ in
  (n₅, n₆, n₇, n₈, n₉, n₁₀).

Theorem surj_prod_6_nat_surj_nat : ∀ A V,
  (∃ g : ℕ * ℕ * ℕ * ℕ * ℕ * ℕ -> A, ∀ a : A, V a
   → ∃ n₁ n₂ n₃ n₄ n₅ n₆, g (n₁, n₂, n₃, n₄, n₅, n₆) = a)
  → ∃ f : ℕ → A, ∀ a : A, V a → ∃ n : ℕ, f n = a.
Proof.
intros * (g & Hg).
exists (λ n, g (prod_6_nat_of_nat n)).
intros a Ha.
specialize (Hg a Ha) as (n₅ & n₆ & n₇ & n₈ & n₉ & n₁₀ & Hg); subst a.
remember (nat_of_prod_nat (n₉, n₁₀)) as n₄.
remember (nat_of_prod_nat (n₇, n₈)) as n₃.
remember (nat_of_prod_nat (n₅, n₆)) as n₂.
remember (nat_of_prod_nat (n₃, n₄)) as n₁.
remember (nat_of_prod_nat (n₁, n₂)) as n.
exists n; subst.
unfold prod_6_nat_of_nat.
now do 5 rewrite prod_nat_of_nat_inv.
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

Theorem surj_bool_prod_nat_surj_prod_nat : ∀ A V,
  (∃ g : bool * ℕ * ℕ -> A, ∀ a, V a → ∃ bnn, g bnn = a)
  → ∃ f : ℕ * ℕ → A, ∀ a, V a → ∃ nn, f nn = a.
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
    if is_neg_vec p then if (b : bool) then p else (- p)%vec
    else if b then (- p)%vec else p
  in
  fold_right rotate p₁ (path_of_nat no).

Theorem normalized_vec_normalize : ∀ v, v ≠ 0%vec → ‖(vec_normalize v)‖ = 1.
Proof.
intros v Hv.
assert (Hvz : ‖v‖ ≠ 0) by now intros H; apply vec_norm_eq_0 in H.
unfold vec_normalize.
rewrite vec_norm_vec_const_mul.
rewrite Rabs_right; [ now rewrite Rinv_l | ].
apply Rle_ge.
specialize (vec_norm_nonneg v) as Hvp.
apply nonneg_inv; lra.
Qed.

(*
Theorem on_sphere_on_unit_sphere : ∀ r p,
  0 < r
  → p ∈ sphere r
  → / r ⁎ p ∈ sphere 1.
Proof.
intros * Hr Hp.
apply on_sphere_norm in Hp; [ | lra ].
apply on_sphere_norm; [ lra | ].
rewrite vec_norm_vec_const_mul, Hp.
rewrite Rabs_right.
 rewrite Rinv_l; [ easy | lra ].

 apply Rinv_0_lt_compat in Hr; lra.
Qed.
*)

Theorem vec_div_in_sphere : ∀ r p,
  r ≠ 0
  → p ∈ sphere r
  → p ⁄ r ∈ sphere 1.
Proof.
intros r (x, y, z) Hr Hp; simpl in Hp; simpl.
do 3 rewrite Rsqr_mult.
do 2 rewrite <- Rmult_plus_distr_l.
rewrite Hp, Rsqr_1.
rewrite Rsqr_inv; [ | lra ].
rewrite Rinv_l; [ easy | ].
intros H; apply Rsqr_eq_0 in H; lra.
Qed.

Theorem vec_mul_in_sphere : ∀ r p,
  p ∈ sphere 1
  → r ⁎ p ∈ sphere r.
Proof.
intros r (x, y, z) Hp; simpl in Hp; simpl.
do 3 rewrite Rsqr_mult.
do 2 rewrite <- Rmult_plus_distr_l.
rewrite Hp, Rsqr_1.
now rewrite Rmult_1_r.
Qed.

Theorem rotation_fixpoint_on_sphere : ∀ r M,
   M ≠ mat_transp M
   → rotation_fixpoint M r ∈ sphere r.
Proof.
intros * Hm.
unfold rotation_fixpoint.
unfold rotation_unit_axis.
remember (rotation_axis M) as ax eqn:Hax.
unfold vec_normalize.
apply vec_mul_in_sphere.
destruct (vec_eq_dec ax 0) as [Hz| Hz].
 move Hz at top; subst ax; symmetry in Hax.
 injection Hax; clear Hax; intros Hz Hy Hx.
 apply Rminus_diag_uniq in Hx.
 apply Rminus_diag_uniq in Hy.
 apply Rminus_diag_uniq in Hz.
 exfalso; apply Hm; unfold mat_transp.
 unfold mkrmat.
 destruct M; simpl in Hx, Hy, Hz |-*.
 now rewrite Hx, Hy, Hz.

 destruct ax as (x, y, z); simpl.
 do 3 rewrite Rsqr_mult.
 do 2 rewrite <- Rmult_plus_distr_l.
 rewrite Rsqr_1, Rsqr_inv.
  rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
  rewrite Rinv_l; [ easy | ].
   intros H; apply sqr_vec_norm_eq_0 in H.
   now destruct H as (H1 & H2 & H3); subst.

  intros H.
  apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
  apply sqr_vec_norm_eq_0 in H.
  now destruct H as (H1 & H2 & H3); subst.
Qed.

Theorem fixpoint_of_path_on_sphere : ∀ r el,
  norm_list el ≠ []
  → fixpoint_of_path r el ∈ sphere r.
Proof.
intros * Hn.
unfold fixpoint_of_path.
remember (mat_of_path el) as M eqn:Hm.
destruct (mat_eq_dec M (mat_transp M)) as [Hmt| Hmt].
 assert (Hrm : is_rotation_matrix M).
  subst M; apply mat_of_path_is_rotation_matrix.

  assert (Hmm : (M * M = mat_id)%mat) by (rewrite Hmt at 2; apply Hrm).
  rewrite Hm in Hmm.
  rewrite <- mat_of_path_app in Hmm.
  exfalso; revert Hmm.
  apply matrix_of_non_empty_path_is_not_identity.
  intros H; apply Hn.
  now apply norm_list_app_diag_is_nil.

 now apply rotation_fixpoint_on_sphere.
Qed.

Theorem rotation_fixpoint_norm : ∀ M r, 0 ≤ r
  → M ≠ mat_transp M
  → ‖(rotation_fixpoint M r)‖ = r.
Proof.
intros * HM Hr.
apply rotation_fixpoint_on_sphere with (r := r) in Hr.
now apply on_sphere_norm.
Qed.

Theorem mat_vec_mul_cross_distr : ∀ M u v,
  is_rotation_matrix M
  → mat_vec_mul M (u × v) = mat_vec_mul M u × mat_vec_mul M v.
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

Theorem mat_axis_mul_const : ∀ M v,
  mat_vec_mul M v = v
  → ∀ k, mat_vec_mul M (vec_const_mul k v) = vec_const_mul k v.
Proof.
intros * Hv k.
rewrite <- mat_const_vec_mul.
rewrite mat_vec_mat_const_mul.
now rewrite Hv.
Qed.

Theorem vec_cross_mul_eq_0 : ∀ u v,
  u ≠ 0%vec
  → v ≠ 0%vec
  → u × v = 0%vec
  → ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ (a ⁎ u + b ⁎ v = 0)%vec.
Proof.
intros * Hu Hv Huv.
destruct u as (u₁, u₂, u₃).
destruct v as (v₁, v₂, v₃).
simpl in Huv; simpl.
injection Huv; clear Huv; intros H₃ H₂ H₁.
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
  destruct H₁ as [H₁| H₁]; [ now exfalso; subst u₃; apply Hu | subst v₂ ].
  rewrite Rmult_0_l in H₂.
  apply Rmult_integral in H₂.
  destruct H₂ as [H₂| H₂]; [ now exfalso; subst u₃; apply Hu | subst v₁ ].
  exists v₃, (- u₃).
  split; [ now intros H; apply Hv; f_equal | ].
  split; [ now apply Ropp_neq_0_compat; intros H; apply Hu; f_equal | ].
  f_equal; lra.

  destruct (Req_dec u₂ 0) as [Hu₂| Hu₂].
   subst u₂; rewrite Rmult_0_l in H₁; symmetry in H₁.
   apply Rmult_integral in H₁.
   destruct H₁ as [H₁| H₁]; [ now exfalso; subst u₃; apply Hu | subst v₂ ].
   exists v₃, (- u₃).
   split; [ now intros H; apply Hv; f_equal | ].
   split; [ now apply Ropp_neq_0_compat; intros H; apply Hu; f_equal | ].
   f_equal; lra.

   destruct (Req_dec u₃ 0) as [Hu₃| Hu₃].
    subst u₃; rewrite Rmult_0_l in H₁.
    apply Rmult_integral in H₁.
    destruct H₁ as [H₁| H₁]; [ easy | subst v₃ ].
    exists v₂, (- u₂).
    split; [ now intros H; apply Hv; f_equal | ].
    split; [ now apply Ropp_neq_0_compat; intros H; apply Hu; f_equal | ].
    f_equal; lra.

    destruct (Req_dec v₂ 0) as [Hv₂| Hv₂].
     subst v₂; rewrite Rmult_0_r in H₁.
     apply Rmult_integral in H₁.
     destruct H₁ as [H₁| H₁]; [ easy | now exfalso; subst v₃; apply Hv ].

     exists v₂, (- u₂).
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
  destruct H₂ as [H₂| H₂]; [ easy | now exfalso; subst v₃; apply Hv ].

  exists v₁, (- u₁).
  split; [ easy | ].
  split; [ now apply Ropp_neq_0_compat | ].
  f_equal; lra.
Qed.

Theorem free_family_diff_norm_vec : ∀ u v,
  ‖u‖ = ‖v‖
  → u ≠ v
  → is_neg_vec u = is_neg_vec v
  → u ≠ 0%vec
  → v ≠ 0%vec
  → ∀ a b : ℝ, (a ⁎ u + b ⁎ v)%vec = 0%vec → a = 0 ∧ b = 0.
Proof.
intros * Hvn Hvv Hn Hv₁ Hv₂ * Hab.
destruct u as (x₁, y₁, z₁).
destruct v as (x₂, y₂, z₂).
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
  apply Rmult_eq_compat_r with (r := / b) in Hx.
  apply Rmult_eq_compat_r with (r := / b) in Hy.
  apply Rmult_eq_compat_r with (r := / b) in Hz.
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
    fold (vec_opp (V x₁ y₁ z₁)) in Hn.
    rewrite is_neg_vec_neg_vec in Hn; [ | easy ].
    now symmetry in Hn; apply no_fixpoint_negb in Hn.

   intros H; apply Hv₁.
   apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
   apply sqr_vec_norm_eq_0 in H.
   now destruct H as (Hx & Hy & Hz); subst.
Qed.

Theorem nonzero_cross_mul : ∀ u v,
  ‖u‖ = ‖v‖
  → is_neg_vec u = is_neg_vec v
  → u ≠ 0%vec
  → v ≠ 0%vec
  → u ≠ v
  → u × v ≠ 0%vec.
Proof.
intros * Hvn Hn Hv₁ Hv₂ Hvv Hvvz.
destruct u as (x₁, y₁, z₁).
destruct v as (x₂, y₂, z₂).
simpl in Hvvz.
injection Hvvz; clear Hvvz; intros Hz Hy Hx.
move Hx after Hy; move Hz after Hy.
apply Rminus_diag_uniq in Hx.
apply Rminus_diag_uniq in Hy.
apply Rminus_diag_uniq in Hz.
simpl in Hn.
destruct (Rlt_dec x₁ 0) as [Hx₁| Hx₁].
 destruct (Rlt_dec x₂ 0) as [Hx₂| Hx₂]; [ clear Hn |  ].
  apply Rmult_eq_compat_r with (r := / x₂) in Hz.
  symmetry in Hz.
  rewrite Rmult_assoc in Hz.
  rewrite Rinv_r in Hz; [  | lra ].
  rewrite Rmult_1_r in Hz.
  rewrite Rmult_shuffle0, fold_Rdiv in Hz.
  apply Rmult_eq_compat_r with (r := / x₂) in Hy.
  rewrite Rmult_assoc in Hy.
  rewrite Rinv_r in Hy; [  | lra ].
  rewrite Rmult_1_r in Hy.
  rewrite Rmult_shuffle0, fold_Rdiv in Hy.
  subst y₁ z₁; clear Hx.
  replace x₁ with (x₁ / x₂ * x₂) in Hvn at 1.
   replace x₁ with (x₁ / x₂ * x₂) in Hvv at 1.
    remember (x₁ / x₂) as k eqn:Hk .
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
   apply Rmult_eq_compat_r with (r := / x₂) in Hz.
   symmetry in Hz.
   rewrite Rmult_assoc in Hz.
   rewrite Rinv_r in Hz; [  | lra ].
   rewrite Rmult_1_r in Hz.
   rewrite Rmult_shuffle0, fold_Rdiv in Hz.
   apply Rmult_eq_compat_r with (r := / x₂) in Hy.
   rewrite Rmult_assoc in Hy.
   rewrite Rinv_r in Hy; [  | lra ].
   rewrite Rmult_1_r in Hy.
   rewrite Rmult_shuffle0, fold_Rdiv in Hy.
   subst y₁ z₁; clear Hx.
   replace x₁ with (x₁ / x₂ * x₂) in Hvn at 1.
    replace x₁ with (x₁ / x₂ * x₂) in Hvv at 1.
     remember (x₁ / x₂) as k eqn:Hk .
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
     apply Rmult_eq_compat_l with (r := / y₁) in Hx.
     do 2 rewrite <- Rmult_assoc in Hx.
     rewrite Rinv_l in Hx; [  | lra ].
     rewrite Rmult_1_l, Rmult_comm, <- Rmult_assoc in Hx.
     rewrite fold_Rdiv in Hx.
     subst z₂.
     replace y₂ with (y₂ / y₁ * y₁) in Hvn at 1.
      replace y₂ with (y₂ / y₁ * y₁) in Hvv at 1.
       replace 0 with (y₂ / y₁ * 0) in Hvn at 2 by lra.
       replace 0 with (y₂ / y₁ * 0) in Hvv at 2 by lra.
       remember (y₂ / y₁) as k eqn:Hk .
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
   apply Rmult_eq_compat_l with (r := / y₁) in Hx.
   do 2 rewrite <- Rmult_assoc in Hx.
   rewrite Rinv_l in Hx; [  | lra ].
   rewrite Rmult_1_l, Rmult_comm, <- Rmult_assoc in Hx.
   rewrite fold_Rdiv in Hx.
   subst z₂.
   replace y₂ with (y₂ / y₁ * y₁) in Hvn at 1.
    replace y₂ with (y₂ / y₁ * y₁) in Hvv at 1.
     replace 0 with (y₂ / y₁ * 0) in Hvn at 2 by lra.
     replace 0 with (y₂ / y₁ * 0) in Hvv at 2 by lra.
     remember (y₂ / y₁) as k eqn:Hk .
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

Theorem vec_cross_mul_are_free_family : ∀ u v,
  ‖u‖ = ‖v‖
  → is_neg_vec u = is_neg_vec v
  → u ≠ 0%vec
  → v ≠ 0%vec
  → u ≠ v
  → ∀ a b c : ℝ,
    (a ⁎ u + b ⁎ v + c ⁎ (u × v))%vec = 0%vec
    → a = 0 ∧ b = 0 ∧ c = 0.
Proof.
intros * Hvn Hn Hu Hv Huv * Hab.
generalize Hab; intros H.
apply (f_equal (vec_dot_mul (u × v))) in H.
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
 now intros H₁; apply Huv.
Qed.

Theorem vec_couple_and_cross_formula : ∀ u v X,
  (u × v · u × v) ⁎ X =
   (((X · u) * (v · v) - (X · v) * (u · v)) ⁎ u +
    ((X · v) * (u · u) - (X · u) * (u · v)) ⁎ v +
    (X · (u × v)) ⁎ (u × v))%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) (x₁, x₂, x₃).
simpl; f_equal; ring.
Qed.

Theorem vec_couple_and_cross_is_base : ∀ u v X,
  (u × v · u × v) ≠ 0
  → ∃ a b c, X = (a ⁎ u + b ⁎ v + c ⁎ (u × v))%vec.
Proof.
intros * Huv.
remember (u × v · u × v) as r eqn:Hr.
exists (((X · u) * (v · v) - (X · v) * (u · v)) / r).
exists (((X · v) * (u · u) - (X · u) * (u · v)) / r).
exists ((X · (u × v)) / r).
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

Theorem fixpoint_unicity : ∀ M u v,
  is_rotation_matrix M
  → M ≠ mat_id
  → ‖u‖ = ‖v‖
  → is_neg_vec u = is_neg_vec v
  → (M * u)%vec = u
  → (M * v)%vec = v
  → u = v.
Proof.
intros * Hm Hnid Hvn Hn Hp₁ Hp₂.
destruct (vec_zerop u) as [Hv₁| Hv₁].
 rewrite Hv₁ in Hvn.
 unfold vec_norm in Hvn at 1.
 rewrite Rsqr_0, Rplus_0_r, Rplus_0_r in Hvn.
 rewrite sqrt_0 in Hvn.
 symmetry in Hvn.
 apply vec_norm_eq_0 in Hvn.
 now rewrite Hvn, Hv₁.

 destruct (vec_zerop v) as [Hv₂| Hv₂].
  rewrite Hv₂ in Hvn.
  unfold vec_norm in Hvn at 2.
  rewrite Rsqr_0, Rplus_0_r, Rplus_0_r in Hvn.
  rewrite sqrt_0 in Hvn.
  now apply vec_norm_eq_0 in Hvn.

  destruct (vec_eq_dec u v) as [Hvv| Hvv]; [ easy | exfalso ].
  remember ((‖u‖ / ‖(u × v)‖) ⁎ (u × v)) as W eqn:HW.
  move W before v.
  assert (Hp₃ : (M * (u × v) = u × v)%vec).
   apply mat_vec_mul_cross_distr with (u := u) (v := v) in Hm.
   now rewrite Hp₁, Hp₂ in Hm.

   move Hp₃ before Hp₂.
   assert (Hucv : ‖(u × v)‖ ≠ 0).
    intros H; apply vec_norm_eq_0 in H.
    apply vec_cross_mul_eq_0 in H; [ | easy | easy ].
    destruct H as (a & b & Ha & Hb & Hab).
    remember (vec_const_mul a u) as au eqn:Hau; symmetry in Hau.
    remember (vec_const_mul b v) as bv eqn:Hbv; symmetry in Hbv.
    destruct au as (ax₁, ay₁, az₁).
    destruct bv as (bx₂, by₂, bz₂).
    simpl in Hab.
    injection Hab; clear Hab; intros Hz Hy Hx.
    move Hx after Hy; move Hz after Hy.
    apply Rplus_opp_r_uniq in Hx.
    apply Rplus_opp_r_uniq in Hy.
    apply Rplus_opp_r_uniq in Hz.
    rewrite Hx, Hy, Hz in Hbv.
    replace (- ax₁) with (-1 * ax₁) in Hbv by lra.
    replace (- ay₁) with (-1 * ay₁) in Hbv by lra.
    replace (- az₁) with (-1 * az₁) in Hbv by lra.
    fold (vec_const_mul (-1) (V ax₁ ay₁ az₁)) in Hbv.
    rewrite <- Hau in Hbv.
    rewrite vec_const_mul_assoc in Hbv.
    replace (-1 * a) with (-a) in Hbv by lra.
    apply vec_const_mul_div in Hbv; [ | easy ].
    rewrite Hbv in Hvn.
    rewrite vec_norm_vec_const_mul in Hvn.
    replace ‖u‖ with (1 * ‖u‖) in Hvn at 1 by lra.
    apply Rmult_eq_reg_r in Hvn; [ | now intros H; apply Hv₁, vec_norm_eq_0 ].
    symmetry in Hvn.
    apply Rabs_or in Hvn.
    destruct Hvn as [Hvn| Hvn]; rewrite Hvn in Hbv.
     now rewrite vec_const_mul_1_l in Hbv; symmetry in Hbv.

     destruct u as (x, y, z); simpl in Hbv.
     do 3 rewrite <- Ropp_mult_distr_l in Hbv.
     do 3 rewrite Rmult_1_l in Hbv.
     fold (vec_opp (V x y z)) in Hbv.
     rewrite Hbv in Hn.
     rewrite is_neg_vec_neg_vec in Hn; [ | easy ].
     now symmetry in Hn; apply no_fixpoint_negb in Hn.

    move Hvv before Hvn.
    assert (HMX : ∀ X, (M * X)%vec = X).
     assert (Huv : u × v · u × v ≠ 0).
      rewrite vec_dot_mul_diag.
      intros Huv; apply Hvv.
      now apply Rsqr_eq_0 in Huv.

      intros X.
      specialize (vec_couple_and_cross_is_base u v X Huv).
      intros (a & b & c & HX).
      subst X.
      do 2 rewrite mat_vec_mul_add_distr_l.
      do 3 rewrite mat_vec_mul_const_distr.
      now rewrite Hp₁, Hp₂, Hp₃.

     move HMX before Hp₃.
     pose proof HMX (V 1 0 0) as H1; simpl in H1.
     pose proof HMX (V 0 1 0) as H2; simpl in H2.
     pose proof HMX (V 0 0 1) as H3; simpl in H3.
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

Theorem axis_and_fixpoint_of_path_collinear : ∀ el p q r,
  p ∈ sphere r
  → q ∈ sphere r
  → norm_list el ≠ []
  → (mat_of_path el * p)%vec = p
  → q = fixpoint_of_path r el
  → p = if bool_dec (is_neg_vec p) (is_neg_vec q) then q else (- q)%vec.
Proof.
intros el p₁ p₂ r Hsr₁ Hsr₂ Hnl Hr Hp₂.
remember (is_neg_vec p₁) as b eqn:Hb.
remember (is_neg_vec p₂) as b₁.
rename Heqb₁ into Hb₁.
move Hb before Hb₁.
symmetry in Hb, Hb₁.
apply rotation_fixpoint_of_path in Hp₂.
move Hp₂ at bottom; move Hr before Hp₂.
remember (is_neg_vec p₁) as b₂ eqn:Hb₂.
symmetry in Hb₂.
move Hb₂ before Hb₁.
destruct b₁, b.
 destruct b₂; [ | easy ].
 rewrite <- Hb₁ in Hb₂.
 eapply fixpoint_unicity; try eassumption.
  apply mat_of_path_is_rotation_matrix.

  intros H.
  now apply matrix_of_non_empty_path_is_not_identity in Hnl.

  destruct p₁ as (x₁, y₁, z₁).
  destruct p₂ as (x₂, y₂, z₂).
  simpl in Hsr₁, Hsr₂; simpl.
  now rewrite Hsr₁, Hsr₂.

 destruct b₂; [ easy | ].
 replace false with (negb true) in Hb₂ by easy.
 rewrite <- Hb₁ in Hb₂.
 eapply fixpoint_unicity; try eassumption.
  apply mat_of_path_is_rotation_matrix.

  intros H.
  now apply matrix_of_non_empty_path_is_not_identity in Hnl.

  destruct p₁ as (x₁, y₁, z₁).
  destruct p₂ as (x₂, y₂, z₂).
  simpl in Hsr₁, Hsr₂; simpl.
  do 3 rewrite <- Rsqr_neg.
  now rewrite Hsr₁, Hsr₂.

  rewrite Hb₂.
  destruct (bool_dec false true) as [| H]; [ easy | clear H ].
  rewrite is_neg_vec_neg_vec; [ easy | ].
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
  apply mat_of_path_is_rotation_matrix.

  intros H.
  now apply matrix_of_non_empty_path_is_not_identity in Hnl.

  destruct p₁ as (x₁, y₁, z₁).
  destruct p₂ as (x₂, y₂, z₂).
  simpl in Hsr₁, Hsr₂; simpl.
  do 3 rewrite <- Rsqr_neg.
  now rewrite Hsr₁, Hsr₂.

  rewrite Hb₂.
  destruct (bool_dec true false) as [| H]; [ easy | clear H ].
  rewrite is_neg_vec_neg_vec; [ easy | ].
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
  apply mat_of_path_is_rotation_matrix.

  intros H.
  now apply matrix_of_non_empty_path_is_not_identity in Hnl.

  destruct p₁ as (x₁, y₁, z₁).
  destruct p₂ as (x₂, y₂, z₂).
  simpl in Hsr₁, Hsr₂; simpl.
  now rewrite Hsr₁, Hsr₂.
Qed.

Theorem D_set_is_countable : ∀ r,
  ∃ f : ℕ → vector, ∀ p : vector,
  p ∈ D ∩ sphere r → ∃ n : ℕ, f n = p.
Proof.
intros r.
apply surj_prod_nat_surj_nat.
apply surj_bool_prod_nat_surj_prod_nat.
exists (fixpoint_of_bool_prod_nat r).
intros p (Hp & Hsr).
destruct Hp as (el₁ & p₁ & (el & Hs) & Hnl & Hr).
rewrite rotate_vec_mul in Hr.
remember (nat_of_path el₁) as nf eqn:Hnf.
remember (nat_of_path (rev_path el)) as no eqn:Hno.
fold (mat_of_path el₁) in Hr.
pose proof mat_of_path_is_rotation_matrix el as H.
generalize Hsr; intros Hsr₁.
eapply on_sphere_after_rotation in Hsr₁; [ clear H | apply H ].
rewrite <- rotate_vec_mul, Hs in Hsr₁.
apply rotate_rev_path in Hs.
remember (mat_of_path el₁) as m eqn:Hm.
remember (rotation_fixpoint m r) as p₂ eqn:Hp₂.
destruct (mat_eq_dec m (mat_transp m)) as [Hmt| Hmt].
 assert (Hrm : is_rotation_matrix m).
  rewrite Hm; apply mat_of_path_is_rotation_matrix.

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
  exists (is_neg_vec p₁, nf, no).
  unfold fixpoint_of_bool_prod_nat.
  rewrite Hno, path_of_nat_inv.
  symmetry; rewrite <- Hs; f_equal.
  rewrite Hnf, path_of_nat_inv.
  rewrite <- Hm, <- Hp₂.
  rewrite <- Hr in Hs.
  subst m.
  fold (fixpoint_of_path r el₁) in Hp₂.
  apply axis_and_fixpoint_of_path_collinear with (p := p₁) in Hp₂;
    try assumption.
  now destruct (is_neg_vec p₁), (is_neg_vec p₂).
Qed.

Definition sphere_sym S := mkset (λ p, (- p)%vec ∈ S).

Theorem sphere_sym_neg_vec : ∀ p, p ∈ sphere_sym D → (- p)%vec ∈ D.
Proof.
intros (x, y, z) (el₁ & p₁ & Hso & Hn & Hr).
now exists el₁, p₁.
Qed.

Theorem neg_vec_in_sphere : ∀ r p, p ∈ sphere r → (- p)%vec ∈ sphere r.
Proof.
intros r (x, y, z) Hp; simpl.
now do 3 rewrite <- Rsqr_neg.
Qed.

Theorem neg_vec_in_ball : ∀ p, p ∈ ball → (- p)%vec ∈ ball.
Proof.
intros (x, y, z) Hp; simpl.
now do 3 rewrite <- Rsqr_neg.
Qed.

Theorem D_set_symmetry_is_countable : ∀ r,
  ∃ f : ℕ → vector, ∀ p : vector,
  p ∈ sphere_sym D ∩ sphere r → ∃ n : ℕ, f n = p.
Proof.
intros r.
specialize (D_set_is_countable r) as (f, Hf).
exists (λ n, (- f n)%vec).
intros p Hp.
enough (Hn : (- p)%vec ∈ D ∩ sphere r).
 specialize (Hf ((- p)%vec) Hn) as (n & Hf).
 exists n; rewrite Hf.
 apply neg_vec_involutive.

 destruct Hp as (Hss, Hs).
 split; [ now apply sphere_sym_neg_vec | ].
 now apply neg_vec_in_sphere.
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
  ∃ f : ℕ → vector, ∀ p : vector,
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

Theorem matrix_of_axis_angle_inv : ∀ v c s,
  0 < s
  → ‖v‖ = 1
  → s² + c² = 1
  → axis_angle_of_matrix (matrix_of_axis_angle (v, s, c)) = (v, s, c).
Proof.
intros v cosθ sinθ Hsp Hvs Hsc.
assert (Hvnz : (v ≠ 0)%vec) by (intros H; rewrite H, vec_norm_0 in Hvs; lra).
remember (v, sinθ, cosθ) as acs2 eqn:Hacs2.
unfold axis_angle_of_matrix.
remember (matrix_of_axis_angle acs2) as M eqn:HM.
remember (mat_trace M) as tr eqn:Htr.
remember ((tr - 1) / 2) as c eqn:Hc.
remember (√ (1 - c²)) as s eqn:Hs.
subst acs2; simpl.
simpl in HM.
destruct v as (x, y, z).
simpl in Hvs.
rewrite Hvs in HM.
progress repeat rewrite Rdiv_1_r in HM.
unfold rotation_unit_axis, rotation_axis; simpl.
unfold "_-_", sub_notation.
rewrite HM; unfold mkrmat ; simpl.
unfold mat_trace in Htr.
rewrite HM in Htr; unfold mkrmat in Htr; simpl in Htr.
rename cosθ into c₁.
do 2 rewrite <- Rplus_assoc in Htr.
replace (x² * (1 - c₁) + c₁ + y² * (1 - c₁) + c₁ + z² * (1 - c₁) + c₁)
with ((x² + y² + z²) * (1 - c₁) + 3 * c₁) in Htr by lra.
assert (Hv2s : x² + y² + z² = 1).
 apply (f_equal Rsqr) in Hvs.
 rewrite Rsqr_sqrt in Hvs; [ | apply nonneg_sqr_vec_norm ].
 rewrite Hvs; apply Rsqr_1.

 rewrite Hv2s, Rmult_1_l in Htr.
 ring_simplify in Htr.
 rewrite Htr in Hc.
 assert (H : c = c₁) by lra.
 move H at top; subst c₁; clear Hc.
 assert (H : sinθ² = 1 - c²) by lra.
 rewrite <- H in Hs.
 rewrite sqrt_Rsqr in Hs; [ | lra ].
 move Hs at top; subst sinθ; clear H.
 f_equal; f_equal; symmetry.
 replace (y * z * (1 - c) + x * s - (y * z * (1 - c) - x * s))
 with (2 * x * s) by lra.
 replace (x * z * (1 - c) + y * s - (x * z * (1 - c) - y * s))
 with (2 * y * s) by lra.
 replace (x * y * (1 - c) + z * s - (x * y * (1 - c) - z * s))
 with (2 * z * s) by lra.
 progress repeat rewrite Rsqr_mult.
 progress repeat rewrite <- Rmult_plus_distr_r.
 progress repeat rewrite <- Rmult_plus_distr_l.
 rewrite Hv2s, Rmult_1_r.
 rewrite <- Rsqr_mult.
 rewrite sqrt_Rsqr; [ | lra ].
 setoid_rewrite Rmult_comm.
 do 3 rewrite fold_Rdiv.
 progress replace (2 * x * s / (2 * s)) with ((2 * s) * / (2 * s) * x) by lra.
 progress replace (2 * y * s / (2 * s)) with ((2 * s) * / (2 * s) * y) by lra.
 progress replace (2 * z * s / (2 * s)) with ((2 * s) * / (2 * s) * z) by lra.
 rewrite Rinv_r; [ | lra ].
 f_equal; lra.
Qed.

(* playing with quaternions, just for fun... *)

Record ℍ := quat { Re : ℝ; Im : vector }.
Arguments quat Re%R Im%vec.

Delimit Scope quat_scope with H.

Definition quat_add '(quat a₁ v₁) '(quat a₂ v₂) :=
  quat (a₁ + a₂) (v₁ + v₂).
Definition quat_mul '(quat a₁ v₁) '(quat a₂ v₂) :=
  quat (a₁ * a₂ - v₁ · v₂) (a₁ ⁎ v₂ + a₂ ⁎ v₁ + v₁ × v₂).

Definition Qi := quat 0 (V 1 0 0).
Definition Qj := quat 0 (V 0 1 0).
Definition Qk := quat 0 (V 0 0 1).

Definition quat_const_mul k '(quat a v) := quat (a * k) (k ⁎ v).

Definition quat_norm '(quat a (V b c d)) := √ (a² + b² + c² + d²).

Definition quat_conj q := quat (Re q) (- Im q).

Definition quat_inv '(quat a v) :=
  let r := a² + v²%vec in
  quat_const_mul (/ r) (quat_conj (quat a v)).

Notation "h₁ + h₂" := (quat_add h₁ h₂) : quat_scope.
Notation "h₁ * h₂" := (quat_mul h₁ h₂) : quat_scope.
Notation "'hi'" := (Qi) : quat_scope.
Notation "'hj'" := (Qj) : quat_scope.
Notation "'hk'" := (Qk) : quat_scope.
Notation "h '⁻¹'" := (quat_inv h) (at level 1, format "h ⁻¹"): quat_scope.
Notation "‖ h ‖" := (quat_norm h) : quat_scope.

Definition hr a := quat a 0.

Theorem hi_sqr : (hi * hi)%H = hr (-1).
Proof. unfold hr; simpl; f_equal; [ lra | f_equal; lra ]. Qed.

Theorem hj_sqr : (hj * hj)%H = hr (-1).
Proof. unfold hr; simpl; f_equal; [ lra | f_equal; lra ]. Qed.

Theorem hk_shr : (hk * hk)%H = hr (-1).
Proof. unfold hr; simpl; f_equal; [ lra | f_equal; lra ]. Qed.

Theorem hi_hj_hk : (hi * hj * hk = hr (-1))%H.
Proof. unfold hr; simpl; f_equal; [ lra | f_equal; lra ]. Qed.

(* works for angle ≠ π *)
Definition quat_of_mat M :=
  let s := √ (1 + mat_trace M) / 2 in
  let x := (a₃₂ M - a₂₃ M) / (4 * s) in
  let y := (a₁₃ M - a₃₁ M) / (4 * s) in
  let z := (a₂₁ M - a₁₂ M) / (4 * s) in
  quat s (V x y z).

Definition mat_of_quat '(quat a (V b c d)) :=
  mkrmat
    (a² + b² - c² - d²) (2 * b * c - 2 * a * d) (2 * a * c + 2 * b * d)
    (2 * a * d + 2 * b * c) (a² - b² + c² - d²) (2 * c * d - 2 * a * b)
    (2 * b * d - 2 * a * c) (2 * a * b + 2 * c * d) (a² - b² - c² + d²).

Definition quat_rotate h v := (h * v * h⁻¹)%H.

Theorem mat_of_quat_inv : ∀ M,
  is_rotation_matrix M
  → mat_trace M ≠ -1
  → mat_of_quat (quat_of_mat M) = M.
Proof.
intros * Hrm Hmt.
unfold quat_of_mat, mat_of_quat; simpl; symmetry.
unfold mat_trace in Hmt.
remember (√ (1 + mat_trace M) / 2) as s eqn:Hs.
remember ((a₃₂ M - a₂₃ M) / (4 * s)) as x eqn:Hx.
remember ((a₁₃ M - a₃₁ M) / (4 * s)) as y eqn:Hy.
remember ((a₂₁ M - a₁₂ M) / (4 * s)) as z eqn:Hz.
unfold mat_trace in Hs.
destruct M; simpl in *; unfold mkrmat.
f_equal.
 generalize Hs; intros Hs2.
 apply (f_equal Rsqr) in Hs2.
 unfold Rdiv in Hs2.
 rewrite Rsqr_mult in Hs2.
 do 3 rewrite Rsqr_pow2 in Hs2.
 replace ((/ 2) ^ 2) with (/ 4) in Hs2 by lra.
 do 2 rewrite <- Rsqr_pow2 in Hs2.
 rewrite Rsqr_sqrt in Hs2.
 rewrite Hs2, Hx, Hy, Hz.
 unfold Rdiv.
 do 3 rewrite Rsqr_mult.
 rewrite Rsqr_inv.
  rewrite Rsqr_mult.
  do 5 rewrite Rsqr_pow2.
  replace (4 ^ 2) with 16 by lra.
  remember 16 as sixteen.
  remember 4 as four.
  rewrite Rinv_mult_distr; [ | lra | ].
  do 3 rewrite <- Rmult_assoc.
  apply Rmult_eq_reg_r with (r := sixteen * s ^ 2).
  unfold Rminus.
  do 9 rewrite Rmult_plus_distr_r.
  do 3 rewrite fold_Rminus.
  subst four sixteen.
  do 10 rewrite fold_Rdiv.
  do 2 rewrite <- Ropp_mult_distr_l.
  do 2 rewrite fold_Rminus.
  replace
    (1 / 4 * (16 * s ^ 2) +
      (a₁₁ / 4 * (16 * s ^ 2) + a₂₂ / 4 * (16 * s ^ 2) +
       a₃₃ / 4 * (16 * s ^ 2)) +
      (a₃₂ - a₂₃) ^ 2 / 16 / s ^ 2 * (16 * s ^ 2) -
      (a₁₃ - a₃₁) ^ 2 / 16 / s ^ 2 * (16 * s ^ 2) -
      (a₂₁ - a₁₂) ^ 2 / 16 / s ^ 2 * (16 * s ^ 2)) with
    (4 * s ^ 2 * (1 + (a₁₁ + a₂₂ + a₃₃)) +
      (a₃₂ - a₂₃) ^ 2 * (/ s ^ 2 * s ^ 2) -
      (a₁₃ - a₃₁) ^ 2 * (/ s ^ 2 * s ^ 2) -
      (a₂₁ - a₁₂) ^ 2 * (/ s ^ 2 * s ^ 2)) by lra.
  rewrite Rinv_l.
   do 3 rewrite Rmult_1_r.
   rewrite Rsqr_pow2 in Hs2.
   replace (1 + (a₁₁ + a₂₂ + a₃₃)) with (4 * s ^ 2) by lra.
   unfold is_rotation_matrix in Hrm; simpl in Hrm.
   unfold mat_transp, mat_det, mat_mul, mat_id, mkrmat in Hrm; simpl in Hrm.
   destruct Hrm as (Hid, Hrm).
   injection Hid; clear Hid; intros.
(* bonjour le merdier... *)
rewrite Hs2.
clear s Hs Hs2 x Hx y Hy z Hz.
Abort. (*

 (* mat_trace M = -1 *)
 rewrite Rsqr_0, Rplus_0_l, Rmult_0_r.
 do 3 rewrite Rmult_0_l, Rplus_0_l, Rminus_0_r.
 rewrite Rminus_0_l.
 remember a₁₁ M - a₂₂ M - a₃₃ M as x₀ eqn:Hx₀.
 remember - a₁₁ M + a₂₂ M - a₃₃ M as y₀ eqn:Hy₀.
 remember - a₁₁ M - a₂₂ M + a₃₃ M as z₀ eqn:Hz₀.
 remember (√ (1 + x₀) / 2) as x eqn:Hx.
 remember (√ (1 + y₀) / 2) as y eqn:Hy.
 remember (√ (1 + z₀) / 2) as z eqn:Hz.
 generalize Hx; intros Hx2.
 generalize Hy; intros Hy2.
 generalize Hz; intros Hz2.
 apply (f_equal Rsqr) in Hx2.
 apply (f_equal Rsqr) in Hy2.
 apply (f_equal Rsqr) in Hz2.
 unfold Rdiv in Hx2, Hy2, Hz2.
 rewrite Rsqr_mult in Hx2, Hy2, Hz2.
 do 3 rewrite Rsqr_pow2 in Hx2, Hy2, Hz2.
 replace (/ 2) ^ 2 with / 4 in Hx2, Hy2, Hz2 by lra.
 do 2 rewrite <- Rsqr_pow2 in Hx2, Hy2, Hz2.
 rewrite fold_Rdiv in Hx2, Hy2, Hz2.
 rewrite Rsqr_sqrt in Hx2.
  rewrite Rsqr_sqrt in Hy2.
   rewrite Rsqr_sqrt in Hz2.
    rewrite Hx2, Hy2, Hz2.
    destruct M; simpl in *; unfold mkrmat.
    subst x₀ y₀ z₀.
    f_equal; try lra.
     rewrite Hx, Hy.
     remember 1 + (a₁₁ - a₂₂ - a₃₃) as x₁.
     remember 1 + (- a₁₁ + a₂₂ - a₃₃) as y₁.
     replace 2 * (√ x₁ / 2) * (√ y₁ / 2) with √ x₁ * √ y₁ / 2 by lra.
     rewrite <- sqrt_mult_alt.
     remember x₁ * y₁ as xy eqn:Hxy.
     rewrite Heqx₁, Heqy₁ in Hxy.
     ring_simplify in Hxy.
     do 3 rewrite <- Rsqr_pow2 in Hxy.
(* seems not to work... *)
*)

Definition vec_le '(V u₁ u₂ u₃) '(V v₁ v₂ v₃) :=
  u₁ ≤ v₁ ∧ u₂ ≤ v₂ ∧ u₃ ≤ v₃.

Notation "u '≤' v" := (vec_le u v) : vec_scope.

Theorem quat_of_mat_inv1 : ∀ h,
  (‖h‖ = 1)%H
  → 0 < Re h
  → quat_of_mat (mat_of_quat h) = h.
Proof.
intros * Hhn Hrp.
destruct h as (a, (b, c, d)); simpl in Hrp; simpl.
apply sqrt_lem_0 in Hhn; [ | apply nonneg_plus_4_sqr | apply Rle_0_1 ].
symmetry in Hhn; rewrite Rmult_1_r in Hhn.
unfold quat_of_mat, mat_of_quat; simpl.
unfold mat_trace; simpl.
remember (a² + b² - c² - d² + (a² - b² + c² - d²) + (a² - b² - c² + d²))
  as t eqn:Ht.
remember (a² + b² - c² - d² - (a² - b² + c² - d²) - (a² - b² - c² + d²))
  as x₀ eqn:Hx₀.
remember (- (a² + b² - c² - d²) + (a² - b² + c² - d²) - (a² - b² - c² + d²))
  as y₀ eqn:Hy₀.
remember (- (a² + b² - c² - d²) - (a² - b² + c² - d²) + (a² - b² - c² + d²))
  as z₀ eqn:Hz₀.
ring_simplify in Ht.
ring_simplify in Hx₀.
ring_simplify in Hy₀.
ring_simplify in Hz₀.
assert (Ht' : t = 4 * a² - 1) by lra.
clear Ht; rename Ht' into Ht.
destruct (Req_dec t (-1)) as [Htd| Htd].
 assert (Ha : a = 0) by (now apply Rsqr_eq_0; lra); subst a.
 now apply Rlt_irrefl in Hrp.

 assert (Ha2 : a² ≠ 0) by lra.
 assert (Ha : a ≠ 0) by now intros H; subst a; apply Ha2, Rsqr_0.
 assert (Haa : Rabs a ≠ 0) by now apply Rabs_no_R0.
 assert (Hta : √ (1 + t) / 2 = Rabs a).
  rewrite Ht, Rplus_minus.
  rewrite Rsqr_pow2.
  replace (4 * a ^ 2) with ((2 * a) ^ 2) by lra.
  rewrite <- Rsqr_pow2, sqrt_Rsqr_abs, Rabs_mult.
  replace (Rabs 2) with (Rabs (IZR 2)) by easy.
  rewrite Rabs_Zabs; simpl.
  rewrite Rmult_div.
  unfold Rdiv.
  rewrite Rinv_r; [ | lra ].
  now rewrite Rmult_1_l.

  rewrite Hta.
  apply Rlt_le in Hrp.
  apply Rabs_pos_eq in Hrp.
  f_equal; [ easy | ].
  assert (Rpm : ∀ a b c, a + b - (b - c) = a + c) by (intros; lra).
  do 3 rewrite Rpm.
  replace (2 * a * b + 2 * a * b) with (4 * a * b) by lra.
  replace (2 * a * c + 2 * a * c) with (4 * a * c) by lra.
  replace (2 * a * d + 2 * a * d) with (4 * a * d) by lra.
  unfold Rdiv.
  rewrite Rinv_mult_distr; [ | lra | easy ].
  do 3 rewrite <- Rmult_assoc.
  replace (4 * a * b * / 4) with (a * b) by lra.
  replace (4 * a * c * / 4) with (a * c) by lra.
  replace (4 * a * d * / 4) with (a * d) by lra.
  rewrite Hrp.
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  now do 3 rewrite Rmult_1_l.
Qed.

Theorem quat_of_mat_inv2 : ∀ h,
  (‖h‖ = 1)%H
  → 0 ≤ Re h
  → (0 ≤ Im h)%vec
  → quat_of_mat (mat_of_quat h) = h.
Proof.
intros * Hhn Hrp Hvp.
destruct h as (a, (b, c, d)); simpl in Hrp, Hvp; simpl.
apply sqrt_lem_0 in Hhn; [ | apply nonneg_plus_4_sqr | apply Rle_0_1 ].
symmetry in Hhn; rewrite Rmult_1_r in Hhn.
unfold quat_of_mat, mat_of_quat; simpl.
unfold mat_trace; simpl.
remember (a² + b² - c² - d² + (a² - b² + c² - d²) + (a² - b² - c² + d²))
  as t eqn:Ht.
remember (a² + b² - c² - d² - (a² - b² + c² - d²) - (a² - b² - c² + d²))
  as x₀ eqn:Hx₀.
remember (- (a² + b² - c² - d²) + (a² - b² + c² - d²) - (a² - b² - c² + d²))
  as y₀ eqn:Hy₀.
remember (- (a² + b² - c² - d²) - (a² - b² + c² - d²) + (a² - b² - c² + d²))
  as z₀ eqn:Hz₀.
ring_simplify in Ht.
ring_simplify in Hx₀.
ring_simplify in Hy₀.
ring_simplify in Hz₀.
assert (Ht' : t = 4 * a² - 1) by lra.
clear Ht; rename Ht' into Ht.
destruct (Req_dec t (-1)) as [Htd| Htd].
 (* here case with trace = -1, i.e. angle = π, not yet treated; I have to
    think of it. Going to next case. *)
Focus 2.
 assert (Ha2 : a² ≠ 0) by lra.
 assert (Ha : a ≠ 0) by now intros H; subst a; apply Ha2, Rsqr_0.
 assert (Haa : Rabs a ≠ 0) by now apply Rabs_no_R0.
 assert (Hta : √ (1 + t) / 2 = Rabs a).
  rewrite Ht, Rplus_minus.
  rewrite Rsqr_pow2.
  replace (4 * a ^ 2) with ((2 * a) ^ 2) by lra.
  rewrite <- Rsqr_pow2, sqrt_Rsqr_abs, Rabs_mult.
  replace (Rabs 2) with (Rabs (IZR 2)) by easy.
  rewrite Rabs_Zabs; simpl.
  rewrite Rmult_div.
  unfold Rdiv.
  rewrite Rinv_r; [ | lra ].
  now rewrite Rmult_1_l.

  rewrite Hta.
  apply Rabs_pos_eq in Hrp.
  f_equal; [ easy | ].
  assert (Rpm : ∀ a b c, a + b - (b - c) = a + c) by (intros; lra).
  do 3 rewrite Rpm.
  replace (2 * a * b + 2 * a * b) with (4 * a * b) by lra.
  replace (2 * a * c + 2 * a * c) with (4 * a * c) by lra.
  replace (2 * a * d + 2 * a * d) with (4 * a * d) by lra.
  unfold Rdiv.
  rewrite Rinv_mult_distr; [ | lra | easy ].
  do 3 rewrite <- Rmult_assoc.
  replace (4 * a * b * / 4) with (a * b) by lra.
  replace (4 * a * c * / 4) with (a * c) by lra.
  replace (4 * a * d * / 4) with (a * d) by lra.
  rewrite Hrp.
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  now do 3 rewrite Rmult_1_l.
Abort.

(* end play with quaternions. *)

Theorem axis_of_matrix_is_eigen_vec : ∀ p cosθ sinθ,
  sinθ² + cosθ² = 1
  → (matrix_of_axis_angle (p, sinθ, cosθ) * p)%vec = p.
Proof.
intros (xp, yp, zp) * Hsc.
remember (√ (xp² + yp² + zp²)) as r eqn:Hr.
destruct (Req_dec r 0) as [Hrz| Hrnz].
 rewrite Hr in Hrz.
 apply sqrt_eq_0 in Hrz; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in Hrz.
 destruct Hrz as (Hx & Hy & Hz); subst xp yp zp.
 now rewrite mat_vec_mul_0_r.

 unfold matrix_of_axis_angle; simpl.
 rewrite <- Hr.
 specialize (z_of_xy xp yp zp r Hr Hrnz) as Hz.
 f_equal; ring_simplify.
  replace (yp / r * sinθ * zp) with (zp / r * sinθ * yp) by lra.
  replace (xp / r * (zp / r) * zp) with (xp * (zp / r) ^ 2) by lra.
  replace (cosθ * (xp / r) * (zp / r) * zp)
  with (cosθ * xp * (zp / r) ^ 2) by lra.
  rewrite Rsqr_pow2, Hz; lra.

  replace (xp / r * sinθ * zp) with (zp / r * sinθ * xp) by lra.
  replace (yp / r * cosθ * (zp / r) * zp) with (yp * cosθ * (zp / r) ^ 2)
    by lra.
  replace (yp / r * (zp / r) * zp) with (yp * (zp / r) ^ 2) by lra.
  rewrite Rsqr_pow2, Hz; lra.

  rewrite Rsqr_pow2, Hz; lra.
Qed.

Theorem ter_bin_of_rotation_surj : ∀ p, p ≠ 0%vec → ∀ (u : ℕ → bool),
  ∃ M, M ∈ rotation_around p ∧ (∀ n : ℕ, ter_bin_of_rotation M n = u n).
Proof.
intros * Hp *.
specialize (ter_bin_of_frac_part_surj u); intros (s & Hs & Hn).
remember (2 * s - 1) as cosθ eqn:Hcosθ.
remember (√ (1 - cosθ²)) as sinθ eqn:Hsinθ.
assert (Hsc : sinθ² = (1 - cosθ²)).
 rewrite Hsinθ, Rsqr_sqrt; [ easy | ].
 rewrite Hcosθ, Rsqr_pow2.
 eapply Rplus_le_reg_r; unfold Rminus.
 rewrite Rplus_assoc, Rplus_opp_l.
 rewrite Rplus_0_l, Rplus_0_r.
 replace 1 with (1 ^ 2) at 4 by lra.
 apply pow_maj_Rabs, Rabs_le; lra.

 exists (matrix_of_axis_angle (p, sinθ, cosθ)).
 split.
  split.
   apply matrix_of_axis_angle_is_rotation_matrix; [ easy | lra ].

   apply axis_of_matrix_is_eigen_vec; lra.

  intros n.
  destruct p as (x, y, z); simpl.
  unfold ter_bin_of_rotation.
  unfold mat_trace; simpl.
  remember (√ (x² + y² + z²)) as r eqn:Hr.
  rewrite <- Hn.
  f_equal.
  apply Rmult_eq_reg_r with (r := 4); [ | lra ].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l; [ | lra ].
  rewrite Rmult_1_r.
  do 3 rewrite fold_Rdiv.
  rename cosθ into c.
  do 2 rewrite <- Rplus_assoc.
  remember ((x / r)² * (1 - c)) as xc.
  remember ((y / r)² * (1 - c)) as yc.
  remember ((z / r)² * (1 - c)) as zc.
  replace (xc + c + yc + c + zc + c) with (xc + yc + zc + 3 * c) by ring.
  subst xc yc zc.
  do 2 rewrite <- Rmult_plus_distr_r.
  replace ((x / r)² + (y / r)² + (z / r)²) with 1.
   ring_simplify; subst c; lra.

   assert (Hrnz : r ≠ 0).
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

Theorem rotate_unicity : ∀ p₁ p₂ el,
  ‖p₁‖ = ‖p₂‖
  → norm_list el ≠ []
  → (mat_of_path el * p₁)%vec = p₁
  → (mat_of_path el * p₂)%vec = p₂
  → p₁ = p₂ ∨ p₁ = (- p₂)%vec.
Proof.
intros * Hpp Hn Hr₁ Hr₂.
remember (mat_of_path el) as M eqn:HM.
assert (H : is_rotation_matrix M ∧ M ≠ mat_id).
 split; [ subst M; apply mat_of_path_is_rotation_matrix | ].
 now rewrite HM; apply matrix_of_non_empty_path_is_not_identity.

 destruct H as (Hrm & Hni).
 destruct (Bool.bool_dec (is_neg_vec p₁) (is_neg_vec p₂)) as [Hnn| Hnn].
  destruct (vec_eq_dec p₁ p₂) as [| Hneq ]; [ now left | exfalso ].

   now specialize (fixpoint_unicity M p₁ p₂ Hrm Hni Hpp Hnn Hr₁ Hr₂).

  destruct (vec_zerop p₂) as [Hz| Hnz].
   subst p₂; rewrite vec_norm_0 in Hpp.
   apply vec_norm_eq_0 in Hpp.
   now left.

   destruct (vec_eq_dec p₁ (- p₂)%vec) as [| Hneq ]; [ now right | exfalso ].
   apply neq_negb in Hnn.
   assert (Hpp2 : ‖p₁‖ = ‖(-p₂)‖).
    rewrite Hpp; destruct p₂ as (x, y, z); simpl.
    now do 3 rewrite <- Rsqr_neg.

    rewrite <- is_neg_vec_neg_vec in Hnn; [ | easy ].
    assert (Hr₂2 : (M * - p₂ = - p₂)%vec).
     now rewrite mat_opp_vec_mul_distr_r, Hr₂.

     specialize (fixpoint_unicity M p₁ (- p₂)%vec Hrm Hni Hpp2 Hnn Hr₁ Hr₂2).
     easy.
Qed.

(* latitude of p₁ relative to p, p being the north pole;
   equal to the dot product and between -1 and 1. *)
Definition latitude p p₁ := (p · p₁) / (‖p‖ * ‖p₁‖).

Arguments latitude p%vec p₁%vec.

Theorem unit_sphere_rotation_implies_same_latitude : ∀ p p₁ p₂ c s,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → p₂ ∈ sphere 1
  → (matrix_of_axis_angle (p, s, c) * p₁ = p₂)%vec
  → latitude p p₁ = latitude p p₂.
Proof.
intros * Hp Hp₁ Hp₂ Hm.
destruct p as (x, y, z).
simpl in Hp; rewrite Rsqr_1 in Hp.
simpl in Hm; rewrite Hp, sqrt_1 in Hm.
do 3 rewrite Rdiv_1_r in Hm.
destruct p₁ as (x₁, y₁, z₁).
destruct p₂ as (x₂, y₂, z₂).
simpl in Hp₁, Hp₂; rewrite Rsqr_1 in Hp₁, Hp₂.
simpl in Hm.
injection Hm; clear Hm; intros Hz Hy Hx.
unfold latitude; simpl.
rewrite Hp, Hp₁, Hp₂, sqrt_1; f_equal.
nsatz.
Qed.

Theorem Rsign_mul_distr : ∀ x y, Rsign (x * y) = Rsign x * Rsign y.
Proof.
intros.
unfold Rsign.
destruct (Req_dec (x * y) 0) as [Hxyz| Hxyz].
 destruct (Req_dec x 0) as [Hx| Hx]; [ lra | ].
 destruct (Req_dec y 0) as [Hy| Hy]; [ lra | ].
 apply Rmult_integral in Hxyz; lra.

 destruct (Req_dec x 0) as [Hxz| Hxz]; [ rewrite Hxz in Hxyz; lra | ].
 destruct (Req_dec y 0) as [Hyz| Hyz]; [ rewrite Hyz in Hxyz; lra | ].
 destruct (Rle_dec 0 (x * y)) as [Hxy| Hxy].
  destruct (Rle_dec 0 x) as [Hx| Hx].
   destruct (Rle_dec 0 y) as [Hy| Hy]; [ lra | exfalso ].
   apply Hy; clear Hy.
   apply Rmult_le_reg_l with (r := x); [ lra | ].
   now rewrite Rmult_0_r.

   destruct (Rle_dec 0 y) as [Hy| Hy]; [ exfalso | lra ].
   apply Hx; clear Hx.
   apply Rmult_le_reg_r with (r := y); [ lra | ].
   now rewrite Rmult_0_l.

  destruct (Rle_dec 0 x) as [Hx| Hx].
   destruct (Rle_dec 0 y) as [Hy| Hy]; [ exfalso | lra ].
   apply Hxy; clear Hxy.
   now apply Rmult_le_pos.

   destruct (Rle_dec 0 y) as [Hy| Hy]; [ lra | exfalso ].
   apply Hxy; clear Hxy.
   rewrite <- Rmult_opp_opp.
   apply Rmult_le_pos; lra.
Qed.

Theorem latitude_mul : ∀ k u v,
  k ≠ 0
  → latitude (k ⁎ u) (k ⁎ v) = latitude u v.
Proof.
intros * Hr.
unfold latitude.
destruct (vec_eq_dec u 0) as [Hu| Hu].
 rewrite Hu.
 rewrite vec_const_mul_0_r.
 now do 2 rewrite vec_dot_mul_0_l, Rdiv_0_l.

 destruct (vec_eq_dec v 0) as [Hv| Hv].
  rewrite Hv.
  rewrite vec_const_mul_0_r.
  now do 2 rewrite vec_dot_mul_0_r, Rdiv_0_l.

  rewrite <- Rmult_vec_dot_mul_distr_l.
  rewrite <- Rmult_vec_dot_mul_distr_r.
  do 2 rewrite vec_norm_vec_const_mul.
  do 2 rewrite <- Rmult_assoc.
  replace (Rabs k * ‖u‖ * Rabs k) with (Rabs k * Rabs k * ‖u‖) by lra.
  rewrite <- Rabs_mult, fold_Rsqr, Rabs_sqr.
  rewrite Rmult_assoc; unfold Rdiv.
  assert (Hr2 : k² ≠ 0) by (intros H; apply Rsqr_eq_0 in H; lra).
  rewrite Rinv_mult_distr; [ | easy | ].
   rewrite <- Rmult_assoc.
   replace (k² * (u · v) * / k²) with (k² * / k² * (u · v)) by lra.
   now rewrite Rinv_r; [ rewrite Rmult_1_l | ].

   intros H; apply Rmult_integral in H.
   destruct H as [H| H]; now apply vec_norm_eq_0 in H.
Qed.

Theorem rotation_implies_same_latitude : ∀ r p p₁ p₂ c s,
  0 < r
  → p ∈ sphere r
  → p₁ ∈ sphere r
  → p₂ ∈ sphere r
  → (matrix_of_axis_angle (p, s, c) * p₁ = p₂)%vec
  → latitude p p₁ = latitude p p₂.
Proof.
intros * Hr Hp Hp₁ Hp₂ Hm.
apply vec_div_in_sphere in Hp; [ | lra ].
apply vec_div_in_sphere in Hp₁; [ | lra ].
apply vec_div_in_sphere in Hp₂; [ | lra ].
assert
  (Hmm :
     ((matrix_of_axis_angle (/ r ⁎ p, s, c) * (/ r ⁎ p₁))%vec = / r ⁎ p₂)).
 rewrite matrix_mul_axis with (k := r); [ | lra ].
 rewrite vec_const_mul_assoc.
 rewrite Rinv_r; [ rewrite vec_const_mul_1_l | lra ].
 rewrite Rsign_of_pos; [ rewrite Rmult_1_l | easy ].
 rewrite mat_vec_mul_const_distr.
 now rewrite Hm.

 assert (Hir : / r ≠ 0) by (apply Rinv_neq_0_compat; lra).
 specialize
   (unit_sphere_rotation_implies_same_latitude (/ r ⁎ p) (/ r ⁎ p₁) (/ r ⁎ p₂) c
      s Hp Hp₁ Hp₂ Hmm) as Hll.
 now do 2 rewrite latitude_mul in Hll.
Qed.

Theorem latitude_norm : ∀ p p₁ v a,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → a = latitude p p₁
  → v = (p₁ - a ⁎ p)%vec
  → ‖v‖ = √ (1 - a²).
Proof.
intros * Hp Hp₁ Ha₁ Hv.
apply on_sphere_norm; [ apply sqrt_pos | ].
destruct v as (xv, yv, zv); simpl.
unfold latitude in Ha₁; simpl in Ha₁.
destruct p as (x, y, z).
destruct p₁ as (x₁, y₁, z₁).
simpl in Hp, Hp₁; simpl.
rewrite Rsqr_1 in Hp, Hp₁.
simpl in Hv.
do 3 rewrite fold_Rminus in Hv.
simpl in Ha₁.
injection Hv; clear Hv; intros Hzq Hyq Hxv.
rewrite Hxv, Hyq, Hzq; simpl.
unfold Rsqr; simpl.
ring_simplify.
progress repeat rewrite <- Rsqr_pow2.
replace z₁² with (1 - x₁² - y₁²) by lra.
ring_simplify.
progress replace (-2 * x₁ * a * x - 2 * a * y₁ * y - 2 * a * z₁ * z)
with (-2 * a * (x * x₁ + y * y₁ + z * z₁)) by lra.
rewrite Hp, Hp₁, sqrt_1, Rmult_1_l, Rdiv_1_r in Ha₁.
rewrite <- Ha₁.
do 3 rewrite Rplus_assoc; rewrite Rplus_comm.
do 2 rewrite <- Rplus_assoc.
do 2 rewrite <- Rmult_plus_distr_l.
rewrite Hp, Rmult_1_r.
rewrite Rsqr_sqrt; [ unfold Rsqr; lra | ].
rewrite fold_Rsqr.
specialize (vec_Lagrange_identity (V x y z) (V x₁ y₁ z₁)) as H.
remember (V x y z × V x₁ y₁ z₁) as c eqn:Hc.
simpl in H.
rewrite Hp, Hp₁ in H.
rewrite sqrt_1, Rsqr_1, Rmult_1_l in H.
rewrite <- Ha₁ in H.
rewrite H; clear H.
rewrite vec_dot_mul_diag.
apply Rle_0_sqr.
Qed.

Theorem rotate_matrix_of_two_vectors : ∀ p v₁ v₂ c s,
  ‖v₁‖ = 1
  → ‖v₂‖ = 1
  → p = v₁ × v₂
  → p ≠ 0%vec
  → c = (v₁ · v₂)
  → s = ‖p‖
  → (matrix_of_axis_angle (p, s, c) * v₁)%vec = v₂.
Proof.
intros * Hv₁ Hv₂ Hp Hpz Hc Hs.
assert (Hcs : c² + s² = 1).
 specialize (vec_Lagrange_identity v₁ v₂) as H.
 rewrite vec_dot_mul_diag in H.
 rewrite Hv₁, Hv₂ in H.
 rewrite Rsqr_1, Rmult_1_r in H.
 rewrite <- Hc, <- Hp, <- Hs in H; lra.

 destruct p as (xp, yp, zp).
 destruct v₁ as (x₁, y₁, z₁).
 destruct v₂ as (x₂, y₂, z₂); simpl.
 simpl in Hp.
 injection Hp; clear Hp; intros Hzp Hyp Hxp.
 simpl in Hv₁, Hv₂, Hc, Hs.
 apply (f_equal Rsqr) in Hv₁.
 apply (f_equal Rsqr) in Hv₂.
 rewrite Rsqr_sqrt in Hv₁; [ | apply nonneg_sqr_vec_norm ].
 rewrite Rsqr_sqrt in Hv₂; [ | apply nonneg_sqr_vec_norm ].
 rewrite Rsqr_1 in Hv₁, Hv₂.
 rewrite <- Hs.
 assert (Hsz : s ≠ 0).
  intros H; rewrite Hs in H.
  apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
  apply sqr_vec_norm_eq_0 in H.
  destruct H as (H1 & H2 & H3).
  now rewrite H1, H2, H3 in Hpz.

  rewrite Rmult_div_same; [ | easy ].
  rewrite Rmult_div_same; [ | easy ].
  rewrite Rmult_div_same; [ | easy ].
  assert (H : xp * x₁ + yp * y₁ + zp * z₁ = 0) by (subst; lra).
  rewrite Rsqr_div; [ | easy ].
  rewrite Rsqr_div; [ | easy ].
  rewrite Rsqr_div; [ | easy ].
  unfold Rsqr, Rdiv.
  rewrite Rinv_mult_distr; [ | lra | lra ].
  do 4 rewrite fold_Rdiv.
  progress replace
    ((xp * xp * (/ s / s) * (1 - c) + c) * x₁ +
     (xp / s * (yp / s) * (1 - c) - zp) * y₁ +
     (xp / s * (zp / s) * (1 - c) + yp) * z₁)
  with
    (xp * (1 - c) * (xp * x₁ + yp * y₁ + zp * z₁) * (/ s / s) +
     c * x₁ - zp * y₁ + yp * z₁) by lra.
  progress replace
    ((xp / s * (yp / s) * (1 - c) + zp) * x₁ +
     (yp * yp * (/ s / s) * (1 - c) + c) * y₁ +
     (yp / s * (zp / s) * (1 - c) - xp) * z₁)
  with
    (yp * (1 - c) * (xp * x₁ + yp * y₁ + zp * z₁) * (/ s / s) +
     zp * x₁ + c * y₁ - xp * z₁) by lra.
  replace
    ((xp / s * (zp / s) * (1 - c) - yp) * x₁ +
     (yp / s * (zp / s) * (1 - c) + xp) * y₁ +
     (zp * zp * (/ s / s) * (1 - c) + c) * z₁)
  with
    (zp * (1 - c) * (xp * x₁ + yp * y₁ + zp * z₁) * (/ s / s) +
     - yp * x₁ + xp * y₁ + c * z₁) by lra.
  rewrite H, Rmult_0_r, Rmult_0_l, Rplus_0_l; clear H.
  do 2 rewrite Rmult_0_r, Rmult_0_l, Rplus_0_l.
  rewrite Hc, Hyp, Hzp.
  do 3 rewrite Rsqr_pow2 in Hv₁.
  f_equal.
   ring_simplify.
   rewrite Rmult_comm.
   do 2 rewrite <- Rmult_plus_distr_l.
   now rewrite Hv₁, Rmult_1_r.

   ring_simplify.
   rewrite Rmult_comm, <- Rmult_plus_distr_l.
   replace (x₁ ^ 2 + y₁ ^ 2) with (1 - z₁ ^ 2) by lra.
   now rewrite Hxp; ring_simplify.

   ring_simplify.
   replace (z₁ ^ 2) with (1 - x₁ ^ 2 - y₁ ^ 2) by lra.
   now rewrite Hxp; ring_simplify.
Qed.

Theorem vec_cross_mul_cross_mul : ∀ u v,
  u · v = 0
  → ‖v‖ = 1
  → (u × v) × v = (- u)%vec.
Proof.
intros (u₁, u₂, u₃) (v₁, v₂, v₃) Huv Hv; simpl in Huv, Hv; simpl.
apply (f_equal Rsqr) in Hv.
rewrite Rsqr_1 in Hv.
rewrite Rsqr_sqrt in Hv; [ | apply nonneg_sqr_vec_norm ].
f_equal; ring_simplify.
 do 2 rewrite <- Rsqr_pow2; nsatz.
 do 2 rewrite <- Rsqr_pow2; nsatz.
 do 2 rewrite <- Rsqr_pow2; nsatz.
Qed.

Theorem unit_sphere_eigenvalue_minus_1_angle_π : ∀ axis sinθ cosθ v,
  axis ∈ sphere 1
  → v ∈ sphere 1
  → (matrix_of_axis_angle (axis, sinθ, cosθ) * v)%vec = (- v)%vec
  → (sinθ, cosθ) = (0, -1).
Proof.
intros * Ha Hv Hmv.
destruct axis as (xa, ya, za).
destruct v as (x, y, z).
simpl in *.
rewrite Rsqr_1 in Ha, Hv.
rewrite Ha, sqrt_1 in Hmv.
do 3 rewrite Rdiv_1_r in Hmv.
injection Hmv; clear Hmv; intros H3 H2 H1.
unfold Rsqr in *.
f_equal; nsatz.
Qed.

Definition rot_sin_cos p u v :=
  let a := latitude p u in
  let u₁ := (u - a ⁎ p) ⁄ √ (1 - a²) in
  let v₁ := (v - a ⁎ p) ⁄ √ (1 - a²) in
  let s := Rsign (p · (u₁ × v₁)) * ‖(u₁ × v₁)‖ / (‖u₁‖ * ‖v₁‖) in
  let c := (u₁ · v₁) / (‖u₁‖ * ‖v₁‖) in
  (s, c).

Theorem simple_unit_sphere_ro_sin_cos_on_equator : ∀ p p₁ p₂ c s,
  ‖p‖ = 1
  → ‖p₁‖ = 1
  → ‖p₂‖ = 1
  → p · p₁ = 0
  → p · p₂ = 0
  → (matrix_of_axis_angle (p, s, c) * p₁)%vec = p₂
  → (s, c) = (p · p₁ × p₂, p₁ · p₂).
Proof.
intros * Hp Hp₁ Hp₂ Ha₁ Ha₂ Hmv.
destruct p as (xp, yp, zp).
destruct p₁ as (xp₁, yp₁, zp₁).
destruct p₂ as (xp₂, yp₂, zp₂).
apply on_sphere_norm in Hp; [ | lra ].
apply on_sphere_norm in Hp₁; [ | lra ].
apply on_sphere_norm in Hp₂; [ | lra ].
simpl in *.
rewrite Rsqr_1 in Hp, Hp₁, Hp₂.
rewrite Hp, sqrt_1 in Hmv.
do 3 rewrite Rdiv_1_r in Hmv.
injection Hmv; clear Hmv; intros H3 H2 H1.
Time f_equal; nsatz.
Qed.

Theorem unit_sphere_rot_sin_cos_on_equator : ∀ p p₁ p₂ c s,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → p₂ ∈ sphere 1
  → latitude p p₁ = 0
  → latitude p p₂ = 0
  → p₁ × p₂ ≠ 0%vec
  → (matrix_of_axis_angle (p, s, c) * p₁)%vec = p₂
  → (s, c) = rot_sin_cos p p₁ p₂.
Proof.
intros * Hp Hp₁ Hp₂ Ha₁ Ha₂ Hppz Hmv.
unfold rot_sin_cos.
rewrite Ha₁, vec_const_mul_0_l, Rsqr_0, Rminus_0_r.
do 2 rewrite vec_sub_0_r.
rewrite sqrt_1, Rinv_1.
do 2 rewrite vec_const_mul_1_l.
apply on_sphere_norm in Hp; [ | lra ].
apply on_sphere_norm in Hp₁; [ | lra ].
apply on_sphere_norm in Hp₂; [ | lra ].
rewrite Hp₁, Hp₂.
rewrite Rmult_1_l, Rdiv_1_r, Rdiv_1_r.
unfold latitude in Ha₁, Ha₂.
rewrite Hp, Hp₁ in Ha₁.
rewrite Hp, Hp₂ in Ha₂.
rewrite Rmult_1_l, Rdiv_1_r in Ha₁, Ha₂.
specialize (vec_Lagrange_identity p (p₁ × p₂)) as Hlag.
rewrite vec_cross_mul_assoc_r in Hlag.
rewrite Hp, Rsqr_1, Rmult_1_l in Hlag.
rewrite Ha₁, Ha₂ in Hlag.
do 2 rewrite vec_const_mul_0_l in Hlag.
rewrite vec_sub_0_r, vec_sqr_0 in Hlag.
apply Rminus_diag_uniq in Hlag.
unfold Rsign.
destruct (Req_dec (p · p₁ × p₂) 0) as [Hppp| Hppp].
 exfalso.
 rewrite Hppp in Hlag.
 rewrite Rsqr_0 in Hlag.
 now apply Rsqr_eq_0, vec_norm_eq_0 in Hlag.

 apply Rsqr_eq_abs_0 in Hlag.
 rewrite Rabs_right in Hlag; [ | apply Rle_ge, vec_norm_nonneg ].
 destruct (Rle_dec 0 (p · p₁ × p₂)) as [Hzpp| Hzpp].
  rewrite Rmult_1_l.
  rewrite Rabs_right in Hlag; [ | now apply Rle_ge ].
  rewrite Hlag; clear Hlag Hzpp Hppp Hppz.
  now apply simple_unit_sphere_ro_sin_cos_on_equator.

  apply Rnot_le_lt in Hzpp.
  rewrite <- Ropp_mult_distr_l, Rmult_1_l.
  rewrite Rabs_left in Hlag; [ | easy ].
  rewrite Hlag, Ropp_involutive; clear Hlag Hzpp Hppp Hppz.
  now apply simple_unit_sphere_ro_sin_cos_on_equator.
Qed.

Theorem vec_unit_cross_mul_eq_0 : ∀ u v,
  ‖u‖ = 1
  → ‖v‖ = 1
  → u × v = 0%vec
  → u = v ∨ u = (- v)%vec.
Proof.
intros * Hu Hv Huxv.
specialize (vec_Lagrange_identity u v) as H.
rewrite Hu, Hv, Huxv, vec_sqr_0 in H.
rewrite Rsqr_1, Rmult_1_l in H.
apply Rminus_diag_uniq in H; symmetry in H.
destruct u as (u₁, u₂, u₃).
destruct v as (v₁, v₂, v₃).
apply on_sphere_norm in Hu; [ | lra ].
apply on_sphere_norm in Hv; [ | lra ].
simpl in *.
rewrite Rsqr_1 in Hu, Hv.
injection Huxv; clear Huxv; intros H3 H2 H1.
apply Rminus_diag_uniq in H1.
apply Rminus_diag_uniq in H2.
apply Rminus_diag_uniq in H3.
replace 1 with 1² in H by apply Rsqr_1.
apply Rsqr_eq_abs_0 in H.
rewrite Rabs_R1 in H.
unfold Rabs in H.
destruct (Rcase_abs (u₁ * v₁ + u₂ * v₂ + u₃ * v₃)) as [Ha| Ha].
 right; clear Ha.
 f_equal; nsatz.

 left; clear Ha.
 f_equal; nsatz.
Qed.

Theorem vec_same_norm_cross_mul_eq_0 : ∀ u v,
  ‖u‖ = ‖v‖
  → u × v = 0%vec
  → u = v ∨ u = (- v)%vec.
Proof.
intros * Huv Huxv.
destruct (vec_eq_dec u 0) as [Hu| Hu].
 rewrite Hu, vec_norm_0 in Huv; symmetry in Huv.
 now apply vec_norm_eq_0 in Huv; subst u v; left.

 remember ‖u‖ as r eqn:Hr.
 assert (Hrz : r ≠ 0).
  intros H; rewrite H in Hr; symmetry in Hr.
  now apply vec_norm_eq_0 in Hr.

  assert (‖(u ⁄ r)‖ = 1 ∧ ‖(v ⁄ r)‖ = 1) as (Hu1, Hv1).
   do 2 rewrite vec_norm_vec_const_mul.
   rewrite <- Hr, <- Huv.
   rewrite Rabs_right; [ now split; rewrite Rinv_l | ].
   apply Rle_ge.
   assert (Hrp : 0 ≤ r) by (rewrite Hr; apply vec_norm_nonneg).
   apply Rmult_le_reg_r with (r := r); [ lra | ].
   rewrite Rmult_0_l.
   rewrite Rinv_l; [ lra | easy ].

   assert (Huvr : (u ⁄ r) × (v ⁄ r) = 0%vec).
    rewrite <- vec_const_mul_cross_distr_l.
    rewrite <- vec_const_mul_cross_distr_r.
    rewrite Huxv.
    now do 2 rewrite vec_const_mul_0_r.

    specialize (vec_unit_cross_mul_eq_0 (u ⁄ r) (v ⁄ r) Hu1 Hv1 Huvr) as H.
    destruct H as [H| H]; [ left | right ].
     apply vec_const_mul_eq_reg_l with (a := / r); [ easy | ].
     now apply Rinv_neq_0_compat.

     rewrite vec_opp_const_mul_distr_r in H.
     apply vec_const_mul_eq_reg_l with (a := / r); [ easy | ].
     now apply Rinv_neq_0_compat.
Qed.

Theorem sqr_latitude_le_1 : ∀ p p₁, (latitude p p₁)² ≤ 1.
Proof.
intros.
destruct (vec_eq_dec p 0) as [Hp| Hp].
 unfold latitude.
 destruct p₁ as (x, y, z).
 rewrite Hp; simpl.
 do 3 rewrite Rmult_0_l.
 do 2 rewrite Rplus_0_l.
 rewrite Rdiv_0_l, Rsqr_0; lra.

 destruct (vec_eq_dec p₁ 0) as [Hp₁| Hp₁].
  unfold latitude.
  destruct p as (x, y, z).
  rewrite Hp₁; simpl.
  do 3 rewrite Rmult_0_r.
  do 2 rewrite Rplus_0_l.
  rewrite Rdiv_0_l, Rsqr_0; lra.

  unfold latitude.
  rewrite Rsqr_div.
   apply Rmult_le_reg_r with (r := (‖p‖ * ‖p₁‖)²).
    rewrite Rsqr_mult.
    apply Rmult_lt_0_compat.
    1, 2: now apply Rlt_0_sqr; intros H; apply vec_norm_eq_0 in H.

    rewrite Rmult_div_same.
     rewrite Rmult_1_l, Rsqr_mult.
     apply vec_Cauchy_Schwarz_inequality.

     rewrite Rsqr_mult.
     intros H; apply Rmult_integral in H.
     destruct H as [H| H].
     1, 2: now apply Rsqr_eq_0, vec_norm_eq_0 in H.

    intros H; apply Rmult_integral in H.
    now destruct H; apply vec_norm_eq_0 in H.
Qed.

Theorem unit_sphere_mat_vec_mul_rot_sin_cos : ∀ p p₁ p₂ a c s,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → p₂ ∈ sphere 1
  → latitude p p₁ = a
  → latitude p p₂ = a
  → a² ≠ 1
  → s² + c² = 1
  → (matrix_of_axis_angle (p, s, c) * p₁)%vec = p₂
  → (s, c) = rot_sin_cos p p₁ p₂.
Proof.
intros * Hp Hp₁ Hp₂ Ha₁ Ha₂ Ha2 Hsc Hmv.
assert (H : a² < 1).
 specialize (sqr_latitude_le_1 p p₁) as H.
 rewrite Ha₁ in H; lra.

 clear Ha2; rename H into Ha2.
 unfold rot_sin_cos.
 rewrite Ha₁.
 remember (p₁ - a ⁎ p)%vec as v₁ eqn:Hv₁.
 remember (p₂ - a ⁎ p)%vec as v₂ eqn:Hv₂.
 remember (v₁ ⁄ √ (1 - a²)) as v'₁ eqn:Hv'₁.
 remember (v₂ ⁄ √ (1 - a²)) as v'₂ eqn:Hv'₂.
 move v₁ before p₂; move v₂ before v₁.
 move v'₁ before v₂; move v'₂ before v'₁.
 assert (Hsa : √ (1 - a²) ≠ 0) by (intros H; apply sqrt_eq_0 in H; lra).
 assert (‖v'₁‖ = 1 ∧ ‖v'₂‖ = 1) as (Hnv'₁, Hnv'₂).
  subst v₁ v₂.
  symmetry in Ha₁, Ha₂.
  eapply latitude_norm in Ha₁; [ | easy | easy | reflexivity ].
  eapply latitude_norm in Ha₂; [ | easy | easy | reflexivity ].
  rewrite Hv'₁, Hv'₂.
  do 2 rewrite vec_norm_vec_const_mul.
  rewrite Rabs_Rinv; [ | easy ].
  rewrite Rabs_sqrt, Ha₁, Ha₂.
  now rewrite Rinv_l.

  assert (‖v₁‖² = 1 - a² ∧ ‖v₂‖² = 1 - a²) as (Hnv₁, Hnv₂).
   rewrite Hv'₁ in Hnv'₁.
   rewrite Hv'₂ in Hnv'₂.
   apply (f_equal Rsqr) in Hnv'₁.
   apply (f_equal Rsqr) in Hnv'₂.
   rewrite <- vec_dot_mul_diag, Rsqr_1 in Hnv'₁, Hnv'₂.
   rewrite vec_sqr_const_mul in Hnv'₁, Hnv'₂.
   rewrite vec_dot_mul_diag in Hnv'₁, Hnv'₂.
   rewrite Rsqr_inv in Hnv'₁; [ | easy ].
   rewrite Rsqr_inv in Hnv'₂; [ | easy ].
   rewrite Rsqr_sqrt in Hnv'₁; [ | lra ].
   rewrite Rsqr_sqrt in Hnv'₂; [ | lra ].
   apply Rmult_eq_compat_l with (r := 1 - a²) in Hnv'₁.
   apply Rmult_eq_compat_l with (r := 1 - a²) in Hnv'₂.
   rewrite <- Rmult_assoc, Rmult_1_r in Hnv'₁, Hnv'₂.
   rewrite Rinv_r in Hnv'₁; [ | lra ].
   rewrite Rinv_r in Hnv'₂; [ | lra ].
   now rewrite Rmult_1_l in Hnv'₁, Hnv'₂.

   rewrite Hnv'₁, Hnv'₂, Rmult_1_l, Rdiv_1_r, Rdiv_1_r.
   assert (H : (1 - a²) * c - v₁ · v₂ = 0).
    subst v₁ v₂.
    destruct p as (xp, yp, zp).
    destruct p₁ as (xp₁, yp₁, zp₁).
    destruct p₂ as (xp₂, yp₂, zp₂).
    unfold latitude in Ha₁, Ha₂; simpl in *.
    rewrite Rsqr_1 in Hp, Hp₁, Hp₂.
    rewrite Hp, Hp₁ in Ha₁.
    rewrite Hp, Hp₂ in Ha₂.
    rewrite Hp in Hmv.
    rewrite sqrt_1 in Ha₁, Ha₂, Hmv.
    rewrite Rmult_1_l, Rdiv_1_r in Ha₁, Ha₂.
    do 3 rewrite Rdiv_1_r in Hmv.
    rewrite Rsqr_sqrt in Hnv₁; [ | apply nonneg_sqr_vec_norm ].
    rewrite Rsqr_sqrt in Hnv₂; [ | apply nonneg_sqr_vec_norm ].
    clear - Ha₁ Ha₂ Hnv₁ Hnv₂ Hmv.
    injection Hmv; clear Hmv; intros H3 H2 H1.
    Time nsatz.

    assert (Hc : c = v'₁ · v'₂).
     rewrite Hv'₁, Hv'₂.
     rewrite <- Rmult_vec_dot_mul_distr_l.
     rewrite <- Rmult_vec_dot_mul_distr_r.
     rewrite <- Rmult_assoc.
     rewrite fold_Rsqr.
     rewrite Rsqr_inv; [ | easy ].
     rewrite Rsqr_sqrt; [ | lra ].
     apply Rmult_eq_reg_l with (r := 1 - a²); [ | lra ].
     rewrite <- Rmult_assoc.
     rewrite Rinv_r; lra.

     f_equal; [ | easy ].
     assert (p · v'₁ = 0 ∧ p · v'₂ = 0) as (Hpv₁, Hpv₂).
      subst v'₁ v'₂ v₁ v₂.
      do 2 rewrite <- Rmult_vec_dot_mul_distr_r.
      do 2 rewrite vec_dot_mul_sub_distr_l.
      rewrite <- Rmult_vec_dot_mul_distr_r.
      apply on_sphere_norm in Hp; [ | lra ].
      apply on_sphere_norm in Hp₁; [ | lra ].
      apply on_sphere_norm in Hp₂; [ | lra ].
      split.
       apply Rmult_eq_0_compat_l.
       rewrite <- Ha₁; unfold latitude.
       rewrite vec_dot_mul_diag, Hp, Hp₁, Rsqr_1.
       rewrite Rmult_1_r, Rmult_1_r, Rdiv_1_r.
       now rewrite Rminus_diag_eq.

       apply Rmult_eq_0_compat_l.
       rewrite <- Ha₂; unfold latitude.
       rewrite vec_dot_mul_diag, Hp, Hp₂, Rsqr_1.
       rewrite Rmult_1_r, Rmult_1_r, Rdiv_1_r.
       now rewrite Rminus_diag_eq.

      assert (Hppvv : (p₂ - p₁ = v₂ - v₁)%vec).
       rewrite Hv₁, Hv₂.
       rewrite vec_sub_sub_distr.
       unfold vec_sub.
       do 2 rewrite <- vec_add_assoc.
       f_equal.
       rewrite vec_add_comm.
       rewrite <- vec_add_assoc.
       rewrite vec_add_opp_diag_r.
       now rewrite vec_add_0_r.

       specialize (vec_Lagrange_identity p (v'₁ × v'₂)) as Hlag.
       apply on_sphere_norm in Hp; [ | lra ].
       rewrite Hp, Rsqr_1, Rmult_1_l in Hlag.
       rewrite vec_cross_mul_assoc_r in Hlag.
       rewrite Hpv₁, Hpv₂ in Hlag.
       do 2 rewrite vec_const_mul_0_l in Hlag.
       rewrite vec_sub_0_r, vec_sqr_0 in Hlag.
       apply Rminus_diag_uniq in Hlag.
       apply Rsqr_eq_abs_0 in Hlag.
       rewrite Rabs_right in Hlag; [ | apply Rle_ge, vec_norm_nonneg ].
       rewrite Hlag.
       unfold Rsign.
       rewrite Hv'₁, Hv'₂ in Hlag at 1.
       rewrite <- vec_const_mul_cross_distr_l in Hlag.
       rewrite <- vec_const_mul_cross_distr_r in Hlag.
       rewrite vec_const_mul_assoc in Hlag.
       rewrite fold_Rsqr in Hlag.
       rewrite Rsqr_inv in Hlag; [ | easy ].
       rewrite Rsqr_sqrt in Hlag; [ | lra ].
       rewrite vec_norm_vec_const_mul in Hlag.
       rewrite Rabs_Rinv in Hlag; [ | lra ].
       rewrite Rabs_right in Hlag; [ | lra ].
       destruct (Req_dec (p · v'₁ × v'₂) 0) as [Hppp| Hppp].
        rewrite Rmult_0_l.
        rewrite Hppp, Rabs_R0 in Hlag.
        apply Rmult_integral in Hlag.
        destruct Hlag as [Hlag| Hlag].
         apply Rinv_neq_0_compat in Hlag; [ easy | lra ].

         rewrite <- Hnv₁ in Hnv₂; symmetry in Hnv₂.
         apply Rsqr_inj in Hnv₂; try apply vec_norm_nonneg.
         apply vec_norm_eq_0 in Hlag.
         apply vec_same_norm_cross_mul_eq_0 in Hlag; [ | easy ].
         destruct Hlag as [Hlag| Hlag].
          move Hlag at top; subst v₂.
          rewrite vec_sub_diag in Hppvv.
          apply vec_sub_diag_uniq in Hppvv.
          move Hppvv at top; subst p₂.
          rewrite <- Hv'₁ in Hv'₂.
          move Hv'₂ at top; subst v'₂.
          rewrite vec_dot_mul_diag, Hnv'₁, Rsqr_1 in Hc.
          clear - Hsc Hc; subst c.
          rewrite Rsqr_1 in Hsc.
          apply Rsqr_eq_0; lra.

          apply (f_equal vec_opp) in Hlag.
          rewrite neg_vec_involutive in Hlag.
          move Hlag at top; subst v₂.
          rewrite <- vec_opp_const_mul_distr_r, <- Hv'₁ in Hv'₂.
          move Hv'₂ at top; subst v'₂.
          rewrite <- vec_opp_dot_mul_distr_r in Hc.
          rewrite vec_dot_mul_diag, Hnv'₁, Rsqr_1 in Hc.
          clear - Hsc Hc; subst c.
          rewrite <- Rsqr_neg, Rsqr_1 in Hsc.
          apply Rsqr_eq_0; lra.

        assert (Hs : s = p · v'₁ × v'₂).
         rewrite Hv'₁, Hv'₂.
         rewrite <- vec_const_mul_cross_distr_l.
         rewrite <- vec_const_mul_cross_distr_r.
         rewrite vec_const_mul_assoc.
         rewrite fold_Rsqr.
         rewrite Rsqr_inv; [ | easy ].
         rewrite Rsqr_sqrt; [ | lra ].
         apply Rmult_eq_reg_l with (r := 1 - a²); [ | lra ].
         rewrite <- Rmult_vec_dot_mul_distr_r.
         rewrite <- Rmult_assoc.
         rewrite Rinv_r; [ | lra ].
         rewrite Rmult_1_l.
         clear v'₁ v'₂ Hv'₁ Hv'₂ Hnv'₁ Hnv'₂ Hc Hpv₁ Hpv₂ Hlag Hppp.
         clear Ha2 Hsa Hppvv.
         subst v₁ v₂.
         destruct p as (xp, yp, zp).
         destruct p₁ as (xp₁, yp₁, zp₁).
         destruct p₂ as (xp₂, yp₂, zp₂).
         apply on_sphere_norm in Hp; [ | lra ].
         unfold latitude in Ha₁, Ha₂; simpl in *.
         rewrite Rsqr_1 in Hp, Hp₁, Hp₂.
         rewrite Hp, Hp₁ in Ha₁.
         rewrite Hp, Hp₂ in Ha₂.
         rewrite Hp in Hmv.
         clear Hp₁ Hp₂ Hsc H.
         rewrite sqrt_1 in Ha₁, Ha₂, Hmv.
         rewrite Rmult_1_l, Rdiv_1_r in Ha₁, Ha₂.
         do 3 rewrite Rdiv_1_r in Hmv.
         rewrite Rsqr_sqrt in Hnv₁; [ | apply nonneg_sqr_vec_norm ].
         rewrite Rsqr_sqrt in Hnv₂; [ | apply nonneg_sqr_vec_norm ].
         do 6 rewrite fold_Rminus.
         do 3 rewrite fold_Rminus in Hnv₁, Hnv₂.
         injection Hmv; clear Hmv; intros H3 H2 H1.
         Time nsatz.

         destruct (Rle_dec 0 (p · v'₁ × v'₂)) as [Hpvv| Hpvv].
          rewrite Rmult_1_l.
          now rewrite Rabs_right; [ | apply Rle_ge ].

          apply Rnot_le_lt in Hpvv.
          rewrite Rabs_left; [ | easy ].
          now rewrite <- Ropp_mult_distr_l, Rmult_1_l, Ropp_involutive.
Qed.

Theorem mat_vec_mul_rot_sin_cos : ∀ r p p₁ p₂ a c s,
  0 < r
  → p ∈ sphere r
  → p₁ ∈ sphere r
  → p₂ ∈ sphere r
  → latitude p p₁ = a
  → latitude p p₂ = a
  → a² ≠ 1
  → s² + c² = 1
  → (matrix_of_axis_angle (p, s, c) * p₁)%vec = p₂
  → (s, c) = rot_sin_cos p p₁ p₂.
Proof.
intros * Hr Hp Hp₁ Hp₂ Ha₁ Ha₂ Ha2 Hsc Hmv.
assert (Hpr : ∀ p, p ∈ sphere r → p ⁄ r ∈ sphere 1).
 clear - Hr; intros.
 apply vec_div_in_sphere; [ lra | easy ].

 assert (Ha : ∀ p p', latitude p p' = latitude (p ⁄ r) (p' ⁄ r)).
  clear - Hr; intros.
  rewrite latitude_mul; [ easy | ].
  apply Rinv_neq_0_compat; lra.

  rewrite Ha in Ha₁, Ha₂.
  apply (f_equal (vec_const_mul (/ r))) in Hmv.
  rewrite <- mat_vec_mul_const_distr in Hmv.
  assert (Hir : / r ≠ 0) by (apply Rinv_neq_0_compat; lra).
  rewrite matrix_mul_axis with (k := / r) in Hmv; [ | easy ].
  assert (Hirp : 0 < / r) by now apply Rinv_0_lt_compat.
  rewrite Rsign_of_pos in Hmv; [ | easy ].
  rewrite Rmult_1_l in Hmv.
  specialize
    (unit_sphere_mat_vec_mul_rot_sin_cos (p ⁄ r) (p₁ ⁄ r) (p₂ ⁄ r) a c s
       (Hpr p Hp) (Hpr p₁ Hp₁) (Hpr p₂ Hp₂) Ha₁ Ha₂ Ha2 Hsc Hmv) as H.
  rewrite H.
  unfold rot_sin_cos; rewrite Ha₁.
  rewrite Ha, Ha₁.
  remember ((p₁ - a ⁎ p) ⁄ √ (1 - a²)) as u₁ eqn:Hu₁.
  remember ((p₂ - a ⁎ p) ⁄ √ (1 - a²)) as u₂ eqn:Hu₂.
  remember ((p₁ ⁄ r - a ⁎ (p ⁄ r)) ⁄ √ (1 - a²)) as v₁ eqn:Hv₁.
  remember ((p₂ ⁄ r - a ⁎ (p ⁄ r)) ⁄ √ (1 - a²)) as v₂ eqn:Hv₂.
  move u₂ before u₁; move v₁ before u₂; move v₂ before v₁.
  rewrite vec_const_mul_assoc in Hv₁, Hv₂.
  rewrite Rmult_comm in Hv₁, Hv₂.
  rewrite <- vec_const_mul_assoc in Hv₁, Hv₂.
  rewrite <- vec_const_mul_sub_distr_l in Hv₁, Hv₂.
  rewrite vec_const_mul_assoc in Hv₁, Hv₂.
  rewrite Rmult_comm in Hv₁, Hv₂.
  rewrite <- vec_const_mul_assoc in Hv₁, Hv₂.
  rewrite <- Hu₁ in Hv₁.
  rewrite <- Hu₂ in Hv₂.
  subst v₁ v₂.
  rewrite <- vec_const_mul_cross_distr_l.
  rewrite <- vec_const_mul_cross_distr_r.
  rewrite vec_const_mul_assoc.
  rewrite <- Rmult_vec_dot_mul_distr_r.
  rewrite fold_Rsqr.
  assert (H' : a² < 1).
   specialize (sqr_latitude_le_1 (p ⁄ r) (p₁ ⁄ r)) as H'.
   rewrite Ha₁ in H'; lra.

   clear Ha2; rename H' into Ha2.
   assert (Hsa : √ (1 - a²) ≠ 0) by (intros J; apply sqrt_eq_0 in J; lra).
   assert (‖u₁‖ = r ∧ ‖u₂‖ = r) as (Hnu₁, Hnu₂).
    subst u₁ u₂.
    symmetry in Ha₁, Ha₂.
    apply Hpr in Hp.
    apply Hpr in Hp₁.
    apply Hpr in Hp₂.
    eapply latitude_norm in Ha₁; [ | easy | easy | reflexivity ].
    eapply latitude_norm in Ha₂; [ | easy | easy | reflexivity ].
    do 2 rewrite vec_norm_vec_const_mul.
    rewrite vec_const_mul_assoc, Rmult_comm in Ha₁, Ha₂.
    rewrite <- vec_const_mul_assoc in Ha₁, Ha₂.
    rewrite <- vec_const_mul_sub_distr_l in Ha₁, Ha₂.
    rewrite vec_norm_vec_const_mul in Ha₁, Ha₂.
    rewrite Rabs_Rinv in Ha₁, Ha₂; [ | lra | lra ].
    rewrite Rabs_right in Ha₁, Ha₂; [ | lra | lra ].
    apply (f_equal (Rmult r)) in Ha₁.
    apply (f_equal (Rmult r)) in Ha₂.
    rewrite <- Rmult_assoc in Ha₁, Ha₂.
    rewrite Rinv_r in Ha₁, Ha₂; [ | lra | lra ].
    rewrite Rmult_1_l in Ha₁, Ha₂.
    rewrite Rabs_Rinv; [ | easy ].
    rewrite Rabs_sqrt, Ha₁, Ha₂.
    rewrite <- Rmult_assoc, Rmult_shuffle0.
    rewrite Rinv_l; [ lra | easy ].

    f_equal.
     do 2 rewrite <- Rdiv_mult.
     f_equal.
      rewrite Rsign_mul_distr.
      rewrite Rsign_of_pos; [ | now apply Rlt_0_sqr ].
      rewrite <- Rmult_vec_dot_mul_distr_l.
      rewrite Rsign_mul_distr.
      rewrite Rsign_of_pos; [ | now apply Rinv_0_lt_compat ].
      now do 2 rewrite Rmult_1_l.

      do 3 rewrite vec_norm_vec_const_mul.
      rewrite Rabs_sqr.
      rewrite Rabs_right; [ | lra ].
      rewrite Rmult_shuffle0.
      rewrite <- Rmult_assoc.
      rewrite fold_Rsqr.
      rewrite Rmult_assoc.
      rewrite Rdiv_mult_simpl_l; [ f_equal; lra | | ].
       now intros H1; apply Rsqr_eq_0 in H1.

       rewrite Hnu₁, Hnu₂, fold_Rsqr.
       intros J; apply Rsqr_eq_0 in J; lra.

      do 2 rewrite vec_norm_vec_const_mul.
      rewrite Rabs_Rinv; [ | lra ].
      rewrite Rabs_right; [ | lra ].
      rewrite Rmult_shuffle0, <- Rmult_assoc, fold_Rsqr.
      rewrite <- Rmult_vec_dot_mul_distr_l.
      rewrite <- Rmult_vec_dot_mul_distr_r.
      rewrite <- Rmult_assoc, fold_Rsqr.
      rewrite Rmult_assoc.
      rewrite Rdiv_mult_simpl_l; [ f_equal; lra | | ].
       intros J; apply Rsqr_eq_0 in J; lra.

       rewrite Hnu₁, Hnu₂, fold_Rsqr.
       intros J; apply Rsqr_eq_0 in J; lra.
Qed.

(* commented because perhaps not useful
Theorem unit_sphere_rot_same_latitude : ∀ p p₁ p₂ v₁ v₂ a c s,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → p₂ ∈ sphere 1
  → a = latitude p p₁
  → a = latitude p p₂
  → a² < 1
  → p₁ × p₂ ≠ 0%vec
  → v₁ = (/ √ (1 - a²) ⁎ (p₁ - a ⁎ p))%vec
  → v₂ = (/ √ (1 - a²) ⁎ (p₂ - a ⁎ p))%vec
  → (s, c) = rot_sin_cos p v₁ v₂
  → (old_matrix_of_axis_angle (p, c, s) * v₁)%vec = v₂.
Proof.
intros * Hp Hp₁ Hp₂ Ha₁ Ha₂ Ha2 Hppz Hv₁ Hv₂ Hcs.
unfold rot_sin_cos in Hcs.
injection Hcs; clear Hcs; intros Hc Hs.
assert (‖v₁‖ = 1 ∧ ‖v₂‖ = 1) as (Hnv₁, Hnv₂).
 assert (H : √ (1 - a²) ≠ 0) by (intros H; apply sqrt_eq_0 in H; lra).
 eapply latitude_norm in Ha₁; [ | easy | easy | reflexivity ].
 eapply latitude_norm in Ha₂; [ | easy | easy | reflexivity ].
 rewrite Hv₁, Hv₂.
 do 2 rewrite vec_norm_vec_const_mul.
 rewrite Rabs_Rinv; [ | easy ].
 rewrite Rabs_sqrt, Ha₁, Ha₂.
 now rewrite Rinv_l.

 rewrite Hnv₁, Hnv₂, Rmult_1_l, Rdiv_1_r in Hs, Hc.
 assert (Hvvp : (v₁ × v₂) × p = 0%vec).
  rewrite vec_double_cross_mul, Hv₁, Hv₂.
  remember (/ √ (1 - a²)) as b eqn:Hb.
  do 2 rewrite <- Rmult_vec_dot_mul_distr_l.
  do 2 rewrite vec_dot_mul_sub_distr_r.
  rewrite Ha₁ at 1; rewrite Ha₂ at 2.
  unfold latitude.
  do 2 rewrite <- Rmult_vec_dot_mul_distr_l.
  rewrite vec_dot_mul_diag.
  apply on_sphere_norm in Hp; [ | lra ].
  rewrite Hp, Rsqr_1.
  do 2 rewrite Rmult_1_r.
  apply on_sphere_norm in Hp₁; [ | lra ].
  apply on_sphere_norm in Hp₂; [ | lra ].
  rewrite Hp₁, Hp₂, Rmult_1_l, Rdiv_1_r, Rdiv_1_r.
  rewrite vec_dot_mul_comm, Rminus_diag_eq; [ | easy ].
  rewrite vec_dot_mul_comm, Rminus_diag_eq; [ | easy ].
  rewrite Rmult_0_r.
  do 2 rewrite vec_const_mul_0_l.
  now rewrite vec_sub_0_r.

  assert (Hpz : p ≠ 0%vec).
   intros H; rewrite H in Hp; simpl in Hp.
   rewrite Rsqr_0, Rsqr_1 in Hp; lra.

   destruct (vec_eq_dec (v₁ × v₂) 0) as [Hvv| Hvv].
    assert (Hpv : p · v₁ = 0).
     rewrite Hv₁.
     remember (/ √ (1 - a²)) as b eqn:Hb.
     rewrite Ha₁; unfold latitude.
     rewrite <- Rmult_vec_dot_mul_distr_r.
     rewrite vec_dot_mul_sub_distr_l.
     rewrite <- Rmult_vec_dot_mul_distr_r.
     apply on_sphere_norm in Hp; [ | lra ].
     apply on_sphere_norm in Hp₁; [ | lra ].
     rewrite vec_dot_mul_diag, Hp, Hp₁, Rsqr_1.
     rewrite Rmult_1_r, Rmult_1_r, Rdiv_1_r.
     now rewrite Rminus_diag_eq, Rmult_0_r.

     rewrite Hvv in Hs.
     rewrite vec_norm_0, Rmult_0_r in Hs; subst s.
     destruct p as (xp, yp, zp); simpl.
     simpl in Hp; rewrite Rsqr_1 in Hp; rewrite Hp.
     rewrite sqrt_1; do 3 rewrite Rdiv_1_r.
     do 3 rewrite Rmult_0_r, Rplus_0_r, Rminus_0_r.
     specialize (vec_Lagrange_identity v₁ v₂) as Hli.
     rewrite Hnv₁, Hnv₂, Hvv, Rsqr_1, Rmult_1_r, vec_sqr_0, <- Hc in Hli.
     apply Rminus_diag_uniq in Hli; symmetry in Hli.
     replace 1 with 1² in Hli by apply Rsqr_1.
     apply Rsqr_eq in Hli.
     destruct Hli as [Hli| Hli]; rewrite Hli.
      rewrite Rminus_diag_eq; [ | easy ].
      do 6 rewrite Rmult_0_r.
      rewrite Rplus_0_l; fold mat_id.
      rewrite mat_vec_mul_id.
      rewrite Hc in Hli.
      clear - Hnv₁ Hnv₂ Hvv Hli.
      destruct v₁ as (x₁, y₁, z₁).
      destruct v₂ as (x₂, y₂, z₂).
      simpl in Hnv₁, Hnv₂, Hvv, Hli.
      apply sqrt_lem_0 in Hnv₁; [ | apply nonneg_sqr_vec_norm | lra ].
      apply sqrt_lem_0 in Hnv₂; [ | apply nonneg_sqr_vec_norm | lra ].
      rewrite Rmult_1_r in Hnv₁, Hnv₂; symmetry in Hnv₁, Hnv₂.
      injection Hvv; clear Hvv; intros H3 H2 H1.
      f_equal; nsatz.

      replace (1 - -1) with 2 by lra.
      do 3 rewrite fold_Rminus.
      assert (Hv₁₂ : v₂ = (-v₁)%vec).
       rewrite Hc in Hli.
       destruct v₁ as (x₁, y₁, z₁).
       destruct v₂ as (x₂, y₂, z₂).
       simpl in Hnv₁, Hnv₂, Hli.
       apply sqrt_lem_0 in Hnv₁; [ | apply nonneg_sqr_vec_norm | lra ].
       apply sqrt_lem_0 in Hnv₂; [ | apply nonneg_sqr_vec_norm | lra ].
       rewrite Rmult_1_r in Hnv₁, Hnv₂; symmetry in Hnv₁, Hnv₂.
       unfold vec_opp.
       clear - Hnv₁ Hnv₂ Hli.
       assert (H : (x₁ + x₂)² + (y₁ + y₂)² + (z₁ + z₂)² = 0) by nsatz.
       apply sqr_vec_norm_eq_0 in H.
       f_equal; lra.

       rewrite Hc in Hli.
       destruct v₁ as (x₁, y₁, z₁).
       destruct v₂ as (x₂, y₂, z₂).
       simpl in Hnv₁, Hnv₂, Hvv, Hli, Hv₁₂.
       injection Hv₁₂; clear Hv₁₂; intros Hz₂ Hy₂ Hx₂.
       subst x₂ y₂ z₂.
       apply sqrt_lem_0 in Hnv₁; [ | apply nonneg_sqr_vec_norm | lra ].
       apply sqrt_lem_0 in Hnv₂; [ | apply nonneg_sqr_vec_norm | lra ].
       rewrite Rmult_1_r in Hnv₁, Hnv₂; symmetry in Hnv₁, Hnv₂.
       clear Hvv Hli Hnv₂ Hvvp.
       unfold Rsqr; simpl in Hpv; simpl.
       rewrite Rmult_minus_distr_r, Rmult_1_l.
       f_equal; nsatz.

    apply vec_cross_mul_eq_0 in Hvvp; [ | easy | easy ].
    destruct Hvvp as (d & e & Hd & He & Hde).
    apply vec_add_move_l in Hde.
    rewrite vec_sub_0_l in Hde.
    rewrite vec_opp_const_mul_distr_l in Hde.
    apply vec_const_mul_div in Hde; [ | easy ].
    unfold latitude in Ha₁, Ha₂.
    remember (- d / e) as k eqn:Hk.
    assert (Hkz : k ≠ 0).
     intros H; rewrite H in Hde.
     now rewrite vec_const_mul_0_l in Hde.

     assert (Hikz : / k ≠ 0) by now apply Rinv_neq_0_compat.
     destruct (Rle_dec 0 k) as [Hkp| Hkn].
      rewrite matrix_mul_axis with (k := / k); [ | easy ].
      apply (f_equal (vec_const_mul (/ k))) in Hde.
      rewrite vec_const_mul_assoc in Hde.
      rewrite Rinv_l in Hde; [ | easy ].
      rewrite vec_const_mul_1_l in Hde.
      apply rotate_matrix_of_two_vectors; try assumption.
       intros H.
       apply eq_vec_const_mul_0 in H.
       destruct H as [H| H]; [ | easy ].
       now apply Rinv_neq_0_compat in H.

       unfold Rsign.
       destruct (Rle_dec 0 (/ k)) as [Hik| Hik].
        rewrite Rmult_1_l, Hs, <- Hde.
        rewrite <- Rmult_vec_dot_mul_distr_r.
        unfold Rsign.
        destruct (Rle_dec 0 (/ k * p²%vec)) as [H| H].
         now rewrite Rmult_1_l.

         exfalso; apply H.
         rewrite vec_dot_mul_diag.
         apply Rmult_le_pos; [ easy | apply Rle_0_sqr ].

        exfalso; apply Hik, Rlt_le.
        apply Rinv_0_lt_compat; lra.

      apply Rnot_le_lt in Hkn.
      rewrite matrix_mul_axis with (k := / k); [ | easy ].
      apply (f_equal (vec_const_mul (/ k))) in Hde.
      rewrite vec_const_mul_assoc in Hde.
      rewrite Rinv_l in Hde; [ | easy ].
      rewrite vec_const_mul_1_l in Hde.
      apply rotate_matrix_of_two_vectors; try assumption.
       intros H.
       apply eq_vec_const_mul_0 in H.
       destruct H as [H| H]; [ | easy ].
       now apply Rinv_neq_0_compat in H.

       unfold Rsign.
       destruct (Rle_dec 0 (/ k)) as [Hik| Hik].
        apply Rle_not_lt in Hik.
        exfalso; apply Hik.
        now apply Rinv_lt_0_compat.

        rewrite Hs, <- Hde.
        rewrite <- Rmult_vec_dot_mul_distr_r.
        unfold Rsign.
        destruct (Rle_dec 0 (/ k * p²%vec)) as [H| H]; [ | lra ].
        exfalso.
        apply Rnot_le_lt in Hik.
        apply Rmult_lt_compat_r with (r := p²%vec) in Hik; [ lra | ].
        rewrite vec_dot_mul_diag.
        apply Rlt_0_sqr.
        now intros H1; apply vec_norm_eq_0 in H1.
Qed.
*)

(* commented because perhaps not useful
Theorem Rsign_mul_pos_l : ∀ x y, 0 < x → Rsign (x * y) = Rsign y.
Proof.
intros * Hx.
unfold Rsign.
destruct (Rle_dec 0 (x * y)) as [Hxy| Hxy].
 destruct (Rle_dec 0 y) as [Hy| Hy]; [ easy | ].
 exfalso; apply Hy.
 apply Rmult_le_reg_l with (r := x); [ easy | ].
 now rewrite Rmult_0_r.

 destruct (Rle_dec 0 y) as [Hy| Hy]; [ | easy ].
 exfalso; apply Hxy.
 replace 0 with (x * 0) by lra.
 apply Rmult_le_compat_l; [ lra | easy ].
Qed.
*)

(* commented because perhaps not useful
Theorem rot_sin_cos_mul : ∀ k p u v,
  0 < k
  → rot_sin_cos (k ⁎ p) (k ⁎ u) (k ⁎ v) = rot_sin_cos p u v.
Proof.
intros * Hk.
unfold rot_sin_cos.
destruct (vec_eq_dec u 0) as [Hu| Hu].
 subst u.
 rewrite vec_const_mul_0_r, vec_cross_mul_0_l, vec_dot_mul_0_r.
 rewrite vec_norm_0, Rmult_0_r.
 rewrite Rdiv_0_l, vec_dot_mul_0_l.
 rewrite Rdiv_0_l, vec_cross_mul_0_l.
 rewrite vec_norm_0, Rmult_0_r, Rdiv_0_l.
 now rewrite vec_dot_mul_0_l, Rdiv_0_l.

 destruct (vec_eq_dec v 0) as [Hv| Hv].
  subst v.
  rewrite vec_const_mul_0_r, vec_cross_mul_0_r, vec_dot_mul_0_r.
  rewrite vec_norm_0, Rmult_0_r.
  rewrite Rdiv_0_l, vec_dot_mul_0_r.
  rewrite Rdiv_0_l, vec_cross_mul_0_r.
  rewrite vec_norm_0, Rmult_0_r, Rdiv_0_l.
  now rewrite vec_dot_mul_0_r, Rdiv_0_l.

  f_equal.
   rewrite <- vec_const_mul_cross_distr_l.
   rewrite <- vec_const_mul_cross_distr_r.
   do 2 rewrite <- Rdiv_mult; f_equal.
    rewrite <- Rmult_vec_dot_mul_distr_l.
    do 2 rewrite <- Rmult_vec_dot_mul_distr_r.
    rewrite Rsign_mul_pos_l; [ | easy ].
    rewrite Rsign_mul_pos_l; [ | easy ].
    now rewrite Rsign_mul_pos_l.

    do 4 rewrite vec_norm_vec_const_mul.
    do 2 rewrite <- Rmult_assoc.
    replace (Rabs k * ‖u‖ * Rabs k) with (Rabs k * Rabs k * ‖u‖) by lra.
    do 3 rewrite Rmult_assoc.
    rewrite Rdiv_mult_simpl_l.
     rewrite Rdiv_mult_simpl_l; [ easy | | ].
      unfold Rabs; destruct (Rcase_abs k); lra.

      intros H; apply Rmult_integral in H.
      destruct H as [H| H]; now apply vec_norm_eq_0 in H.

     unfold Rabs; destruct (Rcase_abs k); lra.

     intros H; apply Rmult_integral in H.
     destruct H as [H| H]; [ apply Rabs_eq_0 in H; lra | ].
     apply Rmult_integral in H.
     destruct H as [H| H]; now apply vec_norm_eq_0 in H.

   rewrite <- Rmult_vec_dot_mul_distr_l.
   rewrite <- Rmult_vec_dot_mul_distr_r.
   do 2 rewrite vec_norm_vec_const_mul.
   do 2 rewrite <- Rmult_assoc.
   replace (Rabs k * ‖u‖ * Rabs k) with (Rabs k * Rabs k * ‖u‖) by lra.
   rewrite <- Rabs_mult.
   fold (Rsqr k); rewrite Rabs_sqr.
   rewrite Rmult_assoc.
   rewrite Rdiv_mult_simpl_l; [ easy | | ].
    intros H; apply Rsqr_eq_0 in H; lra.

    intros H; apply Rmult_integral in H.
    destruct H as [H| H]; now apply vec_norm_eq_0 in H.
Qed.
*)

(* commented because perhaps not useful
Theorem rot_same_latitude : ∀ r p p₁ p₂ v₁ v₂ a c s,
  0 < r
  → p ∈ sphere r
  → p₁ ∈ sphere r
  → p₂ ∈ sphere r
  → a = latitude p p₁
  → a = latitude p p₂
  → a² < 1
  → p₁ × p₂ ≠ 0%vec
  → v₁ = (/ √ (1 - a²) ⁎ (p₁ - a ⁎ p))%vec
  → v₂ = (/ √ (1 - a²) ⁎ (p₂ - a ⁎ p))%vec
  → (s, c) = rot_sin_cos p v₁ v₂
  → (old_matrix_of_axis_angle (p, c, s) * v₁)%vec = v₂.
Proof.
intros * Hr Hp Hp₁ Hp₂ Ha₁ Ha₂ Ha2 Hppz Hv₁ Hv₂ Hcs.
assert (Hrp : ∀ p, p ∈ sphere r → /r ⁎ p ∈ sphere 1).
 now intros q Hq; apply on_sphere_on_unit_sphere.

 assert (Hir : 0 < / r) by now apply Rinv_0_lt_compat.
 rewrite <- latitude_mul with (k := / r) in Ha₁; [ | lra ].
 rewrite <- latitude_mul with (k := / r) in Ha₂; [ | lra ].
 assert (Hrppz : ((/ r ⁎ p₁) × (/ r ⁎ p₂) ≠ 0%vec)).
  rewrite <- vec_const_mul_cross_distr_l.
  rewrite <- vec_const_mul_cross_distr_r.
  rewrite vec_const_mul_assoc.
  intros H; apply eq_vec_const_mul_0 in H.
  destruct H as [H| H]; [ | easy ].
  apply Rmult_integral in H; lra.

  assert
    (Hrv : ∀ vi pi,
     vi = / √ (1 - a²) ⁎ (pi - a ⁎ p)
     → / r ⁎ vi = / √ (1 - a²) ⁎ (/ r ⁎ pi - a ⁎ (/ r ⁎ p))).
   intros * Hvi.
   apply vec_const_mul_eq_reg_l with (a := r); [ | lra ].
   rewrite vec_const_mul_assoc, Rinv_r; [ | lra ].
   rewrite vec_const_mul_1_l, vec_const_mul_assoc, Rmult_comm.
   rewrite <- vec_const_mul_assoc.
   rewrite vec_const_mul_sub_distr_l.
   rewrite vec_const_mul_assoc.
   rewrite Rinv_r; [ | lra ].
   rewrite vec_const_mul_1_l.
   do 2 rewrite vec_const_mul_assoc.
   rewrite Rmult_shuffle0.
   rewrite Rinv_r; [ | lra ].
   now rewrite Rmult_1_l.

   rewrite <- rot_sin_cos_mul with (k := / r) in Hcs; [ | easy ].
   specialize
     (unit_sphere_rot_same_latitude (/ r ⁎ p) (/r ⁎ p₁) (/ r ⁎ p₂)
        (/ r ⁎ v₁) (/ r ⁎ v₂) a c s (Hrp p Hp) (Hrp p₁ Hp₁)
        (Hrp p₂ Hp₂) Ha₁ Ha₂ Ha2 Hrppz (Hrv v₁ p₁ Hv₁) (Hrv v₂ p₂ Hv₂)
        Hcs) as Hsl.
   rewrite mat_vec_mul_const_distr in Hsl.
   apply vec_const_mul_eq_reg_l in Hsl; [ | lra ].
   rewrite matrix_mul_axis with (k := / r); [ | lra ].
   unfold Rsign.
   destruct (Rle_dec 0 (/ r)) as [Hrz| Hrz]; [ | lra ].
   now rewrite Rmult_1_l.
Qed.
*)

(*
(* Given an axis (a point p) and two points p₁ and p₂, there is at most
   one rotation around this axis, transforming p₁ into p₂. Zero if p₁ and
   p₂ are not in the same latitude (p being the north pole), one if they
   are. *)
Theorem one_rotation_max : ∀ r p p₁ p₂ c s c' s',
  0 < r
  → p ∈ sphere r
  → p₁ ∈ sphere r
  → p₂ ∈ sphere r
  → s² + c² = 1
  → s'² + c'² = 1
  → (old_matrix_of_axis_angle (p, c, s) * p₁ = p₂)%vec
  → (old_matrix_of_axis_angle (p, c', s') * p₁ = p₂)%vec
  → c = c' ∧ s = s'.
Proof.
intros * Hr Hp Hp₁ Hp₂ Hcs Hcs' Hm Hm'.
remember (old_matrix_of_axis_angle (p, c, s)) as M eqn:HM.
remember (old_matrix_of_axis_angle (p, c', s')) as M' eqn:HM'.
move M' before M; move HM' before HM.
assert (H : ((mat_transp M * M')%mat * p₁ = p₁)%vec).
 rewrite mat_vec_mul_assoc, Hm', <- Hm.
 rewrite <- mat_vec_mul_assoc.
 remember (mat_transp M) as M₁ eqn:HM₁.
 replace M with (mat_transp (mat_transp M)) by apply mat_transp_involutive.
 rewrite <- HM₁.
 assert (is_rotation_matrix M₁) as (Htr, Hdet).
  rewrite HM₁, HM; apply rotation_transp_is_rotation.
  apply matrix_of_axis_angle_is_rotation_matrix; [ | easy ].
  intros H; rewrite H in Hp; simpl in Hp.
  rewrite Rsqr_0, Rplus_0_l, Rplus_0_l in Hp.
  symmetry in Hp; apply Rsqr_eq_0 in Hp; lra.

  now rewrite Htr, mat_vec_mul_id.

Theorem glop : ∀ M axis c s v,
  axis ∈ sphere 1
  → s² + c² = 1
  → axis × v ≠ 0%vec
  → M = old_matrix_of_axis_angle (axis, c, s)
  → (M * v = v)%vec
  → M = mat_id.
Proof.
intros * Ha Hsc Hv HM Hmv.
assert (Hrm : is_rotation_matrix M).
 subst M; apply matrix_of_axis_angle_is_rotation_matrix; [ | easy ].
 intros H; rewrite H in Ha; simpl in Ha.
 rewrite Rsqr_0, Rsqr_1 in Ha; lra.

 destruct Hrm as (Htr, Hdet).
 unfold mat_vec_mul in Hmv.
 unfold mat_id, mkrmat.
 destruct axis as (xa, ya, za).
 destruct v as (xv, yv, zv).
 simpl in HM.
 simpl in Ha.
 rewrite Rsqr_1 in Ha.
 rewrite Ha, sqrt_1 in HM.
 progress repeat rewrite Rdiv_1_r in HM.
 injection Hmv; clear Hmv; intros.
 unfold mat_mul, mat_transp, mat_id, mkrmat in Htr; simpl in Htr.
 injection Htr; clear Htr; intros.
 unfold mat_det in Hdet.
 destruct M; simpl in *.
 unfold mkrmat in HM.
 injection HM; clear HM; intros.
 f_equal.
  unfold Rsqr in *.
bbb.
  (* polynomial not in the ideal *)
  Time nsatz.

bbb.
intros * Hr Hp Hp₁ Hp₂ Hcs Hcs' Hm Hm'.
remember (old_matrix_of_axis_angle (p, c, s)) as M eqn:HM.
remember (old_matrix_of_axis_angle (p, c', s')) as M' eqn:HM'.
move M' before M; move HM' before HM.
remember ((M - M')%mat * p₁)%vec as q eqn:Hq.
generalize Hq; intros H.
rewrite mat_vec_mul_sub_distr_r in H.
rewrite Hm, Hm', vec_sub_diag in H.
rewrite H in Hq; clear q H; symmetry in Hq.
rewrite HM, HM' in Hq; simpl in Hq.
destruct p as (xp, yp, zp); simpl in Hq.
simpl in Hp.
rewrite Hp in Hq.
rewrite sqrt_Rsqr in Hq; [ | lra ].
unfold mat_sub, mat_opp, mat_add in Hq; simpl in Hq.
do 6 rewrite Ropp_plus_distr in Hq.
do 3 rewrite Ropp_minus_distr in Hq.
do 6 rewrite <- Rplus_assoc in Hq.
do 12 rewrite fold_Rminus in Hq.
remember (xp / r) as x eqn:Hx.
remember (yp / r) as y eqn:Hy.
remember (zp / r) as z eqn:Hz.
destruct p₁ as (xp₁, yp₁, zp₁); simpl in Hq.
injection Hq; clear Hq; intros H3 H2 H1.
ring_simplify in H1.
ring_simplify in H2.
ring_simplify in H3.
bbb.

replace (x² * (1 - c) + c - x² * (1 - c') - c') with
((c - c') * (1 - x²)) in Hq by lra.
replace (y² * (1 - c) + c - y² * (1 - c') - c') with
((c - c') * (1 - y²)) in Hq by lra.
replace (z² * (1 - c) + c - z² * (1 - c') - c') with
((c - c') * (1 - z²)) in Hq by lra.
progress replace  (x * y * (1 - c) - z * s + (z * s' - x * y * (1 - c')))
with  (- x * y * (c - c') - z * (s - s')) in Hq by lra.
progress replace  (x * z * (1 - c) + y * s - x * z * (1 - c') - y * s')
with  (- x * z * (c - c') + y * (s - s')) in Hq by lra.
progress replace (x * y * (1 - c) + z * s - x * y * (1 - c') - z * s')
with (- x * y * (c - c') + z * (s - s')) in Hq by lra.


bbb.
intros * Hr Hp Hp₁ Hp₂ Hcs Hcs' Hm Hm'.
destruct (Req_dec (latitude p p₁) (latitude p p₂)) as [Hll| Hll].
 unfold latitude in Hll.
 destruct p as (xp, yp, zp).
 destruct p₁ as (x₁, y₁, z₁).
 destruct p₂ as (x₂, y₂, z₂).
 simpl in Hll, Hm, Hm', Hp, Hp₁, Hp₂.
 rewrite Hp in Hm, Hm'.
 rewrite sqrt_Rsqr in Hm; [ | lra ].
 rewrite sqrt_Rsqr in Hm'; [ | lra ].
 injection Hm; clear Hm; intros Hz1 Hy1 Hx1.
 injection Hm'; clear Hm'; intros Hz2 Hy2 Hx2.
 symmetry in Hx1, Hy1, Hz1, Hx2, Hy2, Hz2.
 enough (r = 1). (* just to simplify the proof, to see *)
 subst r; clear Hr.
 rewrite Rsqr_1 in Hp, Hp₁, Hp₂.
 do 3 rewrite Rdiv_1_r in Hx1, Hy1, Hz1, Hx2, Hy2, Hz2.
bbb.

split.
unfold Rsqr in *.
bbb.

nsatz.

bbb.
 rewrite Hx2 in Hx1.
 ring_simplify in Hx1.
 unfold Rsqr in Hx1.
 assert
   (H :
     (c - c') * (xp * (xp * x₁ + yp * y₁ + zp * z₁) - x₁) +
      (s - s') * (y₁ * zp - yp * z₁) = 0) by lra.

bbb.
*)

Theorem matrix_of_axis_angle_opp : ∀ p₁ p₂ a c s,
  a ∈ sphere 1
  → c² + s² = 1
  → (matrix_of_axis_angle (a, s, c) * p₁ = p₂)%vec
  → (matrix_of_axis_angle (a, (-s)%R, c) * p₂ = p₁)%vec.
Proof.
intros * Ha Hcs Hacs.
subst p₂; simpl.
destruct a as (ax, ay, az); simpl in Ha.
rewrite Rsqr_1 in Ha; rewrite Ha.
rewrite sqrt_1.
do 3 rewrite Rdiv_1_r.
rewrite <- mat_vec_mul_assoc.
unfold mat_mul; simpl.
unfold mkrmat; simpl.
destruct p₁ as (x₁, y₁, z₁); simpl.
f_equal; ring_simplify.
 rewrite Rsqr_pow2 in Ha, Ha, Ha, Hcs, Hcs.
 progress repeat rewrite Rsqr_pow2.
 replace (s ^ 2) with (1 - c ^ 2) by lra.
 replace (az ^ 2) with (1 - ax ^ 2 - ay ^ 2) by lra.
 ring.

 rewrite Rsqr_pow2 in Ha, Ha, Ha, Hcs, Hcs.
 progress repeat rewrite Rsqr_pow2.
 replace (s ^ 2) with (1 - c ^ 2) by lra.
 replace (az ^ 2) with (1 - ax ^ 2 - ay ^ 2) by lra.
 ring.

 rewrite Rsqr_pow2 in Ha, Ha, Ha, Hcs, Hcs.
 progress repeat rewrite Rsqr_pow2.
 replace (s ^ 2) with (1 - c ^ 2) by lra.
 replace (az ^ 2) with (1 - ax ^ 2 - ay ^ 2) by lra.
 ring.
Qed.

Theorem rot_is_id_for_pt : ∀ M v,
  is_rotation_matrix M
  → (M * v = v)%vec
  → M ≠ mat_transp M
  → ∀ a s c, axis_angle_of_matrix M = (a, s, c) → a × v = 0%vec.
Proof.
intros * Hrm Hmv Hmt a s c Ha.
destruct v as (x, y, z).
destruct M; simpl in *.
destruct Hrm as (Hrm, Hdet).
unfold mat_mul, mat_transp, mat_id, mkrmat in Hrm; simpl in Hrm.
unfold mat_det in Hdet; simpl in Hdet.
unfold mat_transp, mkrmat in Hmt; simpl in Hmt.
injection Hrm; clear Hrm.
intros H33 H32 H31 H23 H22 H21 H13 H12 H11.
clear H21 H31 H32.
injection Hmv; clear Hmv; intros Hz Hy Hx.
unfold axis_angle_of_matrix in Ha; simpl in Ha.
unfold rotation_unit_axis, mat_trace in Ha; simpl in Ha.
unfold "_-_", sub_notation in Ha.
injection Ha; clear Ha; intros Hc Hs Ha.
destruct a as (xa, ya, za); simpl.
injection Ha; clear Ha; intros Hza Hya Hxa.
rewrite Hc in Hs.
remember ((a₃₂ - a₂₃)² + (a₁₃ - a₃₁)² + (a₂₁ - a₁₂)²) as r eqn:Hr.
destruct (Req_dec r 0) as [Hrz| Hrz].
 rewrite Hrz in Hr; clear r Hxa Hya Hza Hrz.
 symmetry in Hr.
 apply sqr_vec_norm_eq_0 in Hr.
 destruct Hr as (H1 & H2 & H3).
 apply Rminus_diag_uniq in H1.
 apply Rminus_diag_uniq in H2.
 apply Rminus_diag_uniq in H3.
 now subst a₃₂ a₁₃ a₂₁.

 assert (Hsq : √ r ≠ 0).
  intros H; apply Hrz, sqrt_eq_0; [ | easy ].
  rewrite Hr; apply nonneg_sqr_vec_norm.

  unfold Rsqr in Hr; ring_simplify in Hr.
  progress repeat rewrite <- Rsqr_pow2 in Hr.
  rewrite Rmult_comm, fold_Rdiv in Hxa, Hya, Hza.
  f_equal.
   rewrite <- Hya, <- Hza.
   apply Rmult_eq_reg_r with (r := √ r); [ | easy ].
   rewrite Rmult_0_l, Rmult_minus_distr_r.
   rewrite Rmult_shuffle0, Rmult_div_same; [ | easy ].
   rewrite Rmult_shuffle0, Rmult_div_same; [ | easy ].
   clear - Hdet H11 H12 H13 H22 H23 Hx Hy Hz.
   Time nsatz.

   rewrite <- Hza, <- Hxa.
   apply Rmult_eq_reg_r with (r := √ r); [ | easy ].
   rewrite Rmult_0_l, Rmult_minus_distr_r.
   rewrite Rmult_shuffle0, Rmult_div_same; [ | easy ].
   rewrite Rmult_shuffle0, Rmult_div_same; [ | easy ].
   clear - Hdet H11 H12 H13 H22 H23 Hx Hy Hz.
   Time nsatz.

   rewrite <- Hxa, <- Hya.
   apply Rmult_eq_reg_r with (r := √ r); [ | easy ].
   rewrite Rmult_0_l, Rmult_minus_distr_r.
   rewrite Rmult_shuffle0, Rmult_div_same; [ | easy ].
   rewrite Rmult_shuffle0, Rmult_div_same; [ | easy ].
   clear - Hdet H11 H12 H13 H22 H23 Hx Hy Hz.
   Time nsatz.
Qed.

(* J₀(axis) = set of angles of rotation around the axis, such that
   for some p in D ∩ sphere(r), R(p) is also in D ∩ sphere(r) where
   r = ‖axis‖. *)
Definition J₀ axis :=
  mkset
    (λ '(sinθ, cosθ),
     sinθ² + cosθ² = 1 ∧
     let R := matrix_of_axis_angle (axis, sinθ, cosθ) in
     let r := ‖axis‖ in
     ∃ p p', p ∈ D ∩ sphere r ∧ p' ∈ D ∩ sphere r ∧
     (R * p)%vec = p').

Definition J₀_of_nat axis n : (ℝ * ℝ) :=
  let '(n₁, n₂) := prod_nat_of_nat n in
  let '(nf, no) := prod_nat_of_nat n₁ in
  let '(nf', no') := prod_nat_of_nat n₂ in
  let r := ‖axis‖ in
  let p₀ := fixpoint_of_nat r nf in
  let p := fold_right rotate p₀ (path_of_nat no) in
  let p'₀ := fixpoint_of_nat r nf' in
  let p' := fold_right rotate p'₀ (path_of_nat no') in
  rot_sin_cos axis p p'.

Theorem unit_sphere_latitude_1 : ∀ p p',
  p ∈ sphere 1
  → p' ∈ sphere 1
  → latitude p p' = 1
  → p = p'.
Proof.
intros * Hp Hp' Hlat.
unfold latitude in Hlat; simpl in Hlat.
apply on_sphere_norm in Hp; [ | lra ].
apply on_sphere_norm in Hp'; [ | lra ].
rewrite Hp, Hp', Rmult_1_l, Rdiv_1_r in Hlat.
specialize (vec_Lagrange_identity p p') as Hlag.
rewrite Hp, Hp', Hlat, Rsqr_1, Rmult_1_l in Hlag.
rewrite Rminus_diag_eq in Hlag; [ | easy ].
symmetry in Hlag.
destruct p as (xp, yp, zp).
destruct p' as (xp', yp', zp').
apply on_sphere_norm in Hp; [ | lra ].
apply on_sphere_norm in Hp'; [ | lra ].
simpl in Hp, Hp', Hlat, Hlag.
rewrite Rsqr_1 in Hp, Hp'.
do 3 rewrite fold_Rsqr in Hlag.
apply sqr_vec_norm_eq_0 in Hlag.
destruct Hlag as (H3 & H2 & H1).
apply Rminus_diag_uniq in H1.
apply Rminus_diag_uniq in H2.
apply Rminus_diag_uniq in H3.
Time f_equal; nsatz.
Qed.

Theorem latitude_1 : ∀ r p p',
  p ∈ sphere r
  → p' ∈ sphere r
  → latitude p p' = 1
  → p = p'.
Proof.
intros * Hp Hp' Hlat.
destruct (Req_dec r 0) as [Hr| Hr].
 subst r.
 unfold latitude in Hlat; simpl in Hlat.
 apply on_sphere_norm in Hp; [ | lra ].
 apply on_sphere_norm in Hp'; [ | lra ].
 apply vec_norm_eq_0 in Hp.
 apply vec_norm_eq_0 in Hp'.
 rewrite Hp, Hp', vec_sqr_0, Rdiv_0_l in Hlat; lra.

 assert (Hpr : ∀ p, p ∈ sphere r → p ⁄ r ∈ sphere 1).
  clear - Hr; intros.
  now apply vec_div_in_sphere.

  assert (Ha : ∀ p p', latitude p p' = latitude (p ⁄ r) (p' ⁄ r)).
   clear - Hr; intros.
   rewrite latitude_mul; [ easy | ].
   apply Rinv_neq_0_compat; lra.

   rewrite Ha in Hlat.
   specialize
     (unit_sphere_latitude_1 (p ⁄ r) (p' ⁄ r) (Hpr p Hp) (Hpr p' Hp') Hlat)
     as H.
   apply (f_equal (vec_const_mul r)) in H.
   do 2 rewrite vec_const_mul_assoc in H.
   rewrite Rinv_r in H; [ | easy ].
   now do 2 rewrite vec_const_mul_1_l in H.
Qed.

Theorem latitude_minus_1 : ∀ r p p',
  p ∈ sphere r
  → p' ∈ sphere r
  → latitude p p' = -1
  → p = (- p')%vec.
Proof.
intros * Hp Hp' Hlat.
apply neg_vec_in_sphere in Hp'.
assert (Hlat2 : latitude p (- p') = 1).
 unfold latitude in Hlat; unfold latitude.
 rewrite <- vec_opp_dot_mul_distr_r, vec_norm_opp, Ropp_div, Hlat.
 apply Ropp_involutive.

 now specialize (latitude_1 r p (- p')%vec Hp Hp' Hlat2).
Qed.

Theorem latitude_opp_r : ∀ p p', latitude p (- p') = - latitude p p'.
Proof.
intros (x, y, z) (x', y', z'); unfold latitude; simpl.
do 3 rewrite <- Rsqr_neg.
do 3 rewrite <- Ropp_mult_distr_r.
do 2 rewrite <- Ropp_plus_distr.
now rewrite Ropp_div.
Qed.

Theorem mat_of_path_fixpoint_rev_path : ∀ el p,
  (mat_of_path el * p = p → mat_of_path (rev_path el) * p = p)%vec.
Proof.
intros * Hmp.
rewrite <- rotate_vec_mul in Hmp.
apply rotate_rev_path in Hmp.
now rewrite rotate_vec_mul in Hmp.
Qed.

Theorem mat_of_rev_path : ∀ el,
  norm_list el ≠ []
  → mat_of_path (rev_path el) = mat_transp (mat_of_path el)%mat.
Proof.
intros * Hn.
setoid_rewrite <- mat_of_path_norm.
rewrite <- rev_path_norm_list.
remember (norm_list el) as nel eqn:Hnel.
assert (Hnn : norm_list nel = nel) by now rewrite Hnel, norm_list_idemp.
clear el Hn Hnel; rename nel into el.
remember (length el) as len eqn:Hlen; symmetry in Hlen.
revert el Hnn Hlen.
induction len; intros.
 now apply length_zero_iff_nil in Hlen; subst el.

 destruct el as [| e₁ el]; [ easy | ].
 simpl in Hlen.
 apply Nat.succ_inj in Hlen.
 rewrite mat_of_path_cons, mat_transp_mul.
 rewrite rev_path_cons, rev_path_single, mat_of_path_app.
 apply norm_list_cons in Hnn.
 rewrite IHlen; [ | easy | easy ].
 f_equal.
 destruct e₁ as (t₁, d₁); simpl.
 unfold mat_of_path; simpl.
 rewrite mat_mul_id_r.
 now destruct t₁, d₁; simpl.
Qed.

Theorem mat_of_path_neq_mat_transp : ∀ el,
  norm_list el ≠ []
  → mat_of_path el ≠ mat_transp (mat_of_path el).
Proof.
intros * Hn Htr.
generalize Htr; intros Htr2.
apply (f_equal (λ M, (M * M)%mat)) in Htr2.
rewrite <- mat_of_rev_path in Htr2; [ | easy ].
do 2 rewrite <- mat_of_path_app in Htr2.
rewrite <- rev_path_app in Htr2.
assert (Hnn : norm_list (el ++ el) ≠ []).
 now intros H; apply norm_list_app_diag_is_nil in H.

 move Hnn before Hn.
 specialize (matrix_of_non_empty_path_is_not_identity (el ++ el) Hnn) as Hm.
 rewrite mat_of_rev_path in Htr2; [ | easy ].
 apply Hm; clear Hm.
 rewrite mat_of_path_app.
 rewrite Htr at 2.
 rewrite <- mat_rot_inv; [ | apply mat_of_path_is_rotation_matrix ].
 unfold mat_inv.
 rewrite <- mat_const_mul_distr_r.
 rewrite mat_mul_compl_r.
 rewrite mat_const_mul_assoc.
 rewrite Rinv_l; [ now rewrite mat_const_mul_1_l | ].
 intros H.
 specialize (mat_of_path_is_rotation_matrix el) as (Hr, Hdet).
 lra.
Qed.

Theorem mat_of_path_neq_mat_of_rev_path : ∀ el,
  norm_list el ≠ []
  → mat_of_path el ≠ mat_of_path (rev_path el).
Proof.
intros * Hn Htr.
rewrite mat_of_rev_path in Htr; [ | easy ].
now apply mat_of_path_neq_mat_transp in Htr.
Qed.

Theorem fixpoint_of_rev_path : ∀ r el,
  0 < r
  → norm_list el ≠ []
  → fixpoint_of_path r (rev_path el) = (- fixpoint_of_path r el)%vec.
Proof.
intros * Hr Hn.
remember (fixpoint_of_path r el) as p eqn:Hp.
remember (fixpoint_of_path r (rev_path el)) as p' eqn:Hp'.
unfold fixpoint_of_path in Hp, Hp'.
generalize Hp; intros Hpr.
apply rotation_fixpoint_of_path in Hpr.
generalize Hp'; intros Hpr'.
apply rotation_fixpoint_of_path in Hpr'.
apply mat_of_path_fixpoint_rev_path in Hpr'.
rewrite rev_path_involutive in Hpr'.
generalize Hpr; intros H.
apply rotate_unicity with (p₁ := p') in H; [ | | easy | easy ].
 destruct H as [H| H]; [ | easy ].
 exfalso; move H at top; subst p'; clear Hpr'.
 rewrite Hp in Hp'.
 unfold rotation_fixpoint in Hp'.
 apply (f_equal (vec_const_mul (/ r))) in Hp'.
 do 2 rewrite vec_const_mul_assoc in Hp'.
 rewrite Rinv_l in Hp'; [ | lra ].
 do 2 rewrite vec_const_mul_1_l in Hp'.
 unfold rotation_unit_axis in Hp'.
 unfold vec_normalize in Hp'.
 remember (rotation_axis (mat_of_path el)) as ra eqn:Hra.
 remember (rotation_axis (mat_of_path (rev_path el))) as ra' eqn:Hra'.
 unfold rotation_axis in Hra, Hra'.
 unfold "_-_", sub_notation in Hra, Hra'.
 rewrite mat_of_rev_path in Hra'; [ | easy ].
 remember (mat_of_path el) as M eqn:HM.
 assert (Hneg : ra' = (- ra)%vec).
  rewrite Hra, Hra'; clear.
  destruct M; simpl.
  f_equal; lra.

  rewrite Hneg in Hp'.
  rewrite vec_norm_opp in Hp'.
  destruct (vec_eq_dec ra 0) as [Hraz| Hraz].
   move Hraz at top; subst ra.
   symmetry in Hra; injection Hra; clear Hra; intros H3 H2 H1.
   apply Rminus_diag_uniq in H1.
   apply Rminus_diag_uniq in H2.
   apply Rminus_diag_uniq in H3.
   clear ra' Hra' Hneg Hp'.
   clear p Hp Hpr r Hr.
   rewrite <- mat_of_path_norm in HM.
   remember (norm_list el) as nel eqn:Hnel.
   assert (Hnn : norm_list nel = nel) by now rewrite Hnel, norm_list_idemp.
   clear el Hnel; rename nel into el.
   move M before el; move Hnn before Hn.
   assert (Htr : M = mat_transp M).
    unfold mat_transp, mkrmat.
    destruct M; simpl in H1, H2, H3; simpl.
    now rewrite H1, H2, H3.

    rewrite HM in Htr.
    apply mat_of_path_neq_mat_transp in Htr; [ easy | ].
    now rewrite Hnn.

   apply (f_equal (vec_const_mul ‖ra‖)) in Hp'.
   do 2 rewrite vec_const_mul_assoc in Hp'.
   rewrite Rinv_r in Hp'; [ | now apply vec_norm_neq_0 ].
   do 2 rewrite vec_const_mul_1_l in Hp'.
   apply Hraz; clear - Hp'.
   destruct ra as (x, y, z); simpl in Hp'.
   injection Hp'; clear Hp'; intros.
   f_equal; lra.

 rewrite Hp, Hp'.
 rewrite rotation_fixpoint_norm; [ | lra | ].
  rewrite rotation_fixpoint_norm; [ easy | lra | ].
  now apply mat_of_path_neq_mat_transp.

  apply mat_of_path_neq_mat_transp.
  rewrite <- rev_path_norm_list.
  intros HH; apply Hn.
  now apply rev_path_is_nil in HH.
Qed.

Theorem J₀_is_countable : ∀ axis,
  axis ∉ D
  → (- axis)%vec ∉ D
  → ∀ sc, sc ∈ J₀ axis → ∃ n : ℕ, J₀_of_nat axis n = sc.
Proof.
intros axis Had Hnad (s, c) Ha.
destruct Ha as (Hcs & p & p' & Hp & Hp' & Hv).
apply -> in_intersection in Hp.
apply -> in_intersection in Hp'.
destruct Hp as (Hpd & Hps).
destruct Hp' as (Hpd' & Hps').
destruct (vec_eq_dec axis 0) as [Haz| Haz].
 rewrite Haz in Had.
 rewrite Haz in Hps; simpl in Hps.
 rewrite Rsqr_0, Rplus_0_l, Rplus_0_l, sqrt_0, Rsqr_0 in Hps (*, Hps'*).
 destruct p as (xp, yp, zp).
 apply sqr_vec_norm_eq_0 in Hps.
 destruct Hps as (Hxp & Hyp & Hzp).
 now subst xp yp zp (*xp' yp' zp'*).

 assert (Hll : latitude axis p = latitude axis p').
  eapply rotation_implies_same_latitude; try eassumption.
  2: apply on_sphere_norm; [ apply vec_norm_nonneg | easy ].
  specialize (vec_norm_nonneg axis) as H.
  enough (‖axis‖ ≠ 0) by lra.
  clear H; intros H.
  now apply vec_norm_eq_0 in H.

  assert (p ≠ axis ∧ p ≠ (- axis)%vec) as (Hpa, Hpna).
   now split; intros H; move H at top; subst p.
  
   remember ‖axis‖ as r eqn:Hr.
   move r before c; move Hr before r.
   remember (matrix_of_axis_angle (axis, s, c)) as M eqn:HM.
   destruct Hpd as (el₀ & p₀ & (el & Hso) & Hn & Hp₀).
   destruct Hpd' as (el'₀ & p'₀ & (el' & Hso') & Hn' & Hp'₀).
   move el'₀ before el₀; move el before el'₀; move el' before el.
   move p'₀ before p₀.
   move Hso' before Hso; move Hn' before Hn; move Hp'₀ before Hp₀.
   move Hp₀ after Hso; move Hp'₀ before Hp₀.
   assert (H : p₀ ∈ sphere r ∧ p'₀ ∈ sphere r).
    rewrite <- Hso, <- Hso'; do 2 rewrite rotate_vec_mul.
    split.
    1, 2 : apply on_sphere_after_rotation; [ easy | ].
    1, 2 : apply mat_of_path_is_rotation_matrix.

    destruct H as (Hp₀s, Hp'₀s).
    assert (Hax : axis ∈ sphere r).
     rewrite Hr.
     destruct axis as (x, y, z); simpl.
     rewrite Rsqr_sqrt; [ easy | apply nonneg_sqr_vec_norm ].

     remember (latitude axis p) as a eqn:Ha.
     rename Hll into Ha'.
     symmetry in Ha, Ha'.
     assert (Ha21 : a² ≠ 1).
      intros H.
      replace 1 with 1² in H by apply Rsqr_1.
      apply Rsqr_eq_abs_0 in H.
      rewrite Rabs_R1 in H.
      apply Rabs_or in H.
      destruct H as [H| H].
       rewrite H in Ha.
       apply (latitude_1 r) in Ha; [ | easy | easy ].
       now symmetry in Ha.

       rewrite H in Ha.
       apply (latitude_minus_1 r) in Ha; [ | easy | easy ].
       now rewrite Ha, neg_vec_involutive in Hpna.

      apply rotate_rev_path in Hso.
      apply rotate_rev_path in Hso'.
      remember (fixpoint_of_path r el₀) as q eqn:Hq.
      remember (fixpoint_of_path r el'₀) as q' eqn:Hq'.
      rewrite rotate_vec_mul in Hp₀, Hp'₀, Hso, Hso'.
      generalize Hq; intros Hpq.
      apply axis_and_fixpoint_of_path_collinear with (p := p₀) in Hpq;
        try assumption; [ | now subst q; apply fixpoint_of_path_on_sphere ].
      generalize Hq'; intros Hpq'.
      apply axis_and_fixpoint_of_path_collinear with (p := p'₀) in Hpq';
        try assumption; [ | now subst q'; apply fixpoint_of_path_on_sphere ].
      destruct (bool_dec (is_neg_vec p₀) (is_neg_vec q)) as [Hb| Hb].
       move Hpq at top; subst q; clear Hb.
       destruct (bool_dec (is_neg_vec p'₀) (is_neg_vec q')) as [Hb| Hb].
        move Hpq' at top; subst q'.
        unfold J₀_of_nat.
        remember (nat_of_path el₀) as nf eqn:Hnf.
        remember (nat_of_path (rev_path el)) as no eqn:Hno.
        remember (nat_of_path el'₀) as nf' eqn:Hnf'.
        remember (nat_of_path (rev_path el')) as no' eqn:Hno'.
        move no before nf; move nf' before nf; move no' before no.
        remember (nat_of_prod_nat (nf, no)) as nfo eqn:Hnfo.
        remember (nat_of_prod_nat (nf', no')) as nfo' eqn:Hnfo'.
        remember (nat_of_prod_nat (nfo, nfo')) as n eqn:Hnn.
        exists n; subst n.
        rewrite prod_nat_of_nat_inv; subst nfo.
        rewrite prod_nat_of_nat_inv; subst nfo'.
        rewrite prod_nat_of_nat_inv.
        subst nf no nf' no'.
        unfold fixpoint_of_nat.
        do 4 rewrite path_of_nat_inv.
        rewrite <- Hr, <- Hq, <- Hq'.
        do 2 rewrite rotate_vec_mul.
        rewrite Hso, Hso'.
        subst M; clear - Hax Haz Hcs Hr Hps Hps' Ha Ha' Hv Hpa Hpna Ha21.
        symmetry.
        apply mat_vec_mul_rot_sin_cos with (r := r) (a := a); try assumption.
        assert (H : ‖axis‖ ≠ 0) by now intros H; apply vec_norm_eq_0 in H.
        rewrite <- Hr in H.
        apply Rdichotomy in H.
        destruct H as [H| H]; [ | lra ].
        apply Rlt_not_le in H.
        exfalso; apply H; rewrite Hr.
        apply vec_norm_nonneg.

        apply (f_equal vec_opp) in Hpq'.
        rewrite neg_vec_involutive in Hpq'.
        move Hpq' at top; subst q'; clear Hb.
        unfold J₀_of_nat.
        remember (nat_of_path el₀) as nf eqn:Hnf.
        remember (nat_of_path (rev_path el)) as no eqn:Hno.
        remember (nat_of_path (rev_path el'₀)) as nf' eqn:Hnf'.
        remember (nat_of_path (rev_path el')) as no' eqn:Hno'.
        move no before nf; move nf' before nf; move no' before no.
        remember (nat_of_prod_nat (nf, no)) as nfo eqn:Hnfo.
        remember (nat_of_prod_nat (nf', no')) as nfo' eqn:Hnfo'.
        remember (nat_of_prod_nat (nfo, nfo')) as n eqn:Hnn.
        exists n; subst n.
        rewrite prod_nat_of_nat_inv; subst nfo.
        rewrite prod_nat_of_nat_inv; subst nfo'.
        rewrite prod_nat_of_nat_inv.
        subst nf no nf' no'.
        unfold fixpoint_of_nat.
        do 4 rewrite path_of_nat_inv.
        rewrite <- Hr, <- Hq.
        assert (H : p'₀ = fixpoint_of_path r (rev_path el'₀)).
         rewrite fixpoint_of_rev_path, <- Hq'; [ | | easy ].
         now rewrite neg_vec_involutive.

         rewrite Hr; apply vec_norm_neq_0 in Haz.
         now specialize (vec_norm_nonneg axis); lra.

        rewrite <- H.
        do 2 rewrite rotate_vec_mul.
        rewrite Hso, Hso'.
        subst M; clear - Hax Haz Hcs Hr Hps Hps' Ha Ha' Hv Hpa Hpna Ha21.
        symmetry.
        apply mat_vec_mul_rot_sin_cos with (r := r) (a := a); try assumption.
        assert (H : ‖axis‖ ≠ 0) by now intros H; apply vec_norm_eq_0 in H.
        rewrite <- Hr in H.
        apply Rdichotomy in H.
        destruct H as [H| H]; [ | lra ].
        apply Rlt_not_le in H.
        exfalso; apply H; rewrite Hr.
        apply vec_norm_nonneg.

       apply (f_equal vec_opp) in Hpq.
       rewrite neg_vec_involutive in Hpq.
       move Hpq at top; subst q; clear Hb.
       destruct (bool_dec (is_neg_vec p'₀) (is_neg_vec q')) as [Hb| Hb].
        move Hpq' at top; subst q'.
        unfold J₀_of_nat.
        remember (nat_of_path (rev_path el₀)) as nf eqn:Hnf.
        remember (nat_of_path (rev_path el)) as no eqn:Hno.
        remember (nat_of_path el'₀) as nf' eqn:Hnf'.
        remember (nat_of_path (rev_path el')) as no' eqn:Hno'.
        move no before nf; move nf' before nf; move no' before no.
        remember (nat_of_prod_nat (nf, no)) as nfo eqn:Hnfo.
        remember (nat_of_prod_nat (nf', no')) as nfo' eqn:Hnfo'.
        remember (nat_of_prod_nat (nfo, nfo')) as n eqn:Hnn.
        exists n; subst n.
        rewrite prod_nat_of_nat_inv; subst nfo.
        rewrite prod_nat_of_nat_inv; subst nfo'.
        rewrite prod_nat_of_nat_inv.
        subst nf no nf' no'.
        unfold fixpoint_of_nat.
        do 4 rewrite path_of_nat_inv.
        rewrite <- Hr, <- Hq'.
        assert (H : p₀ = fixpoint_of_path r (rev_path el₀)).
         rewrite fixpoint_of_rev_path, <- Hq; [ | | easy ].
         now rewrite neg_vec_involutive.

         rewrite Hr; apply vec_norm_neq_0 in Haz.
         now specialize (vec_norm_nonneg axis); lra.

        rewrite <- H.
        do 2 rewrite rotate_vec_mul.
        rewrite Hso, Hso'.
        subst M; clear - Hax Haz Hcs Hr Hps Hps' Ha Ha' Hv Hpa Hpna Ha21.
        symmetry.
        apply mat_vec_mul_rot_sin_cos with (r := r) (a := a); try assumption.
        assert (H : ‖axis‖ ≠ 0) by now intros H; apply vec_norm_eq_0 in H.
        rewrite <- Hr in H.
        apply Rdichotomy in H.
        destruct H as [H| H]; [ | lra ].
        apply Rlt_not_le in H.
        exfalso; apply H; rewrite Hr.
        apply vec_norm_nonneg.

        apply (f_equal vec_opp) in Hpq'.
        rewrite neg_vec_involutive in Hpq'.
        move Hpq' at top; subst q'; clear Hb.
        unfold J₀_of_nat.
        remember (nat_of_path (rev_path el₀)) as nf eqn:Hnf.
        remember (nat_of_path (rev_path el)) as no eqn:Hno.
        remember (nat_of_path (rev_path el'₀)) as nf' eqn:Hnf'.
        remember (nat_of_path (rev_path el')) as no' eqn:Hno'.
        move no before nf; move nf' before nf; move no' before no.
        remember (nat_of_prod_nat (nf, no)) as nfo eqn:Hnfo.
        remember (nat_of_prod_nat (nf', no')) as nfo' eqn:Hnfo'.
        remember (nat_of_prod_nat (nfo, nfo')) as n eqn:Hnn.
        exists n; subst n.
        rewrite prod_nat_of_nat_inv; subst nfo.
        rewrite prod_nat_of_nat_inv; subst nfo'.
        rewrite prod_nat_of_nat_inv.
        subst nf no nf' no'.
        unfold fixpoint_of_nat.
        do 4 rewrite path_of_nat_inv.
        rewrite <- Hr.
        assert (H : p'₀ = fixpoint_of_path r (rev_path el'₀)).
         rewrite fixpoint_of_rev_path, <- Hq'; [ | | easy ].
         now rewrite neg_vec_involutive.

         rewrite Hr; apply vec_norm_neq_0 in Haz.
         now specialize (vec_norm_nonneg axis); lra.

        rewrite <- H; clear H.
        assert (H : p₀ = fixpoint_of_path r (rev_path el₀)).
         rewrite fixpoint_of_rev_path, <- Hq; [ | | easy ].
         now rewrite neg_vec_involutive.

         rewrite Hr; apply vec_norm_neq_0 in Haz.
         now specialize (vec_norm_nonneg axis); lra.

        rewrite <- H; clear H.
        do 2 rewrite rotate_vec_mul.
        rewrite Hso, Hso'.
        subst M; clear - Hax Haz Hcs Hr Hps Hps' Ha Ha' Hv Hpa Hpna Ha21.
        symmetry.
        apply mat_vec_mul_rot_sin_cos with (r := r) (a := a); try assumption.
        assert (H : ‖axis‖ ≠ 0) by now intros H; apply vec_norm_eq_0 in H.
        rewrite <- Hr in H.
        apply Rdichotomy in H.
        destruct H as [H| H]; [ | lra ].
        apply Rlt_not_le in H.
        exfalso; apply H; rewrite Hr.
        apply vec_norm_nonneg.
Qed.

(* J(axis) = set of angles of rotation around the axis, such that
   for some p in D ∩ sphere(r), for some naturals n and k,
   R((angle+2kπ)/n) is also in D ∩ sphere(r) where r = ‖axis‖. *)
Definition J axis :=
  mkset
    (λ '(sinθ, cosθ),
    ∃ sinθ₀ cosθ₀ n k,
    (sinθ₀, cosθ₀) ∈ J₀ axis ∧
    sinθ = sin ((asin sinθ₀ + 2 * INR k * PI) / INR n) ∧
    cosθ = cos ((acos cosθ₀ + 2 * INR k * PI) / INR n)).

Definition J_of_nat axis n : (ℝ * ℝ) :=
  let '(nj, n₂) := prod_nat_of_nat n in
  let '(nk, nn) := prod_nat_of_nat n₂ in
  let '(sinθ₀, cosθ₀) := J₀_of_nat axis nj in
  let sinθ := sin ((asin sinθ₀ + 2 * INR nk * PI) / INR nn) in
  let cosθ := cos ((acos cosθ₀ + 2 * INR nk * PI) / INR nn) in
  (sinθ, cosθ).

Theorem J_is_countable : ∀ axis,
  axis ∉ D
  → (- axis)%vec ∉ D
  → ∀ sc, sc ∈ J axis → ∃ n : ℕ, J_of_nat axis n = sc.
Proof.
intros axis Had Hnad (s, c) Ha.
destruct Ha as (s₀ & c₀ & n & k & Ha & Hs & Hc).
specialize (J₀_is_countable axis Had Hnad) as HJ.
specialize (HJ (s₀, c₀) Ha) as (nj, Hnj).
destruct Ha as (Hsc₀ & p & p' & (Hp & Hp' & Hmp)).
unfold J_of_nat.
remember (nat_of_prod_nat (k, n)) as n₂ eqn:Hn₂.
remember (nat_of_prod_nat (nj, n₂)) as m eqn:Hm.
exists m; subst m n₂.
do 2 rewrite prod_nat_of_nat_inv.
rewrite Hnj.
now f_equal.
Qed.

Theorem rotation_unit_axis_neq_0 : ∀ M,
  M ≠ mat_transp M
  → rotation_unit_axis M ≠ 0%vec.
Proof.
intros M HM.
unfold rotation_unit_axis.
unfold vec_normalize.
remember ‖(rotation_axis M)‖ as r eqn:Hr.
unfold rotation_axis; simpl.
intros Ha.
injection Ha; clear Ha; intros H3 H2 H1.
simpl in Hr.
destruct (Req_dec r 0) as [Hrz| Hrz].
 move Hrz at top; subst r.
 symmetry in Hr.
 apply sqrt_eq_0 in Hr; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in Hr.
 destruct Hr as (H6 & H5 & H4).
 apply Rminus_diag_uniq in H4.
 apply Rminus_diag_uniq in H5.
 apply Rminus_diag_uniq in H6.
 apply HM; simpl.
 unfold mat_transp, mkrmat.
 destruct M; simpl in *.
 now rewrite H4, H5, H6.

 apply Rinv_neq_0_compat in Hrz.
 apply Rmult_integral in H1.
 destruct H1 as [H1| H1]; [ easy | ].
 apply Rmult_integral in H2.
 destruct H2 as [H2| H2]; [ easy | ].
 apply Rmult_integral in H3.
 destruct H3 as [H3| H3]; [ easy | ].
 apply Rminus_diag_uniq in H1.
 apply Rminus_diag_uniq in H2.
 apply Rminus_diag_uniq in H3.
 apply HM; simpl.
 unfold mat_transp, mkrmat.
 destruct M; simpl in *.
 now rewrite H1, H2, H3.
Qed.

(*
Theorem axis_angle_of_matrix_inv : ∀ M,
  is_rotation_matrix M
  → M ≠ mat_transp M
  → matrix_of_axis_angle (axis_angle_of_matrix M) = M.
Proof.
intros M Hrm Hntr; symmetry.
generalize Hrm; intros (Hmtr, Hdet).
remember (matrix_of_axis_angle (axis_angle_of_matrix M)) as M' eqn:HM'.
assert (Hmt : -1 ≤ mat_trace M').
 rewrite HM'.
 remember (axis_angle_of_matrix M) as asc eqn:Hasc.
 symmetry in Hasc.
 destruct asc as ((a, s), c).
 apply mat_of_axis_angle_trace_interv.

bbb.
 apply mat_trace_ge_minus_1.
  unfold axis_angle_of_matrix in Hasc.
  injection Hasc; clear Hasc; intros Hc Hs Ha.
  rewrite <- Ha.
  now apply rotation_unit_axis_neq_0.

  unfold axis_angle_of_matrix in Hasc.
  injection Hasc; clear Hasc; intros Hc Hs Ha.
  rewrite <- Hc, <- Hs.
  rewrite Rsqr_sqrt; [ lra | ].
  eapply Rplus_le_reg_r.
  rewrite Rminus_plus.
  rewrite Rplus_0_l.
  rewrite Rsqr_div; [ | lra ].
  apply Rmult_le_reg_r with (r := 2²); [ unfold Rsqr; lra | ].
  rewrite Rmult_div_same; [ | unfold Rsqr; lra ].
  rewrite Rmult_1_l.
  specialize (mat_trace_large_interv M Hrm) as (H1, H2).
  apply Rsqr_neg_pos_le_1; [ | lra | lra ].

bbb.

unfold matrix_of_axis_angle, axis_angle_of_matrix.
remember (rotation_unit_axis M) as axis eqn:Hax.
destruct axis as (x, y, z).
unfold rotation_unit_axis in Hax.
remember (rotation_axis M) as v eqn:Hv.
destruct v as (x₀, y₀, z₀).
simpl in Hax.
injection Hax; clear Hax; intros Hz Hy Hx; simpl.
remember (√ (x₀² + y₀² + z₀²)) as r₀ eqn:Hr₀.
remember (√ (x² + y² + z²)) as r eqn:Hr.
remember (mat_trace M) as tr eqn:Htr.
remember ((tr - 1) / 2) as c eqn:Hc.
unfold mat_trace in Hc.
unfold mat_transp, mat_id, mat_mul, mkrmat in Hrm.
unfold mat_det in Hdet.
unfold mat_transp, mkrmat in Hntr.
unfold mat_trace in Htr; simpl in Htr.
unfold mkrmat.
destruct M; simpl in *.
injection Hrm; clear Hrm.
intros H33 H32 H31 H23 H22 H21 H13 H12 H11.
unfold rotation_axis in Hv; simpl in Hv.
injection Hv; clear Hv; intros Hz' Hy' Hx'.
destruct (Req_dec r₀ 0) as [Hr₀z| Hr₀nz].
 move Hr₀z at top; subst r₀.
 symmetry in Hr₀.
 apply sqrt_eq_0 in Hr₀; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in Hr₀.
 move Hr₀ at top; destruct Hr₀ as (H1 & H2 & H3); subst x₀ y₀ z₀.
 symmetry in Hx', Hy', Hz'.
 apply Rminus_diag_uniq in Hx'.
 apply Rminus_diag_uniq in Hy'.
 apply Rminus_diag_uniq in Hz'.
 move Hx' at top; subst a₃₂.
 move Hy' at top; subst a₁₃.
 move Hz' at top; subst a₂₁.
 easy.

 assert (H : r₀² ≠ 0 ∧ r = 1).
  split; [ now intros H; apply Hr₀nz; apply Rsqr_eq_0 in H | ].
  rewrite Hr, Hx, Hy, Hz.
  do 3 rewrite Rsqr_mult.
  rewrite Rsqr_inv; [ | easy ].
  do 2 rewrite <- Rmult_plus_distr_l.
  rewrite sqrt_mult; [ | | apply nonneg_sqr_vec_norm ].
   rewrite <- Hr₀.
   rewrite sqrt_inv.
    rewrite sqrt_Rsqr; [ | rewrite Hr₀; apply sqrt_pos ].
    rewrite Rinv_l; [ easy | lra ].

    specialize (Rle_0_sqr r₀) as H.
    enough (r₀² ≠ 0) by lra.
    now clear H; intros H; apply Rsqr_eq_0 in H.

   apply nonneg_inv.
   specialize (Rle_0_sqr r₀) as H.
   enough (r₀² ≠ 0) by lra.
   now clear H; intros H; apply Rsqr_eq_0 in H.

  destruct H as (Hr₀2 & Hr1).
  move Hr1 at top; subst r.
  progress repeat rewrite Rdiv_1_r.
  clear H23 H13 H12 H11.
  subst x y z c.
  rewrite Rsqr_div; [ | lra ].
  symmetry.
  f_equal.
   apply Rmult_eq_reg_r with (r := 2 * r₀²); [ | lra ].
   rewrite Rmult_plus_distr_r, Rsqr_mult.
   rewrite Rsqr_inv; [ | lra ].
   progress replace (/ r₀² * x₀² * (1 - (tr - 1) / 2) * (2 * r₀²))
   with (x₀² * (3 - tr) * (r₀² * / r₀²)) by lra.
   progress replace ((tr - 1) / 2 * (2 * r₀²))
   with ((tr - 1) * r₀²) by lra.
   rewrite Rinv_r; [ rewrite Rmult_1_r, Hr₀ | easy ].
   rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
   subst x₀ y₀ z₀ tr; ring_simplify.
   clear r₀ Hr Hr₀ Hr₀nz Hr₀2 Hntr.
   Time nsatz.

   apply Rmult_eq_reg_l with (r := 4 * r₀²); [ | lra ].
   rewrite Rmult_minus_distr_l.
   do 6 rewrite <- Rmult_assoc.
   do 3 rewrite Rsqr_pow2.
   progress replace (4 * r₀ ^ 2 * / r₀ * x₀ * / r₀ * y₀)
   with (4 * x₀ * y₀ * (r₀ / r₀) * (r₀ / r₀)) by lra.
   progress replace (4 * r₀ ^ 2 * / r₀ * z₀)
   with (4 * r₀ * z₀ * (r₀ / r₀)) by lra.
   rewrite Rdiv_same; [ do 3 rewrite Rmult_1_r | lra ].
   replace (2 ^ 2) with 4 by lra.
   progress replace (1 - (tr - 1) ^ 2 / 4) with ((4 - (tr - 1) ^ 2) / 4)
     by lra.
   rewrite sqrt_div; [ | | lra ].
Focus 2.
enough (-1 ≤ tr ≤ 3).
assert (-2 ≤ tr - 1 ≤ 2) by lra.
remember (tr - 1) as a.
clear -H0.
rewrite <- Rsqr_pow2.
apply Rplus_le_reg_r with (r := a²).
rewrite Rplus_0_l.
rewrite Rminus_plus.
replace 4 with (2 ^ 2) by lra.
rewrite <- Rsqr_pow2.
apply Rsqr_le_abs_1.
replace (Rabs 2) with 2; [ now apply Rabs_le | ].
unfold Rabs.
destruct (Rcase_abs 2); [ lra | easy ].
Abort.
(* requires to first prove that -1 ≤ tr ≤ 3 *)

bbb.
*)

Definition J_mat axis :=
  mkset
    (λ R,
     let '(v, sinθ, cosθ) := axis_angle_of_matrix R in
     v = axis ∧ (sinθ, cosθ) ∈ J axis).

Definition J_mat_of_nat axis n : matrix ℝ :=
  let '(sinθ, cosθ) := J_of_nat axis n in
  matrix_of_axis_angle (axis, sinθ, cosθ).

(*
Theorem J_mat_is_countable : ∀ axis,
  ∀ M, M ∈ J_mat axis → ∃ n : ℕ, J_mat_of_nat axis n = M.
Proof.
intros * HM.
unfold J_mat in HM.
remember axis_angle_of_matrix as f.
remember J as K.
simpl in HM; subst f K.
remember (axis_angle_of_matrix M) as vcs eqn:Hvcs.
symmetry in Hvcs.
destruct vcs as ((v, c), s).
destruct HM as (Hv & Hscj).
specialize (J_is_countable _ _ Hscj) as (n, HJ).
unfold J_mat_of_nat.
exists n.
rewrite HJ.
subst v; symmetry.
apply (f_equal matrix_of_axis_angle) in Hvcs.
Search (matrix_of_axis_angle (axis_angle_of_matrix _)).
(* above exists but not terminated (aborted) *)
bbb.
rewrite axis_angle_of_matrix_inv in Hvcs.
bbb.
*)

Definition I_of_ℝ x :=
  if Rlt_dec x 0 then 1 / (- x + 1) / 2
  else 1 / (x + 1) / 2 + 1 / 2.

Definition ℝ_of_I i :=
  if Rlt_dec i (1 / 2) then -1 / (i * 2) + 1
  else 1 / ((i - 1 / 2) * 2) - 1.

Theorem ℝ_of_I_inv : ∀ x, ℝ_of_I (I_of_ℝ x) = x.
Proof.
intros.
unfold ℝ_of_I, I_of_ℝ.
destruct (Rlt_dec x 0) as [Hxl| Hxl].
 destruct (Rlt_dec (1 / (- x + 1) / 2) (1 / 2)) as [Hlt| Hge].
  rewrite Rmult_div_same; [ | lra ].
  unfold Rdiv; rewrite Rmult_1_l.
  rewrite Rinv_involutive; lra.

  exfalso.
  apply Rnot_lt_le in Hge.
  apply Rmult_le_compat_r with (r := 2) in Hge; [ | lra ].
  rewrite Rmult_div_same in Hge; [ | lra ].
  rewrite Rmult_div_same in Hge; [ | lra ].
  apply Rmult_le_compat_r with (r := (- x + 1)) in Hge; [ | lra ].
  rewrite Rmult_1_l in Hge.
  rewrite Rmult_div_same in Hge; lra.

 apply Rnot_lt_le in Hxl.
 destruct (Rlt_dec (1 / (x + 1) / 2 + 1 / 2) (1 / 2)) as [Hlt| Hge].
  exfalso.
  apply Rmult_lt_compat_r with (r := 2) in Hlt; [ | lra ].
  rewrite Rmult_plus_distr_r in Hlt.
  rewrite Rmult_div_same in Hlt; [ | lra ].
  rewrite Rmult_div_same in Hlt; [ | lra ].
  apply Rmult_lt_compat_r with (r := (x + 1)) in Hlt; [ | lra ].
  rewrite Rmult_plus_distr_r in Hlt.
  rewrite Rmult_div_same in Hlt; lra.

  clear Hge.
  rewrite Rmult_minus_distr_r.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_div_same; [ | lra ].
  rewrite Rmult_div_same; [ | lra ].
  unfold Rminus; rewrite Rplus_assoc.
  rewrite Rplus_opp_r, Rplus_0_r.
  rewrite fold_Rminus.
  unfold Rdiv; do 2 rewrite Rmult_1_l.
  rewrite Rinv_involutive; lra.
Qed.

Theorem I_of_ℝ_interv : ∀ x, 0 ≤ I_of_ℝ x ≤ 1.
Proof.
intros x.
unfold I_of_ℝ.
destruct (Rlt_dec x 0) as [Hx| Hx].
 split.
  apply Rmult_le_reg_r with (r := 2); [ lra | ].
  rewrite Rmult_0_l, Rmult_div_same; [ | lra ].
  apply Rmult_le_reg_r with (r := - x + 1); [ lra | ].
  rewrite Rmult_0_l, Rmult_div_same; lra.

  apply Rmult_le_reg_r with (r := 2); [ lra | ].
  rewrite Rmult_div_same; [ | lra ].
  rewrite Rmult_1_l.
  apply Rmult_le_reg_r with (r := - x + 1); [ lra | ].
  rewrite Rmult_div_same; lra.

 split.
  apply Rmult_le_reg_r with (r := 2); [ lra | ].
  rewrite Rmult_plus_distr_r, Rmult_0_l.
  rewrite Rmult_div_same; [ | lra ].
  rewrite Rmult_div_same; [ | lra ].
  apply Rmult_le_reg_r with (r := x + 1); [ lra | ].
  rewrite Rmult_0_l.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_div_same; lra.

  apply Rnot_lt_le in Hx.
  apply Rmult_le_reg_r with (r := 2); [ lra | ].
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_div_same; [ | lra ].
  rewrite Rmult_div_same; [ | lra ].
  rewrite Rmult_1_l.
  apply Rmult_le_reg_r with (r := x + 1); [ lra | ].
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_div_same; lra.
Qed.

Theorem Cantor_ℕ_I : ∀ f : nat → R, ∃ x : R, 0 ≤ x ≤ 1 ∧ ∀ n : nat, x ≠ f n.
Proof.
intros f.
remember (λ n, ℝ_of_I (f n)) as g eqn:Hg.
specialize (Cantor_ℕ_ℝ g) as (x, Hx).
exists (I_of_ℝ x).
split; [ apply I_of_ℝ_interv | ].
intros n H.
subst g.
specialize (Hx n).
rewrite <- H in Hx.
apply Hx.
symmetry; apply ℝ_of_I_inv.
Qed.

Theorem rotations_not_countable :
  ∀ f : ℕ → ℝ * ℝ, ∃ sinθ cosθ,
  sinθ² + cosθ² = 1 ∧ ∀ n, f n ≠ (sinθ, cosθ).
Proof.
intros f.
specialize Cantor_ℕ_I as Hr.
specialize (Hr (λ n, fst (f n))) as (s & Hs & Ht).
exists s, (√ (1 - s²)).
split.
 rewrite Rsqr_sqrt; [ lra | ].
 apply Rplus_le_reg_r with (r := s²).
 rewrite Rplus_0_l, Rminus_plus.
 replace 1 with 1² by apply Rsqr_1.
 apply Rsqr_incr_1; [ easy | easy | lra ].

 intros n.
 intros H.
 apply (Ht n).
 now rewrite H.
Qed.

Theorem unit_sphere_matrix_of_angle_power : ∀ p s c n,
  ‖p‖ = 1
  → (matrix_of_axis_angle (p, s, c) ^ n)%mat =
    matrix_of_axis_angle (p, sin (INR n * asin s), cos (INR n * acos c)).
Proof.
intros * Hp.
induction n; intros.
 rewrite mat_pow_0.
 do 2 rewrite Rmult_0_l.
 rewrite sin_0, cos_0.
 symmetry; apply mat_sin_cos_0.

 remember (matrix_of_axis_angle (p, s, c)) as M eqn:HM.
 rewrite mat_pow_succ.
 rewrite S_INR.
 destruct p as (x, y, z).
 simpl in Hp, HM, IHn; simpl.
 rewrite Hp in HM, IHn; rewrite Hp.
 progress repeat rewrite Rdiv_1_r in HM, IHn.
 progress repeat rewrite Rdiv_1_r.
 rewrite IHn, HM.
 unfold mat_mul; simpl.
 f_equal.
  progress repeat rewrite Rmult_plus_distr_r.
  clear.
  apply Rminus_diag_uniq.
  unfold Rsqr.
  ring_simplify.
  progress repeat rewrite <- Rsqr_pow2.
Abort. (*
bbb.

 do 2 rewrite Rmult_plus_distr_r.
 do 2 rewrite Rmult_1_l.
 rewrite sin_plus, cos_plus.
bbb.

 rewrite sin_asin, cos_acos.
Search (sin (_ * _)).
Search (sin (acos _)).
Search (cos (asin _)).
bbb.

intros (x, y, z); intros * Hp.
unfold matrix_of_axis_angle.
simpl in Hp; rewrite Hp.
progress repeat rewrite Rdiv_1_r.
unfold matrix_of_unit_axis_angle.
Search (cos (_ * _)).

bbb.

Theorem matrix_of_angle_power : ∀ p s c n,
  (matrix_of_axis_angle (p, s, c) ^ n)%mat =
  matrix_of_axis_angle (p, sin (INR n * asin s), cos (INR n * acos c)).
Proof.
intros (x, y, z); intros.
unfold matrix_of_axis_angle.
remember (√ (x² + y² + z²)) as r eqn:Hr.
unfold matrix_of_unit_axis_angle.
bbb.

intros.
revert s c.
induction n; intros.
 rewrite mat_pow_0.
 do 2 rewrite Rmult_0_l.
 rewrite sin_0, cos_0.
 symmetry; apply mat_sin_cos_0.

 rewrite S_INR.
 do 2 rewrite Rmult_plus_distr_r.
 do 2 rewrite Rmult_1_l.
 rewrite sin_plus, cos_plus.
 rewrite sin_asin, cos_acos.
Search (sin (_ * _)).
Search (sin (acos _)).
Search (cos (asin _)).
bbb.
*)

Theorem equidec_ball_with_and_without_fixpoints :
  equidecomposable ball ball_but_fixpoints.
Proof.
intros.
assert (H : ∃ p₁, p₁ ∈ ball ∖ D ∧ (-p₁)%vec ∈ ball ∖ D).
 unfold "∈", "∖".
 specialize (D_set_and_its_symmetric_are_countable 1) as (f, Hdnc).
 specialize (ball_set_not_countable 1 Rlt_0_1 f) as (p & Hps & Hp).
 exists p.
 split.
  split.
   apply on_sphere_in_ball in Hps; [ easy | ].
   split; [ apply Rle_0_1 | apply Rle_refl ].

   intros HD.
   assert (H : p ∈ (D ∪ sphere_sym D) ∩ sphere 1).
    now rewrite intersection_union_distr_r; left.

    specialize (Hdnc p H) as (n, Hdnc).
    revert Hdnc; apply Hp.

  split.
   apply neg_vec_in_ball.
   apply on_sphere_in_ball in Hps; [ easy | ].
   split; [ apply Rle_0_1 | apply Rle_refl ].

   intros HD.
   assert (H : p ∈ (D ∪ sphere_sym D) ∩ sphere 1).
    now rewrite intersection_union_distr_r; right.

    specialize (Hdnc p H) as (n, Hdnc).
    revert Hdnc; apply Hp.

 destruct H as (p₁ & (Hpb & Hpnd) & (Hqb & Hqnd)).
 assert (∃ s c, s² + c² = 1 ∧ (s, c) ∉ J p₁) as (s & c & Hsc & Hj).
  specialize (J_is_countable p₁ Hpnd Hqnd) as Hjc.
  specialize (rotations_not_countable (J_of_nat p₁)) as (s, (c, (Hsc, Hn))).
  exists s, c; split; [ easy | intros H ].
  specialize (Hjc _ H) as (n, Hjc).
  now specialize (Hn n).

  assert (Hp₁z : p₁ ≠ 0%vec).
   intros H; apply Hpnd; rewrite H; simpl.
   exists (ạ :: []), 0%vec.
   split.
    exists (ạ :: []).
    now rewrite rotate_vec_mul, mat_vec_mul_0_r.

    split; [ easy | ].
    now rewrite rotate_vec_mul, mat_vec_mul_0_r.

   remember (matrix_of_axis_angle (p₁, s, c)) as ρ eqn:Hρ.
   remember (sphere ‖p₁‖) as S₂ eqn:HS₂.
   remember (mkset (λ p, ∃ p₀ n, p₀ ∈ D ∩ S₂ ∧ p = ((ρ ^ n)%mat * p₀)%vec))
     as E eqn:HE.
   assert (Hpart : is_partition S₂ [E; S₂ ∖ E]).
    split.
     simpl; rewrite union_empty_r.
     split; intros H.
      now destruct (EM (x ∈ E)) as [Hi| Hni]; [ left | right ].

      rename x into v.
      destruct H as [H| H]; [ | now destruct H ].
      rewrite HE in H; simpl in H.
      destruct H as (p₀ & n & ((el & p & Hso & Hnl & Hel) & Hp₀) & Hv).
      subst S₂ v.
      apply on_sphere_after_rotation; [ easy | ].
      apply mat_pow_is_rotation_matrix; rewrite Hρ.
      now apply matrix_of_axis_angle_is_rotation_matrix.

     intros i j Hij.
     destruct i.
      destruct j; [ easy | ].
      destruct j.
       intros v.
       now split; intros Hv; [ simpl in Hv | ].

       simpl; rewrite match_id.
       apply intersection_empty_r.

      destruct j.
       destruct i.
        intros v.
        now split; intros Hv; [ simpl in Hv | ].

        simpl; rewrite match_id.
        apply intersection_empty_l.

       destruct i.
        destruct j; [ easy | ].
        simpl; rewrite match_id.
        apply intersection_empty_r.

        destruct j.
         simpl; rewrite match_id.
         apply intersection_empty_l.

         simpl; do 2 rewrite match_id.
         apply intersection_empty_l.

    remember (mkset (λ u, ∃ v, v ∈ E ∧ u = (ρ * v)%vec)) as ρE eqn:HρE.
    assert (Hdec : equidecomposable S₂ (ρE ∪ (S₂ ∖ E))).
     unfold equidecomposable.
     exists [E; S₂ ∖ E], [ρE; S₂ ∖ E].
     split; [ easy | ].
     split.
      split; [ now simpl; rewrite union_empty_r | ].
      intros i j Hij.
      assert (H : (ρE ∩ (S₂ ∖ E) = ∅)%S).
       split; intros H; [ | easy ].
       simpl in H.
       destruct H as (HxρE & HxS₂ & HxnE).
       rewrite HρE in HxρE; simpl in HxρE.
       destruct HxρE as (v & Hv & Hxv).
       rewrite Hxv in HxnE.
       exfalso; apply HxnE; clear HxnE.
       rewrite HE in Hv |-*.
       simpl in Hv; simpl.
       destruct Hv as (p₀ & n & Hv).
       exists p₀, (S n).
       destruct Hv as (((el & p₂ & Hel) & Hp₀) & Hv).
       split.
        now split; [ exists el, p₂ | ].

        rewrite Hv, <- mat_vec_mul_assoc.
        now rewrite <- mat_pow_succ.

       destruct i.
        destruct j; [ easy | ].
        destruct j; [ easy | ].
        simpl; rewrite match_id.
        apply intersection_empty_r.

        destruct i.
         destruct j; [ now rewrite intersection_comm | ].
         destruct j; [ easy | ].
         simpl; rewrite match_id.
         apply intersection_empty_r.

         destruct j.
          simpl; rewrite match_id.
          apply intersection_empty_l.

          destruct j.
           simpl; rewrite match_id.
           apply intersection_empty_l.

           simpl; do 2 rewrite match_id.
           apply intersection_empty_l.

      constructor.
       assert (Hρm : is_rotation_matrix ρ).
        rewrite Hρ.
        now apply matrix_of_axis_angle_is_rotation_matrix.

        exists (Rot ρ Hρm); simpl.
        intros v.
        split; intros H.
         destruct H as (u & H).
         rewrite HρE; simpl.
         now exists u.

         rewrite HρE in H; simpl in H.
         destruct H as (u & H); simpl.
         now exists u.

       constructor; [ | constructor ].
       exists gr_ident.
       apply app_gr_ident.

     assert (ρE = E ∖ D)%S.
      intros v.
      split; intros H.
       rewrite HρE in H.
       destruct H as (u & Hu & Hv).
       remember D as d; simpl; subst d.
       split.
        rewrite HE in Hu; rewrite HE.
        remember D as d; remember intersection as b.
        simpl in Hu; simpl; subst d b.
        destruct Hu as (p₀ & n & Hp₀ & Hu).
        exists p₀, (S n).
        split; [ easy | simpl ].
        now rewrite mat_vec_mul_assoc, <- Hu.

        unfold J in Hj.
        remember J₀ as a; simpl in Hj; subst a.
        intros Hvn.
        apply Hj; clear Hj.
        rewrite HE in Hu.
        remember D as d; remember intersection as b.
        simpl in Hu; subst d b.
        destruct Hu as (p₀ & n & (Hp₀d & Hp₀S) & Hu).
(* this θ₀ is a rotation from p₀ to v... *)
Print J₀.
bbb.
Check mat_eq_dec.
 assert
   (H : ∃ sinθ₀ cosθ₀,
    ∀ p p' n sinθ cosθ,
    p ∈ D ∩ sphere ‖p₁‖ ∧
    p' ∈ D ∩ sphere ‖p₁‖ ∧
    sinθ = sin (asin sinθ₀ / INR n) ∧
    cosθ = cos (acos cosθ₀ / INR n)
    → (matrix_of_axis_angle (p₁, sinθ, cosθ) * p ≠ p')%vec).
  assert (Hp₁nz : p₁ ≠ 0%vec).
   intros H; apply Hpnd; subst p₁; simpl.
   exists (ạ :: []), 0%vec.
   split; [ apply same_orbit_refl | ].
   split; [ easy | simpl; f_equal; lra ].

   specialize (J_is_countable p₁) as Hjc.
   specialize (rotations_not_countable (J_of_nat p₁)) as (s, (c, (Hsc, Hn))).
   exists s, c.
   intros * (Hp & Hp' & Hs & Hc) H.
   unfold J_of_nat in Hn.
   specialize (Hn n).
   remember (prod_nat_of_nat n) as nj eqn:Hnj; symmetry in Hnj.
   destruct nj as (nj, n₂).
   remember (prod_nat_of_nat n₂) as nkn eqn:Hnkn; symmetry in Hnkn.
   destruct nkn as (nk, nn).
   remember (J₀_of_nat p₁ nj) as sc₀ eqn:Hsc₀.
   destruct sc₀ as (s₀, c₀).
   unfold J₀_of_nat in Hsc₀.
   remember (prod_nat_of_nat nj) as n₁₂ eqn:Hn₁₂; symmetry in Hn₁₂.
   destruct n₁₂ as (n₁, n'₂).
   remember (prod_nat_of_nat n₁) as nfo eqn:Hnfo; symmetry in Hnfo.
   destruct nfo as (nf, no).
   remember (prod_nat_of_nat n'₂) as nfo' eqn:Hnfo'; symmetry in Hnfo'.
   destruct nfo' as (nf', no').
   remember (fixpoint_of_nat ‖p₁‖ nf) as v₁ eqn:Hv₁.
   remember (fixpoint_of_nat ‖p₁‖ nf') as v'₁ eqn:Hv'₁.
   remember (path_of_nat no) as el eqn:Hel.
   remember (path_of_nat no') as el' eqn:Hel'.
   remember (fold_right rotate v₁ el) as u₁ eqn:Hu₁.
   remember (fold_right rotate v'₁ el') as u'₁ eqn:Hu'₁.
   unfold rot_sin_cos in Hsc₀.
   remember (latitude p₁ u₁) as a eqn:Ha.
   remember (u₁ - a ⁎ p₁)%vec as w₁ eqn:Hw₁.
   remember (u'₁ - a ⁎ p₁)%vec as w'₁ eqn:Hw'₁.
   remember (√ (1 - a²)) as r eqn:Hr.

bbb.

 assert
   (H : ∃ R₁, R₁ ∈ rotation_around p₁
    ∧ ∀ n p p', p ∈ D ∩ sphere ‖p₁‖ → p' ∈ D ∩ sphere ‖p₁‖
    → ((R₁ ^ n)%mat * p ≠ p')%vec).
  assert (Hp₁nz : p₁ ≠ 0%vec).
   intros H; apply Hpnd; subst p₁; simpl.
   exists (ạ :: []), 0%vec.
   split; [ apply same_orbit_refl | ].
   split; [ easy | simpl; f_equal; lra ].

(**)
bbb.
rotation_around =
λ p : vector,
{| setp := λ R : matrix ℝ, is_rotation_matrix R ∧ (R * p)%vec = p |}
     : vector → set (matrix ℝ)

J =
λ axis : vector,
{|
setp := λ '(sinθ, cosθ),
        ∃ (sinθ₀ cosθ₀ : ℝ) (n k : ℕ),
        (sinθ₀, cosθ₀) ∈ J₀ axis
        ∧ sinθ = sin ((asin sinθ₀ + 2 * INR k * PI) / INR n)
          ∧ cosθ = cos ((acos cosθ₀ + 2 * INR k * PI) / INR n) |}
     : vector → set (ℝ * ℝ)

bbb.
   specialize (J_is_countable p₁) as (f, Hdnc); [ easy | easy | ].
   specialize (rotation_around_not_countable p₁ Hp₁nz f) as (R₁ & HR₁ & Hn).
   exists R₁.
   split; [ easy | ].
   intros * Hp Hp' HRnp.
   assert (H : R₁ ∈ J p₁).
    split; [ easy | ].
    now exists p, p', n.

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
