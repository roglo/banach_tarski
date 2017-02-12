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

Definition ter_bin_of_vec r '(V x y z) := ter_bin_of_frac_part (x / r).

Theorem ter_bin_of_ball_surj : ∀ r, (0 < r)%R → ∀ (u : ℕ → bool),
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
  apply in_sphere_in_ball with (r := 1); [ | easy ].
  split; [ apply Rle_0_1 | apply Rle_refl ].

  intros n Hn.
  specialize (H n).
  destruct H.
  now symmetry in Hn.
Qed.

Theorem ball_set_not_countable : ∀ r, (0 < r)%R →
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

(* Non-nul vector belonging to the axis of rotation.
   Works for rotations angles different from 0 and π,
   i.e. transpositor ≠ 0 (a "transpositor" is a name I
   give to a vector which is nul iff the matrix is equal
   to its transpose; this name is inspired from the
   name "commutator") *)
Definition rotation_axis (M : matrix ℝ) :=
  let x := (a₃₂ M - a₂₃ M)%R in
  let y := (a₁₃ M - a₃₁ M)%R in
  let z := (a₂₁ M - a₁₂ M)%R in
  V x y z.

Definition vec_normalize '(V x y z) :=
  let r := ∥(V x y z)∥ in
  V (x / r) (y / r) (z / r).

Definition rotation_unit_axis (M : matrix ℝ) :=
  vec_normalize (rotation_axis M).

Definition rotation_fixpoint (m : matrix ℝ) k :=
  vec_const_mul k (rotation_unit_axis m).

Definition fixpoint_of_path r el :=
  rotation_fixpoint (mat_of_path el) r.

Definition fixpoint_of_nat r n :=
  fixpoint_of_path r (path_of_nat n).

(* https://en.wikipedia.org/wiki/Rotation_matrix#Determining_the_angle *)
Definition cos_rot_angle M := ((mat_trace M - 1) / 2)%R.

Theorem ortho_matrix_sqr_coeff_le_1 : ∀ M,
  (M * mat_transp M)%mat = mat_id
  → (((a₁₁ M)² ≤ 1 ∧ (a₁₂ M)² ≤ 1 ∧ (a₁₃ M)² ≤ 1) ∧
     ((a₂₁ M)² ≤ 1 ∧ (a₂₂ M)² ≤ 1 ∧ (a₂₃ M)² ≤ 1) ∧
     ((a₃₁ M)² ≤ 1 ∧ (a₃₂ M)² ≤ 1 ∧ (a₃₃ M)² ≤ 1))%R.
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
  replace (a₁₁²)%R with (a₁₁² + 0)%R at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_shuffle0, Rplus_comm.
  replace (a₁₂²)%R with (a₁₂² + 0)%R at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_comm.
  replace (a₁₃²)%R with (a₁₃² + 0)%R at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

 rewrite <- H22.
 split; [ | split ].
  rewrite Rplus_assoc.
  replace (a₂₁²)%R with (a₂₁² + 0)%R at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_shuffle0, Rplus_comm.
  replace (a₂₂²)%R with (a₂₂² + 0)%R at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_comm.
  replace (a₂₃²)%R with (a₂₃² + 0)%R at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

 rewrite <- H33.
 split; [ | split ].
  rewrite Rplus_assoc.
  replace (a₃₁²)%R with (a₃₁² + 0)%R at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_shuffle0, Rplus_comm.
  replace (a₃₂²)%R with (a₃₂² + 0)%R at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.

  rewrite Rplus_comm.
  replace (a₃₃²)%R with (a₃₃² + 0)%R at 1 by lra.
  apply Rplus_le_compat_l, nonneg_plus_sqr.
Qed.

Theorem Rsqr_le_1_interv : ∀ x, (x² ≤ 1 → -1 ≤ x ≤ 1)%R.
Proof.
intros * Hx.
replace 1%R with (1 ^ 2)%R in Hx by lra.
rewrite <- Rsqr_pow2 in Hx.
split; [ apply Rsqr_neg_pos_le_0; lra | ].
apply Rsqr_incr_0_var; lra.
Qed.

Theorem ortho_matrix_coeff_interv : ∀ M,
  (M * mat_transp M)%mat = mat_id
  → ((-1 ≤ a₁₁ M ≤ 1 ∧ -1 ≤ a₁₂ M ≤ 1 ∧ -1 ≤ a₁₃ M ≤ 1) ∧
     (-1 ≤ a₂₁ M ≤ 1 ∧ -1 ≤ a₂₂ M ≤ 1 ∧ -1 ≤ a₂₃ M ≤ 1) ∧
     (-1 ≤ a₃₁ M ≤ 1 ∧ -1 ≤ a₃₂ M ≤ 1 ∧ -1 ≤ a₃₃ M ≤ 1))%R.
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

Theorem mat_trace_interv : ∀ M,
  is_rotation_matrix M
  → (-1 ≤ mat_trace M ≤ 3)%R.
Proof.
intros * (Hrm & Hdet).
specialize (ortho_matrix_coeff_interv _ Hrm) as Ha.
destruct Ha as (Ha₁ & Ha₂ & Ha₃).
destruct Ha₁ as (Ha₁₁ & Ha₁₂ & Ha₁₃).
destruct Ha₂ as (Ha₂₁ & Ha₂₂ & Ha₂₃).
destruct Ha₃ as (Ha₃₁ & Ha₃₂ & Ha₃₃).
unfold mat_trace.
split; [ | lra ].
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
remember (a₁₂ * (a₂₃ * a₃₁ - a₃₃ * a₂₁))%R as u eqn:Hu.
remember (a₁₃ * (a₂₁ * a₃₂ - a₃₁ * a₂₂))%R as v eqn:Hv.
remember (u + v)%R as w eqn:Hw; subst u v.
apply Rplus_eq_compat_r with (r := (- w)%R) in Hdet.
rewrite Rplus_assoc, fold_Rminus in Hdet.
replace (w - w)%R with 0%R in Hdet by lra.
rewrite Rplus_0_r, fold_Rminus in Hdet.
destruct (Req_dec w 1%R) as [Hw1| Hw1].
 move Hw1 at top; subst w.
 replace (1 - 1)%R with 0%R in Hdet by lra.
 symmetry in Hw.
 apply Rmult_integral in Hdet.
 destruct Hdet as [Hdet| Hdet].
  subst a₁₁; clear Ha₁₁.
  rewrite Rsqr_0, Rplus_0_l in H11.
  rewrite Rmult_0_l, Rplus_0_l in H12, H13.
  rewrite Rplus_0_l.
  remember (a₁₃ * (a₂₁ * a₃₂ - a₃₁ * a₂₂))%R as v eqn:Hv.
  apply Rplus_eq_compat_r with (r := (- v)%R) in Hw.
  rewrite Rplus_assoc, fold_Rminus in Hw.
  replace (v - v)%R with 0%R in Hw by lra.
  rewrite Rplus_0_r, fold_Rminus in Hw.
  destruct (Req_dec v 1%R) as [Hv1| Hv1].
   move Hv1 at top; subst v.
   replace (1 - 1)%R with 0%R in Hw by lra.
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
    apply Rmult_eq_compat_r with (r := (/ a₃₃)%R) in Hw.
    symmetry in Hw; rewrite Rmult_shuffle0 in Hw.
    rewrite Rinv_r in Hw; [ rewrite Rmult_1_l in Hw | lra ].
    subst a₂₁.
    replace (a₂₃ * a₃₁ * / a₃₃ * a₃₂ - a₃₁ * a₂₂)%R
    with (a₃₁ * (a₂₃ * / a₃₃ * a₃₂ - a₂₂))%R in Hv by lra.
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
    replace ((a₂₃ * / a₃₃ * a₃₂ - a₂₂) * a₃₃)%R
    with (a₂₃ * a₃₂ * (/ a₃₃ * a₃₃) - a₂₂ * a₃₃)%R in Hv by lra.
    rewrite Rinv_l in Hv; [ | lra ].
    rewrite Rmult_1_r, Rmult_1_l in Hv.
    rewrite Rsqr_mult in H22.
    apply Rmult_eq_compat_r with (r := (a₃₃²)%R) in H22.
    rewrite Rplus_assoc in H22.
    rewrite Rmult_plus_distr_r in H22.
    rewrite Rmult_assoc in H22.
    rewrite <- Rsqr_mult in H22.
    rewrite Rinv_l in H22; [ | lra ].
    rewrite Rsqr_1 in H22.
    rewrite Rmult_1_r, Rmult_1_l in H22.
    assert (H : ((a₂₃ * a₃₁)² = a₃₃² * (1 - (a₂₂² + a₂₃²)))%R) by lra.
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
   (a₁₁ * a₂₂ * a₃₃ + a₃₂ * a₂₁ * a₁₃ + a₂₃ * a₁₂ * a₃₁ =
    a₁₁ * a₃₂ * a₂₃ + a₂₂ * a₃₁ * a₁₃ + a₃₃ * a₁₂ * a₂₁ + 1)%R) by lra.
 clear Hdet; rename Hdet' into Hdet.
bbb.
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
remember (a₃₂ M - a₂₃ M)%R as x eqn:Hx.
remember (a₁₃ M - a₃₁ M)%R as y eqn:Hy.
remember (a₂₁ M - a₁₂ M)%R as z eqn:Hz.
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
 replace (k * x)%R with (x * k)%R by apply Rmult_comm.
 replace (k * y)%R with (y * k)%R by apply Rmult_comm.
 replace (k * z)%R with (z * k)%R by apply Rmult_comm.
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
remember ∥(V x y z)∥ as r eqn:Hr.
unfold Rdiv.
setoid_rewrite Rmult_comm.
rewrite vec_mul_diag.
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

Theorem normalized_vec_normalize : ∀ v, v ≠ 0%vec → ∥(vec_normalize v)∥ = 1%R.
Proof.
intros (x, y, z) Hv; simpl.
remember (√ (x² + y² + z²)) as r eqn:Hr.
destruct (Req_dec r 0) as [Hrz| Hrnz].
 rewrite Hrz in Hr; symmetry in Hr.
 apply (f_equal Rsqr) in Hrz.
 apply sqrt_eq_0 in Hr; [ | apply nonneg_sqr_vec_norm ].
 apply sqr_vec_norm_eq_0 in Hr.
 exfalso; apply Hv; f_equal; lra.

 rewrite Rsqr_div; [ | easy ].
 rewrite Rsqr_div; [ | easy ].
 rewrite Rsqr_div; [ | easy ].
 do 2 rewrite <- Rdiv_plus_distr.
 rewrite sqrt_div_alt; [ | now apply Rlt_0_sqr ].
 rewrite Hr, sqrt_Rsqr; [ | apply sqrt_pos ].
 rewrite Rdiv_same; [ easy | now subst r ].
Qed.

Theorem rotation_fixpoint_on_sphere : ∀ r M,
   M ≠ mat_transp M
   → rotation_fixpoint M r ∈ sphere r.
Proof.
intros * Hm.
unfold rotation_fixpoint; simpl.
do 3 rewrite Rsqr_mult.
do 2 rewrite <- Rmult_plus_distr_l.
remember (a₃₂ M - a₂₃ M)%R as x eqn:Hx.
remember (a₁₃ M - a₃₁ M)%R as y eqn:Hy.
remember (a₂₁ M - a₁₂ M)%R as z eqn:Hz.
remember (x² + y² + z²)%R as r₁ eqn:Hr₁.
destruct (Req_dec r₁ 0) as [Hrz| Hrz].
 move Hrz at top; subst r₁; symmetry in Hr₁.
 apply sqr_vec_norm_eq_0 in Hr₁.
 destruct Hr₁ as (H1 & H2 & H3); subst x y z.
 apply Rminus_diag_uniq in H1.
 apply Rminus_diag_uniq in H2.
 apply Rminus_diag_uniq in H3.
 unfold mat_transp, mkrmat.
 destruct M; simpl in *.
 now subst.

 destruct (Req_dec (√ r₁) 0) as [Hsrz| Hsrz].
  apply sqrt_eq_0 in Hsrz; [ easy | ].
  rewrite Hr₁; apply nonneg_sqr_vec_norm.

  rewrite Rsqr_div; [ | easy ].
  rewrite Rsqr_div; [ | easy ].
  rewrite Rsqr_div; [ | easy ].
  do 2 rewrite <- Rdiv_plus_distr.
  rewrite Rsqr_sqrt; [ | subst r₁; apply nonneg_sqr_vec_norm ].
  rewrite <- Hr₁.
  rewrite Rdiv_same; [ now rewrite Rmult_1_r | easy ].
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

Theorem rotation_fixpoint_norm : ∀ M r, (0 ≤ r)%R
  → M ≠ mat_transp M
  → ∥(rotation_fixpoint M r)∥ = r.
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
  → ∃ a b, a ≠ 0%R ∧ b ≠ 0%R ∧ (a ⁎ u + b ⁎ v = 0)%vec.
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
  exists v₃, (- u₃)%R.
  split; [ now intros H; apply Hv; f_equal | ].
  split; [ now apply Ropp_neq_0_compat; intros H; apply Hu; f_equal | ].
  f_equal; lra.

  destruct (Req_dec u₂ 0) as [Hu₂| Hu₂].
   subst u₂; rewrite Rmult_0_l in H₁; symmetry in H₁.
   apply Rmult_integral in H₁.
   destruct H₁ as [H₁| H₁]; [ now exfalso; subst u₃; apply Hu | subst v₂ ].
   exists v₃, (- u₃)%R.
   split; [ now intros H; apply Hv; f_equal | ].
   split; [ now apply Ropp_neq_0_compat; intros H; apply Hu; f_equal | ].
   f_equal; lra.

   destruct (Req_dec u₃ 0) as [Hu₃| Hu₃].
    subst u₃; rewrite Rmult_0_l in H₁.
    apply Rmult_integral in H₁.
    destruct H₁ as [H₁| H₁]; [ easy | subst v₃ ].
    exists v₂, (-u₂)%R.
    split; [ now intros H; apply Hv; f_equal | ].
    split; [ now apply Ropp_neq_0_compat; intros H; apply Hu; f_equal | ].
    f_equal; lra.

    destruct (Req_dec v₂ 0) as [Hv₂| Hv₂].
     subst v₂; rewrite Rmult_0_r in H₁.
     apply Rmult_integral in H₁.
     destruct H₁ as [H₁| H₁]; [ easy | now exfalso; subst v₃; apply Hv ].

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
  destruct H₂ as [H₂| H₂]; [ easy | now exfalso; subst v₃; apply Hv ].

  exists v₁, (- u₁)%R.
  split; [ easy | ].
  split; [ now apply Ropp_neq_0_compat | ].
  f_equal; lra.
Qed.

Theorem free_family_diff_norm_vec : ∀ u v,
  ∥u∥ = ∥v∥
  → u ≠ v
  → is_neg_vec u = is_neg_vec v
  → u ≠ 0%vec
  → v ≠ 0%vec
  → ∀ a b : ℝ, (a ⁎ u + b ⁎ v)%vec = 0%vec → a = 0%R ∧ b = 0%R.
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
    fold (vec_opp (V x₁ y₁ z₁)) in Hn.
    rewrite is_neg_vec_neg_vec in Hn; [ | easy ].
    now symmetry in Hn; apply no_fixpoint_negb in Hn.

   intros H; apply Hv₁.
   apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
   apply sqr_vec_norm_eq_0 in H.
   now destruct H as (Hx & Hy & Hz); subst.
Qed.

Theorem nonzero_cross_mul : ∀ u v,
  ∥u∥ = ∥v∥
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

Theorem vec_cross_mul_are_free_family : ∀ u v,
  ∥u∥ = ∥v∥
  → is_neg_vec u = is_neg_vec v
  → u ≠ 0%vec
  → v ≠ 0%vec
  → u ≠ v
  → ∀ a b c : ℝ,
    (a ⁎ u + b ⁎ v + c ⁎ (u × v))%vec = 0%vec
    → a = 0%R ∧ b = 0%R ∧ c = 0%R.
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
  (u × v · u × v) ≠ 0%R
  → ∃ a b c, X = (a ⁎ u + b ⁎ v + c ⁎ (u × v))%vec.
Proof.
intros * Huv.
remember (u × v · u × v) as r eqn:Hr.
exists (((X · u) * (v · v) - (X · v) * (u · v)) / r)%R.
exists (((X · v) * (u · u) - (X · u) * (u · v)) / r)%R.
exists ((X · (u × v)) / r)%R.
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
  → ∥u∥ = ∥v∥
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
  remember (vec_const_mul (∥u∥ / ∥(u × v)∥)%R (u × v)) as W eqn:HW.
  move W before v.
  assert (Hp₃ : (M * (u × v) = u × v)%vec).
   apply mat_vec_mul_cross_distr with (u := u) (v := v) in Hm.
   now rewrite Hp₁, Hp₂ in Hm.

   move Hp₃ before Hp₂.
   assert (Hucv : ∥(u × v)∥ ≠ 0%R).
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
    replace (- ax₁)%R with (-1 * ax₁)%R in Hbv by lra.
    replace (- ay₁)%R with (-1 * ay₁)%R in Hbv by lra.
    replace (- az₁)%R with (-1 * az₁)%R in Hbv by lra.
    fold (vec_const_mul (-1) (V ax₁ ay₁ az₁)) in Hbv.
    rewrite <- Hau in Hbv.
    rewrite vec_const_mul_assoc in Hbv.
    replace (-1 * a)%R with (-a)%R in Hbv by lra.
    apply vec_const_mul_div in Hbv; [ | easy ].
    rewrite Hbv in Hvn.
    rewrite vec_norm_vec_const_mul in Hvn.
    replace (∥u∥) with (1 * ∥u∥)%R in Hvn at 1 by lra.
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
     assert (Huv : u × v · u × v ≠ 0%R).
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

(* We know, from theory of linear algebra, that tr(M) = 1 + 2 cos θ.
   Therefore, when θ varies from 0 to 2π, tr(M) varies between -1 and 3.
   Then (tr(M)+1)/4 varies from 0 to 1. *)
Definition ter_bin_of_rotation M :=
  ter_bin_of_frac_part ((mat_trace M + 1) / 4).

Definition matrix_of_unit_axis_angle '(V x y z, c, s) :=
  mkrmat
    (x²*(1-c)+c) (x*y*(1-c)-z*s) (x*z*(1-c)+y*s)
    (x*y*(1-c)+z*s) (y²*(1-c)+c) (y*z*(1-c)-x*s)
    (x*z*(1-c)-y*s) (y*z*(1-c)+x*s) (z²*(1-c)+c).

Definition matrix_of_axis_angle '(V x y z, c, s) :=
  let r := (√ (x² + y² + z²))%R in
  let ux := (x / r)%R in
  let uy := (y / r)%R in
  let uz := (z / r)%R in
  matrix_of_unit_axis_angle (V ux uy uz, c, s).

Definition axis_angle_of_matrix M :=
  let cosθ := ((mat_trace M - 1) / 2)%R in
  let sinθ := √ (1 - cosθ²) in
  let v := rotation_unit_axis M in
  (v, cosθ, sinθ).

Arguments axis_angle_of_matrix M%mat.

Theorem matrix_of_axis_angle_inv : ∀ v c s,
  (0 < s)%R
  → ∥v∥ = 1%R
  → (s² + c² = 1)%R
  → axis_angle_of_matrix (matrix_of_axis_angle (v, c, s)) = (v, c, s).
Proof.
intros v cosθ sinθ Hsp Hvs Hsc.
assert (Hvnz : (v ≠ 0)%vec) by (intros H; rewrite H, vec_norm_0 in Hvs; lra).
remember (v, cosθ, sinθ) as acs eqn:Hacs.
unfold axis_angle_of_matrix.
remember (matrix_of_axis_angle acs) as M eqn:HM.
remember (mat_trace M) as tr eqn:Htr.
remember ((tr - 1) / 2)%R as c eqn:Hc.
remember (√ (1 - c²))%R as s eqn:Hs.
subst acs; simpl.
simpl in HM.
destruct v as (x, y, z).
simpl in Hvs.
rewrite Hvs in HM.
progress repeat rewrite Rdiv_1_r in HM.
unfold rotation_unit_axis, rotation_axis; simpl.
rewrite HM; unfold mkrmat ; simpl.
unfold mat_trace in Htr.
rewrite HM in Htr; unfold mkrmat in Htr; simpl in Htr.
rename cosθ into c₁.
do 2 rewrite <- Rplus_assoc in Htr.
replace (x² * (1 - c₁) + c₁ + y² * (1 - c₁) + c₁ + z² * (1 - c₁) + c₁)%R
with ((x² + y² + z²) * (1 - c₁) + 3 * c₁)%R in Htr by lra.
assert (Hv2s : (x² + y² + z² = 1)%R).
 apply (f_equal Rsqr) in Hvs.
 rewrite Rsqr_sqrt in Hvs; [ | apply nonneg_sqr_vec_norm ].
 rewrite Hvs; apply Rsqr_1.

 rewrite Hv2s, Rmult_1_l in Htr.
 ring_simplify in Htr.
 rewrite Htr in Hc.
 assert (H : c = c₁) by lra.
 move H at top; subst c₁; clear Hc.
 assert (H : (sinθ² = 1 - c²)%R) by lra.
 rewrite <- H in Hs.
 rewrite sqrt_Rsqr in Hs; [ | lra ].
 move Hs at top; subst sinθ; clear H.
 f_equal; f_equal; symmetry.
 replace (y * z * (1 - c) + x * s - (y * z * (1 - c) - x * s))%R
 with (2 * x * s)%R by lra.
 replace (x * z * (1 - c) + y * s - (x * z * (1 - c) - y * s))%R
 with (2 * y * s)%R by lra.
 replace (x * y * (1 - c) + z * s - (x * y * (1 - c) - z * s))%R
 with (2 * z * s)%R by lra.
 progress repeat rewrite Rsqr_mult.
 progress repeat rewrite <- Rmult_plus_distr_r.
 progress repeat rewrite <- Rmult_plus_distr_l.
 rewrite Hv2s, Rmult_1_r.
 rewrite <- Rsqr_mult.
 rewrite sqrt_Rsqr; [ | lra ].
 replace (2 * x * s / (2 * s))%R with ((2 * s) * / (2 * s) * x)%R by lra.
 replace (2 * y * s / (2 * s))%R with ((2 * s) * / (2 * s) * y)%R by lra.
 replace (2 * z * s / (2 * s))%R with ((2 * s) * / (2 * s) * z)%R by lra.
 rewrite Rinv_r; [ | lra ].
 f_equal; lra.
Qed.

Theorem axis_angle_of_matrix_inv : ∀ M,
  is_rotation_matrix M
  → M ≠ mat_transp M
  → matrix_of_axis_angle (axis_angle_of_matrix M) = M.
Proof.
intros M (Hrm, Hdet) Hntr; symmetry.
unfold matrix_of_axis_angle, axis_angle_of_matrix.
remember (rotation_unit_axis M) as axis eqn:Hax.
destruct axis as (x, y, z).
unfold rotation_unit_axis in Hax.
remember (rotation_axis M) as v eqn:Hv.
destruct v as (x₀, y₀, z₀).
simpl in Hax.
injection Hax; clear Hax; intros Hz Hy Hx; simpl.
remember (√ (x₀² + y₀² + z₀²))%R as r₀ eqn:Hr₀.
remember (√ (x² + y² + z²))%R as r eqn:Hr.
remember (mat_trace M) as tr eqn:Htr.
remember ((tr - 1) / 2)%R as c eqn:Hc.
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

 assert (H : (r₀² ≠ 0 ∧ r = 1)%R).
  split; [ now intros H; apply Hr₀nz; apply Rsqr_eq_0 in H | ].
  rewrite Hr, Hx, Hy, Hz.
  rewrite Rsqr_div; [ | easy ].
  rewrite Rsqr_div; [ | easy ].
  rewrite Rsqr_div; [ | easy ].
  do 2 rewrite <- Rdiv_plus_distr.
  rewrite sqrt_div; [ | apply nonneg_sqr_vec_norm | now apply Rlt_0_sqr ].
  rewrite <- Hr₀.
  rewrite sqrt_Rsqr; [ | rewrite Hr₀; apply sqrt_pos ].
  rewrite Rdiv_same; [ easy | lra ].

  destruct H as (Hr₀2 & Hr1).
  move Hr1 at top; subst r.
  progress repeat rewrite Rdiv_1_r.
  clear H23 H13 H12 H11.
  subst x y z c.
  rewrite Rsqr_div; [ | easy ].
  symmetry.
  f_equal.
   apply Rmult_eq_reg_r with (r := (2 * r₀²)%R); [ | lra ].
   rewrite Rmult_plus_distr_r.
   replace (x₀² / r₀² * (1 - (tr - 1) / 2) * (2 * r₀²))%R
   with (x₀² * (3 - tr) * (r₀² * / r₀²))%R by lra.
   replace ((tr - 1) / 2 * (2 * r₀²))%R
   with ((tr - 1) * r₀²)%R by lra.
   rewrite Rinv_r; [ rewrite Rmult_1_r, Hr₀ | easy ].
   rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
   subst x₀ y₀ z₀ tr; ring_simplify.
   clear r₀ Hr Hr₀ Hr₀nz Hr₀2 Hntr.
   Time nsatz.

   apply Rmult_eq_reg_l with (r := (4 * r₀²)%R); [ | lra ].
   rewrite Rmult_minus_distr_l.
   do 3 rewrite <- Rmult_assoc.
   do 2 rewrite Rsqr_pow2.
   replace (4 * r₀ ^ 2 * (x₀ / r₀) * (y₀ / r₀))%R
   with (4 * x₀ * y₀ * (r₀ / r₀) * (r₀ / r₀))%R by lra.
   replace (4 * r₀ ^ 2 * (z₀ / r₀))%R
   with (4 * r₀ * z₀ * (r₀ / r₀))%R by lra.
   rewrite Rdiv_same; [ do 3 rewrite Rmult_1_r | lra ].
   replace (1 - ((tr - 1) / 2) ^ 2)%R with ((4 - (tr - 1) ^ 2) / 4)%R
     by lra.
   rewrite sqrt_div; [ | | lra ].
Focus 2.
enough (-1 ≤ tr ≤ 3)%R.
assert (-2 ≤ tr - 1 ≤ 2)%R by lra.
remember (tr - 1)%R as a.
clear -H0.
rewrite <- Rsqr_pow2.
apply Rplus_le_reg_r with (r := (a²)%R).
rewrite Rplus_0_l.
rewrite Rminus_plus.
replace 4%R with (2 ^ 2)%R by lra.
rewrite <- Rsqr_pow2.
apply Rsqr_le_abs_1.
replace (Rabs 2)%R with 2%R; [ now apply Rabs_le | ].
unfold Rabs.
destruct (Rcase_abs 2); [ lra | easy ].
Abort.
(* requires to first prove that -1 ≤ tr ≤ 3 *)

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
  let r := (a² + v²%vec)%R in
  quat_const_mul (/ r) (quat_conj (quat a v)).

Notation "h₁ + h₂" := (quat_add h₁ h₂) : quat_scope.
Notation "h₁ * h₂" := (quat_mul h₁ h₂) : quat_scope.
Notation "'hi'" := (Qi) : quat_scope.
Notation "'hj'" := (Qj) : quat_scope.
Notation "'hk'" := (Qk) : quat_scope.
Notation "h '⁻¹'" := (quat_inv h) (at level 1, format "h ⁻¹"): quat_scope.
Notation "∥ h ∥" := (quat_norm h) : quat_scope.

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
  let s := (√ (1 + mat_trace M) / 2)%R in
  let x := ((a₃₂ M - a₂₃ M) / (4 * s))%R in
  let y := ((a₁₃ M - a₃₁ M) / (4 * s))%R in
  let z := ((a₂₁ M - a₁₂ M) / (4 * s))%R in
  quat s (V x y z).

Definition mat_of_quat '(quat a (V b c d)) :=
  mkrmat
    (a² + b² - c² - d²) (2 * b * c - 2 * a * d) (2 * a * c + 2 * b * d)
    (2 * a * d + 2 * b * c) (a² - b² + c² - d²) (2 * c * d - 2 * a * b)
    (2 * b * d - 2 * a * c) (2 * a * b + 2 * c * d) (a² - b² - c² + d²).

Definition quat_rotate h v := (h * v * h⁻¹)%H.

Theorem mat_of_quat_inv : ∀ M,
  is_rotation_matrix M
  → mat_trace M ≠ -1%R
  → mat_of_quat (quat_of_mat M) = M.
Proof.
intros * Hrm Hmt.
unfold quat_of_mat, mat_of_quat; simpl; symmetry.
unfold mat_trace in Hmt.
remember (√ (1 + mat_trace M) / 2)%R as s eqn:Hs.
remember ((a₃₂ M - a₂₃ M) / (4 * s))%R as x eqn:Hx.
remember ((a₁₃ M - a₃₁ M) / (4 * s))%R as y eqn:Hy.
remember ((a₂₁ M - a₁₂ M) / (4 * s))%R as z eqn:Hz.
unfold mat_trace in Hs.
destruct M; simpl in *; unfold mkrmat.
f_equal.
 generalize Hs; intros Hs2.
 apply (f_equal Rsqr) in Hs2.
 unfold Rdiv in Hs2.
 rewrite Rsqr_mult in Hs2.
 do 3 rewrite Rsqr_pow2 in Hs2.
 replace ((/ 2) ^ 2)%R with (/ 4)%R in Hs2 by lra.
 do 2 rewrite <- Rsqr_pow2 in Hs2.
 rewrite Rsqr_sqrt in Hs2.
 rewrite Hs2, Hx, Hy, Hz.
 unfold Rdiv.
 do 3 rewrite Rsqr_mult.
 rewrite Rsqr_inv.
  rewrite Rsqr_mult.
  do 5 rewrite Rsqr_pow2.
  replace (4 ^ 2)%R with 16%R by lra.
  remember 16%R as sixteen.
  remember 4%R as four.
  rewrite Rinv_mult_distr; [ | lra | ].
  do 3 rewrite <- Rmult_assoc.
  apply Rmult_eq_reg_r with (r := (sixteen * s ^ 2)%R).
  unfold Rminus.
  do 9 rewrite Rmult_plus_distr_r.
  do 3 rewrite fold_Rminus.
  subst four sixteen.
  do 10 rewrite fold_Rdiv.
  do 2 rewrite <- Ropp_mult_distr_l.
  do 2 rewrite fold_Rminus.
  replace
    ((1 / 4 * (16 * s ^ 2) +
      (a₁₁ / 4 * (16 * s ^ 2) + a₂₂ / 4 * (16 * s ^ 2) +
       a₃₃ / 4 * (16 * s ^ 2)) +
      (a₃₂ - a₂₃) ^ 2 / 16 / s ^ 2 * (16 * s ^ 2) -
      (a₁₃ - a₃₁) ^ 2 / 16 / s ^ 2 * (16 * s ^ 2) -
      (a₂₁ - a₁₂) ^ 2 / 16 / s ^ 2 * (16 * s ^ 2))%R) with
    ((4 * s ^ 2 * (1 + (a₁₁ + a₂₂ + a₃₃)) +
      (a₃₂ - a₂₃) ^ 2 * (/ s ^ 2 * s ^ 2) -
      (a₁₃ - a₃₁) ^ 2 * (/ s ^ 2 * s ^ 2) -
      (a₂₁ - a₁₂) ^ 2 * (/ s ^ 2 * s ^ 2))%R) by lra.
  rewrite Rinv_l.
   do 3 rewrite Rmult_1_r.
   rewrite Rsqr_pow2 in Hs2.
   replace (1 + (a₁₁ + a₂₂ + a₃₃))%R with (4 * s ^ 2)%R by lra.
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
 remember (a₁₁ M - a₂₂ M - a₃₃ M)%R as x₀ eqn:Hx₀.
 remember (- a₁₁ M + a₂₂ M - a₃₃ M)%R as y₀ eqn:Hy₀.
 remember (- a₁₁ M - a₂₂ M + a₃₃ M)%R as z₀ eqn:Hz₀.
 remember ((√ (1 + x₀) / 2)%R) as x eqn:Hx.
 remember ((√ (1 + y₀) / 2)%R) as y eqn:Hy.
 remember ((√ (1 + z₀) / 2)%R) as z eqn:Hz.
 generalize Hx; intros Hx2.
 generalize Hy; intros Hy2.
 generalize Hz; intros Hz2.
 apply (f_equal Rsqr) in Hx2.
 apply (f_equal Rsqr) in Hy2.
 apply (f_equal Rsqr) in Hz2.
 unfold Rdiv in Hx2, Hy2, Hz2.
 rewrite Rsqr_mult in Hx2, Hy2, Hz2.
 do 3 rewrite Rsqr_pow2 in Hx2, Hy2, Hz2.
 replace ((/ 2) ^ 2)%R with (/ 4)%R in Hx2, Hy2, Hz2 by lra.
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
     remember (1 + (a₁₁ - a₂₂ - a₃₃))%R as x₁.
     remember (1 + (- a₁₁ + a₂₂ - a₃₃))%R as y₁.
     replace (2 * (√ x₁ / 2) * (√ y₁ / 2))%R with (√ x₁ * √ y₁ / 2)%R by lra.
     rewrite <- sqrt_mult_alt.
     remember (x₁ * y₁)%R as xy eqn:Hxy.
     rewrite Heqx₁, Heqy₁ in Hxy.
     ring_simplify in Hxy.
     do 3 rewrite <- Rsqr_pow2 in Hxy.
(* seems not to work... *)
*)

Definition vec_le '(V u₁ u₂ u₃) '(V v₁ v₂ v₃) :=
  (u₁ ≤ v₁ ∧ u₂ ≤ v₂ ∧ u₃ ≤ v₃)%R.

Notation "u '≤' v" := (vec_le u v) : vec_scope.

Theorem quat_of_mat_inv1 : ∀ h,
  (∥h∥ = 1%R)%H
  → (0 < Re h)%R
  → quat_of_mat (mat_of_quat h) = h.
Proof.
intros * Hhn Hrp.
destruct h as (a, (b, c, d)); simpl in Hrp; simpl.
apply sqrt_lem_0 in Hhn; [ | apply nonneg_plus_4_sqr | apply Rle_0_1 ].
symmetry in Hhn; rewrite Rmult_1_r in Hhn.
unfold quat_of_mat, mat_of_quat; simpl.
unfold mat_trace; simpl.
remember (a² + b² - c² - d² + (a² - b² + c² - d²) + (a² - b² - c² + d²))%R
  as t eqn:Ht.
remember (a² + b² - c² - d² - (a² - b² + c² - d²) - (a² - b² - c² + d²))%R
  as x₀ eqn:Hx₀.
remember (- (a² + b² - c² - d²) + (a² - b² + c² - d²) - (a² - b² - c² + d²))%R
  as y₀ eqn:Hy₀.
remember (- (a² + b² - c² - d²) - (a² - b² + c² - d²) + (a² - b² - c² + d²))%R
  as z₀ eqn:Hz₀.
ring_simplify in Ht.
ring_simplify in Hx₀.
ring_simplify in Hy₀.
ring_simplify in Hz₀.
assert (Ht' : t = (4 * a² - 1)%R) by lra.
clear Ht; rename Ht' into Ht.
destruct (Req_dec t (-1)) as [Htd| Htd].
 assert (Ha : (a = 0)%R) by (now apply Rsqr_eq_0; lra); subst a.
 now apply Rlt_irrefl in Hrp.

 assert (Ha2 : (a² ≠ 0)%R) by lra.
 assert (Ha : (a ≠ 0)%R) by now intros H; subst a; apply Ha2, Rsqr_0.
 assert (Haa : (Rabs a ≠ 0)%R) by now apply Rabs_no_R0.
 assert (Hta : (√ (1 + t) / 2 = Rabs a)%R).
  rewrite Ht, Rplus_minus.
  rewrite Rsqr_pow2.
  replace (4 * a ^ 2)%R with ((2 * a) ^ 2)%R by lra.
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
  assert (Rpm : ∀ a b c, (a + b - (b - c) = a + c)%R) by (intros; lra).
  do 3 rewrite Rpm.
  replace (2 * a * b + 2 * a * b)%R with (4 * a * b)%R by lra.
  replace (2 * a * c + 2 * a * c)%R with (4 * a * c)%R by lra.
  replace (2 * a * d + 2 * a * d)%R with (4 * a * d)%R by lra.
  unfold Rdiv.
  rewrite Rinv_mult_distr; [ | lra | easy ].
  do 3 rewrite <- Rmult_assoc.
  replace (4 * a * b * / 4)%R with (a * b)%R by lra.
  replace (4 * a * c * / 4)%R with (a * c)%R by lra.
  replace (4 * a * d * / 4)%R with (a * d)%R by lra.
  rewrite Hrp.
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  now do 3 rewrite Rmult_1_l.
Qed.

Theorem quat_of_mat_inv2 : ∀ h,
  (∥h∥ = 1%R)%H
  → (0 ≤ Re h)%R
  → (0 ≤ Im h)%vec
  → quat_of_mat (mat_of_quat h) = h.
Proof.
intros * Hhn Hrp Hvp.
destruct h as (a, (b, c, d)); simpl in Hrp, Hvp; simpl.
apply sqrt_lem_0 in Hhn; [ | apply nonneg_plus_4_sqr | apply Rle_0_1 ].
symmetry in Hhn; rewrite Rmult_1_r in Hhn.
unfold quat_of_mat, mat_of_quat; simpl.
unfold mat_trace; simpl.
remember (a² + b² - c² - d² + (a² - b² + c² - d²) + (a² - b² - c² + d²))%R
  as t eqn:Ht.
remember (a² + b² - c² - d² - (a² - b² + c² - d²) - (a² - b² - c² + d²))%R
  as x₀ eqn:Hx₀.
remember (- (a² + b² - c² - d²) + (a² - b² + c² - d²) - (a² - b² - c² + d²))%R
  as y₀ eqn:Hy₀.
remember (- (a² + b² - c² - d²) - (a² - b² + c² - d²) + (a² - b² - c² + d²))%R
  as z₀ eqn:Hz₀.
ring_simplify in Ht.
ring_simplify in Hx₀.
ring_simplify in Hy₀.
ring_simplify in Hz₀.
assert (Ht' : t = (4 * a² - 1)%R) by lra.
clear Ht; rename Ht' into Ht.
destruct (Req_dec t (-1)) as [Htd| Htd].
 (* here case with trace = -1, i.e. angle = π, not yet treated; I have to
    think of it. Going to next case. *)
Focus 2.
 assert (Ha2 : (a² ≠ 0)%R) by lra.
 assert (Ha : (a ≠ 0)%R) by now intros H; subst a; apply Ha2, Rsqr_0.
 assert (Haa : (Rabs a ≠ 0)%R) by now apply Rabs_no_R0.
 assert (Hta : (√ (1 + t) / 2 = Rabs a)%R).
  rewrite Ht, Rplus_minus.
  rewrite Rsqr_pow2.
  replace (4 * a ^ 2)%R with ((2 * a) ^ 2)%R by lra.
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
  assert (Rpm : ∀ a b c, (a + b - (b - c) = a + c)%R) by (intros; lra).
  do 3 rewrite Rpm.
  replace (2 * a * b + 2 * a * b)%R with (4 * a * b)%R by lra.
  replace (2 * a * c + 2 * a * c)%R with (4 * a * c)%R by lra.
  replace (2 * a * d + 2 * a * d)%R with (4 * a * d)%R by lra.
  unfold Rdiv.
  rewrite Rinv_mult_distr; [ | lra | easy ].
  do 3 rewrite <- Rmult_assoc.
  replace (4 * a * b * / 4)%R with (a * b)%R by lra.
  replace (4 * a * c * / 4)%R with (a * c)%R by lra.
  replace (4 * a * d * / 4)%R with (a * d)%R by lra.
  rewrite Hrp.
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  rewrite Rmult_shuffle0, Rinv_r; [ | easy ].
  now do 3 rewrite Rmult_1_l.
Abort.

(* end play with quaternions. *)

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
  → is_rotation_matrix (matrix_of_axis_angle (p, cosθ, sinθ)).
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

Theorem axis_of_matrix_is_eigen_vec : ∀ p cosθ sinθ,
  (sinθ² + cosθ² = 1)%R
  → (matrix_of_axis_angle (p, cosθ, sinθ) * p)%vec = p.
Proof.
intros (xp, yp, zp) * Hsc.
remember ((√ (xp² + yp² + zp²))%R) as r eqn:Hr.
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

 exists (matrix_of_axis_angle (p, cosθ, sinθ)).
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

Theorem rotate_unicity : ∀ p₁ p₂ el,
  ∥p₁∥ = ∥p₂∥
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
   assert (Hpp2 : ∥p₁∥ = ∥(-p₂)∥).
    rewrite Hpp; destruct p₂ as (x, y, z); simpl.
    now do 3 rewrite <- Rsqr_neg.

    rewrite <- is_neg_vec_neg_vec in Hnn; [ | easy ].
    assert (Hr₂2 : (M * - p₂ = - p₂)%vec).
     now rewrite mat_opp_vec_mul_distr_r, Hr₂.

     specialize (fixpoint_unicity M p₁ (- p₂)%vec Hrm Hni Hpp2 Hnn Hr₁ Hr₂2).
     easy.
Qed.

(* latitude of p₁ relative to p, p being the north pole;
   equal to the dot product and between -r and r, supposing
   that p and p₁ belong to the sphere of ray r. *)
Definition latitude p p₁ := (p · p₁).

Theorem rotation_same_latitude : ∀ p p₁ p₂ c s,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → p₂ ∈ sphere 1
  → (matrix_of_axis_angle (p, c, s) * p₁ = p₂)%vec
  → latitude p p₁ = latitude p p₂.
Proof.
intros * Hp Hp₁ Hp₂ Hm.
unfold latitude.
destruct p as (x, y, z).
simpl in Hp; rewrite Rsqr_1 in Hp.
simpl in Hm; rewrite Hp, sqrt_1 in Hm.
do 3 rewrite Rdiv_1_r in Hm.
destruct p₁ as (x₁, y₁, z₁).
destruct p₂ as (x₂, y₂, z₂).
simpl in Hp₁, Hp₂; rewrite Rsqr_1 in Hp₁, Hp₂.
simpl in Hm.
injection Hm; clear Hm; intros Hz Hy Hx.
simpl; nsatz.
Qed.

Theorem latitude_norm : ∀ p p₁ v a,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → a = latitude p p₁
  → v = (p₁ - a ⁎ p)%vec
  → ∥v∥ = √ (1 - a²).
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
replace z₁²%R with (1 - x₁² - y₁²)%R by lra.
ring_simplify.
progress replace (-2 * x₁ * a * x - 2 * a * y₁ * y - 2 * a * z₁ * z)%R
with (-2 * a * (x * x₁ + y * y₁ + z * z₁))%R by lra.
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
  ∥v₁∥ = 1%R
  → ∥v₂∥ = 1%R
  → p = v₁ × v₂
  → p ≠ 0%vec
  → c = (v₁ · v₂)
  → s = ∥p∥
  → (matrix_of_axis_angle (p, c, s) * v₁)%vec = v₂.
Proof.
intros * Hv₁ Hv₂ Hp Hpz Hc Hs.
assert (Hcs : (c² + s² = 1)%R).
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
 assert (Hsz : s ≠ 0%R).
  intros H; rewrite Hs in H.
  apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
  apply sqr_vec_norm_eq_0 in H.
  destruct H as (H1 & H2 & H3).
  now rewrite H1, H2, H3 in Hpz.

  rewrite Rmult_div_same; [ | easy ].
  rewrite Rmult_div_same; [ | easy ].
  rewrite Rmult_div_same; [ | easy ].
  assert (H : (xp * x₁ + yp * y₁ + zp * z₁ = 0)%R) by (subst; lra).
  rewrite Rsqr_div; [ | easy ].
  rewrite Rsqr_div; [ | easy ].
  rewrite Rsqr_div; [ | easy ].
  unfold Rsqr, Rdiv.
  rewrite Rinv_mult_distr; [ | lra | lra ].
  do 4 rewrite fold_Rdiv.
  progress replace
    ((xp * xp * (/ s / s) * (1 - c) + c) * x₁ +
     (xp / s * (yp / s) * (1 - c) - zp) * y₁ +
     (xp / s * (zp / s) * (1 - c) + yp) * z₁)%R
  with
    (xp * (1 - c) * (xp * x₁ + yp * y₁ + zp * z₁) * (/ s / s) +
     c * x₁ - zp * y₁ + yp * z₁)%R by lra.
  progress replace
    ((xp / s * (yp / s) * (1 - c) + zp) * x₁ +
     (yp * yp * (/ s / s) * (1 - c) + c) * y₁ +
     (yp / s * (zp / s) * (1 - c) - xp) * z₁)%R
  with
    (yp * (1 - c) * (xp * x₁ + yp * y₁ + zp * z₁) * (/ s / s) +
     zp * x₁ + c * y₁ - xp * z₁)%R by lra.
  replace
    ((xp / s * (zp / s) * (1 - c) - yp) * x₁ +
     (yp / s * (zp / s) * (1 - c) + xp) * y₁ +
     (zp * zp * (/ s / s) * (1 - c) + c) * z₁)%R
  with
    (zp * (1 - c) * (xp * x₁ + yp * y₁ + zp * z₁) * (/ s / s) +
     - yp * x₁ + xp * y₁ + c * z₁)%R by lra.
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
   replace (x₁ ^ 2 + y₁ ^ 2)%R with (1 - z₁ ^ 2)%R by lra.
   now rewrite Hxp; ring_simplify.

   ring_simplify.
   replace (z₁ ^ 2)%R with (1 - x₁ ^ 2 - y₁ ^ 2)%R by lra.
   now rewrite Hxp; ring_simplify.
Qed.

Theorem matrix_mul_axis : ∀ p c s k,
  (0 < k)%R
  → matrix_of_axis_angle (p, c, s) = matrix_of_axis_angle (k ⁎ p, c, s).
Proof.
intros * Hk.
destruct (vec_eq_dec p 0%vec) as [Hpz| Hpz].
 now subst p; simpl; rewrite Rmult_0_r.

 destruct p as (xp, yp, zp); simpl.
 remember (√ ((k * xp)² + (k * yp)² + (k * zp)²))%R as a eqn:Ha.
 do 3 rewrite Rsqr_mult in Ha.
 do 2 rewrite <- Rmult_plus_distr_l in Ha.
 rewrite sqrt_mult in Ha; [ | apply Rle_0_sqr | apply nonneg_sqr_vec_norm ].
 rewrite sqrt_Rsqr in Ha; [ | lra ].
 remember (√ (xp² + yp² + zp²)) as b eqn:Hb.
 assert (Hx : ∀ x, (k * x / a = x / b)%R).
  assert (Hbz : b ≠ 0%R).
   subst b; intros H.
   apply sqrt_eq_0 in H; [ | apply nonneg_sqr_vec_norm ].
   apply sqr_vec_norm_eq_0 in H.
   destruct H as (H1 & H2 & H3).
   now rewrite H1, H2, H3 in Hpz.

   intros x; subst a; unfold Rdiv.
   rewrite Rinv_mult_distr; [ | lra | easy ].
   rewrite <- Rmult_assoc.
   replace (k * x * / k)%R with (/ k * k * x)%R by lra.
   rewrite Rinv_l; lra.

  now do 3 rewrite Hx.
Qed.

(* not sure this lemma is required *)
Theorem rotate_matrix_of_two_vectors_with_mul_axis : ∀ p v₁ v₂ c s k,
  (0 ≤ k)%R
  → ∥v₁∥ = 1%R
  → ∥v₂∥ = 1%R
  → p = k ⁎ (v₁ × v₂)
  → p ≠ 0%vec
  → c = (v₁ · v₂)
  → s = ∥(/ k ⁎ p)∥
  → (matrix_of_axis_angle (p, c, s) * v₁)%vec = v₂.
Proof.
intros * Hknn Hv₁ Hv₂ Hp Hpz Hc Hs.
destruct (Req_dec k 0) as [Hkz| Hkz].
 now rewrite Hkz, vec_const_mul_0_l in Hp.

 rewrite matrix_mul_axis with (k := (/ k)%R).
  apply (f_equal (vec_const_mul (/ k))) in Hp.
  rewrite vec_const_mul_assoc in Hp.
  rewrite Rinv_l in Hp; [ | easy ].
  rewrite vec_const_mul_1_l in Hp.
  apply rotate_matrix_of_two_vectors; try assumption.
  intros H.
  apply eq_vec_const_mul_0 in H.
  destruct H as [H| H]; [ | easy ].
  now apply Rinv_neq_0_compat in H.

  apply Rmult_lt_reg_r with (r := k); [ lra | ].
  rewrite Rinv_l; [ lra | easy ].
Qed.

Theorem vec_cross_mul_cross_mul : ∀ u v,
  u · v = 0%R
  → ∥v∥ = 1%R
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

Theorem toto : ∀ p p₁ p₂ v₁ v₂ a c s,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → p₂ ∈ sphere 1
  → a = latitude p p₁
  → a = latitude p p₂
  → (a² < 1)%R
  → p₁ × p₂ ≠ 0%vec
  → v₁ = (/ √ (1 - a²) ⁎ (p₁ - a ⁎ p))%vec
  → v₂ = (/ √ (1 - a²) ⁎ (p₂ - a ⁎ p))%vec
  → c = v₁ · v₂
  → s = ∥(v₁ × v₂)∥
  → (matrix_of_axis_angle (p, c, s) * v₁)%vec = v₂.
Proof.
intros * Hp Hp₁ Hp₂ Ha₁ Ha₂ Ha2 Hppz Hv₁ Hv₂ Hc Hs.
assert (∥v₁∥ = 1%R ∧ ∥v₂∥ = 1%R) as (Hnv₁, Hnv₂).
 assert (H : √ (1 - a²) ≠ 0%R) by (intros H; apply sqrt_eq_0 in H; lra).
 eapply latitude_norm in Ha₁; [ | easy | easy | reflexivity ].
 eapply latitude_norm in Ha₂; [ | easy | easy | reflexivity ].
 rewrite Hv₁, Hv₂.
 do 2 rewrite vec_norm_vec_const_mul.
 rewrite Rabs_Rinv; [ | easy ].
 rewrite Rabs_sqrt, Ha₁, Ha₂.
 now rewrite Rinv_l.

 unfold latitude in Ha₁, Ha₂.
 specialize
   (rotate_matrix_of_two_vectors_with_mul_axis p v₁ v₂ c s) as H.
bbb.
 assert (∃ k, p = k ⁎ (v₁ × v₂)) as (k, Hk).
  rewrite Hv₁, Hv₂.
  remember (/ √ (1 - a²))%R as b eqn:Hb.

bbb.
  (* ∃ k, p = k ⁎ (v₁ × v₂) *)
  rewrite matrix_mul_axis with (k := (/ k)%R).
  apply rotate_matrix_of_two_vectors; try easy.
bbb.
(*
 assert (Hvvz : v₁ × v₂ ≠ 0%vec).
  rewrite Hv₁, Hv₂; intros H.
  rewrite <- vec_const_mul_cross_distr_l in H.
  rewrite <- vec_const_mul_cross_distr_r in H.
  apply eq_vec_const_mul_0 in H.
  destruct H as [H| H].
   apply Rinv_neq_0_compat in H; [ easy | ].
   clear H; intros H.
   apply sqrt_eq_0 in H; lra.

   apply eq_vec_const_mul_0 in H.
   destruct H as [H| H].
    apply Rinv_neq_0_compat in H; [ easy | ].
    clear H; intros H.
    apply sqrt_eq_0 in H; lra.

    rewrite vec_cross_mul_sub_distr_l in H.
    rewrite vec_cross_mul_sub_distr_r in H.
    rewrite <- vec_const_mul_cross_distr_l in H.
    rewrite <- vec_const_mul_cross_distr_r in H.
    rewrite vec_cross_mul_sub_distr_r in H.
    rewrite vec_const_mul_sub_distr_l in H.
    rewrite <- vec_const_mul_cross_distr_l in H.
    rewrite <- vec_const_mul_sub_distr_l in H.
    rewrite vec_cross_mul_diag in H.
    rewrite vec_const_mul_0_r in H.
    rewrite vec_sub_0_r in H.
    unfold vec_sub in H.
    rewrite <- vec_add_assoc in H.
    do 2 rewrite vec_opp_const_mul_distr_l in H.
    rewrite <- vec_const_mul_add_distr_l in H.
    replace (p₁ × p) with (- (p × p₁))%vec in H.
    2: symmetry; apply vec_cross_mul_anticomm.
    rewrite <- vec_opp_const_mul_distr_l in H.
    do 2 rewrite fold_vec_sub in H.
    rewrite <- vec_cross_mul_sub_distr_l in H.
    (* bof, pas convainquant, tout ça... *)
bbb.

  destruct p as (xp, yp, zp).
  destruct p₁ as (x₁, y₁, z₁).
  destruct p₂ as (x₂, y₂, z₂); simpl.

  do 2 rewrite vec_const_mul_sub_distr_l.
  rewrite vec_cross_mul_sub_distr_l.
  do 2 rewrite vec_cross_mul_sub_distr_r.
bbb.

rewrite vec_cross_mul_sub_distr_l.

bbb.
*)
bbb.

 assert (Hpvv : p = v₁ × v₂).
(* ah bin non c'est pas ça *)
bbb.
  destruct p as (xp, yp, zp).
  destruct p₁ as (x₁, y₁, z₁).
  destruct p₂ as (x₂, y₂, z₂).
  rewrite Hv₁, Hv₂; simpl.

  Inspect 1.

  assert (Hcs : (c² + s² = 1)%R).
bbb.

Theorem glop : ∀ p p₁ p₂ v₁ v₂ a c s,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → p₂ ∈ sphere 1
  → a = latitude p p₁
  → a = latitude p p₂
  → (a² < 1)%R
  → v₁ = (p₁ - a ⁎ p)%vec
  → v₂ = (p₂ - a ⁎ p)%vec
  → c = ((v₁ · v₂) / (1 - a²))%R
  → s = (∥(v₁ × v₂)∥ / (1 - a²))%R
  → (matrix_of_axis_angle (p, c, s) * v₁ = v₂)%vec.
Proof.
intros * Hp Hp₁ Hp₂ Ha₁ Ha₂ Ha2 Hv₁ Hv₂ Hc Hs.

bbb.

assert (Hqa₁ : ∥v₁∥ = √ (1 - a²)) by now apply (latitude_norm p p₁).
assert (Hqa₂ : ∥v₂∥ = √ (1 - a²)) by now apply (latitude_norm p p₂).
assert (Hcs : (c² + s² = 1)%R).
 specialize (vec_Lagrange_identity v₁ v₂) as H.
 rewrite vec_dot_mul_diag in H.
 rewrite Hqa₁, Hqa₂ in H.
 rewrite Rsqr_sqrt in H; [ | lra ].
 rewrite fold_Rsqr in H.
 apply Rmult_eq_compat_r with (r := (/ (1 - a²))²%R) in H.
 rewrite Rmult_minus_distr_r in H.
 do 3 rewrite <- Rsqr_mult, fold_Rdiv in H.
 rewrite <- Hc, <- Hs in H.
 rewrite Rdiv_same in H; [ rewrite Rsqr_1 in H; lra | lra ].

(**)
 assert (H : (matrix_of_axis_angle (p, c, s) * v₁ = v₂)%vec).
  remember (√ (1 - a²))%R as b eqn:Hb.
  apply (f_equal Rsqr) in Hb.
  rewrite Rsqr_sqrt in Hb; [ | lra ].
  rewrite <- Hb in Hc, Hs.
  assert (Hbz : (0 < b²)%R) by lra.
  rewrite <- Rsqr_0 in Hbz.
  apply Rsqr_incrst_0 in Hbz; [ | lra | ].
   clear a p₁ p₂ Hp₁ Hp₂ Ha₁ Ha₂ Ha2 Hb Hv₁ Hv₂.
bbb.
   destruct p as (xp, yp, zp).
   destruct v₁ as (x₁, y₁, z₁).
   destruct v₂ as (x₂, y₂, z₂); simpl in *.
   rewrite Rsqr_1 in Hp.
   rewrite Hp, sqrt_1; do 3 rewrite Rdiv_1_r.
   apply (f_equal Rsqr) in Hqa₁.
   apply (f_equal Rsqr) in Hqa₂.
   rewrite Rsqr_sqrt in Hqa₁; [ | apply nonneg_sqr_vec_norm ].
   rewrite Rsqr_sqrt in Hqa₂; [ | apply nonneg_sqr_vec_norm ].
   assert (Hpv₁ : (xp * x₁ + yp * y₁ + zp * z₁ = 0)%R).
   Focus 2.
   f_equal.
    unfold Rsqr.
    progress replace
      ((xp * xp * (1 - c) + c) * x₁ + (xp * yp * (1 - c) - zp * s) * y₁ +
       (xp * zp * (1 - c) + yp * s) * z₁)%R
    with
      (xp * (xp * x₁ + yp * y₁ + zp * z₁) +
       (x₁ - xp * (xp * x₁ + yp * y₁ + zp * z₁)) * c +
       - (zp * y₁ - yp * z₁) * s)%R
     by lra.
    rewrite Hpv₁, Rmult_0_r, Rplus_0_l, Rminus_0_r.
    apply Rplus_eq_reg_r with (r := -x₂%R).
    rewrite Rplus_opp_r.
    rewrite Rplus_shuffle0.
    apply Rplus_eq_reg_r with (r := ((zp * y₁ - yp * z₁) * s)%R).
    rewrite Rplus_assoc.
    rewrite <- Ropp_mult_distr_l.
    rewrite Rplus_opp_l, Rplus_0_r, Rplus_0_l.
    rewrite fold_Rminus.
(**)
apply Rsqr_inj.
Focus 3.
rewrite Rsqr_mult.
replace s²%R with (1 - c²)%R by lra.
apply Rminus_diag_uniq.
remember (zp * y₁ - yp * z₁)²%R as u eqn:Hu.
unfold Rsqr; ring_simplify.
progress repeat rewrite <- Rsqr_pow2.
replace (x₁² * c² - 2 * x₁ * c * x₂ + c² * u + x₂² - u)%R
with ((x₁² + u) * c² - 2 * x₁ * x₂ * c + (x₂² - u))%R
by lra.
apply Rmult_eq_reg_r with (r := b⁴%R).
rewrite Rmult_0_l.
unfold Rminus.
do 2 rewrite Rmult_plus_distr_r.
rewrite <- Ropp_mult_distr_l.
do 2 rewrite fold_Rminus.
do 2 rewrite Rmult_assoc.
progress repeat rewrite Rsqr_pow2.
replace (c ^ 2 * b⁴)%R with ((c * b ^ 2) ^ 2)%R by lra.
replace (c * b⁴)%R with (b ^ 2 * (c * b ^ 2))%R by lra.
progress repeat rewrite <- Rsqr_pow2.
rewrite Hc.
rewrite Rmult_div_same.
ring_simplify.
bbb.

replace z₁²%R with (b² - x₁² - y₁²)%R by lra.
replace z₂²%R with (b² - x₂² - y₂²)%R by lra.
ring_simplify.

bbb.
bbb.
    apply Rmult_eq_reg_r with (r := b²%R).
     rewrite Rmult_plus_distr_r.
     rewrite <- Ropp_mult_distr_l, fold_Rminus.
     do 2 rewrite Rmult_assoc.
     rewrite Hc, Hs.
     unfold Rdiv.
     do 2 rewrite Rmult_assoc.
     rewrite Rinv_l.
      do 2 rewrite Rmult_1_r.
      apply Rsqr_inj.
      Focus 3.
       rewrite Rsqr_mult.
       rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
       clear - Hp Hqa₁ Hqa₂ Hpv₁.
       apply Rminus_diag_uniq.
bbb.
       unfold Rsqr in *.
bbb.

bbb.
   rewrite <- Hqa₁; apply vec_norm_nonneg.
bbb.


 destruct p as (xp, yp, zp).
 destruct p₁ as (xp₁, yp₁, zp₁).
 destruct p₂ as (xp₂, yp₂, zp₂).
 simpl in *.
 rewrite Rsqr_1 in Hp, Hp₁, Hp₂.
 do 3 rewrite fold_Rminus in Hv₁, Hv₂.
 rewrite Hp, sqrt_1; do 3 rewrite Rdiv_1_r.
 rewrite Hv₁, Hv₂; simpl.
 f_equal.
  rewrite Rplus_assoc.
  progress replace
    ((xp * yp * (1 - c) - zp * s) * (yp₁ - a * yp) +
     (xp * zp * (1 - c) + yp * s) * (zp₁ - a * zp))%R
  with
    ((xp * yp * (1 - c)) * (yp₁ - a * yp) +
     (xp * zp * (1 - c)) * (zp₁ - a * zp) -
     (zp * (yp₁ - a * yp) - yp * (zp₁ - a * zp)) * s)%R
    by lra.
  unfold Rminus; do 2 rewrite <- Rplus_assoc.
  progress repeat rewrite fold_Rminus.
  remember ((zp * (yp₁ - a * yp) - yp * (zp₁ - a * zp)) * s)%R as u eqn:Hu.
  remember (xp₂ - a * xp)%R as v eqn:Hv.
  apply Rplus_eq_reg_r with (r := (u - v)%R).
  rewrite Rplus_minus.
  unfold Rminus; rewrite Rplus_assoc.
  replace (- u + (u + - v))%R with (- v)%R by lra.
  progress repeat rewrite fold_Rminus.
  subst u v.
  apply Rmult_eq_reg_r with (r := (1 - a²)%R); [ | lra ].
  do 5 rewrite Rmult_assoc.
  replace (s * (1 - a²))%R with ∥(v₁ × v₂)∥.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_minus_distr_r.
  do 3 rewrite Rmult_plus_distr_r.
  remember (xp₁ - a * xp)%R as x₁.
  remember (yp₁ - a * yp)%R as y₁.
  remember (zp₁ - a * zp)%R as z₁.
  progress replace
    (xp² * (1 - c) * x₁ * (1 - a²) +
     c * x₁ * (1 - a²) +
     xp * (yp * ((1 - c) * y₁)) * (1 - a²) +
     xp * (zp * ((1 - c) * z₁)) * (1 - a²))%R
  with
    ((xp² * (1 - a²) - xp² * (c * (1 - a²))) * x₁ +
     x₁ * (c * (1 - a²)) +
     xp * yp * y₁ * (1 - a²) - xp * yp * y₁ * (c * (1 - a²)) +
     xp * zp * z₁ * (1 - a²) - xp * zp * z₁ * (c * (1 - a²)))%R
    by lra.
  replace (c * (1 - a²))%R with (v₁ · v₂).
  apply Rsqr_inj.
  Focus 3.
  rewrite Rsqr_mult.
  rewrite <- vec_dot_mul_diag.
  rewrite Hv₁, Hv₂; simpl.
  remember (xp₂ - a * xp)%R as x₂.
  remember (yp₂ - a * yp)%R as y₂.
  remember (zp₂ - a * zp)%R as z₂.
  eapply Rplus_eq_reg_r.
  symmetry; rewrite Rplus_opp_r; symmetry.
  rewrite fold_Rminus.
  move y₁ before x₁; move z₁ before y₁.
  move x₂ before z₁; move y₂ before x₂; move z₂ before y₂.
  move Hv₁ before z₂; move Hv₂ before Hv₁.
remember (x₁ * x₂ + y₁ * y₂ + z₁ * z₂)%R as xyz eqn:Hxyz.
remember (y₁ * z₂ - z₁ * y₂)%R as X eqn:HX.
remember (z₁ * x₂ - x₁ * z₂)%R as Y eqn:HY.
remember (x₁ * y₂ - y₁ * x₂)%R as Z eqn:HZ.
move Y before X; move Z before Y.
progress repeat rewrite fold_Rsqr.
bbb.

 destruct p as (xp, yp, zp).
 destruct q₁ as (xq₁, yq₁, zq₁).
 destruct q₂ as (xq₂, yq₂, zq₂); simpl.
 simpl in Hp; rewrite Rsqr_1 in Hp; rewrite Hp.
 rewrite sqrt_1; do 3 rewrite Rdiv_1_r.
 f_equal.
bbb.

bbb.
destruct p₁ as (x₁, y₁, z₁).
destruct p₂ as (x₂, y₂, z₂); simpl in *.
rewrite Rsqr_1 in Hp, Hp₁, Hp₂.
do 3 rewrite fold_Rminus in Hq₁, Hq₂.
rewrite Hp, sqrt_1.
do 3 rewrite Rdiv_1_r.
subst q₁ q₂; simpl in Hc, Hs.
simpl.
f_equal.


bbb.
remember ((x₁ - a * xp) * (x₂ - a * xp))%R as u eqn:Hu.
rewrite Ha₁ in Hu at 1.
rewrite Ha₂ in Hu.
ring_simplify in Hu.
repeat rewrite <- Rsqr_pow2 in Hu.
ring_simplify in Hu.
replace zp²%R with (1 - xp² - yp²)%R in Hu by lra.
ring_simplify in Hu.
progress repeat rewrite Rsqr_pow2 in Hu.
replace ((xp ^ 2) ^ 2)%R with xp⁴%R in Hu by lra.
ring_simplify in Hu.

bbb.
unfold Rsqr in Hp.
rewrite Ha₁ in Hc at 1 3 5.
rewrite Ha₂ in Hc.
ring_simplify in Hc.
progress repeat rewrite <- Rsqr_pow2 in Hc.
remember s²%R as ss eqn:Hss.
rewrite Hs in Hss.
rewrite Rsqr_sqrt in Hss; [ | apply nonneg_sqr_vec_norm ].
progress repeat rewrite Rsqr_pow2 in Hss.
ring_simplify in Hss.
progress repeat rewrite <- Rsqr_pow2 in Hss.
rewrite Ha₁ in Hs at 1 3 5 7 9 11.
rewrite Ha₂ in Hs.
progress repeat rewrite Rsqr_pow2 in Hs.
ring_simplify in Hs.
progress repeat rewrite <- Rsqr_pow2 in Hs.

bbb.

(* false, I think *)
Theorem glop : ∀ p p₁ p₂ q₁ q₂ c s,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → p₂ ∈ sphere 1
  → latitude p p₁ = latitude p p₂
  → q₁ = (/ ∥ (p₁ × p)∥ ⁎ (p₁ × p))%vec
  → q₂ = (/ ∥ (p₂ × p)∥ ⁎ (p₂ × p))%vec
  → p₁ × p ≠ 0%vec
  → p₂ × p ≠ 0%vec
  → c = q₁ · q₂
  → s = ∥(q₁ × q₂)∥%R
  → (matrix_of_axis_angle (p, c, s) * q₁ = q₂)%vec.
Proof.
intros * Hp Hp₁ Hp₂ Hll Hq₁ Hq₂ Hq₁nz Hq₂nz Hc Hs.
assert (H : q₁ ∈ sphere 1 ∧ q₂ ∈ sphere 1).
 specialize (normalized_vector (p₁ × p) q₁ Hq₁nz Hq₁) as H₁.
 specialize (normalized_vector (p₂ × p) q₂ Hq₂nz Hq₂) as H₂.
 apply on_sphere_norm in H₁; [ | lra ].
 apply on_sphere_norm in H₂; [ | lra ].
 easy.

 destruct H as (Hq₁s, Hq₂s).
 specialize (vec_Lagrange_identity q₁ q₂) as Hli.
 destruct q₁ as (xq₁, yq₁, zq₁).
 destruct q₂ as (xq₂, yq₂, zq₂).
 simpl in Hq₁s, Hq₂s.
 rewrite Rsqr_1 in Hq₁s, Hq₂s.
 simpl in Hli.
 rewrite Hq₁s, Hq₂s in Hli.
 rewrite sqrt_1, Rsqr_1, Rmult_1_l in Hli.
bbb.

 destruct p as (xp, yp, zp); simpl in Hp.
 destruct p₁ as (x₁, y₁, z₁).
 destruct p₂ as (x₂, y₂, z₂); simpl in *.
 rewrite Rsqr_1 in Hp, Hp₁, Hp₂.
 rewrite Hp, sqrt_1.
 do 3 rewrite Rdiv_1_r.
remember (∥q₁∥ * ∥q₂∥)%R as rq eqn:Hrq.
subst c s.
remember (q₁ · q₂) as c eqn:Hc.
remember ∥(q₁ × q₂)∥ as s eqn:Hs.
specialize (vec_Lagrange_identity q₁ q₂) as Hli.
rewrite <- Rsqr_mult in Hli.
rewrite vec_dot_mul_diag in Hli.
rewrite <- Hrq, <- Hc, <- Hs in Hli.
rewrite Hq₁, Hq₂; simpl.
f_equal.
 apply Rmult_eq_reg_r with (r := rq).
 field_simplify.
 do 2 rewrite Rdiv_1_r.
 rewrite Rsqr_pow2.
 ring_simplify.
 progress repeat rewrite <- Rsqr_pow2.
 replace zp²%R with (1 - xp² - yp²)%R by lra.
 progress repeat rewrite Rsqr_pow2.
 ring_simplify.
 progress repeat rewrite <- Rsqr_pow2.
 apply Rplus_eq_reg_r with (r := (- (- yp * rq * z₂ + zp * rq * y₂)%R)).
 rewrite Rplus_opp_r.
 rewrite fold_Rminus.
 ring_simplify.
 progress repeat rewrite Rsqr_pow2.
 progress replace
   (- xp ^ 2 * s * x₁ + s * x₁ - s * xp * y₁ * yp - s * xp * zp * z₁ +
    y₁ * zp * c - yp * z₁ * c + yp * rq * z₂ - zp * rq * y₂)%R
 with
   (s * (x₁ - xp * (xp * x₁ + y₁ * yp  + zp * z₁)) +
    c * (y₁ * zp - yp * z₁) + rq * (yp * z₂ - zp * y₂))%R
 by lra.
 replace (y₁ * yp)%R with (yp * y₁)%R by lra.
 rewrite Hll.
bbb.

Theorem glop : ∀ p p₁ p₂ q₁ q₂ c s,
  p ∈ sphere 1
  → p₁ ∈ sphere 1
  → p₂ ∈ sphere 1
  → latitude p p₁ = latitude p p₂
  → q₁ = (p × p₁)
  → q₂ = (p × p₂)
  → q₁ ≠ 0%vec
  → q₂ ≠ 0%vec
  → c = (/ (∥q₁∥ * ∥q₂∥) * (q₁ · q₂))%R
  → s = (/ (∥q₁∥ * ∥q₂∥) * ∥(q₁ × q₂)∥)%R
  → (matrix_of_axis_angle (p, c, s) * p₁ = p₂)%vec.
Proof.
intros * Hp Hp₁ Hp₂ Hll Hq₁ Hq₂ Hq₁nz Hq₂nz Hc Hs.
destruct p as (xp, yp, zp); simpl in Hp.
destruct p₁ as (x₁, y₁, z₁).
destruct p₂ as (x₂, y₂, z₂); simpl in *.
rewrite Rsqr_1 in Hp, Hp₁, Hp₂.
rewrite Hp, sqrt_1.
do 3 rewrite Rdiv_1_r.
remember (∥q₁∥ * ∥q₂∥)%R as rq eqn:Hrq.
subst c s.
remember (q₁ · q₂) as c eqn:Hc.
remember ∥(q₁ × q₂)∥ as s eqn:Hs.
specialize (vec_Lagrange_identity q₁ q₂) as Hli.
rewrite <- Rsqr_mult in Hli.
rewrite vec_dot_mul_diag in Hli.
rewrite <- Hrq, <- Hc, <- Hs in Hli.
f_equal.
 apply Rmult_eq_reg_r with (r := rq).
 field_simplify.
 do 2 rewrite Rdiv_1_r.
 unfold Rsqr.
 progress replace
   (xp * xp * rq * x₁ - xp * xp * c * x₁ + rq * xp * yp * y₁ +
    rq * xp * zp * z₁ + c * x₁ - c * xp * yp * y₁ - c * xp * zp * z₁ +
    yp * s * z₁ - zp * s * y₁)%R
 with
   (xp * (rq - c) * (xp * x₁ + yp * y₁ + zp * z₁) +
    c * x₁ + s * (yp * z₁ - zp * y₁))%R
   by lra.
 rewrite Hll.
 move c before rq; move s before c.
 rewrite Hq₁, Hq₂ in Hc.
 simpl in Hc.
 unfold Rsqr in Hp.
 progress replace
   (xp * (rq - c) * (xp * x₂ + yp * y₂ + zp * z₂) +
    c * x₁ + s * (yp * z₁ - zp * y₁))%R
 with
   (xp * xp * (rq - c) * x₂ +
    xp * (rq - c) * (yp * y₂ + zp * z₂) +
    c * x₁ + s * (yp * z₁ - zp * y₁))%R
   by lra.
 replace (xp * xp)%R with (1 - yp * yp - zp * zp)%R by lra.
 replace ((1 - yp * yp - zp * zp) * (rq - c) * x₂)%R
 with (rq * x₂ - c * x₂ - (yp * yp + zp * zp) * (rq - c) * x₂)%R by lra.
 apply Rplus_eq_reg_l with (r := (- (rq * x₂))%R).
 rewrite Rplus_opp_l.
 unfold Rminus.
 do 5 rewrite <- Rplus_assoc.
 rewrite Rplus_opp_l, Rplus_0_l.
 progress repeat rewrite fold_Rminus.
 progress replace
   (- (c * x₂) - (yp * yp + zp * zp) * (rq - c) * x₂ +
    xp * (rq - c) * (yp * y₂ + zp * z₂) + c * x₁)%R
 with
   (c * (x₁ - x₂) +
    (rq - c) * (xp * (yp * y₂ + zp * z₂) - (yp * yp + zp * zp) * x₂))%R
   by lra.

bbb.
destruct q₁ as (xq₁, yq₁, zq₁).
destruct q₂ as (xq₂, yq₂, zq₂).
simpl in Hc, Hs.
rewrite <- sqrt_mult_alt in Hc; [ | apply nonneg_sqr_vec_norm ].
rewrite <- sqrt_mult_alt in Hs; [ | apply nonneg_sqr_vec_norm ].
bbb.

Theorem glop : ∀ r p p₁ p₂ q₁ q₂ c s,
  (0 < r)%R
  → p ∈ sphere r
  → p₁ ∈ sphere r
  → p₂ ∈ sphere r
  → latitude p p₁ = latitude p p₂
  → q₁ = (p × p₁)
  → q₂ = (p × p₂)
  → q₁ ≠ 0%vec
  → q₂ ≠ 0%vec
  → c = (/ (∥q₁∥ * ∥q₂∥) * (q₁ · q₂))%R
  → s = (/ (∥q₁∥ * ∥q₂∥) * ∥(q₁ × q₂)∥)%R
  → (matrix_of_axis_angle (p, c, s) * p₁ = p₂)%vec.
Proof.
intros * Hr Hp Hp₁ Hp₂ Hll Hq₁ Hq₂ Hq₁nz Hq₂nz Hc Hs.
destruct p as (xp, yp, zp); simpl in Hp.
destruct p₁ as (x₁, y₁, z₁).
destruct p₂ as (x₂, y₂, z₂); simpl in *.
rewrite Hp.
rewrite sqrt_Rsqr; [ | lra ].
rewrite Rsqr_div; [ | lra ].
rewrite Rsqr_div; [ | lra ].
rewrite Rsqr_div; [ | lra ].
f_equal.
 field_simplify.
 rewrite Rdiv_1_r.
 apply Rmult_eq_reg_r with (r := r⁴%R).
 progress repeat rewrite Rsqr_pow2.
 replace (r ^ 2 * r ^ 2)%R with r⁴%R by lra.
 rewrite Rmult_div_same.
 ring_simplify.
 progress repeat rewrite <- Rsqr_pow2.
 subst c s.
 replace (- xp² * (/ r² * (q₁ · q₂)) * x₁ * r²)%R
 with (- xp² * (q₁ · q₂) * x₁ * (/ r² * r²))%R by lra.
 replace (xp * (/ r² * (q₁ · q₂)) * r² * yp * y₁)%R
 with (xp * (q₁ · q₂) * yp * y₁ * (/ r² * r²))%R by lra.
 replace (xp * (/ r² * (q₁ · q₂)) * r² * zp * z₁)%R
 with (xp * (q₁ · q₂) * zp * z₁ * (/ r² * r²))%R by lra.
 replace (/ r² * (q₁ · q₂) * x₁ * r⁴)%R
 with (r ^ 2 * (q₁ · q₂) * x₁ * (/ r² * r ^ 2))%R by lra.
 replace (r³ * yp * z₁ * (/ r² * ∥(q₁ × q₂)∥))%R
 with (r * yp * z₁ * ∥(q₁ × q₂)∥ * (/ r² * r ^ 2))%R by lra.
 replace (r³ * y₁ * zp * (/ r² * ∥(q₁ × q₂)∥))%R
 with (r * y₁ * zp * ∥(q₁ × q₂)∥ * (/ r² * r ^ 2))%R by lra.
 rewrite <- Rsqr_pow2.
 rewrite Rinv_l.
 progress repeat rewrite Rmult_1_r.
 ring_simplify.
 remember (q₁ · q₂) as dq eqn:Hdq.
 rewrite Hq₁, Hq₂ in Hdq; simpl in Hdq.
 remember (q₁ × q₂) as cq eqn:Hcq.
 rewrite Hq₁, Hq₂ in Hcq; simpl in Hcq.
 destruct cq as (cx, cy, cz).
 unfold vec_norm.
 injection Hcq; clear Hcq; intros Hcz Hcy Hcx.
 remember (cx² + cy² + cz²)%R as rx eqn:Hrx.
 subst cx cy cz.
 progress repeat rewrite Rsqr_pow2 in Hrx.
 ring_simplify in Hrx.
 progress repeat rewrite <- Rsqr_pow2 in Hrx.
bbb.

destruct q₁ as (x₃, y₃, z₃).
destruct q₂ as (x₄, y₄, z₄); simpl in *.
injection Hq₁; clear Hq₁; intros Hz₃ Hy₃ Hx₃.
injection Hq₂; clear Hq₂; intros Hz₄ Hy₄ Hx₄.

bbb.
intros * Hr Hp Hp₁ Hp₂ Hll Hq₁ Hq₂ Hq₁nz Hq₂nz Hc Hs.
subst c s; simpl.
destruct p as (xp, yp, zp); simpl in Hp.
rewrite Hp.
rewrite sqrt_Rsqr; [ | lra ].
rewrite Rsqr_div; [ | lra ].
rewrite Rsqr_div; [ | lra ].
rewrite Rsqr_div; [ | lra ].
enough (r = 1%R). (* just to simplify the proof, to see *)
subst r; clear Hr.
simpl in Hp₁, Hp₂.
rewrite Rsqr_1 in Hp, Hp₁, Hp₂.
rewrite Rsqr_1.
do 6 rewrite Rdiv_1_r.
rewrite Rinv_1.
progress repeat rewrite Rmult_1_l.
destruct p₁ as (x₁, y₁, z₁).
destruct p₂ as (x₂, y₂, z₂); simpl.
simpl in Hq₁, Hq₂, Hq₁nz, Hq₂nz.
simpl in Hll.
f_equal.
 progress repeat rewrite Rsqr_pow2.
 ring_simplify.
 progress repeat rewrite <- Rsqr_pow2.
bbb.

(* Given an axis (a point p) and two points p₁ and p₂, there is at most
   one rotation around this axis, transforming p₁ into p₂. Zero if p₁ and
   p₂ are not in the same latitude (p being the north pole), one if they
   are. *)
Theorem one_rotation_max : ∀ r p p₁ p₂ c s c' s',
  (0 < r)%R
  → p ∈ sphere r
  → p₁ ∈ sphere r
  → p₂ ∈ sphere r
  → (c² + s² = 1)%R
  → (c'² + s'² = 1)%R
  → (matrix_of_axis_angle (p, c, s) * p₁ = p₂)%vec
  → (matrix_of_axis_angle (p, c', s') * p₁ = p₂)%vec
  → c = c' ∧ s = s'.
Proof.
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
 enough (r = 1%R). (* just to simplify the proof, to see *)
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
     ((c - c') * (xp * (xp * x₁ + yp * y₁ + zp * z₁) - x₁) +
      (s - s') * (y₁ * zp - yp * z₁))%R = 0%R) by lra.

bbb.

(* below: partially true, therefore false; indeed, there is a rotation
   transforming a point p₁ into a point p₂ (with axis equal to p₁ × p₂),
   but there are an uncountable set of axis transforming p₁ into p₂:
   just consider the plan separating symmetrically p₁ and p₂. Any point
   in the intersection of this plan and the sphere can be an axis of
   a possible rotation between p₁ and p₂ *)

Definition axis_angle_of_couple p₁ p₂ :=
  let a := (/ ∥(p₁ × p₂)∥ ⁎ (p₁ × p₂))%vec in
  let c := ((p₁ · p₂) / (∥p₁∥ * ∥p₂∥))%R in
  let s := (∥(p₁ × p₂)∥ / (∥p₁∥ * ∥p₂∥))%R in
  (a, c, s).

Theorem rotation_between_2_points : ∀ r p₁ p₂ a c s,
  (0 < r)%R
  → p₁ ∈ sphere r
  → p₂ ∈ sphere r
  → p₁ × p₂ ≠ 0%vec
  → axis_angle_of_couple p₁ p₂ = (a, c, s)
  → a ∈ sphere 1 ∧ (c² + s² = 1)%R ∧
    (matrix_of_axis_angle (a, c, s) * p₁ = p₂)%vec.
Proof.
intros * Hr Hp₁ Hp₂ Hpp Hacs.
symmetry in Hacs; injection Hacs; clear Hacs.
intros Hs Hc Ha.
assert (Hcs : (c² + s² = 1)%R).
 assert (H : (∥p₁∥ * ∥p₂∥ ≠ 0)%R).
  apply on_sphere_norm in Hp₁; [ | lra ].
  apply on_sphere_norm in Hp₂; [ | lra ].
  rewrite Hp₁, Hp₂.
  intros H; apply Rsqr_eq_0 in H; lra.
  rewrite Hc, Hs.
  rewrite Rsqr_div; [ | easy ].
  rewrite Rsqr_div; [ | easy ].
  rewrite <- Rdiv_plus_distr.
  rewrite <- vec_dot_mul_diag.
  rewrite <- vec_Lagrange_identity.
  rewrite Rplus_minus.
  rewrite Rsqr_mult.
  rewrite Rdiv_same; [ easy | ].
  rewrite <- Rsqr_mult.
  intros HH; apply H.
  now apply Rsqr_eq_0 in HH.

 split; [ | split ]; [ | easy | ].
  simpl.
  rewrite Ha; clear a Ha.
  remember (p₁ × p₂) as v eqn:Hv.
  destruct v as (vx, vy, vz); simpl.
  remember (√ (vx² + vy² + vz²)) as vr eqn:Hvr.
  replace (r * (/ vr * vx))%R with (r * vx * / vr)%R by lra.
  replace (r * (/ vr * vy))%R with (r * vy * / vr)%R by lra.
  replace (r * (/ vr * vz))%R with (r * vz * / vr)%R by lra.
  do 3 rewrite Rsqr_mult.
  do 2 rewrite <- Rmult_plus_distr_l.
  apply (f_equal Rsqr) in Hvr.
  assert (Hrz : (vr ≠ 0)%R).
   intros H; rewrite H in *; clear H.
   symmetry in Hvr.
   rewrite Rsqr_sqrt in Hvr; [ | apply nonneg_sqr_vec_norm ].
   rewrite Rsqr_0 in Hvr.
   apply sqr_vec_norm_eq_0 in Hvr.
   destruct Hvr as (H1 & H2 & H3).
   now rewrite H1, H2, H3 in Hpp.

   rewrite Rsqr_sqrt in Hvr; [ | apply nonneg_sqr_vec_norm ].
   rewrite <- Hvr.
   rewrite Rsqr_inv; [ | easy ].
   rewrite Rinv_l; [ now rewrite Rsqr_1 | ].
   intros H; apply Hrz.
   now apply Rsqr_eq_0 in H.

  simpl.
  remember (p₁ × p₂) as pp eqn:Hcm.
  destruct a as (xa, ya, za).
  destruct p₁ as (x₁, y₁, z₁).
  destruct p₂ as (x₂, y₂, z₂); simpl in *.
  rewrite Hp₁, Hp₂ in Hs, Hc.
  rewrite sqrt_Rsqr in Hs; [ | lra ].
  rewrite sqrt_Rsqr in Hc; [ | lra ].
  destruct pp as (xp, yp, zp).
  simpl in Hs.
  simpl in Ha.
  remember (√ (xp² + yp² + zp²)) as rp eqn:Hrp.
  assert (Hrpz : rp ≠ 0%R).
   intros H; rewrite H in Hrp; symmetry in Hrp.
   apply sqrt_eq_0 in Hrp; [ | apply nonneg_sqr_vec_norm ].
   apply sqr_vec_norm_eq_0 in Hrp.
   destruct Hrp as (H1 & H2 & H3).
   now rewrite H1, H2, H3 in Hpp.

   injection Ha; clear Ha; intros Hza Hya Hxa.
   assert (Hra : √ (xa² + ya² + za²) = 1%R).
    rewrite Hxa, Hya, Hza.
    progress repeat rewrite Rsqr_mult.
    do 2 rewrite <- Rmult_plus_distr_l.
    rewrite sqrt_mult_alt; [ | apply Rle_0_sqr ].
    rewrite <- Hrp.
    rewrite sqrt_Rsqr; [ now rewrite Rinv_l | ].
    apply Rlt_le, Rinv_0_lt_compat.
    enough (0 ≤ rp)%R by lra.
    rewrite Hrp; apply sqrt_pos.

    rewrite Hra.
    do 3 rewrite Rdiv_1_r.
    injection Hcm; clear Hcm; intros Hzp Hyp Hxp.
    rewrite Hxa, Hya, Hza.
    progress repeat rewrite Rsqr_mult.
    unfold Rsqr.
    replace
      ((/ rp * / rp * (xp * xp) * (1 - c) + c) * x₁ +
       (/ rp * xp * (/ rp * yp) * (1 - c) - / rp * zp * s) * y₁ +
       (/ rp * xp * (/ rp * zp) * (1 - c) + / rp * yp * s) * z₁)%R
    with
    (/ rp * / rp * xp * (1 - c) * (xp * x₁ + yp * y₁ + zp * z₁) +
     c * x₁ + s * (yp * z₁ - zp * y₁) * / rp)%R by lra.
    replace
      ((/ rp * xp * (/ rp * yp) * (1 - c) + / rp * zp * s) * x₁ +
       (/ rp * / rp * (yp * yp) * (1 - c) + c) * y₁ +
       (/ rp * yp * (/ rp * zp) * (1 - c) - / rp * xp * s) * z₁)%R
    with
    (/ rp * / rp * yp * (1 - c) * (xp * x₁ + yp * y₁ + zp * z₁) +
     c * y₁ + s * (zp * x₁ - xp * z₁) * / rp)%R by lra.
    replace
      ((/ rp * xp * (/ rp * zp) * (1 - c) - / rp * yp * s) * x₁ +
       (/ rp * yp * (/ rp * zp) * (1 - c) + / rp * xp * s) * y₁ +
       (/ rp * / rp * (zp * zp) * (1 - c) + c) * z₁)%R
    with
    (/ rp * / rp * zp * (1 - c) * (xp * x₁ + yp * y₁ + zp * z₁) +
     c * z₁ + s * (xp * y₁ - yp * x₁) * / rp)%R by lra.
    remember (xp * x₁ + yp * y₁ + zp * z₁)%R as u eqn:Hu.
    rewrite Hxp, Hyp, Hzp in Hu.
    ring_simplify in Hu; subst u.
    do 3 rewrite Rmult_0_r, Rplus_0_l.
    rewrite fold_Rsqr in Hc, Hs.
    assert (Hr2 : (r² ≠ 0)%R) by (intros H; apply Rsqr_eq_0 in H; lra).
    f_equal.
     apply Rmult_eq_reg_r with (r := rp); [ | easy ].
     rewrite Rmult_plus_distr_r.
     repeat rewrite Rmult_assoc.
     rewrite Rinv_l; [ | easy ].
     rewrite Rmult_1_r.
     apply Rmult_eq_reg_r with (r := r²%R); [ | easy ].
     rewrite Rmult_plus_distr_r.
     remember (c * (x₁ * rp) * r²)%R as u eqn:Hu.
     rewrite Rmult_shuffle0 in Hu.
     rewrite Hc in Hu.
     rewrite Rmult_div_same in Hu; [ | easy ].
     subst u.
     remember (s * (yp * z₁ - zp * y₁) * r²)%R as u eqn:Hu.
     rewrite Rmult_shuffle0 in Hu.
     rewrite Hs in Hu.
     rewrite Rmult_div_same in Hu; [ | easy ].
     rewrite Rmult_comm in Hu; subst u.
     rewrite <- Rmult_assoc.
     rewrite <- Rmult_plus_distr_r.
     rewrite Rmult_shuffle0.
     f_equal.
     rewrite Hyp, Hzp.
     ring_simplify.
     do 3 rewrite <- Rsqr_pow2.
     rewrite Rmult_comm.
     do 2 rewrite <- Rmult_plus_distr_l.
     now rewrite Hp₁.

     apply Rmult_eq_reg_r with (r := rp); [ | easy ].
     rewrite Rmult_plus_distr_r.
     repeat rewrite Rmult_assoc.
     rewrite Rinv_l; [ | easy ].
     rewrite Rmult_1_r.
     apply Rmult_eq_reg_r with (r := r²%R); [ | easy ].
     rewrite Rmult_plus_distr_r.
     remember (c * (y₁ * rp) * r²)%R as u eqn:Hu.
     rewrite Rmult_shuffle0 in Hu.
     rewrite Hc in Hu.
     rewrite Rmult_div_same in Hu; [ | easy ].
     subst u.
     remember (s * (zp * x₁ - xp * z₁) * r²)%R as u eqn:Hu.
     rewrite Rmult_shuffle0 in Hu.
     rewrite Hs in Hu.
     rewrite Rmult_div_same in Hu; [ | easy ].
     rewrite Rmult_comm in Hu; subst u.
     rewrite <- Rmult_assoc.
     rewrite <- Rmult_plus_distr_r.
     rewrite Rmult_shuffle0.
     f_equal.
     rewrite Hzp, Hxp.
     ring_simplify.
     do 3 rewrite <- Rsqr_pow2.
     rewrite <- Rmult_plus_distr_r.
     rewrite Rmult_comm.
     rewrite <- Rmult_plus_distr_l.
     now rewrite Hp₁.

     apply Rmult_eq_reg_r with (r := rp); [ | easy ].
     rewrite Rmult_plus_distr_r.
     repeat rewrite Rmult_assoc.
     rewrite Rinv_l; [ | easy ].
     rewrite Rmult_1_r.
     apply Rmult_eq_reg_r with (r := r²%R); [ | easy ].
     rewrite Rmult_plus_distr_r.
     remember (c * (z₁ * rp) * r²)%R as u eqn:Hu.
     rewrite Rmult_shuffle0 in Hu.
     rewrite Hc in Hu.
     rewrite Rmult_div_same in Hu; [ | easy ].
     subst u.
     remember (s * (xp * y₁ - yp * x₁) * r²)%R as u eqn:Hu.
     rewrite Rmult_shuffle0 in Hu.
     rewrite Hs in Hu.
     rewrite Rmult_div_same in Hu; [ | easy ].
     rewrite Rmult_comm in Hu; subst u.
     rewrite <- Rmult_assoc.
     rewrite <- Rmult_plus_distr_r.
     rewrite Rmult_shuffle0.
     f_equal.
     rewrite Hxp, Hyp.
     ring_simplify.
     do 3 rewrite <- Rsqr_pow2.
     do 2 rewrite <- Rmult_plus_distr_r.
     rewrite Rmult_comm.
     now rewrite Hp₁.
Qed.

Theorem matrix_of_axis_angle_opp : ∀ p₁ p₂ a c s,
  a ∈ sphere 1
  → (c² + s² = 1)%R
  → (matrix_of_axis_angle (a, c, s) * p₁ = p₂)%vec
  → (matrix_of_axis_angle (a, c, (-s)%R) * p₂ = p₁)%vec.
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
 replace (s ^ 2)%R with (1 - c ^ 2)%R by lra.
 replace (az ^ 2)%R with (1 - ax ^ 2 - ay ^ 2)%R by lra.
 ring.

 rewrite Rsqr_pow2 in Ha, Ha, Ha, Hcs, Hcs.
 progress repeat rewrite Rsqr_pow2.
 replace (s ^ 2)%R with (1 - c ^ 2)%R by lra.
 replace (az ^ 2)%R with (1 - ax ^ 2 - ay ^ 2)%R by lra.
 ring.

 rewrite Rsqr_pow2 in Ha, Ha, Ha, Hcs, Hcs.
 progress repeat rewrite Rsqr_pow2.
 replace (s ^ 2)%R with (1 - c ^ 2)%R by lra.
 replace (az ^ 2)%R with (1 - ax ^ 2 - ay ^ 2)%R by lra.
 ring.
Qed.

Theorem rot_is_id_for_pt : ∀ M v,
  is_rotation_matrix M
  → (M * v = v)%vec
  → M ≠ mat_transp M
  → ∀ a c s, axis_angle_of_matrix M = (a, c, s) → a × v = 0%vec.
Proof.
intros * Hrm Hmv Hmt a c s Ha.
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
injection Ha; clear Ha; intros Hs Hc Ha.
destruct a as (xa, ya, za); simpl.
injection Ha; clear Ha; intros Hza Hya Hxa.
rewrite Hc in Hs.
remember ((a₃₂ - a₂₃)² + (a₁₃ - a₃₁)² + (a₂₁ - a₁₂)²)%R as r eqn:Hr.
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

Theorem unicity_rotation_between_2_points : ∀ r p₁ p₂,
  (0 < r)%R
  → p₁ ∈ sphere r
  → p₂ ∈ sphere r
  → p₁ × p₂ ≠ 0%vec
  → ∃ a c s,
    a ∈ sphere 1 ∧ (c² + s² = 1)%R ∧
    (matrix_of_axis_angle (a, c, s) * p₁ = p₂)%vec ∧
    ∀ a' c' s',
    a' ∈ sphere 1 ∧ (c'² + s'² = 1)%R ∧
    (matrix_of_axis_angle (a', c', s') * p₁ = p₂)%vec
    → a = a' ∧ c = c' ∧ s = s' ∨
      a = (-a')%vec ∧ c = c' ∧ s = (- s')%R.
Proof.
intros * Hr Hp₁ Hp₂ Hpp.
remember (axis_angle_of_couple p₁ p₂) as acs eqn:H.
destruct acs as ((a & c) & s).
symmetry in H.
eapply rotation_between_2_points in H; try eassumption.
destruct H as (Ha & Hcs & Hm).
exists a, c, s.
split; [ easy | ].
split; [ easy | ].
split; [ easy | ].
intros * (Ha' & Hcs' & H').
apply matrix_of_axis_angle_opp in H'; [ | easy | easy ].
rewrite <- H' in Hm.
rewrite <- mat_vec_mul_assoc in Hm.
remember (matrix_of_axis_angle (a, c, s)) as M eqn:HM.
remember (matrix_of_axis_angle (a', c', (-s')%R)) as M' eqn:HM'.
move M' before M.
generalize Hm; intros H.
remember (axis_angle_of_matrix (M * M')) as acs' eqn:Hacs'.
symmetry in Hacs'.
destruct acs' as ((aa', cc'), ss').
eapply rot_is_id_for_pt in H; try eassumption.
unfold axis_angle_of_matrix in Hacs'.
injection Hacs'; clear Hacs'; intros Hss' Hcc' Haa'.
bbb.

unfold mat_mul in Hm.
simpl in Hm.
destruct a as (xa, ya, za).
destruct a' as (xa', ya', za').
simpl in Hm.
simpl in Ha, Ha'.
rewrite Rsqr_1 in Ha, Ha'.
rewrite Ha, Ha' in Hm.
rewrite sqrt_1 in Hm.
progress repeat rewrite Rdiv_1_r in Hm.
destruct p₂ as (x₂, y₂, z₂).
simpl in Hm.
injection Hm; clear Hm; intros Hz₂ Hy₂ Hx₂.
ring_simplify in Hx₂.
progress repeat rewrite Rsqr_pow2 in Ha, Ha'.
progress repeat rewrite Rsqr_pow2 in Hcs, Hcs'.
progress repeat rewrite Rsqr_pow2 in Hx₂.
repeat replace (za' ^ 2)%R with (1 - xa' ^ 2 - ya' ^ 2)%R in Hx₂ by lra.
ring_simplify in Hx₂.
progress replace (s' ^ 2)%R with (1 - c' ^ 2)%R in Hx₂ by lra.

bbb.

(* J₁(r) = set of rotations given by its axis and its angle, such that
   for some p in D ∩ sphere(r), R(p) is also in D ∩ sphere(r). *)
Definition J₁ r :=
  mkset
    (λ '(axis, cosθ, sinθ),
     ∥axis∥ = r ∧ (cosθ² + sinθ² = 1)%R ∧
     let R := matrix_of_axis_angle (axis, cosθ, sinθ) in
     ∃ p p', p × p' ≠ 0%vec ∧ p ∈ D ∩ sphere r ∧ p' ∈ D ∩ sphere r ∧
     (R * p)%vec = p').

Definition J₁_of_nats r '(nf, no, nf', no') : (vector * ℝ * ℝ) :=
  let p₂ := fixpoint_of_nat r nf in
  let p := fold_right rotate p₂ (path_of_nat no) in
  let p₃ := fixpoint_of_nat r nf' in
  let p' := fold_right rotate p₃ (path_of_nat no') in
  let θ := acos ((p · p') / r²) in
  let px := p × p' in
  (px, cos θ, sin θ).

Theorem J₁_is_countable : ∀ r, r ≠ 0%R →
  ∃ f : ℕ → vector * ℝ * ℝ, ∀ acs, acs ∈ J₁ r → ∃ n : ℕ, f n = acs.
Proof.
intros r Hr.
apply surj_prod_4_nat_surj_nat.
exists (J₁_of_nats r).
intros ((v, c), s) Hv.
destruct Hv as (Hvn & Hcs & p & p' & Hpp & Hp & Hp' & Hv).
remember (matrix_of_axis_angle (v, c, s)) as M eqn:HM.
destruct Hp as ((el & p₂ & (el₂ & Hso₂) & Hn₂ & Hr₂) & Hp).
destruct Hp' as ((el' & p₃ & (el₃ & Hso₃) & Hn₃& Hr₃) & Hp').
assert (H : p₂ ∈ sphere r ∧ p₃ ∈ sphere r).
 split.
  rewrite rotate_vec_mul in Hso₂.
  rewrite <- Hso₂.
  apply on_sphere_after_rotation; [ easy | ].
  apply mat_of_path_is_rotation_matrix.

  rewrite rotate_vec_mul in Hso₃.
  rewrite <- Hso₃.
  apply on_sphere_after_rotation; [ easy | ].
  apply mat_of_path_is_rotation_matrix.

 destruct H as (Hp₂s, Hp₃s).
 apply rotate_rev_path in Hso₂.
 apply rotate_rev_path in Hso₃.
 remember (nat_of_path el) as nf eqn:Hnf.
 remember (nat_of_path (rev_path el₂)) as no eqn:Hno.
 remember (nat_of_path el') as nf' eqn:Hnf'.
 remember (nat_of_path (rev_path el₃)) as no' eqn:Hno'.
 remember (fixpoint_of_nat r nf) as q₂ eqn:Hq₂.
 remember (fixpoint_of_nat r nf') as q₃ eqn:Hq₃.
 move no before nf; move nf' before no; move no' before nf'.
 move el after p; move el' before el.
 move el₂ before el'; move el₃ before el₂.
 move p₃ before p₂; move q₂ before p₃; move q₃ before q₂.
 move Hn₂ after Hso₂; move Hn₃ before Hn₂.
 move Hso₃ before Hso₂; move Hr₃ before Hr₂.
 move Hp' before Hp; move Hp₂s before Hp'; move Hp₃s before Hp₂s.
 assert (Hpq₂ :
  p₂ =
    if bool_dec (is_neg_vec p₂) (is_neg_vec q₂) then q₂
    else (- q₂)%vec).
  subst nf.
  unfold fixpoint_of_nat in Hq₂.
  rewrite path_of_nat_inv in Hq₂.
  rewrite rotate_vec_mul in Hr₂.
  clear Hn₃.
  eapply axis_and_fixpoint_of_path_collinear; try eassumption.
  now subst q₂; apply fixpoint_of_path_on_sphere.

  assert (Hpq₃ :
   p₃ =
     if bool_dec (is_neg_vec p₃) (is_neg_vec q₃) then q₃
     else (- q₃)%vec).
   subst nf'.
   unfold fixpoint_of_nat in Hq₃.
   rewrite path_of_nat_inv in Hq₃.
   rewrite rotate_vec_mul in Hr₃.
   eapply axis_and_fixpoint_of_path_collinear; try eassumption.
   now subst q₃; apply fixpoint_of_path_on_sphere.

   destruct (bool_dec (is_neg_vec p₂) (is_neg_vec q₂)) as [Hb₂| Hb₂].
    move Hpq₂ at top; subst q₂; clear Hb₂.
    destruct (bool_dec (is_neg_vec p₃) (is_neg_vec q₃)) as [Hb₃| Hb₃].
     move Hpq₃ at top; subst q₃; clear Hb₃.
     exists nf, no.
     exists nf', no'.
     unfold J₁_of_nats.
     rewrite <- Hq₂, <- Hq₃.
     rewrite Hno, path_of_nat_inv.
     rewrite Hno', path_of_nat_inv.
     rewrite Hso₂, Hso₃.
     remember (acos ((p · p') / r²)) as a eqn:Ha.
     assert (Hppi : (-1 < (p · p') / r² < 1)%R).
      apply Rabs_lt.
      rewrite Rabs_div; [ | now intros H; apply Hr; apply Rsqr_eq_0 ].
      rewrite Rabs_sqr.
      apply Rmult_lt_reg_r with (r := (r²)%R); [ now apply Rlt_0_sqr | ].
      unfold Rdiv; rewrite Rmult_assoc.
      rewrite Rinv_l; [ | now intros H; apply Rsqr_eq_0 in H ].
      rewrite Rmult_1_r, Rmult_1_l.
      rewrite <- Rabs_sqr.
      apply Rsqr_lt_abs_0.
      replace (p · p')²%R with (∥p∥² * ∥p'∥² - (p × p')²%vec)%R
       by (rewrite <- vec_Lagrange_identity; lra).
      assert (H : (0 ≤ r)%R) by (rewrite <- Hvn; apply vec_norm_nonneg).
      apply on_sphere_norm in Hp; [ | easy ].
      apply on_sphere_norm in Hp'; [ | easy ].
      rewrite Hp, Hp'.
      fold (Rsqr (r²)).
      enough (0 < (p × p')²%vec)%R by lra.
      rewrite vec_dot_mul_diag.
      apply Rlt_0_sqr.
      clear H.
      symmetry in Hp, Hp'.
      assert (H1 : (p ≠ 0)%vec) by now intros H; rewrite H, vec_norm_0 in Hp.
      assert (H2 : (p' ≠ 0)%vec) by now intros H; rewrite H, vec_norm_0 in Hp'.
      intros H.
      now apply vec_norm_eq_0 in H.

      rewrite Ha at 1.
      rewrite cos_acos; [ | easy ].
      rewrite HM in Hv.
      simpl in Hv.
      destruct v as (x, y, z).
      simpl in Hvn.
      rewrite Hvn in Hv.
      unfold mat_vec_mul in Hv; simpl in Hv.
      destruct p as (xp, yp, zp).
      destruct p' as (xp', yp', zp').
      injection Hv; clear Hv; intros Hzp Hyp Hxp.
      simpl in Ha, Hp'; simpl.
      f_equal; [ f_equal | ].
(* on s'attaque au cosinus *)
Focus 2.
assert (Hr2 : (r² ≠ 0)%R) by now intros H; apply Rsqr_eq_0 in H.
apply Rmult_eq_reg_r with (r := (r²)%R); [ | easy ].
rewrite Rmult_div_same; [ | easy ].
(**)
rewrite Rsqr_div in Hxp; [ | easy ].
progress repeat rewrite Rsqr_pow2 in Hxp.
field_simplify in Hxp.
apply Rmult_eq_compat_r with (r := (r ^ 2)%R) in Hxp.
progress repeat rewrite <- Rsqr_pow2 in Hxp.
rewrite Rmult_div_same in Hxp; [ | easy ].
rewrite Rdiv_1_r in Hxp.
rewrite Rsqr_div in Hyp; [ | easy ].
progress repeat rewrite Rsqr_pow2 in Hyp.
field_simplify in Hyp.
apply Rmult_eq_compat_r with (r := (r ^ 2)%R) in Hyp.
progress repeat rewrite <- Rsqr_pow2 in Hyp.
rewrite Rmult_div_same in Hyp; [ | easy ].
rewrite Rdiv_1_r in Hyp.
rewrite Rsqr_div in Hzp; [ | easy ].
progress repeat rewrite Rsqr_pow2 in Hzp.
field_simplify in Hzp.
apply Rmult_eq_compat_r with (r := (r ^ 2)%R) in Hzp.
progress repeat rewrite <- Rsqr_pow2 in Hzp.
rewrite Rmult_div_same in Hzp; [ | easy ].
rewrite Rdiv_1_r in Hzp.
simpl in Hp.
simpl in Hppi.
destruct (Req_dec r 1) as [Hr1| Hr1].
 rewrite Hr1 in *; clear Hr1.
 apply (f_equal Rsqr) in Hvn.
 rewrite Rsqr_sqrt in Hvn.
 replace 1²%R with 1%R in * by now rewrite Rsqr_1.
 progress repeat rewrite Rmult_1_l in *.
 progress repeat rewrite Rmult_1_r in *.
 unfold Rsqr in *.
 rewrite Rdiv_1_r in Hppi.
 unfold vec_cross_mul in Hpp.
 clear - Hvn Hp Hp' Hxp Hyp Hzp Hppi Hcs.

bbb.
(* works not *)
nsatz.
bbb.

(* previous version with R^n instead of R, but difficult to prove... *)

(* J₁(r) = set of rotations given by its axis and its angle, such that
   for some natural number n, and some p in D ∩ sphere(r), R^n(p) is
   also in D ∩ sphere(r). *)
Definition J₁ r :=
  mkset
    (λ '(axis, cosθ, sinθ),
     ∥axis∥ = 1%R ∧ (cosθ² + sinθ² = 1)%R ∧
     let R := matrix_of_axis_angle (axis, cosθ, sinθ) in
     ∃ p p' n, p ∈ D ∩ sphere r ∧ p' ∈ D ∩ sphere r ∧
     ((R ^ n)%mat * p)%vec = p').

Definition J₁_of_nats r '(nf, no, nf', no', n, k) : (vector * ℝ * ℝ) :=
  let p₂ := fixpoint_of_nat r nf in
  let p := fold_right rotate p₂ (path_of_nat no) in
  let p₃ := fixpoint_of_nat r nf' in
  let p' := fold_right rotate p₃ (path_of_nat no') in
  let a := acos ((p · p') / r²) in
  let θ := (a / INR n + 2 * INR k * PI / INR n)%R in
  let px := p × p' in
  (px, cos θ, sin θ).

(* J₀(r) = set of rotations R, such that for some natural number n,
   and some p in D ∩ sphere(r), R^n(p) is also in D ∩ sphere(r). *)
Definition J₀ r :=
  mkset
    (λ R, is_rotation_matrix R ∧
     ∃ p p' n, p ∈ D ∩ sphere r ∧ p' ∈ D ∩ sphere r ∧
     ((R ^ n)%mat * p)%vec = p').

(* J(p₁) = subset of J₀(∥p₁∥) of rotations aroung a vec p₁. *)
Definition J p₁ := mkset (λ R₁, R₁ ∈ rotation_around p₁ ∧ R₁ ∈ J₀ ∥p₁∥).

Definition J₀_of_nats r '(nf, no, nf', no', n, k) : matrix ℝ :=
  let p₂ := fixpoint_of_nat r nf in
  let p := fold_right rotate p₂ (path_of_nat no) in
  let p₃ := fixpoint_of_nat r nf' in
  let p' := fold_right rotate p₃ (path_of_nat no') in
  let a := acos ((p · p') / r²) in
  let θ := (a / INR n + 2 * INR k * PI / INR n)%R in
  let px := p × p' in
  if vec_zerop px then mat_id
  else matrix_of_axis_angle (px, cos θ, sin θ).

Theorem matrix_pow : ∀ v c s n,
  ∥v∥ = 1%R
  → (c² + s² = 1)%R
  → (-1 < c < 1)%R
  → let c' := cos (INR n * acos c) in
    let s' := sin (INR n * asin c) in
    (matrix_of_axis_angle (v, c, s) ^ n = matrix_of_axis_angle (v, c', s'))%mat.
Proof.
intros * Hv Hcs Hc *; subst c' s'.
induction n.
 destruct v as (x, y, z); simpl.
 unfold mat_id, mkrmat; symmetry.
 do 2 rewrite Rmult_0_l.
 rewrite cos_0, sin_0.
 f_equal; lra.

 rewrite mat_pow_succ, IHn.
 destruct v as (x, y, z).
 simpl in Hv.
 unfold mat_mul.
 remember (S n) as sn; simpl; subst sn.
 rewrite Hv.
 do 3 rewrite Rdiv_1_r.
 remember (INR n * acos c)%R as a eqn:Ha.
 remember (INR n * asin c)%R as b eqn:Hb.
 remember (INR (S n) * acos c)%R as a' eqn:Ha'.
 remember (INR (S n) * asin c)%R as b' eqn:Hb'.
 move b before a; move a' before b; move b' before a'.
 rewrite S_INR in Ha', Hb'.
 rewrite Rmult_plus_distr_r, Rmult_1_l in Ha', Hb'.
 rewrite <- Ha in Ha'; rewrite <- Hb in Hb'.
 subst a' b'.
 rewrite cos_plus, sin_plus.
 rewrite sin_asin; [ | easy ].
 rewrite cos_acos; [ | easy ].
 unfold mkrmat; f_equal.
bbb.

Theorem J₁_is_countable : ∀ r,
  ∃ f : ℕ → vector * ℝ * ℝ, ∀ acs, acs ∈ J₁ r → ∃ n : ℕ, f n = acs.
Proof.
intros r.
apply surj_prod_6_nat_surj_nat.
exists (J₁_of_nats r).
intros ((v, c), s) Hv.
destruct Hv as (Hvn & Hcs & p & p' & n & Hp & Hp' & Hv).
remember (matrix_of_axis_angle (v, c, s)) as M eqn:HM.
destruct Hp as ((el & p₂ & (el₂ & Hso₂) & Hn₂ & Hr₂) & Hp).
destruct Hp' as ((el' & p₃ & (el₃ & Hso₃) & Hn₃& Hr₃) & Hp').
assert (H : p₂ ∈ sphere r ∧ p₃ ∈ sphere r).
 split.
  rewrite rotate_vec_mul in Hso₂.
  rewrite <- Hso₂.
  apply on_sphere_after_rotation; [ easy | ].
  apply mat_of_path_is_rotation_matrix.

  rewrite rotate_vec_mul in Hso₃.
  rewrite <- Hso₃.
  apply on_sphere_after_rotation; [ easy | ].
  apply mat_of_path_is_rotation_matrix.

 destruct H as (Hp₂s, Hp₃s).
 apply rotate_rev_path in Hso₂.
 apply rotate_rev_path in Hso₃.
 remember (nat_of_path el) as nf eqn:Hnf.
 remember (nat_of_path (rev_path el₂)) as no eqn:Hno.
 remember (nat_of_path el') as nf' eqn:Hnf'.
 remember (nat_of_path (rev_path el₃)) as no' eqn:Hno'.
 remember (fixpoint_of_nat r nf) as q₂ eqn:Hq₂.
 remember (fixpoint_of_nat r nf') as q₃ eqn:Hq₃.
 assert (Hpq₂ :
  p₂ =
    if bool_dec (is_neg_vec p₂) (is_neg_vec q₂) then q₂
    else (- q₂)%vec).
  subst nf.
  unfold fixpoint_of_nat in Hq₂.
  rewrite path_of_nat_inv in Hq₂.
  rewrite rotate_vec_mul in Hr₂.
  clear Hn₃.
  eapply axis_and_fixpoint_of_path_collinear; try eassumption.
  now subst q₂; apply fixpoint_of_path_on_sphere.
  assert (Hpq₃ :
   p₃ =
     if bool_dec (is_neg_vec p₃) (is_neg_vec q₃) then q₃
     else (- q₃)%vec).
   subst nf'.
   unfold fixpoint_of_nat in Hq₃.
   rewrite path_of_nat_inv in Hq₃.
   rewrite rotate_vec_mul in Hr₃.
   eapply axis_and_fixpoint_of_path_collinear; try eassumption.
   now subst q₃; apply fixpoint_of_path_on_sphere.

   destruct (bool_dec (is_neg_vec p₂) (is_neg_vec q₂)) as [Hb₂| Hb₂].
    move Hpq₂ at top; subst q₂; clear Hb₂.
    exists nf, no.
    destruct (bool_dec (is_neg_vec p₃) (is_neg_vec q₃)) as [Hb₃| Hb₃].
     move Hpq₃ at top; subst q₃; clear Hb₃.
     exists nf', no'.
     remember (acos ((p · p') / r²)) as a eqn:Ha.
     remember (Z.to_nat (Int_part (a / (2 * PI)))) as k eqn:Hk.
     exists n, k.
     unfold J₁_of_nats.
     rewrite <- Hq₂, <- Hq₃.
     rewrite Hno, path_of_nat_inv.
     rewrite Hno', path_of_nat_inv.
     rewrite Hso₂, Hso₃.
     rewrite cos_plus, sin_plus.
     rewrite <- Ha.
     remember (a / INR n)%R as θ eqn:Hθ.
rewrite HM in Hv.
rewrite matrix_pow in Hv.

bbb.
     simpl in HM.
     destruct v as (x, y, z).
     remember (√ (x² + y² + z²)) as r₁ eqn:Hr₁.
bbb.

Theorem J₀_is_countable : ∀ r,
  ∃ f : ℕ → matrix ℝ, ∀ M : matrix ℝ, M ∈ J₀ r → ∃ n : ℕ, f n = M.
Proof.
intros r.
apply surj_prod_6_nat_surj_nat.
exists (J₀_of_nats r).
intros M HM.
destruct HM as (Hrm & p & p' & n & Hp & Hp' & HM).
destruct Hp as ((el & p₂ & Hso₂ & Hn₂ & Hr₂) & Hp).
destruct Hp' as ((el' & p₃ & Hso₃ & Hn₃& Hr₃) & Hp').
destruct Hso₂ as (el₂ & Hso₂).
destruct Hso₃ as (el₃ & Hso₃).
assert (H : p₂ ∈ sphere r ∧ p₃ ∈ sphere r).
 split.
  rewrite rotate_vec_mul in Hso₂.
  rewrite <- Hso₂.
  apply on_sphere_after_rotation; [ easy | ].
  apply mat_of_path_is_rotation_matrix.

  rewrite rotate_vec_mul in Hso₃.
  rewrite <- Hso₃.
  apply on_sphere_after_rotation; [ easy | ].
  apply mat_of_path_is_rotation_matrix.

 destruct H as (Hp₂s, Hp₃s).
 apply rotate_rev_path in Hso₂.
 apply rotate_rev_path in Hso₃.
 remember (nat_of_path el) as nf eqn:Hnf.
 remember (nat_of_path (rev_path el₂)) as no eqn:Hno.
 remember (nat_of_path el') as nf' eqn:Hnf'.
 remember (nat_of_path (rev_path el₃)) as no' eqn:Hno'.
 remember (fixpoint_of_nat r nf) as q₂ eqn:Hq₂.
 remember (fixpoint_of_nat r nf') as q₃ eqn:Hq₃.
 assert (Hpq₂ :
  p₂ =
    if bool_dec (is_neg_vec p₂) (is_neg_vec q₂) then q₂
    else (- q₂)%vec).
  subst nf.
  unfold fixpoint_of_nat in Hq₂.
  rewrite path_of_nat_inv in Hq₂.
  rewrite rotate_vec_mul in Hr₂.
  clear Hn₃.
  eapply axis_and_fixpoint_of_path_collinear; try eassumption.
  now subst q₂; apply fixpoint_of_path_on_sphere.

  assert (Hpq₃ :
   p₃ =
     if bool_dec (is_neg_vec p₃) (is_neg_vec q₃) then q₃
     else (- q₃)%vec).
   subst nf'.
   unfold fixpoint_of_nat in Hq₃.
   rewrite path_of_nat_inv in Hq₃.
   rewrite rotate_vec_mul in Hr₃.
   eapply axis_and_fixpoint_of_path_collinear; try eassumption.
   now subst q₃; apply fixpoint_of_path_on_sphere.

   destruct (bool_dec (is_neg_vec p₂) (is_neg_vec q₂)) as [Hb₂| Hb₂].
    move Hpq₂ at top; subst q₂; clear Hb₂.
    exists nf, no.
    destruct (bool_dec (is_neg_vec p₃) (is_neg_vec q₃)) as [Hb₃| Hb₃].
     move Hpq₃ at top; subst q₃; clear Hb₃.
     exists nf', no'.
     remember (acos ((p · p') / r²)) as a eqn:Ha.
     remember (Z.to_nat (Int_part (a / (2 * PI)))) as k eqn:Hk.
     exists n, k.
     unfold J₀_of_nats.
     rewrite <- Hq₂, <- Hq₃.
     do 2 rewrite rotate_vec_mul.
     rewrite Hno, path_of_nat_inv.
     rewrite Hno', path_of_nat_inv.
     rewrite rotate_vec_mul in Hso₂, Hso₃.
     remember (mat_of_path (rev_path el₂)) as M₂ eqn:HM₂.
     remember (mat_of_path (rev_path el₃)) as M₃ eqn:HM₃.
     rewrite Hso₂, Hso₃, <- Ha.
     remember (a / INR n + 2 * INR k * PI / INR n)%R as θ eqn:Hθ.
     remember (p × p') as px eqn:Hpx.
     symmetry.
     destruct (vec_zerop px) as [Hpxz| Hpxz].
      move Hpxz at top; subst px.
      symmetry in Hpx.

      Focus 2.
      destruct px as (xp, yp, zp); simpl.
      remember (√ (xp² + yp² + zp²)) as rp eqn:Hrp.
      do 3 rewrite Rsqr_mult.
      do 2 rewrite <- Rmult_plus_distr_l.
      rewrite sqrt_mult_alt.
       rewrite <- Hrp.
        rewrite sqrt_Rsqr.
         rewrite Rinv_l.
          do 3 rewrite Rdiv_1_r.
          replace (/ rp * xp)%R with (xp / rp)%R by lra.
          replace (/ rp * yp)%R with (yp / rp)%R by lra.
          replace (/ rp * zp)%R with (zp / rp)%R by lra.
          move M at bottom.
          move Ha at bottom.
          move Hθ at bottom.
          move Hk at bottom.
          move Hp before HM.
          move Hp' before HM.
          rewrite Hpx in Hpxz.
          move Hpxz after Hp'.
          symmetry in Hpx; move Hpx at bottom.
          move Hrp at bottom.
          destruct M; simpl in *.
          unfold mkrmat; f_equal.
           unfold is_rotation_matrix, mat_transp in Hrm; simpl in Hrm.
           unfold mat_id, mat_det, mkrmat in Hrm; simpl in Hrm.
           destruct Hrm as (Hrm & Hdet).
           injection Hrm; clear Hrm.
           intros H33 H32 H31 H23 H22 H21 H13 H12 H11.

bbb.

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
   apply in_sphere_in_ball in Hps; [ easy | ].
   split; [ apply Rle_0_1 | apply Rle_refl ].

   intros HD.
   assert (H : p ∈ (D ∪ sphere_sym D) ∩ sphere 1).
    now rewrite intersection_union_distr_r; left.

    specialize (Hdnc p H) as (n, Hdnc).
    revert Hdnc; apply Hp.

  split.
   apply neg_vec_in_ball.
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
    ∧ ∀ n p p', p ∈ D ∩ sphere ∥p₁∥ → p' ∈ D ∩ sphere ∥p₁∥
    → ((R₁ ^ n)%mat * p ≠ p')%vec).
  assert (Hp₁nz : p₁ ≠ 0%vec).
   intros H; apply Hpnd; subst p₁; simpl.
   exists (ạ :: []), 0%vec.
   split; [ apply same_orbit_refl | ].
   split; [ easy | simpl; f_equal; lra ].

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
