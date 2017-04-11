(* Banach-Tarski paradox. *)
(* Inspirations:
   - Stan Wagon: The Banach-Tarski Paradox, Cambridge University Press
   - Wikipedia: Banach–Tarski paradox
   - http://people.math.umass.edu/~weston/oldpapers/banach.pdf *)
(* Coq v8.6 *)

Require Import Utf8 List Relations NPeano Wf_nat.
Import ListNotations.
Require Import Reals Psatz Nsatz.

Require Import Misc Words Normalize Reverse MiscReals MiscTrigo.
Require Import Matrix Pset Orbit.
Require Import Partition OrbitRepr GroupTransf Equidecomp.
Require Import Countable RnCountable NotEmptyPath.

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
  equidecomposable (ball ∖ D)
    (transl (V 3 0 0) (ball ∖ D) ∪ transl (V 6 0 0) (ball ∖ D))%S.
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
  (map (transl (V 3 0 0)) [A₁; rot ạ A₂] ++
   map (transl (V 6 0 0)) [A₃; rot ḅ A₄]); simpl.
split.
 subst A₁ A₂ A₃ A₄.
 eapply r_decomposed_4; now try eassumption.

 split.
  pose proof r_decomposed_2_a f Hosf os Hos as Ha.
  pose proof r_decomposed_2_b f Hosf os Hos as Hb.
  eapply partition_group_map with (g := Transl (V 3 0 0)) in Ha; try eassumption.
  eapply partition_group_map with (g := Transl (V 6 0 0)) in Hb; try eassumption.
  eapply partition_union in Hb; [ | | apply Ha ].
   apply Hb.

   unfold set_inter, set_eq; intros (x, y, z).
   split; [ intros (H₁, H₂) | easy ].
   simpl in H₁, H₂.
   unfold empty_set; simpl.
   destruct H₁ as (H₁, H₃).
   destruct H₂ as (H₂, H₄).
   unfold ball in H₁, H₂.
   rewrite Ropp_0 in H₁, H₂; do 2 rewrite Rplus_0_r in H₁, H₂.
   rewrite fold_Rminus in H₁, H₂.
   now apply (Rno_intersect_balls_x3_x6 x y z).

  constructor; [ now exists (Transl (V 3 0 0)) | ].
  constructor.
   now exists (Comb (Transl (V 3 0 0)) (rot_elem ạ)); rewrite rot_set_map_mul.

   constructor; [ now exists (Transl (V 6 0 0)) | ].
   constructor; [ | constructor ].
   now exists (Comb (Transl (V 6 0 0)) (rot_elem ḅ)); rewrite rot_set_map_mul.
Qed.

Theorem equidec_transl : ∀ d E F,
  equidecomposable E F
  → equidecomposable (transl d E) (transl d F).
Proof.
intros * HEF.
destruct HEF as (PE & PF & HPE & HPF & HEF).
unfold equidecomposable.
exists (map (transl d) PE), (map (transl d) PF).
split; [ apply (partition_group_map E PE (Transl d) HPE) | ].
split; [ apply (partition_group_map F PF (Transl d) HPF) | ].
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
exists (Comb (Transl d) (Comb g (Transl (-d)))); simpl.
rewrite transl_transl, vec_add_opp_diag_l.
now rewrite transl_0, HEF₁.
Qed.

Theorem separated_balls_without_fixpoints :
  (transl (V 3 0 0) (ball ∖ D) ∩ transl (V 6 0 0) (ball ∖ D) = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6); simpl | easy ].
simpl in H3, H6.
destruct H3 as (H3, _).
destruct H6 as (H6, _).
rewrite Ropp_0 in H3, H6; do 2 rewrite Rplus_0_r in H3, H6.
rewrite fold_Rminus in H3, H6.
now apply (Rno_intersect_balls_x3_x6 x y z).
Qed.

Theorem separated_balls :
  (transl (V 3 0 0) ball ∩ transl (V 6 0 0) ball = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6) | easy ].
unfold ball in H3, H6.
simpl in H3, H6.
rewrite Ropp_0 in H3, H6; do 2 rewrite Rplus_0_r in H3, H6.
rewrite fold_Rminus in H3, H6.
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

Definition fixpoint_of_path r el :=
  rotation_fixpoint (mat_of_path el) r.

Definition fixpoint_of_nat r n :=
  fixpoint_of_path r (path_of_nat n).

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
 Time f_equal; nsatz.
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

Definition fixpoint_of_bool_prod_nat r '(b, nf, no) :=
  let p := rotation_fixpoint (mat_of_path (path_of_nat nf)) r in
  let p₁ :=
    if is_neg_vec p then if (b : bool) then p else (- p)%vec
    else if b then (- p)%vec else p
  in
  fold_right rotate p₁ (path_of_nat no).

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
 Time clear H₁ H₂ H₃ H₄ H₅ H₆; nsatz.
 Time clear H₁ H₂ H₃ H₇ H₈ H₉; nsatz.
 Time clear H₄ H₅ H₆ H₇ H₈ H₉; nsatz.
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

Theorem sphere_sym_neg_vec : ∀ p, p ∈ sphere_sym D ↔ (- p)%vec ∈ D.
Proof.
intros (x, y, z).
split.
 intros (el₁ & p₁ & Hso & Hn & Hr).
 now exists el₁, p₁.

 intros (el₁ & p₁ & Hso & Hn & Hr).
 now exists el₁, p₁.
Qed.

Theorem neg_vec_in_sphere : ∀ r p, p ∈ sphere r → (- p)%vec ∈ sphere r.
Proof.
intros r (x, y, z) Hp; simpl.
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
 now rewrite set_inter_union_distr_r in Hp.

 apply countable_union; [ apply D_set_is_countable | ].
 apply D_set_symmetry_is_countable.
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
Time nsatz.
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

Definition rot_sin_cos p u v :=
  let a := latitude p u in
  let u₁ := (u - a ⁎ p) ⁄ √ (1 - a²) in
  let v₁ := (v - a ⁎ p) ⁄ √ (1 - a²) in
  let s := Rsign (p · (u₁ × v₁)) * ‖(u₁ × v₁)‖ / (‖u₁‖ * ‖v₁‖) in
  let c := (u₁ · v₁) / (‖u₁‖ * ‖v₁‖) in
  (s, c).

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
 Time f_equal; nsatz.

 left; clear Ha.
 Time f_equal; nsatz.
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
       unfold Rsign, Rsignp.
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
apply -> in_set_inter in Hp.
apply -> in_set_inter in Hp'.
destruct Hp as (Hpd & Hps).
destruct Hp' as (Hpd' & Hps').
destruct (vec_eq_dec axis 0) as [Haz| Haz].
 rewrite Haz in Had.
 rewrite Haz in Hps; simpl in Hps.
 rewrite Rsqr_0, Rplus_0_l, Rplus_0_l, sqrt_0, Rsqr_0 in Hps.
 destruct p as (xp, yp, zp).
 apply sqr_vec_norm_eq_0 in Hps.
 destruct Hps as (Hxp & Hyp & Hzp).
 now subst xp yp zp.

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
    ∃ sinθ₀ cosθ₀, (sinθ₀, cosθ₀) ∈ J₀ axis ∧
    let θ₀ := angle_of_sin_cos sinθ₀ cosθ₀ in
    ∃ n k,
    sinθ = sin ((θ₀ + 2 * IZR k * PI) / INR n) ∧
    cosθ = cos ((θ₀ + 2 * IZR k * PI) / INR n)).

Definition J_of_nat axis n : (ℝ * ℝ) :=
  let '(nj, n₂) := prod_nat_of_nat n in
  let '(nnk, nn) := prod_nat_of_nat n₂ in
  let nk := z_of_nat nnk in
  let '(sinθ₀, cosθ₀) := J₀_of_nat axis nj in
  let θ₀ := angle_of_sin_cos sinθ₀ cosθ₀ in
  let sinθ := sin ((θ₀ + 2 * IZR nk * PI) / INR nn) in
  let cosθ := cos ((θ₀ + 2 * IZR nk * PI) / INR nn) in
  (sinθ, cosθ).

Theorem J_is_countable : ∀ axis,
  axis ∉ D
  → (- axis)%vec ∉ D
  → ∀ sc, sc ∈ J axis → ∃ n : ℕ, J_of_nat axis n = sc.
Proof.
intros axis Had Hnad (s, c) Ha.
destruct Ha as (s₀ & c₀ & Ha & n & k & Hs & Hc).
specialize (J₀_is_countable axis Had Hnad) as HJ.
specialize (HJ (s₀, c₀) Ha) as (nj, Hnj).
destruct Ha as (Hsc₀ & p & p' & (Hp & Hp' & Hmp)).
unfold J_of_nat.
remember (nat_of_z k) as nk eqn:Hk.
remember (nat_of_prod_nat (nk, n)) as n₂ eqn:Hn₂.
remember (nat_of_prod_nat (nj, n₂)) as m eqn:Hm.
exists m; subst m n₂.
do 2 rewrite prod_nat_of_nat_inv.
rewrite Hnj, Hk.
rewrite z_of_nat_inv.
now f_equal.
Qed.

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

Theorem vec_const_mul_in_D : ∀ v r, r ≠ 0 → v ∈ D → r ⁎ v ∈ D.
Proof.
intros * Hr Hv.
destruct Hv as (el & u & (Hso & Hnl & Hru)); simpl.
exists el, (r ⁎ u).
split.
 destruct Hso as (el₁ & Hso).
 exists el₁.
 rewrite rotate_vec_mul in Hso |-*.
 rewrite mat_vec_mul_const_distr.
 now f_equal.

 split; [ easy | ].
 rewrite rotate_vec_mul in Hru |-*.
 rewrite mat_vec_mul_const_distr.
 now f_equal.
Qed.

Definition set_of_vec (v : vector) := mkset (λ u, u = v).
Arguments set_of_vec v%vec.

Definition center := set_of_vec 0.

Theorem sphere_ball_but_center : ∀ p,
   (∃ r, 0 < r ≤ 1 ∧ p ∈ sphere r) ↔ p ∈ ball ∖ center.
Proof.
intros (x, y, z); simpl.
split.
 intros (r & Hr & Hs); rewrite Hs.
 replace 1 with 1² by apply Rsqr_1.
 split.
  apply Rsqr_incr_1; [ easy | lra | lra ].

  intros H; injection H; clear H; intros Hz Hy Hx.
  subst x y z; rewrite Rsqr_0 in Hs.
  do 2 rewrite Rplus_0_r in Hs.
  symmetry in Hs; apply Rsqr_eq_0 in Hs; lra.

 intros (Hle & Hnz).
 exists (√ (x² + y² + z²)).
 split.
  split.
   apply Rnot_le_lt; intros H1.
   specialize (sqrt_pos (x² + y² + z²)) as H2.
   apply Rle_antisym in H2; [ | easy ].
   apply sqrt_eq_0 in H2; [ | apply nonneg_sqr_vec_norm ].
   apply sqr_vec_norm_eq_0 in H2.
   now destruct H2 as (Hx & Hy & Hz); subst x y z.

   apply sqrt_le_1_alt in Hle.
   now rewrite sqrt_1 in Hle.

  rewrite Rsqr_sqrt; [ easy | apply nonneg_sqr_vec_norm ].
Qed.

Theorem in_ball_but_center_after_rotation : ∀ p M,
  p ∈ ball ∖ center
  → is_rotation_matrix M
  → mat_vec_mul M p ∈ ball ∖ center.
Proof.
intros * His HM.
apply sphere_ball_but_center in His.
destruct His as (r & Hr & Hs).
apply sphere_ball_but_center.
exists r.
split; [ easy | ].
now apply on_sphere_after_rotation.
Qed.

Theorem fold_in_ball : ∀ v,
  (let 'V x y z := v in x² + y² + z² ≤ 1) = v ∈ ball.
Proof. easy. Qed.

Theorem equidec_with_ball_but_center_with_and_without_fixpoints :
  ∀ p₁ s c ρ E ρE,
  p₁ ∈ sphere 1 ∖ D
  → (- p₁)%vec ∈ sphere 1 ∖ D
  → s² + c² = 1
  → (s, c) ∉ J p₁
  → ρ = matrix_of_axis_angle (p₁, s, c)
  → E =
      mkset
        (λ p, ∃ p₀ n, p₀ ∈ D ∩ ball ∖ center ∧ p = ((ρ ^ n)%mat * p₀)%vec)
  → ρE = mkset (λ u, ∃ v, v ∈ E ∧ u = (ρ * v)%vec)
  → equidecomposable_with (ball ∖ center) (ball ∖ center ∖ D)
       [E; ball ∖ center ∖ E] [ρE; ball ∖ center ∖ E].
Proof.
intros * (Hp₁s & Hp₁d) (Hnp₁s & Hnp₁d) Hsc Hj Hρ HE HρE.
assert (Hp₁ : ‖p₁‖ = 1) by (apply on_sphere_norm in Hp₁s; [ easy | lra ]).
assert (Hp₁z : p₁ ≠ 0%vec) by (apply vec_norm_neq_0; lra).
split; [ easy | ].
split.
 apply is_partition_sub.
 rewrite HE.
 intros p Hp; simpl in Hp.
 destruct Hp as (p₀ & n & Hp & Hq).
 rewrite Hq.
 apply in_ball_but_center_after_rotation; [ easy | ].
 apply mat_pow_is_rotation_matrix; rewrite Hρ.
 now apply matrix_of_axis_angle_is_rotation_matrix.

 split.
  assert (HSD : ((E ∖ D) ∪ (ball ∖ center ∖ E) = ball ∖ center ∖ D)%S).
   intros v; split; intros Hv.
    destruct Hv as [(HvE, HvD)| (HvS, HvE)].
     split; [ | easy ].
     rewrite HE in HvE.
     destruct HvE as (u & n & ((HuD & HuB) & HuS) & Hv).
     rewrite Hv.
     apply in_ball_but_center_after_rotation; [ easy | ].
     apply mat_pow_is_rotation_matrix; rewrite Hρ.
     now apply matrix_of_axis_angle_is_rotation_matrix.

     split; [ easy | ].
     intros Hv; apply HvE; clear HvE.
     rewrite HE; exists v, 0%nat.
     destruct HvS as (Hvb & Hvc).
     split; [ now split | ].
     now rewrite mat_pow_0, mat_vec_mul_id.

    destruct Hv as (HvS & HvD).
    now destruct (EM (v ∈ E)); [ left | right ].

   rewrite <- HSD.
   assert (HED : (ρE = E ∖ D)%S).
    intros v.
    split; intros H.
     rewrite HρE in H.
     destruct H as (u & Hu & Hv).
     remember D as d; simpl; subst d.
     split.
      rewrite HE in Hu; rewrite HE.
      remember D as d; remember set_inter as b.
      simpl in Hu; simpl; subst d b.
      destruct Hu as (p₀ & n & Hp₀ & Hu).
      exists p₀, (S n).
      split; [ easy | simpl ].
      now rewrite mat_vec_mul_assoc, <- Hu.

      intros Hvn.
      apply Hj; clear Hj; unfold J.
      remember J₀ as a; simpl; subst a.
      rewrite HE in Hu.
      remember D as d; remember set_inter as b.
      simpl in Hu; subst d b.
      destruct Hu as (p₀ & n & (Hp₀d & Hp₀S) & Hu).
      rewrite Hu in Hv.
      rewrite <- mat_vec_mul_assoc in Hv.
      replace (ρ * ρ ^ n)%mat with (ρ ^ S n)%mat in Hv by easy.
      remember (angle_of_sin_cos s c) as θ eqn:Hθ.
      remember (sin (θ * INR (S n))) as s₀ eqn:Hs₀.
      remember (cos (θ * INR (S n))) as c₀ eqn:Hc₀.
      exists s₀, c₀.
      split.
       split; [ subst s₀ c₀; apply sin2_cos2 | ].
       remember (matrix_of_axis_angle (p₁, s₀, c₀)) as ρ₀ eqn:Hρ₀.
       remember D as d; remember sphere as sph; simpl; subst d sph.
       exists (p₀ ⁄ ‖p₀‖), (v ⁄ ‖p₀‖).
       split.
        split.
         destruct Hp₀d as (Hp₀d, Hp₀b).
         apply vec_const_mul_in_D; [ | easy ].
         now apply Rinv_neq_0_compat, vec_norm_neq_0.

         rewrite Hp₁.
         apply vec_div_in_sphere; [ now apply vec_norm_neq_0 | ].
         apply in_its_sphere.

        split.
         split.
          apply vec_const_mul_in_D; [ | easy ].
          now apply Rinv_neq_0_compat, vec_norm_neq_0.

          rewrite Hp₁.
          apply vec_div_in_sphere; [ now apply vec_norm_neq_0 | ].
          rewrite Hv.
          apply on_sphere_after_rotation; [ apply in_its_sphere | ].
          apply mat_pow_is_rotation_matrix; rewrite Hρ.
          now apply matrix_of_axis_angle_is_rotation_matrix.

         rewrite mat_vec_mul_const_distr; f_equal.
         rewrite Hv, Hρ, Hρ₀.
         rewrite Rmult_comm in Hs₀, Hc₀.
         now erewrite matrix_of_mul_angle; try eassumption.

       rewrite Hc₀, Hs₀.
       rewrite angle_of_sin_cos_inv.
       remember ((θ * INR (S n)) // (2 * PI)) as k eqn:Hk.
       exists (S n), k.
       replace ((θ * INR (S n)) rmod (2 * PI) + 2 * IZR k * PI)
       with (2 * PI * IZR k + (θ * INR (S n)) rmod (2 * PI)) by lra.
       rewrite Hk.
       rewrite <- Rdiv_mod; [ | specialize PI_neq0; lra ].
       rewrite Rmult_div.
       rewrite Rmult_div_same.
        rewrite Hθ.
        now rewrite sin_angle_of_sin_cos, cos_angle_of_sin_cos.

        now replace 0 with (INR 0) by easy; apply not_INR.

     destruct H as (Hv & HnD).
     rewrite HE in Hv.
     destruct Hv as (u & n & Hu & Hv).
     rewrite HρE; simpl.
     destruct n.
      simpl in Hv; rewrite mat_vec_mul_id in Hv; rewrite Hv in HnD.
      now destruct Hu as (Hu, _); destruct Hu.

      exists ((ρ ^ n)%mat * u)%vec.
      rewrite <- mat_vec_mul_assoc.
      split; [ | easy ].
      now rewrite HE; exists u, n.

   rewrite <- HED.
   split; [ now simpl; rewrite set_union_empty_r | ].
   intros i j Hij.
   assert (H : (ρE ∩ (ball ∖ center ∖ E) = ∅)%S).
    intros u.
    split; [ intros H | easy ].
    remember (ball ∖ center) as bc; simpl in H; subst bc.
    destruct H as (HuρE & HuS₂ & HunE).
    rewrite HρE in HuρE; simpl in HuρE.
    destruct HuρE as (v & Hv & Huv).
    rewrite Huv in HunE.
    exfalso; apply HunE; clear HunE.
    rewrite HE in Hv |-*.
    simpl in Hv; simpl.
    destruct Hv as (p₀ & n & Hv).
    exists p₀, (S n).
    destruct Hv as ((((el & p₂ & Hel) & Hp₀b) & Hp₀) & Hv).
    rewrite fold_in_ball in Hp₀b.
    rewrite fold_in_ball.
    split.
     split; [ | easy ].
     now split; [ exists el, p₂ | ].

     rewrite Hv, <- mat_vec_mul_assoc.
     now rewrite <- mat_pow_succ.

     destruct i.
      destruct j; [ easy | ].
      destruct j; [ easy | ].
      simpl; rewrite match_id.
      apply set_inter_empty_r.

      destruct i.
       destruct j; [ now rewrite set_inter_comm | ].
       destruct j; [ easy | ].
       simpl; rewrite match_id.
       apply set_inter_empty_r.

       destruct j.
        simpl; rewrite match_id.
        apply set_inter_empty_l.

        destruct j.
         simpl; rewrite match_id.
         apply set_inter_empty_l.

         simpl; do 2 rewrite match_id.
         apply set_inter_empty_l.

  assert (Hρm : is_rotation_matrix ρ).
   rewrite Hρ.
   now apply matrix_of_axis_angle_is_rotation_matrix.

   exists [Rot ρ Hρm; gr_ident].
   intros i Hilen.
   simpl in Hilen.
   destruct i.
    simpl; intros v.
    split; intros H.
     destruct H as (u & H).
     rewrite HρE; simpl.
     now exists u.

     rewrite HρE in H; simpl in H.
     destruct H as (u & H); simpl.
     now exists u.

    destruct i; [ now simpl; rewrite transl_0 | lia ].
Qed.

Theorem equidec_ball_but_center_with_and_without_fixpoints :
  equidecomposable (ball ∖ center) (ball ∖ center ∖ D).
Proof.
assert (H : ∃ p₁, p₁ ∈ ball ∖ center ∖ D ∧ (- p₁)%vec ∈ ball ∖ center ∖ D).
 specialize (D_set_and_its_symmetric_are_countable 1) as (f, Hdnc).
 specialize (ball_set_not_countable 1 Rlt_0_1 f) as (p & Hps & Hp).
 exists p.
 split.
  split.
   apply sphere_ball_but_center.
   exists 1; split; [ lra | easy ].

   intros HD.
   assert (H : p ∈ (D ∪ sphere_sym D) ∩ sphere 1).
    rewrite set_inter_union_distr_r; left.
    split; [ | easy ].
    destruct HD as (el & p₁ & Hso & Hnl & Hel).
    now exists el, p₁.

    specialize (Hdnc p H) as (n, Hdnc).
    revert Hdnc; apply Hp.

  split.
   apply sphere_ball_but_center.
   exists 1; split; [ lra | ].
   now apply neg_vec_in_sphere in Hps.

   intros HD.
   assert (H : p ∈ (D ∪ sphere_sym D) ∩ sphere 1).
    rewrite set_inter_union_distr_r; right.
    split; [ | easy ].
    destruct HD as (el & p₁ & Hso & Hnl & Hel).
    now exists el, p₁.

    specialize (Hdnc p H) as (n, Hdnc).
    revert Hdnc; apply Hp.

 destruct H as (p₁ & Hp & Hq).
 assert (∃ s c, s² + c² = 1 ∧ (s, c) ∉ J p₁) as (s & c & Hsc & Hj).
  destruct Hp as (Hps, Hpnd).
  destruct Hq as (Hqs, Hqnd).
  specialize (J_is_countable p₁ Hpnd Hqnd) as Hjc.
  specialize (rotations_not_countable (J_of_nat p₁)) as (s, (c, (Hsc, Hn))).
  exists s, c; split; [ easy | intros H ].
  specialize (Hjc _ H) as (n, Hjc).
  now specialize (Hn n).

  assert (Hpz : p₁ ≠ 0%vec).
   destruct Hp as (Hp, _).
   intros H; rewrite H in Hp; simpl in Hp.
   rewrite Rsqr_0, Rplus_0_l, Rplus_0_l in Hp.
   now destruct Hp.

   remember (p₁ ⁄ ‖p₁‖) as p'₁ eqn:Hp'₁.
   remember (matrix_of_axis_angle (p'₁, s, c)) as ρ eqn:Hρ.
   remember
     (mkset (λ p, ∃ p₀ n, p₀ ∈ D ∩ ball ∖ center ∧ p = ((ρ ^ n)%mat * p₀)%vec))
     as E eqn:HE.
   remember (mkset (λ u, ∃ v, v ∈ E ∧ u = (ρ * v)%vec)) as ρE eqn:HρE.
   assert (Hp' : p'₁ ∈ sphere 1 ∖ D).
    split.
     rewrite Hp'₁.
     apply vec_div_in_sphere; [ now apply vec_norm_neq_0 | ].
     apply in_its_sphere.

     rewrite Hp'₁.
     intros H.
     apply vec_const_mul_in_D with (r := ‖p₁‖) in H.
      rewrite vec_const_mul_assoc in H.
      rewrite Rinv_r in H; [ | now apply vec_norm_neq_0 ].
      rewrite vec_const_mul_1_l in H.
      now destruct Hp as (_, Hp).

      now apply vec_norm_neq_0.

    assert (Hnp' : (- p'₁)%vec ∈ sphere 1 ∖ D).
     split; [ now apply neg_vec_in_sphere; destruct Hp' | ].
     intros H; apply Hp'.
     apply vec_const_mul_in_D with (r := -1) in H; [ | lra ].
     rewrite <- vec_opp_const_mul_distr_l in H.
     rewrite vec_const_mul_1_l in H.
     now rewrite neg_vec_involutive in H.

     assert (Hj' : (s, c) ∉ J p'₁).
      intros H; apply Hj.
      unfold J in H; unfold J.
      remember J₀ as x; simpl in H; simpl; subst x.
      destruct H as (s₀ & c₀ & Hsc₀ & H).
      exists s₀, c₀; split; [ | easy ].
      unfold J₀ in Hsc₀; unfold J₀.
      remember D as d; remember sphere as sp.
      remember matrix_of_axis_angle as m; simpl in Hsc₀; simpl.
      subst d sp m.
      split; [ easy | ].
      destruct Hsc₀ as (Hsc₀ & p & p' & Hpp & Hpp' & Hmp).
      assert (Hp1 : ‖p'₁‖ = 1).
       now apply on_sphere_norm; [ lra | destruct Hp' ].

       exists (‖p₁‖ ⁎ p), (‖p₁‖ ⁎ p').
       split.
        split.
         apply vec_const_mul_in_D; [ now apply vec_norm_neq_0 | easy ].

         apply vec_mul_in_sphere.
         now rewrite Hp1 in Hpp.

        split.
         split.
          apply vec_const_mul_in_D; [ now apply vec_norm_neq_0 | easy ].

          apply vec_mul_in_sphere.
          now rewrite Hp1 in Hpp'.

         rewrite mat_vec_mul_const_distr.
         f_equal.
         rewrite matrix_mul_axis with (k := ‖p₁‖) in Hmp.
          rewrite Hp'₁ in Hmp.
          rewrite vec_const_mul_assoc in Hmp.
          rewrite Rinv_r in Hmp; [ | now apply vec_norm_neq_0 ].
          rewrite vec_const_mul_1_l in Hmp.
          rewrite Rsign_of_pos in Hmp; [ now rewrite Rmult_1_l in Hmp | ].
          now apply vec_norm_pos.

          now apply vec_norm_neq_0.

      specialize
        (equidec_with_ball_but_center_with_and_without_fixpoints p'₁ s c ρ E
           ρE Hp' Hnp' Hsc Hj' Hρ HE HρE) as H.
      now apply equidec_with_equidec in H.
Qed.

Theorem equidec_ball_ball_but_1_0_0 :
  equidecomposable ball (ball ∖ set_of_vec (V 1 0 0)).
Proof.
remember (V 1 0 0) as p₀ eqn:Hp₀.
remember (set_of_vec p₀) as E eqn:HE.
remember (mkset (λ p, ∃ n, ((rot_z ^ n)%mat * p₀)%vec = p)) as F eqn:HF.
remember (mkset (λ p, ∃ n, ((rot_z ^ S n)%mat * p₀)%vec = p)) as rF eqn:HrF.
exists [F; ball ∖ F].
exists [rF; ball ∖ F].
split.
 apply is_partition_sub.
 rewrite HF.
 intros v Hv; simpl in Hv.
 destruct Hv as (n & Hv).
 rewrite <- Hv, Hp₀.
 apply in_ball_after_rotation; [ simpl; rewrite Rsqr_0, Rsqr_1; lra | ].
 apply mat_pow_is_rotation_matrix.
 apply rot_z_is_rotation_matrix.

 split.
  assert (HED : (rF = F ∖ E)%S).
   intros v.
   split; intros H.
    rewrite HrF in H; simpl in H; simpl.
    destruct H as (n, Hv).
    split; [ now rewrite HF; exists (S n) | ].
    intros HvE.
    rewrite HE in HvE; simpl in HvE.
    move HvE at top; subst v.
    rewrite <- mat_pow_succ in Hv.
    replace rot_z with (mat_of_elem ḅ) in Hv by easy.
    replace (mat_of_elem ḅ) with (mat_of_path [ḅ]) in Hv
      by apply mat_mul_id_r.
    rewrite mat_of_path_elem_pow in Hv.
    rewrite <- rotate_vec_mul in Hv.
    revert Hv; rewrite Hp₀.
    eapply rotate_1_0_0_is_diff with (el₁ := repeat ḅ n) (d := false).
     now rewrite app_repeat_diag.

     apply norm_list_repeat.

    rewrite HF in H; rewrite HrF; simpl in H; simpl.
    destruct H as ((n & Hv) & HvnE).
    destruct n; [ | now exists n].
    rewrite mat_pow_0, mat_vec_mul_id in Hv; subst v.
    now rewrite HE in HvnE; simpl in HvnE.

   assert (HSD : ((F ∖ E) ∪ (ball ∖ F) = ball ∖ E)%S).
    intros v; split; intros Hv.
     destruct Hv as [(HvE, HvD)| (HvS, HvE)].
      split; [ | easy ].
      rewrite HF in HvE.
      simpl in HvE.
      destruct HvE as (n & Hv).
      rewrite <- Hv.
      apply in_ball_after_rotation.
       rewrite Hp₀; simpl.
       rewrite Rsqr_0, Rsqr_1; lra.

       apply mat_pow_is_rotation_matrix.
       apply rot_z_is_rotation_matrix.

      split; [ easy | ].
      intros Hv; apply HvE; clear HvE.
      rewrite HE in Hv; simpl in Hv; subst v.
      rewrite HF; simpl.
      exists 0%nat.
      now rewrite mat_pow_0, mat_vec_mul_id.

     destruct Hv as (HvS & HvD).
     now destruct (EM (v ∈ F)); [ left | right ].

    rewrite <- HSD, <- HED.
    replace [rF; ball ∖ F] with ([rF] ++ [ball ∖ F]) by easy.
    apply partition_union; try apply is_partition_single.
    intros p.
    split; intros Hp; [ simpl | easy ].
    destruct Hp as (Hp & Hpb & HpF).
    apply HpF.
    rewrite HrF in Hp; rewrite HF.
    simpl in Hp; simpl.
    destruct Hp as (n, Hp).
    now exists (S n); simpl.

  constructor.
   exists (Rot rot_z rot_z_is_rotation_matrix); simpl.
   intros p.
   split; intros Hp.
    rewrite HrF; simpl in Hp; simpl.
    destruct Hp as (q & Hq & Hp).
    rewrite HF in Hq; simpl in Hq.
    destruct Hq as (n, Hq).
    rewrite <- Hq in Hp.
    exists n.
    now rewrite <- mat_vec_mul_assoc in Hp.

    rewrite HrF in Hp; simpl in Hp; simpl.
    destruct Hp as (n & Hp).
    exists ((rot_z ^ n)%mat * p₀)%vec.
    rewrite mat_vec_mul_assoc in Hp.
    split; [ | easy ].
    rewrite HF; simpl.
    now exists n.

   constructor; [ | constructor ].
   exists gr_ident.
   apply app_gr_ident.
Qed.

Theorem equidec_ball_but_1_0_0_ball_but_center :
  equidecomposable (ball ∖ set_of_vec (V 1 0 0)) (ball ∖ center).
Proof.
remember (set_of_vec (V 1 0 0)) as E eqn:HE.
exists [center; ball ∖ E ∖ center].
exists [E; ball ∖ center ∖ E].
split.
 apply is_partition_sub.
 intros p Hp; subst E.
 simpl in Hp; subst p; simpl.
 split; [ rewrite Rsqr_0; lra | ].
 intros H; simpl in H.
 injection H; clear H; intros H; lra.

 split.
  apply is_partition_sub.
  intros p Hp; subst E.
  simpl in Hp; subst p; simpl.
  split; [ rewrite Rsqr_0, Rsqr_1; lra | ].
  intros H; simpl in H.
  injection H; clear H; intros H; lra.

  constructor.
   exists (Transl (V 1 0 0)).
   intros (x, y, z); subst E; simpl.
   split; intros Hv.
    injection Hv; clear Hv; intros Hz Hy Hx.
    rewrite Ropp_0 in Hy, Hz; rewrite Rplus_0_r in Hy, Hz.
    subst y z; f_equal; lra.

    injection Hv; clear Hv; intros Hz Hy Hx.
    subst x y z; f_equal; lra.

    constructor; [ | constructor ].
    exists gr_ident.
    rewrite set_sub_sub_swap.
    apply app_gr_ident.
Qed.

Theorem equidec_ball_ball_but_center :
  equidecomposable ball (ball ∖ center).
Proof.
rewrite <- equidec_ball_but_1_0_0_ball_but_center.
apply equidec_ball_ball_but_1_0_0.
Qed.

Theorem equidec_ball_with_and_without_fixpoints :
  equidecomposable ball (ball ∖ D).
Proof.
rewrite equidec_ball_ball_but_center at 1.
rewrite equidec_ball_but_center_with_and_without_fixpoints.
rewrite set_sub_sub_swap.
enough (HD : ((ball ∖ D) ∖ center = ball ∖ D)%S) by now rewrite HD.
intros p; split; intros Hp; [ now destruct Hp | ].
split; [ easy | ].
destruct Hp as (Hpb, HpD).
intros H; apply HpD.
simpl in H; subst p; simpl.
exists (ạ :: []), 0%vec.
split; [ easy | ].
split; [ easy | ].
rewrite rotate_vec_mul.
apply mat_vec_mul_0_r.
Qed.

Theorem Banach_Tarski_paradox :
  equidecomposable ball (transl (V 3 0 0) ball ∪ transl (V 6 0 0) ball)%S.
Proof.
transitivity (ball ∖ D).
 apply equidec_ball_with_and_without_fixpoints.

 etransitivity.
  apply Banach_Tarski_paradox_but_fixpoints.

  apply equidec_set_union.
   apply separated_balls_without_fixpoints.

   apply separated_balls.

   apply equidec_transl; symmetry.
   apply equidec_ball_with_and_without_fixpoints.

   apply equidec_transl; symmetry.
   apply equidec_ball_with_and_without_fixpoints.
Qed.

Check Banach_Tarski_paradox.
