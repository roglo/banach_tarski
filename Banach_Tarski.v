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

Theorem Rno_intersect_spheres_x3_x6 : ∀ x y z,
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
  equidecomposable sphere_but_fixpoints
    (xtransl 3 sphere_but_fixpoints ∪ xtransl 6 sphere_but_fixpoints)%S.
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
   unfold sphere in H₁, H₂.
   now apply (Rno_intersect_spheres_x3_x6 x y z).

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

Theorem separated_spheres_without_fixpoints :
  (xtransl 3 sphere_but_fixpoints ∩ xtransl 6 sphere_but_fixpoints = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6); simpl | easy ].
unfold sphere_but_fixpoints in H3, H6.
simpl in H3, H6.
destruct H3 as (H3, _).
destruct H6 as (H6, _).
now apply (Rno_intersect_spheres_x3_x6 x y z).
Qed.

Theorem separated_spheres :
  (xtransl 3 sphere ∩ xtransl 6 sphere = ∅)%S.
Proof.
intros * (x, y, z); split; [ intros (H3, H6) | easy ].
unfold sphere in H3, H6.
simpl in H3, H6.
now apply (Rno_intersect_spheres_x3_x6 x y z).
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

Definition ter_bin_of_point '(P x y z) := ter_bin_of_frac_part x.

Theorem ter_bin_of_sphere_surj : ∀ u : ℕ → bool,
  ∃ p : point, p ∈ sphere ∧ (∀ n, ter_bin_of_point p n = u n).
Proof.
intros.
specialize (ter_bin_of_frac_part_surj u); intros (r & Hr & Hn).
exists (P r 0 0); simpl in Hr; simpl.
split; [ | easy ].
do 2 rewrite Rsqr_pow2.
rewrite pow_i; [ | apply Nat.lt_0_succ ].
do 2 rewrite Rplus_0_r.
replace 1%R with (1 ^ 2)%R by lra.
apply pow_incr; lra.
Qed.

Theorem sphere_not_countable : ¬ (is_countable {p : point | p ∈ sphere}).
Proof.
intros H.
unfold is_countable in H.
destruct H as (f, Hf).
enough (Hcontr : ∃ a, a ∈ sphere ∧ ∀ n, proj1_sig (f n) ≠ a).
 destruct Hcontr as (a & Ha & Hnn).
 specialize (Hf (exist _ a Ha)).
 destruct Hf as (n, Hn).
 specialize (Hnn n).
 now rewrite Hn in Hnn; apply Hnn.

 specialize
  (Cantor_gen ℕ ℕ point (setp sphere) id ter_bin_of_point id_nat
     ter_bin_of_sphere_surj).
 intros H.
 specialize (H (λ n, proj1_sig (f n))) as (p, H).
 exists p.
 split; [ apply (H O) | ].
 intros n Hn.
 specialize (H n).
 destruct H.
 now symmetry in Hn.
Qed.

Theorem sphere_set_not_countable :
  ∀ f : ℕ → point, ∃ p : point, p ∈ sphere ∧ ∀ n : ℕ, f n ≠ p.
Proof.
intros f.
specialize
 (Cantor_gen ℕ ℕ point (setp sphere) id ter_bin_of_point id_nat
    ter_bin_of_sphere_surj f) as (p, Hp).
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

Theorem rotation_fixpoint_on_sphere_ray : ∀ r m,
  m ≠ mat_transp m
  → rotation_fixpoint m r ∈ sphere_ray r.
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

Theorem free_family_diff_norm_vec : ∀ V₁ V₂,
  ∥V₁∥ = ∥V₂∥
  → is_neg_point V₁ = is_neg_point V₂
  → V₁ ≠ 0%vec
  → V₂ ≠ 0%vec
  → V₁ ≠ V₂
  → ∀ a b : ℝ, (a ⁎ V₁ + b ⁎ V₂)%vec = 0%vec → a = 0%R ∧ b = 0%R.
Proof.
intros * Hvn Hn Hv₁ Hv₂ Hvv * Hab.
destruct V₁ as (x₁, y₁, z₁).
destruct V₂ as (x₂, y₂, z₂).
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

Theorem nonzero_cross_mul : ∀ V₁ V₂,
  ∥V₁∥ = ∥V₂∥
  → is_neg_point V₁ = is_neg_point V₂
  → V₁ ≠ 0%vec
  → V₂ ≠ 0%vec
  → V₁ ≠ V₂
  → V₁ × V₂ ≠ 0%vec.
Proof.
intros * Hvn Hn Hv₁ Hv₂ Hvv Hvvz.
destruct V₁ as (x₁, y₁, z₁).
destruct V₂ as (x₂, y₂, z₂).
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
       rewrite vec_const_mul_1 in Hvv.
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
        rewrite vec_const_mul_1 in Hvv.
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
          rewrite vec_const_mul_1 in Hvv.
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
        rewrite vec_const_mul_1 in Hvv.
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

Theorem vect_and_cross_mul_are_free_family : ∀ V₁ V₂ V₃,
  ∥V₁∥ = ∥V₂∥
  → is_neg_point V₁ = is_neg_point V₂
  → V₁ ≠ 0%vec
  → V₂ ≠ 0%vec
  → V₁ ≠ V₂
  → V₃ = V₁ × V₂
  → ∀ a b : ℝ, (a ⁎ V₁ + b ⁎ V₃)%vec = 0%vec → a = 0%R ∧ b = 0%R.
Proof.
intros * Hvn Hn Hv₁ Hv₂ Hvv Hv₃ * Hab.
destruct (Req_dec a 0) as [Ha| Ha]; [ | exfalso ].
 subst a; split; [ easy |  ].
 rewrite vec_const_mul_0_l in Hab.
 rewrite vec_add_0_l in Hab.
 apply vec_cross_mul_integral in Hab.
 destruct Hab as [| Hab]; [ easy | exfalso ].
 revert Hab; rewrite Hv₃.
 now apply nonzero_cross_mul.

 apply (f_equal (vec_dot_mul V₁)) in Hab.
 rewrite vec_dot_mul_0_r in Hab.
 rewrite vec_dot_mul_add_distr_l in Hab.
 do 2 rewrite <- Rmult_vec_dot_mul_distr_r in Hab.
 subst V₃.
 rewrite vec_dot_cross_mul in Hab.
 rewrite Rmult_0_r, Rplus_0_r in Hab.
 apply Rmult_integral in Hab.
 destruct Hab as [| Hab]; [ easy | ].
Theorem vec_dot_mul_diag : ∀ V, V · V = (∥V∥²)%R.
Proof.

bbb.
 destruct V₁ as (x₁, y₁, z₁).
 destruct V₂ as (x₂, y₂, z₂).
 simpl in Hab.
 injection Hab; clear Hab; intros Hz Hy Hx.
 rewrite Rplus_comm in Hx, Hy, Hz.
 apply Rplus_opp_r_uniq in Hx.
 apply Rplus_opp_r_uniq in Hy.
 apply Rplus_opp_r_uniq in Hz.
 apply Rmult_eq_compat_r with (r := (/ a)%R) in Hx.
 apply Rmult_eq_compat_r with (r := (/ a)%R) in Hy.
 apply Rmult_eq_compat_r with (r := (/ a)%R) in Hz.
 rewrite Rmult_shuffle0 in Hx, Hy, Hz.
 rewrite Rinv_r in Hx; [ | easy ].
 rewrite Rinv_r in Hy; [ | easy ].
 rewrite Rinv_r in Hz; [ | easy ].
 rewrite Rmult_1_l in Hx, Hy, Hz.
 rewrite Ropp_mult_distr_l, Rmult_shuffle0 in Hx, Hy, Hz.
 rewrite fold_Rdiv in Hx, Hy, Hz.
 remember (- b / a)%R as k eqn:Hk.
 simpl in Hn.
 destruct (Rlt_dec x₁ 0) as [Hlx₁| Hlx₁].
  destruct (Rlt_dec x₂ 0) as [Hlx₂| Hlx₂]; [ clear Hn | ].
bbb.

 rewrite Hx in Hz.
 rewrite Hy in Hz at 2.
 do 2 rewrite Rmult_assoc in Hz.
 rewrite <- Rmult_minus_distr_l in Hz.
 rewrite <- Rmult_assoc in Hz.
 rewrite fold_Rsqr in Hz.
 unfold Rdiv in Hz.
 rewrite <- Ropp_mult_distr_l, fold_Rdiv in Hz.
 rewrite <- Rsqr_neg in Hz.

bbb.

 simpl in Hn.
 destruct (Rlt_dec x₁ 0) as [Hx₁| Hx₁].
  destruct (Rlt_dec x₂ 0) as [Hx₂| Hx₂]; [ clear Hn |  ].
bbb.
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
bbb.

Theorem fixpoint_unicity : ∀ M V₁ V₂,
  is_rotation_matrix M
  → M ≠ mat_id
  → vec_norm V₁ = vec_norm V₂
  → is_neg_point V₁ = is_neg_point V₂
  → mat_vec_mul M V₁ = V₁
  → mat_vec_mul M V₂ = V₂
  → V₁ = V₂.
Proof.
intros * Hm Hnid Hvn Hn Hp₁ Hp₂.
bbb.

intros * Hm Hnid Hvn Hn Hp₁ Hp₂.
destruct (eq_point_dec V₁ (P 0 0 0)) as [Hv₁| Hv₁].
 rewrite Hv₁ in Hvn.
 unfold vec_norm in Hvn at 1.
 rewrite Rsqr_0, Rplus_0_r, Rplus_0_r in Hvn.
 rewrite sqrt_0 in Hvn.
 symmetry in Hvn.
 apply vec_norm_eq_0 in Hvn.
 now rewrite Hvn, Hv₁.

 destruct (eq_point_dec V₂ (P 0 0 0)) as [Hv₂| Hv₂].
  rewrite Hv₂ in Hvn.
  unfold vec_norm in Hvn at 2.
  rewrite Rsqr_0, Rplus_0_r, Rplus_0_r in Hvn.
  rewrite sqrt_0 in Hvn.
  now apply vec_norm_eq_0 in Hvn.

  destruct (eq_point_dec V₁ V₂) as [Hvv| Hvv]; [ easy | exfalso ].
  remember (vec_const_mul (∥V₁∥ / ∥(V₁ × V₂)∥)%R (V₁ × V₂)) as V₃ eqn:HV₃.
  move V₃ before V₂.
  assert (Hp₃ : mat_vec_mul M V₃ = V₃).
   subst V₃; apply mat_eigenvec_mul_const.
   rewrite mat_vec_mul_cross_distr; [ | easy ].
   now rewrite Hp₁, Hp₂.

   move Hp₃ before Hp₂.
   assert (HVV : ∥(V₁ × V₂)∥ ≠ 0%R).
    intros H; apply vec_norm_eq_0 in H.
    apply vec_cross_mul_eq_0 in H; [ | easy | easy ].
    destruct H as (a & b & Ha & Hb & Hab).
    remember (vec_const_mul a V₁) as aV₁ eqn:HaV₁; symmetry in HaV₁.
    remember (vec_const_mul b V₂) as bV₂ eqn:HbV₂; symmetry in HbV₂.
    destruct aV₁ as (ax₁, ay₁, az₁).
    destruct bV₂ as (bx₂, by₂, bz₂).
    simpl in Hab.
    injection Hab; clear Hab; intros Hz Hy Hx.
    move Hx after Hy; move Hz after Hy.
    apply Rplus_opp_r_uniq in Hx.
    apply Rplus_opp_r_uniq in Hy.
    apply Rplus_opp_r_uniq in Hz.
    rewrite Hx, Hy, Hz in HbV₂.
    replace (- ax₁)%R with (-1 * ax₁)%R in HbV₂ by lra.
    replace (- ay₁)%R with (-1 * ay₁)%R in HbV₂ by lra.
    replace (- az₁)%R with (-1 * az₁)%R in HbV₂ by lra.
    fold (vec_const_mul (-1) (P ax₁ ay₁ az₁)) in HbV₂.
    rewrite <- HaV₁ in HbV₂.
    rewrite vec_const_mul_assoc in HbV₂.
    replace (-1 * a)%R with (-a)%R in HbV₂ by lra.
    apply vec_const_mul_div in HbV₂; [ | easy ].
    rewrite HbV₂ in Hvn.
    rewrite vec_norm_vec_const_mul in Hvn.
    replace (∥V₁∥) with (1 * ∥V₁∥)%R in Hvn at 1 by lra.
    apply Rmult_eq_reg_r in Hvn; [ | now intros H; apply Hv₁, vec_norm_eq_0 ].
    symmetry in Hvn.
    apply Rabs_or in Hvn.
    destruct Hvn as [Hvn| Hvn]; rewrite Hvn in HbV₂.
     now rewrite vec_const_mul_1 in HbV₂; symmetry in HbV₂.

     destruct V₁ as (x, y, z); simpl in HbV₂.
     do 3 rewrite <- Ropp_mult_distr_l in HbV₂.
     do 3 rewrite Rmult_1_l in HbV₂.
     fold (neg_point (P x y z)) in HbV₂.
     rewrite HbV₂ in Hn.
     rewrite is_neg_point_neg_point in Hn; [ | easy ].
     now symmetry in Hn; apply no_fixpoint_negb in Hn.

    move HVV before Hvn.
    assert (Hvn' : ∥V₃∥ = ∥V₁∥).
     subst V₃; remember (V₁ × V₂) as VV.
     unfold vec_const_mul.
     destruct VV as (x, y, z); simpl in HVV; simpl.
     unfold Rdiv; do 6 rewrite Rsqr_mult.
     setoid_rewrite Rmult_shuffle0.
     do 2 rewrite <- Rmult_plus_distr_r.
     do 2 rewrite <- Rmult_plus_distr_l.
     rewrite Rsqr_inv; [ | easy ].
     rewrite Rsqr_sqrt; [ | apply nonneg_sqr_vec_norm ].
     rewrite Rmult_assoc.
     rewrite Rinv_r.
      rewrite Rmult_1_r.
      rewrite sqrt_Rsqr; [ easy | apply vec_norm_nonneg ].

      intros H; apply HVV; rewrite H.
      apply sqrt_0.

     move Hvn' before Hvn.
     assert (Hfree2 : ∀ a b, (a ⁎ V₁ + b ⁎ V₂ = 0 → a = 0%R ∧ b = 0%R)%vec).
      now apply free_family_diff_norm_vec.

(*
      assert (Hgen : ∀ V, ∃ x y z, V = (x ⁎ V₁ + y ⁎ V₂ + z ⁎ V₃)%vec).
       intros (v₁, v₂, v₃).
       destruct V₁ as (v₁₁, v₁₂, v₁₃).
       destruct V₂ as (v₂₁, v₂₂, v₂₃).
       destruct V₃ as (v₃₁, v₃₂, v₃₃).
       simpl.
       remember (mkrmat v₁₁ v₂₁ v₃₁ v₁₂ v₂₂ v₃₂ v₁₃ v₂₃ v₃₃) as Mv eqn:Hv.
       remember (mkrmat v₁ v₂₁ v₃₁ v₂ v₂₂ v₃₂ v₃ v₂₃ v₃₃) as Mx eqn:Hmx.
       remember (mkrmat v₁₁ v₁ v₃₁ v₁₂ v₂ v₃₂ v₁₃ v₃ v₃₃) as My eqn:Hmy.
       remember (mkrmat v₁₁ v₂₁ v₃ v₁₂ v₂₂ v₂ v₁₃ v₂₃ v₃) as Mz eqn:Hmz.
       exists (mat_det Mx / mat_det Mv)%R.
       exists (mat_det My / mat_det Mv)%R.
       exists (mat_det Mz / mat_det Mv)%R.
       f_equal.
       unfold mat_det; subst Mv Mx My Mz; simpl.
*)
      assert
        (Hfree3 : ∀ a b c,
         (a ⁎ V₁ + b ⁎ V₂ + c ⁎ V₃ = 0 → a = 0%R ∧ b = 0%R ∧ c = 0%R)%vec).
(*
intros * Habc.
destruct V₁ as (v₁₁, v₁₂, v₁₃).
destruct V₂ as (v₂₁, v₂₂, v₂₃).
destruct V₃ as (v₃₁, v₃₂, v₃₃).
set (B := mkrmat v₁₁ v₁₂ v₁₃ v₁₁ v₁₂ v₁₃ v₁₁ v₁₂ v₁₃).
remember (mat_det B) as d eqn:Hd.
symmetry in Hd.
assert (d ≠ 0)%R.
 clear Hfree2 a b c Habc.
 intros H; rewrite H in Hd; clear H.
 unfold mat_det, B in Hd.
 clear B.
 simpl in Hd.
 remember is_neg_point as f; simpl in *; subst f.
 remember (√ (v₁₁² + v₁₂² + v₁₃²)) as r eqn:Hr.
 symmetry in Hvn'.
 remember (√
             ((v₁₂ * v₂₃ - v₁₃ * v₂₂)² + (v₁₃ * v₂₁ - v₁₁ * v₂₃)² +
              (v₁₁ * v₂₂ - v₁₂ * v₂₁)²)) as rr.
 injection Hp₁; clear Hp₁; intros.
 injection Hp₂; clear Hp₂; intros.
 injection Hp₃; clear Hp₃; intros.
 injection HV₃; clear HV₃; intros.
 remember (r/rr)%R as k eqn:Hk.
 assert (0 < k)%R.
  subst k.
  apply Rmult_lt_reg_r with (r := rr).
   enough (0 ≤ rr)%R by lra.
   rewrite Heqrr.
   apply sqrt_pos.

   unfold Rdiv.
   rewrite Rmult_assoc.
   rewrite Rinv_l; [ | easy ].
   rewrite Rmult_0_l, Rmult_1_r.
   assert (0 ≤ r)%R by (rewrite Hr; apply sqrt_pos).
   enough (r ≠ 0)%R by lra.
   intros HH; move HH at top; subst r; apply Hv₁.
   symmetry in Hr.
   apply sqrt_eq_0 in Hr; [ | apply nonneg_sqr_vec_norm ].
   apply sqr_vec_norm_eq_0 in Hr.
   now destruct Hr; destruct H13; subst.

  clear r rr Hr Hvn Hvn' Heqrr HVV Hk.
  unfold is_rotation_matrix in Hm.
  destruct Hm as (Ht, Hm).
  unfold mat_det in Hm.
  unfold mat_id in Hnid.
  destruct M; simpl in *.
  unfold mat_transp in Ht; simpl in Ht.
  unfold mat_id in Ht; simpl in Ht.
  injection Ht; clear Ht; intros.
  unfold mkrmat in Hnid.

bbb.
*)
(*
      intros * Habc.
clear Hfree2.
      destruct V₁ as (x₁, y₁, z₁).
      destruct V₂ as (x₂, y₂, z₂).
      destruct V₃ as (x₃, y₃, z₃).
      simpl in Habc.
      injection Habc; clear Habc; intros Hz Hy Hx.
      simpl in Hvn.
      destruct (Req_dec a 0) as [Ha| Ha].
       subst a; split; [ easy | ].
       rewrite Rmult_0_l, Rplus_0_l in Hx, Hy, Hz.
       destruct (Req_dec b 0) as [Hb| Hb].
        subst b; split; [ easy | ].
        rewrite Rmult_0_l, Rplus_0_l in Hx, Hy, Hz.
        apply Rmult_integral in Hx; destruct Hx as [Hx| Hx]; [ easy | ].
        apply Rmult_integral in Hy; destruct Hy as [Hy| Hy]; [ easy | ].
        apply Rmult_integral in Hz; destruct Hz as [Hz| Hz]; [ easy | ].
        exfalso; subst; symmetry in Hvn'.
        rewrite vec_norm_0 in Hvn'.
        now apply vec_norm_eq_0 in Hvn'.

        exfalso.
        destruct (Req_dec c 0) as [Hc| Hc].
         subst c.
         rewrite Rmult_0_l, Rplus_0_r in Hx, Hy, Hz.
         apply Rmult_integral in Hx.
         apply Rmult_integral in Hy.
         apply Rmult_integral in Hz.
         destruct Hx as [| Hx]; [ easy | ].
         destruct Hy as [| Hy]; [ easy | ].
         destruct Hz as [| Hz]; [ easy | ].
         now subst x₂ y₂ z₂; apply Hv₂.

         apply Rplus_opp_r_uniq in Hx.
         apply Rplus_opp_r_uniq in Hy.
         apply Rplus_opp_r_uniq in Hz.
         apply Rmult_eq_compat_r with (r := (/ c)%R) in Hx.
         apply Rmult_eq_compat_r with (r := (/ c)%R) in Hy.
         apply Rmult_eq_compat_r with (r := (/ c)%R) in Hz.
         rewrite Rmult_shuffle0, Rinv_r in Hx; [ | easy ].
         rewrite Rmult_shuffle0, Rinv_r in Hy; [ | easy ].
         rewrite Rmult_shuffle0, Rinv_r in Hz; [ | easy ].
         rewrite Rmult_1_l, fold_Rdiv in Hx, Hy, Hz.
         rewrite Ropp_mult_distr_l in Hx, Hy, Hz.
         rewrite Rmult_div in Hx, Hy, Hz.
         subst x₃ y₃ z₃.
         simpl in HV₃.
         remember (√ (x₁² + y₁² + z₁²)) as r eqn:Hr.
         remember (y₁ * z₂ - z₁ * y₂)%R as rr₁ eqn:Hrr₁.
         remember (z₁ * x₂ - x₁ * z₂)%R as rr₂ eqn:Hrr₂.
         remember (x₁ * y₂ - y₁ * x₂)%R as rr₃ eqn:Hrr₃.
         remember (√ (rr₁² + rr₂² + rr₃²)) as rr eqn:Hrr.
         injection HV₃; clear HV₃; intros Hz Hy Hx.
bbb.
*)
      intros * Habc.
      remember (a ⁎ V₁ + b ⁎ V₂)%vec as V eqn:Hv.
      symmetry in Hv.
      destruct (eq_point_dec V 0%vec) as [H₁| H₁].
       subst V.
       apply Hfree2 in H₁.
       destruct H₁; subst a b.
       do 2 rewrite vec_const_mul_0_l in Habc.
       do 2 rewrite vec_add_0_l in Habc.
       apply eq_vec_const_mul_0 in Habc.
       split; [ easy | ].
       split; [ easy | ].
       destruct Habc as [Habc | Habc]; [ easy | ].
       rewrite HV₃ in Habc.
       apply eq_vec_const_mul_0 in Habc.
       destruct Habc as [Habc| Habc].
        exfalso.
        apply Rmult_eq_compat_r with (r := ∥(V₁ × V₂)∥) in Habc.
        unfold Rdiv in Habc.
        rewrite Rmult_assoc in Habc.
        rewrite Rinv_l in Habc; [ | easy ].
        rewrite Rmult_1_r, Rmult_0_l in Habc.
        now apply vec_norm_eq_0 in Habc.

        now apply vec_norm_eq_0 in Habc.

       assert (Hc: (c ≠ 0)%R).
        intros Hc; subst c.
        rewrite vec_const_mul_0_l in Habc.
        now rewrite vec_add_0_r in Habc.

        exfalso.
        remember (∥V₁∥ / ∥(V₁ × V₂)∥)%R as k eqn:Hk.
        rewrite HV₃ in Habc.
        unfold vec_cross_mul in Habc.
        destruct V₁ as (x₁, y₁, z₁).
        destruct V₂ as (x₂, y₂, z₂).
        simpl in Habc.
        rewrite <- Hv in Habc.
        simpl in Habc.
        injection Habc; clear Habc; intros Hz Hy Hx.
        simpl in Hv.
        remember (∥(P x₁ y₁ z₁ × P x₂ y₂ z₂)∥) as u eqn:Hu.
        apply Rmult_eq_compat_r with (r := u) in Hk.
        unfold Rdiv in Hk.
        rewrite Rmult_assoc in Hk.
        rewrite Rinv_l in Hk; [ | easy ].
        rewrite Rmult_1_r in Hk.
        simpl in Hk.
        assert (Hkz : (k ≠ 0)%R).
         intros H; subst k.
         rewrite Rmult_0_l in Hk; symmetry in Hk.
         apply sqrt_eq_0 in Hk; [ | apply nonneg_sqr_vec_norm ].
         apply sqr_vec_norm_eq_0 in Hk.
         destruct Hk as (Hk₁ & Hk₂ & Hk₃); subst x₁ y₁ z₁.
         now apply Hv₁.

rename Hk into Hkbidon.
         destruct (Req_dec a 0) as [Ha| Ha].
          subst a.
          rewrite Rmult_0_l, Rplus_0_l in Hx, Hy, Hz.
          do 3 rewrite Rmult_0_l, Rplus_0_l in Hv.
          destruct (Req_dec b 0) as [Hb| Hb].
           subst b; rewrite <- Hv in H₁.
           do 3 rewrite Rmult_0_l in H₁.
           now exfalso; apply H₁.

           destruct (Req_dec x₁ 0) as [Hx₁| Hx₁].
            subst x₁.
            rewrite Rmult_0_l, Rminus_0_r in Hy.
            rewrite Rmult_0_l, Rminus_0_l in Hz.
            destruct (Req_dec y₁ 0) as [Hy₁| Hy₁].
             subst y₁.
             rewrite Rmult_0_l, Rminus_0_l in Hx.
             rewrite Rmult_0_l, Ropp_0, Rmult_0_r, Rmult_0_r in Hz.
             rewrite Rplus_0_r in Hz.
             apply Rmult_integral in Hz.
             destruct Hz as [Hz| Hz]; [ easy | subst z₂ ].
             rewrite Rmult_0_r in Hv.
             rewrite <- Ropp_mult_distr_r in Hx.
             rewrite <- Ropp_mult_distr_r in Hx.
             rewrite fold_Rminus in Hx.
             apply Rminus_diag_uniq in Hx.
             apply Rmult_eq_compat_r with (r := y₂) in Hx.
             apply Rmult_eq_compat_r with (r := x₂) in Hy.
             rewrite Rmult_0_l in Hy.
             rewrite Rmult_plus_distr_r in Hy.
             rewrite Rmult_shuffle0 in Hy.
             rewrite Hx in Hy.
             do 6 rewrite Rmult_assoc in Hy.
             rewrite <- Rmult_plus_distr_l in Hy.
             apply Rmult_integral in Hy.
             destruct Hy as [Hy| Hy]; [ easy | ].
             rewrite <- Rmult_plus_distr_l in Hy.
             apply Rmult_integral in Hy.
             destruct Hy as [Hy| Hy]; [ easy | ].
             rewrite <- Rmult_plus_distr_l in Hy.
             apply Rmult_integral in Hy.
             destruct Hy as [| Hy]; [ now subst z₁; exfalso; apply Hv₁ | ].
             fold (Rsqr x₂) in Hy.
             fold (Rsqr y₂) in Hy.
             apply Rplus_sqr_eq_0 in Hy.
             destruct Hy; subst x₂ y₂.
             now exfalso; apply Hv₂.

             destruct (Req_dec z₁ 0) as [Hz₁| Hz₁].
              subst z₁.
              rewrite Rmult_0_l, Rminus_0_r in Hx.
              rewrite <- Ropp_mult_distr_r in Hz.
              rewrite <- Ropp_mult_distr_r in Hz.
              rewrite fold_Rminus in Hz.
              apply Rminus_diag_uniq in Hz.
              apply Rmult_eq_compat_r with (r := x₂) in Hz.
              apply Rmult_eq_compat_r with (r := z₂) in Hx.
              rewrite Rmult_0_l in Hx.
              rewrite Rmult_plus_distr_r in Hx.
              rewrite Rmult_shuffle0 in Hz.
              rewrite Hz in Hx.
              do 6 rewrite Rmult_assoc in Hx.
              rewrite <- Rmult_plus_distr_l in Hx.
              apply Rmult_integral in Hx.
              destruct Hx as [Hx| Hx]; [ easy | ].
              rewrite <- Rmult_plus_distr_l in Hx.
              apply Rmult_integral in Hx.
              destruct Hx as [Hx| Hx]; [ easy | ].
              rewrite <- Rmult_plus_distr_l in Hx.
              apply Rmult_integral in Hx.
              destruct Hx as [| Hx]; [ easy | ].
              fold (Rsqr x₂) in Hx.
              fold (Rsqr z₂) in Hx.
              apply Rplus_sqr_eq_0 in Hx.
              destruct Hx; subst x₂ z₂.
              subst u; simpl in HVV.
              setoid_rewrite Rmult_0_r in HVV.
              setoid_rewrite Rmult_0_l in HVV.
              rewrite Rminus_0_r in HVV.
              rewrite Rsqr_0 in HVV.
              do 2 rewrite Rplus_0_r in HVV.
              rewrite sqrt_0 in HVV.
              now exfalso; apply HVV.

              destruct (Req_dec y₂ 0) as [Hy₂| Hy₂].
               subst y₂.
               rewrite Rmult_0_r, Rplus_0_l in Hy.
               apply Rmult_integral in Hy.
               destruct Hy as [| Hy]; [ easy | ].
               apply Rmult_integral in Hy.
                destruct Hy as [Hy| Hy]; [ easy | ].
                apply Rmult_integral in Hy.
                destruct Hy; [ easy | subst x₂ ].
                rewrite Rmult_0_r, Ropp_0 in Hz.
                do 2 rewrite Rmult_0_r in Hz.
                rewrite Rplus_0_r in Hz.
                apply Rmult_integral in Hz.
                destruct Hz; [ easy | subst z₂ ].
                now exfalso; apply Hv₂.

              destruct (Req_dec x₂ 0) as [Hx₂| Hx₂].
               subst x₂.
               rewrite Rmult_0_r, Rplus_0_l in Hx.
               apply Rmult_integral in Hx.
               destruct Hx as [Hx| Hx]; [ easy | ].
               apply Rmult_integral in Hx.
               destruct Hx as [Hx| Hx]; [ easy | ].
               destruct (Req_dec z₂ 0) as [Hz₂| Hz₂].
                subst z₂.
                rewrite Rmult_0_r, Rminus_0_l in Hx.
                apply RMicromega.Ropp_0 in Hx.
                apply Rmult_integral in Hx.
                now destruct Hx.

                rewrite Rmult_0_r, Ropp_0 in Hz.
                do 2 rewrite Rmult_0_r in Hz.
                rewrite Rplus_0_r in Hz.
                apply Rmult_integral in Hz.
                now destruct Hz.

               destruct (Req_dec z₂ 0) as [Hz₂| Hz₂].
                subst z₂.
                rewrite Rmult_0_r, Rplus_0_l in Hz.
                apply Rmult_integral in Hz.
                destruct Hz as [Hz| Hz]; [ easy | ].
                apply Rmult_integral in Hz.
                destruct Hz as [Hz| Hz]; [ easy | ].
                apply RMicromega.Ropp_0 in Hz.
                apply Rmult_integral in Hz.
                now destruct Hz.

                do 2 rewrite <- Ropp_mult_distr_r in Hz.
                rewrite fold_Rminus in Hz.
                apply Rminus_diag_uniq in Hz.
                apply Rmult_eq_compat_r with (r := y₂) in Hz.
                apply Rmult_eq_compat_r with (r := z₂) in Hy.
                rewrite Rmult_0_l in Hy.
                rewrite Rmult_plus_distr_r in Hy.
                rewrite Rmult_shuffle0 in Hz.
                rewrite Hz in Hy.
                do 6 rewrite Rmult_assoc in Hy.
                rewrite <- Rmult_plus_distr_l in Hy.
                apply Rmult_integral in Hy.
                destruct Hy as [Hy| Hy]; [ easy | ].
                rewrite <- Rmult_plus_distr_l in Hy.
                apply Rmult_integral in Hy.
                destruct Hy as [Hy| Hy]; [ easy | ].
                setoid_rewrite Rmult_comm in Hy.
                setoid_rewrite Rmult_assoc in Hy.
                rewrite <- Rmult_plus_distr_l in Hy.
                apply Rmult_integral in Hy.
                destruct Hy as [Hy| Hy]; [ easy | ].
                rewrite Rplus_comm in Hy.
                apply Rplus_opp_r_uniq in Hy.
                do 2 rewrite <- Rmult_assoc in Hz.
                symmetry in Hz.
                rewrite Rmult_shuffle0 in Hz.
                rewrite Rmult_comm, Rmult_assoc in Hz.
                rewrite Rmult_comm in Hy.
                rewrite Hy in Hz.
                replace (z₂ * z₁)%R with (z₁ * z₂)%R in Hz by lra.
                rewrite Ropp_mult_distr_l in Hz.
                do 3 rewrite <- Rmult_assoc in Hz.
                rewrite <- Ropp_mult_distr_r in Hz.
                apply Rmult_eq_reg_r in Hz; [ | easy ].
                apply Rmult_eq_compat_r with (r := x₂) in Hz.
                apply Rmult_eq_compat_r with (r := y₂) in Hx.
                rewrite Rmult_0_l in Hx.
                rewrite Rmult_plus_distr_r in Hx.
                symmetry in Hz; rewrite Rmult_shuffle0 in Hz.
                rewrite Hz in Hx.
                assert
                   (H :
                      (c * (k *
                       ((- x₂ * z₁) * x₂ + ((y₁ * z₂ - z₁ * y₂) * y₂))))%R
                      = 0%R)
                   by lra.
                 apply Rmult_integral in H.
                 destruct H as [H| H]; [ easy | ].
                 apply Rmult_integral in H.
                 destruct H as [H| H]; [ easy | ].
                 assert (H₂ : (y₁ * y₂ * z₂ = z₁ * (x₂² + y₂²))%R)
                   by (unfold Rsqr; lra).
                 clear H.
                 rewrite Hy in H₂.
                 rewrite Ropp_mult_distr_l in H₂.
                 rewrite Rmult_shuffle0 in H₂.
                 rewrite Rmult_comm in H₂.
                 apply Rmult_eq_reg_l in H₂; [ | easy ].
                 rewrite <- Ropp_mult_distr_l in H₂.
                 fold (Rsqr z₂) in H₂.
                 assert (H :(x₂² + y₂² + z₂² = 0)%R) by lra.
                 apply sqr_vec_norm_eq_0 in H.
                 now destruct H.

           idtac.
(*
           apply Rmult_eq_compat_r with (r := y₂) in Hx.
           apply Rmult_eq_compat_r with (r := x₂) in Hy.
           rewrite Rmult_0_l in Hx, Hy.
           rewrite Rmult_plus_distr_r in Hx, Hy.
           rewrite Rmult_shuffle0, Rplus_comm in Hy.
           apply Rplus_opp_r_uniq in Hy.
           rewrite Hy in Hx.
           rewrite Ropp_mult_distr_r in Hx.
           do 4 rewrite Rmult_assoc in Hx.
           rewrite <- Rmult_plus_distr_l in Hx.
           apply Rmult_integral in Hx.
           destruct Hx as [Hx| Hx]; [ easy | ].
           rewrite <- Rmult_plus_distr_l in Hx.
           apply Rmult_integral in Hx.
           destruct Hx as [Hx| Hx]; [ easy | ].
           unfold Rminus in Hx.
           do 2 rewrite Rmult_plus_distr_r in Hx.
           do 2 rewrite <- Ropp_mult_distr_r in Hx.
           do 2 rewrite <- Ropp_mult_distr_l in Hx.
           rewrite Ropp_involutive in Hx.
           rewrite <- Rplus_assoc, Rplus_comm in Hx.
           do 2 rewrite <- Rplus_assoc in Hx.
           do 2 rewrite Rmult_assoc in Hx.
           setoid_rewrite Ropp_mult_distr_r in Hx.
           rewrite <- Rmult_plus_distr_l in Hx.
           rewrite <- Ropp_plus_distr in Hx.
           rewrite <- Ropp_mult_distr_r in Hx.
           setoid_rewrite Rmult_shuffle0 in Hx.
           rewrite Rplus_assoc in Hx.
           rewrite <- Rmult_plus_distr_r in Hx.
           do 2 rewrite fold_Rsqr in Hx.
           apply Rplus_opp_r_uniq in Hx.
           rewrite Ropp_involutive in Hx.
           rewrite Rmult_comm in Hx.
           symmetry in Hx; rewrite Rplus_comm in Hx.
bbb.
*)
           clear Hv₁.
           destruct (Req_dec x₂ 0) as [Hx₂| Hx₂].
            subst x₂.
            rewrite Rmult_0_r, Rplus_0_l in Hx.
            rewrite Rmult_0_r, Rminus_0_l in Hy.
            rewrite Rmult_0_r, Rminus_0_r in Hz.
            apply Rmult_integral in Hx.
            destruct Hx as [| Hx]; [ easy | ].
            apply Rmult_integral in Hx.
            destruct Hx as [| Hx]; [ easy | ].
            destruct (Req_dec y₁ 0) as [Hy₁| Hy₁].
             subst y₁.
             rewrite Rmult_0_l, Rminus_0_l in Hx.
             apply RMicromega.Ropp_0 in Hx.
             apply Rmult_integral in Hx.
             destruct Hx as [Hx| Hx].
              subst z₁.
              destruct (Req_dec y₂ 0) as [Hy₂| Hy₂].
               subst y₂.
               rewrite Rmult_0_r, Rplus_0_l in Hy.
               do 3 rewrite Rmult_0_r in Hz.
               rewrite Rplus_0_r in Hz.
               apply Rmult_integral in Hz.
               destruct Hz as [| Hz]; [ easy | ].
               subst z₂.
               now exfalso; apply Hv₂.

               destruct (Req_dec z₂ 0) as [Hz₂| Hz₂].
                subst z₂.
                rewrite Rmult_0_r in Hy.
                rewrite Ropp_0 in Hy.
                do 2 rewrite Rmult_0_r in Hy.
                rewrite Rplus_0_r in Hy.
                apply Rmult_integral in Hy.
                now destruct Hy.

                do 2 rewrite <- Ropp_mult_distr_r in Hy.
                rewrite fold_Rminus in Hy.
                apply Rminus_diag_uniq in Hy.
                apply Rmult_eq_compat_r with (r := z₂) in Hy.
                apply Rmult_eq_compat_r with (r := y₂) in Hz.
                rewrite Rmult_0_l in Hz.
                rewrite Rmult_plus_distr_r in Hz.
                rewrite Rmult_shuffle0 in Hz.
                rewrite Hy in Hz.
                do 6 rewrite Rmult_assoc in Hz.
                rewrite <- Rmult_plus_distr_l in Hz.
                apply Rmult_integral in Hz.
                destruct Hz as [| Hz]; [ easy | ].
                rewrite <- Rmult_plus_distr_l in Hz.
                apply Rmult_integral in Hz.
                destruct Hz as [| Hz]; [ easy | ].
                rewrite <- Rmult_plus_distr_l in Hz.
                apply Rmult_integral in Hz.
                destruct Hz as [| Hz]; [ easy | ].
                do 2 rewrite fold_Rsqr in Hz.
                apply Rplus_sqr_eq_0 in Hz.
                destruct Hz; subst y₂ z₂.
                now exfalso; apply Hv₂.

              subst y₂.
              do 3 rewrite Rmult_0_r in Hz.
              rewrite Rplus_0_r in Hz.
              apply Rmult_integral in Hz.
              destruct Hz as [| Hz]; [ easy | ].
              subst z₂.
              now exfalso; apply Hv₂.

             destruct (Req_dec y₂ 0) as [Hy₂| Hy₂].
              subst y₂.
              do 3 rewrite Rmult_0_r in Hz.
              rewrite Rplus_0_r in Hz.
              apply Rmult_integral in Hz.
              destruct Hz as [| Hz]; [ easy | ].
              subst z₂.
              now exfalso; apply Hv₂.

              destruct (Req_dec z₂ 0) as [Hz₂| Hz₂].
               subst z₂.
               rewrite Rmult_0_r, Rplus_0_l in Hz.
               apply Rmult_integral in Hz.
               destruct Hz as [| Hz]; [ easy | ].
               apply Rmult_integral in Hz.
               destruct Hz as [| Hz]; [ easy | ].
               apply Rmult_integral in Hz.
               now destruct Hz.

               do 2 rewrite <- Ropp_mult_distr_r in Hy.
               apply Rminus_diag_uniq in Hy.
               apply Rmult_eq_compat_r with (r := z₂) in Hy.
               apply Rmult_eq_compat_r with (r := y₂) in Hz.
               rewrite Rmult_0_l in Hz.
               rewrite Rmult_plus_distr_r in Hz.
               rewrite Rmult_shuffle0 in Hz.
               rewrite Hy in Hz.
               do 6 rewrite Rmult_assoc in Hz.
               rewrite <- Rmult_plus_distr_l in Hz.
               apply Rmult_integral in Hz.
               destruct Hz as [| Hz]; [ easy | ].
               rewrite <- Rmult_plus_distr_l in Hz.
               apply Rmult_integral in Hz.
               destruct Hz as [| Hz]; [ easy | ].
               rewrite <- Rmult_plus_distr_l in Hz.
               apply Rmult_integral in Hz.
               destruct Hz as [| Hz]; [ easy | ].
               do 2 rewrite fold_Rsqr in Hz.
               apply Rplus_sqr_eq_0 in Hz.
               now destruct Hz.

            destruct (Req_dec y₁ 0) as [Hy₁| Hy₁].
             subst y₁.
             rewrite Rmult_0_l, Rminus_0_l in Hx.
             rewrite Rmult_0_l, Rminus_0_r in Hz.
             destruct (Req_dec y₂ 0) as [Hy₂| Hy₂].
              subst y₂.
              do 3 rewrite Rmult_0_r in Hz.
              rewrite Rplus_0_r in Hz.
              apply Rmult_integral in Hz.
              destruct Hz; [ easy | subst z₂ ].
              rewrite Rmult_0_r, Ropp_0 in Hx.
              do 2 rewrite Rmult_0_r in Hx.
              rewrite Rplus_0_r in Hx.
              apply Rmult_integral in Hx.
              now destruct Hx.
              destruct (Req_dec z₂ 0) as [Hz₂| Hz₂].
               subst z₂.
               rewrite Rmult_0_r, Rplus_0_l in Hz.
               apply Rmult_integral in Hz.
               destruct Hz as [| Hz]; [ easy | ].
               apply Rmult_integral in Hz.
               destruct Hz as [| Hz]; [ easy | ].
               apply Rmult_integral in Hz.
               now destruct Hz.

               destruct (Req_dec z₁ 0) as [Hz₁| Hz₁].
                subst z₁.
                rewrite Rmult_0_l, Ropp_0 in Hx.
                do 2 rewrite Rmult_0_r in Hx.
                rewrite Rplus_0_r in Hx.
                apply Rmult_integral in Hx.
                now destruct Hx.

                apply Rmult_eq_compat_r with (r := y₂) in Hx.
                apply Rmult_eq_compat_r with (r := x₂) in Hy.
                rewrite Rmult_0_l in Hx, Hy.
                rewrite Rmult_plus_distr_r in Hx, Hy.
                rewrite Rmult_shuffle0, Rplus_comm in Hy.
                apply Rplus_opp_r_uniq in Hy.
                rewrite Hy in Hx.
                rewrite Ropp_mult_distr_r in Hx.
                do 4 rewrite Rmult_assoc in Hx.
                rewrite <- Rmult_plus_distr_l in Hx.
                apply Rmult_integral in Hx.
                destruct Hx as [Hx| Hx]; [ easy | ].
                rewrite <- Rmult_plus_distr_l in Hx.
                apply Rmult_integral in Hx.
                destruct Hx as [Hx| Hx]; [ easy | ].
                unfold Rminus in Hx.
                rewrite Rmult_plus_distr_r in Hx.
                do 2 rewrite <- Ropp_mult_distr_r in Hx.
                do 2 rewrite <- Ropp_mult_distr_l in Hx.
                rewrite Ropp_involutive in Hx.
                rewrite Rplus_comm in Hx.
                rewrite <- Rplus_assoc in Hx.
                do 2 rewrite Rmult_assoc in Hx.
                setoid_rewrite Ropp_mult_distr_r in Hx.
                rewrite <- Rmult_plus_distr_l in Hx.
                rewrite <- Ropp_plus_distr in Hx.
                rewrite <- Ropp_mult_distr_r in Hx.
                rewrite Rmult_shuffle0 in Hx.
                do 2 rewrite fold_Rsqr in Hx.
                apply Rplus_opp_r_uniq in Hx.
                rewrite Ropp_involutive in Hx.
                rewrite Rmult_comm in Hx.
                symmetry in Hx; rewrite Rplus_comm in Hx.
                apply Rmult_eq_compat_r with (r := z₂) in Hy.
                apply Rmult_eq_compat_r with (r := (x₂ * y₂)%R) in Hz.
                rewrite Rmult_0_l in Hz.
                rewrite Rmult_plus_distr_r in Hz.
                rewrite Rmult_shuffle0 in Hz.
                do 2 rewrite <- Rmult_assoc in Hz.
                rewrite Hy in Hz.
                rewrite Ropp_mult_distr_r in Hz.
                do 7 rewrite Rmult_assoc in Hz.
                do 2 rewrite <- Rmult_plus_distr_l in Hz.
                apply Rmult_integral in Hz.
                destruct Hz as [| Hz]; [ easy | ].
                apply Rmult_integral in Hz.
                destruct Hz as [| Hz]; [ easy | ].
                ring_simplify in Hz.
                do 3 rewrite <- Rsqr_pow2 in Hz.
                rewrite Rplus_comm, <- Rplus_assoc in Hz.
                rewrite Rplus_comm, <- Rplus_assoc in Hz.
                do 2 rewrite <- Ropp_mult_distr_l in Hz.
                rewrite fold_Rminus in Hz.
                apply Rminus_diag_uniq in Hz.
                replace (x₁ * x₂)%R with (x₂ * x₁)%R in Hz by apply Rmult_comm.
                rewrite <- Rmult_plus_distr_l in Hz.
                rewrite Rplus_comm in Hz.
                rewrite  Rmult_assoc in Hz.
                unfold Rsqr in Hz at 3.
                symmetry in Hz.
                rewrite Rmult_assoc, Rmult_comm in Hz.
                do 2 rewrite Rmult_assoc in Hz.
                apply Rmult_eq_reg_l in Hz; [ | easy ].
                rewrite <- Rmult_assoc, Rmult_shuffle0 in Hz.
                rewrite Rmult_assoc in Hz.
                symmetry in Hz.
                move Hz before Hx.
bbb.

                 do 2 rewrite Rmult_assoc in Hx.
                 rewrite Ropp_mult_distr_l in Hx.
                 rewrite Rmult_comm in Hx.
                 do 3 rewrite <- Rmult_assoc in Hx.


bbb.

             rewrite <- Rmult_plus_distr_l in Hx.
             apply Rmult_integral in Hx.
             destruct Hx as [Hx| Hx].
              move Hx at top; subst k.
              rewrite Rmult_0_l in Hk.
              now apply Rabs_eq_0 in Hk.

              rewrite <- Rmult_plus_distr_l in Hx.
              apply Rmult_integral in Hx.
              destruct Hx as [| Hx]; [ easy | ].
              fold (Rsqr x₂) in Hx.
              fold (Rsqr z₂) in Hx.
              apply Rplus_sqr_eq_0 in Hx.
              destruct Hx; subst x₂ z₂.
              subst u; simpl in HVV.
              setoid_rewrite Rmult_0_r in HVV.
              setoid_rewrite Rmult_0_l in HVV.
              rewrite Rminus_0_r in HVV.
              rewrite Rsqr_0 in HVV.
              do 2 rewrite Rplus_0_r in HVV.
              rewrite sqrt_0 in HVV.
              now exfalso; apply HVV.
bbb.
              rewrite Rmult_0_r, Rminus_0_r in Hx.
bbb.
             remember (∥(P 0 0 z₁ × P x₂ y₂ 0)∥) as u eqn:Hu.
             apply Rmult_eq_compat_r with (r := u) in Hk.
             unfold Rdiv in Hk.
             rewrite Rmult_0_l, Rmult_assoc in Hk.
             rewrite Rinv_l in Hk; [ | easy ].
             rewrite Rmult_1_r in Hk.
             simpl in Hk.
             rewrite Rsqr_0 in Hk.
             do 2 rewrite Rplus_0_l in Hk.
             symmetry in Hk; apply sqrt_eq_0 in Hk; [ | apply Rle_0_sqr ].
             apply Rsqr_0_uniq in Hk.
             now subst z₁; exfalso; apply Hv₁.

             rewrite <- Rmult_plus_distr_l in Hy.
             apply Rmult_integral in Hy.
             destruct Hy as [| Hy]; [ now subst z₁; exfalso; apply Hv₁ | ].
             fold (Rsqr x₂) in Hy.
             fold (Rsqr y₂) in Hy.
             apply Rplus_sqr_eq_0 in Hy.
             destruct Hy; subst x₂ y₂.
             now exfalso; apply Hv₂.

bbb.
            destruct (Req_dec z₁ 0) as [Hz₁| Hz₁].
             now subst z₁; exfalso; apply Hv₁.

             destruct (Req_dec x₂ 0) as [Hx₂| Hx₂].
              subst x₂.
              do 3 rewrite Rmult_0_r in Hy.
              rewrite Rplus_0_r in Hy.
              apply Rmult_integral in Hy.
              destruct Hy as [Hy| Hy]; [ easy | subst y₂ ].
              now rewrite Rmult_0_r in Hv; symmetry in Hv.

              destruct (Req_dec y₂ 0) as [Hy₂| Hy₂].
               subst y₂.
               rewrite Rmult_0_r, Ropp_0 in Hx.
               do 2 rewrite Rmult_0_r in Hx.
               rewrite Rplus_0_r in Hx.
               apply Rmult_integral in Hx.
               now destruct Hx.

(*
               destruct (Rlt_dec 0 0) as [H₂| H₂].
                now apply Rlt_irrefl in H₂.

                destruct (Rgt_dec 0 0) as [H₃| H₃].
                 now apply Rgt_irrefl in H₃.

                 destruct (Rlt_dec z₁ 0) as [H₄| H₄].
                  destruct (Rlt_dec x₂ 0) as [H₅| H₅].
*)
               idtac.

bbb.
        symmetry in Habc.
Theorem vec_add_comm : ∀ U V, (U + V)%vec = (V + U)%vec.
Proof.
intros.
destruct U as (u₁, u₂, u₃).
destruct V as (v₁, v₂, v₃); simpl.
f_equal; lra.
Qed.
        rewrite vec_add_comm in Habc.
        apply vec_sub_move_r in Habc.
        unfold vec_sub in Habc.
        rewrite vec_add_0_l in Habc.
bbb.


      destruct V₁ as (x₁, y₁, z₁).
      destruct V₂ as (x₂, y₂, z₂).
      destruct V₃ as (x₃, y₃, z₃).
      simpl in Habc.
      injection Habc; clear Habc; intros Hz Hy Hx.
      move Hx after Hy; move Hz after Hy.

bbb.
     assert (∀ V, (M * V)%vec = V).
      intros V.
      enough (∀ V, ∃ a b c, V = (a ⁎ V₁ + b ⁎ V₂ + c ⁎ V₃)%vec).
       specialize (H V) as (a & b & c & HV).
       subst V.
       do 2 rewrite mat_vec_add_cross_distr.
       do 3 rewrite mat_vec_mul_const_distr.
       now rewrite Hp₁, Hp₂, Hp₃.

       clear V; intros V.
       exists (V · V₁), (V · V₂), (V · V₃).
       destruct V as (x, y, z).
       destruct V₁ as (x₁, y₁, z₁).
       destruct V₂ as (x₂, y₂, z₂).
       destruct V₃ as (x₃, y₃, z₃).
       simpl; f_equal.
bbb.
   rewrite <- Rmult_plus_distr_l.
   simpl.

   subst V₃; unfold vec_norm, vec_const_mul, "×"; simpl.
   destruct V₁ as (x₁, y₁, z₁).
   destruct V₂ as (x₂, y₂, z₂).
   f_equal.

  assert
    (∃ V'₂,
     mat_vec_mul M V'₂ = V'₂ ∧ ∥ V'₂ ∥ = ∥ V₁ ∥ ∧
     vec_dot_mul V₁ V'₂ = 0)%R.
   remember (√ (V₁ · V₁ * (V₁ · V₁ + V₂ · V₂))) as r eqn:Hr.
   remember (- (V₁ · V₂) / r)%R as a eqn:Ha.
   remember (V₁ · V₁ / r)%R as b eqn:Hb.
   exists (vec_add (vec_const_mul a V₁) (vec_const_mul b V₂)).
   split.
    unfold vec_add; simpl.
    unfold vec_const_mul; simpl.
    destruct V₁ as (x₁, y₁, z₁).
    destruct V₂ as (x₂, y₂, z₂); simpl.
    f_equal.
bbb.
*)

Theorem D_set_is_countable : ∀ r,
  ∃ f : ℕ → point, ∀ p : point,
  p ∈ D ∩ sphere_ray r → ∃ n : ℕ, f n = p.
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
eapply on_sphere_ray_after_rotation in Hsr₁; [ clear H | apply H ].
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

  pose proof rotation_fixpoint_on_sphere_ray r m Hmt as Hsr₂.
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
bbb.

     induction el₁ as [| e₁ el₁]; [ now apply Hnl | ].
     simpl in H.
     remember (norm_list el₁) as el eqn:Hel.
      symmetry in Hel.
      destruct el as [| e el].
       destruct el₁ as [| e₂ el₁].
        simpl in H.
        rewrite mat_mul_id_r in H.
        unfold mat_id in H.
        destruct e₁ as (t, d); destruct t, d; simpl in H.
         injection H; clear H; intros; lra.
         injection H; clear H; intros; lra.
         injection H; clear H; intros; lra.
         injection H; clear H; intros; lra.

        simpl in H.

SearchAbout mat_of_path.
bbb.
simpl.
remember (mat_of_path (path_of_nat nf)) as m eqn:Hm.
unfold rotation_fixpoint.
unfold rotation_unit_eigenvec.
simpl.
remember (√ ((a₂₃ m - a₃₂ m)² + (a₃₁ m - a₁₃ m)² + (a₁₂ m - a₂₁ m)²)) as r.
do 3 rewrite Rmult_1_l.

bbb.

exists (λ '(nf, no), fold_right rotate (fixpoint_of_nat nf) (path_of_nat no)).
intros p Hp.
destruct Hp as (el₁ & p₁ & (el & Hs) & Hnl & Hr).
remember (nat_of_path el₁) as nf₁ eqn:Hnf.
remember (nat_of_path (rev_path el)) as no₁ eqn:Hno.
(* it can be (no₁, nf₁) if neg_point(p₁) = neg_point(ev);
   otherwise... I don't know! *)
Print fixpoint_of_nat.
bbb.

Check matrix_fixpoints_ok.
SearchAbout is_rotation_matrix.
SearchAbout (nat * nat → point).
Check D_of_prod_nat.
bbb.

mat_of_path_is_rotation_matrix:
  ∀ el : list free_elem, is_rotation_matrix (mat_of_path el)

bbb.

remember (fixpoint_of_nat nf₁) as p₂ eqn:Hp₂.
remember (mat_of_path (path_of_nat nf₁)) as m eqn:Hm.
remember (P (a₂₃ m - a₃₂ m) (a₃₁ m - a₁₃ m) (a₁₂ m - a₂₁ m)) as ev eqn:Hev.
remember (neg_point ev) as b.
rename Heqb into Hb.
remember (neg_point p₁) as b₁ eqn:Hb₁.
destruct (Bool.bool_dec b b₁) as [Hbe| Hbne].
 subst b b₁.
 exists (nf₁, no₁); simpl.
 subst nf₁ no₁.
 rewrite path_of_nat_inv in Hm.
 unfold fixpoint_of_nat.
 do 2 rewrite path_of_nat_inv.
 apply rotate_rev_path in Hs.
 rewrite <- Hs; f_equal.
 move Hr at bottom.
 unfold fixpoint_of_path; rewrite <- Hm.
 unfold rotation_fixpoint.
 unfold vec_const_mul.
 remember (rotation_unit_eigenvec m) as v eqn:Hv.
 symmetry in Hv.
 destruct v as (x, y, z).
 do 3 rewrite Rmult_1_l.
 unfold rotation_unit_eigenvec in Hv.
 remember (vec_norm (P (a₂₃ m - a₃₂ m) (a₃₁ m - a₁₃ m) (a₁₂ m - a₂₁ m))) as r.
 injection Hv; clear Hv; intros Hz Hy Hx.
 move Hx after Hy; move Hz after Hy.
 destruct ev as (ex, ey, ez).
 injection Hev; clear Hev; intros Hez Hey Hex.
 move Hex after Hey; move Hez after Hey.
 rewrite <- Hex in Hx; rewrite <- Hey in Hy; rewrite <- Hez in Hz.
 subst x y z.
 rewrite <- Hex, <- Hey, <- Hez in Heqr.
Check matrix_fixpoints_ok.

bbb.

Theorem toto : ∀ el x y z,
  fixpoint_of_path el = P x y z
  → fixpoint_of_path (rev_path el) = P (-x) (-y) (-z).
Proof.
intros * Hel.
unfold fixpoint_of_path in Hel |-*.
unfold rotation_fixpoint in Hel |-*.
bbb.

clear -Hnl Hr.
revert p₁ Hr.
induction el₁ as [| e₁ el₁]; intros; [ now exfalso; apply Hnl | ].
simpl in Hr.
unfold fixpoint_of_path; simpl.
unfold not_empty_path_of_path; simpl.
remember (norm_list el₁) as el₂ eqn:Hel₂.
symmetry in Hel₂.
destruct el₂ as [| e₂ el₂].
 simpl.
 unfold mat_of_path; simpl.
 rewrite mat_mul_id_r.
 rewrite rotate_rotate_norm, Hel₂ in Hr.
 simpl in Hr.
 unfold rotate in Hr.
 destruct p₁ as (x, y, z).
 simpl in Hr.
 unfold rotation_fixpoint; simpl.
 do 3 rewrite Rmult_1_l.
 injection Hr; clear Hr; intros Hz Hy Hx.
 f_equal.
 destruct e₁ as (t, d); destruct t, d; simpl in *.

unfold fixpoint_of_path.
(* actually, there are two possible fixpoints p₁ and -p₁ *)


bbb.

Theorem glop : ∀ m₁ m₂ k,
  (k ≠ 0)%R
  → rotation_fixpoint m₁ k = rotation_fixpoint m₂ k
  → m₁ = m₂.
Proof.
intros * Hk Hm.
unfold rotation_fixpoint in Hm.
remember
 (√ ((a₃₂ m₁ - a₂₃ m₁)² + (a₁₃ m₁ - a₃₁ m₁)² + (a₂₁ m₁ - a₁₂ m₁)²)) as r₁.
remember
 (√ ((a₃₂ m₂ - a₂₃ m₂)² + (a₁₃ m₂ - a₃₁ m₂)² + (a₂₁ m₂ - a₁₂ m₂)²)) as r₂.
injection Hm; clear Hm; intros H2 H1 H3; move H2 after H1.
do 2 rewrite Rmult_div in H1, H2, H3.
unfold Rdiv in H1, H2, H3.
do 2 rewrite Rmult_assoc in H1, H2, H3.
apply Rmult_eq_reg_l in H1; [ | easy ].
apply Rmult_eq_reg_l in H2; [ | easy ].
apply Rmult_eq_reg_l in H3; [ | easy ].
enough (H : r₁ = r₂).
 move H at top; subst r₂.
 apply Rmult_eq_reg_l in H1.
 apply Rmult_eq_reg_l in H2.
 apply Rmult_eq_reg_l in H3.
bbb.

 remember (norm_list el) as el₂ eqn:Hel₂.
 symmetry in Hel₂.
 destruct el₂ as [| e₂ el₂].
  Focus 2.
  SearchAbout not_empty_path_of_path.
  rewrite not_empty_rev_path; [ | now intros H; rewrite Hel₂ in H ].
  f_equal.
  unfold not_empty_path_of_path.
  unfold map_empty_path_to_single.
  rewrite Hel₂ at 1.

bbb.

(* old proof of old D_is_countable *)
exists (λ n, exist _ (D_of_nat n) (D_of_nat_in_D n)).
unfold FinFun.Surjective.
intros (p, Hp).
destruct Hp as (el₁ & p₁ & (el & Hs) & Hnl & Hr).
fold (toto p p₁ el el₁ Hnl Hr Hs).
remember (nat_of_path el₁) as nf eqn:Hnf.
remember (nat_of_path (not_empty_path_of_path (rev_path el))) as no eqn:Hno.
remember (nat_of_prod_nat (nf, no)) as n eqn:Hn.
exists n.
apply EqdepFacts.eq_dep_eq_sig.
set (P := λ p : point, @setp point D p).
rename p into q.
set (p := D_of_nat n : point); simpl in p.
set (x := D_of_nat_in_D n : P p); simpl in x.
set (y := toto q p₁ el el₁ Hnl Hr Hs).
enough (H : p = q).
 subst q; unfold toto in y; fold y.
 enough (H : x = y) by (rewrite H; constructor).
Focus 2.
 subst p; rename q into p.
 unfold D_of_nat.
 unfold D_of_prod_nat.
 remember (prod_nat_of_nat n) as nfo eqn:Hnfo.
 destruct nfo as (nf', no').
 unfold D_of_nat_nat.
 unfold fixpoint_of_nat.
 unfold fixpoint_of_path.
 remember (not_empty_path_of_path (path_of_nat nf')) as el₂ eqn:Hel₂.
 remember (rotation_fixpoint (mat_of_path el₂) 1) as p₂ eqn:Hp₂.
 remember (not_empty_path_of_nat no') as el₃ eqn:Hel₃.
 generalize Hnfo; intros H.
 eapply D_of_nat_prop in H; try eassumption; [ | reflexivity ].
 destruct H as (Hso₂ & Hnel₂ & Hr₂).
 rewrite Hn in Hnfo.
 rewrite prod_nat_of_nat_inv in Hnfo.
 injection Hnfo; clear Hnfo; intros H1 H2.
 move H1 at top; move H2 at top.
 subst nf' no'.
 rewrite Hno in Hel₃.
 unfold not_empty_path_of_nat in Hel₃.
 rewrite path_of_nat_inv in Hel₃.
 rewrite Hnf in Hel₂.
 rewrite path_of_nat_inv in Hel₂.
 clear Hso₂.
 destruct el₁ as [| e₁ el₁]; [ now exfalso; apply Hnl | ].
 unfold not_empty_path_of_path in Hel₂.
 unfold map_empty_path_to_single in Hel₂.
 remember (norm_list (e₁ :: el₁)) as el₄ eqn:Hel₄.
 clear y.
 destruct el₄ as [| e el₄]; [ now exfalso; apply Hnl | clear Hnl ].
 subst el₂.
 rewrite rotate_rotate_norm, <- Hel₄ in Hr.
 move Hr at bottom.
 move Hr₂ at bottom.
 subst el₃.
(*
 rewrite rotate_rotate_norm in Hs.
 rewrite rotate_rotate_norm.
 rewrite norm_list_not_empty_path.
 rewrite <- rev_path_norm_list.
*)
 (* two fixpoints with the same path: should be equal... *)
 enough (H : p₁ = p₂).
  move H at top; subst p₂; clear Hr₂.
  unfold nat_of_path in Hno.
  remember (not_empty_path_of_path (rev_path el)) as el₆ eqn:Hel₆.
  symmetry in Hel₆.
  destruct el₆ as [| e₆ el₆].
   remember (rev_path el) as rel eqn:Hrel.
   symmetry in Hrel.
   destruct rel as [| re rel]; [ easy | ].
   unfold not_empty_path_of_path in Hel₆.
   simpl in Hel₆.
   remember (norm_list rel) as el₇ eqn:Hel₇.
   symmetry in Hel₇.
   destruct el₇ as [| e₇ el₇]; [ easy | ].
   now destruct (letter_opp_dec re e₇) as [H| H]; destruct el₇.

   remember (rev_path el) as rel eqn:Hrel.
   symmetry in Hrel.
   destruct rel as [| re rel].
    unfold not_empty_path_of_path in Hel₆.
    simpl in Hel₆.
    injection Hel₆; clear Hel₆; intros; subst e₆ el₆.
    simpl in Hno; subst no.
    apply rev_path_is_nil in Hrel; subst el.
    simpl in Hs; subst p; simpl.
    subst P; simpl in x.
    subst n.
    unfold D_of_nat in x.
    rewrite prod_nat_of_nat_inv in x.
    destruct x as (el & p₂ & Hso & Hnl & Hr₁).
    simpl in Hso.
    unfold D_of_nat_nat in Hso.
    remember fixpoint_of_nat as f; simpl in Hso; subst f.
    unfold fixpoint_of_nat in Hso.
    subst nf.
    rewrite path_of_nat_inv in Hso.
    unfold fixpoint_of_path in Hso.
    unfold not_empty_path_of_path in Hso.
    rewrite <- Hel₄ in Hso.
    unfold map_empty_path_to_single in Hso.
    rewrite <- Hp₂ in Hso.
bbb.

 apply rev_path_is_nil in Hel₆.
 subst el no.
 simpl in Hn.
 rewrite Nat.mul_1_r in Hn.
 do 2 rewrite Nat.add_0_r in Hn.
 subst n.
unfold D_of_nat in x.
unfold D_of_prod_nat in x.
unfold prod_nat_of_nat in x.
rewrite Nat.sqrt_square in x.
rewrite Nat.pow_2_r in x.
rewrite Nat.sub_diag in x.
rewrite Nat.sub_0_r in x.
unfold D_of_nat_nat in x.
remember fixpoint_of_nat as f; simpl in x; subst f.


bbb.

   rewrite not_empty_rev_path.
bbb.

 subst el₂.
subst P; simpl in x.
destruct x as (el₂ & p₃ & Hso & Hnl & Hr₁).
subst n.
unfold D_of_nat in Hso.
rewrite prod_nat_of_nat_inv in Hso.
simpl in Hso.
subst nf no.
simpl in Hso.
unfold D_of_nat_nat in Hso.
remember (S (nat_of_path_aux el₁ * 4 + nat_of_free_elem e₁)) as n eqn:Hn.
assert (H : not_empty_path_of_nat (nat_of_path el) = el₃).
 unfold not_empty_path_of_nat.
 now rewrite path_of_nat_inv.

 rewrite H in Hso; clear H.
 assert (H : n = nat_of_path (e₁ :: el₁)) by easy.
 rewrite H in Hso; clear H.
 unfold fixpoint_of_nat in Hso.
 rewrite path_of_nat_inv in Hso.
 unfold fixpoint_of_path in Hso.

bbb.

 destruct el as [| e₁ el].
  simpl in Hs; subst p.
  unfold not_empty_path_of_path in Hel₃; simpl in Hel₃.
  subst el₃; simpl.


bbb.

 unfold prod_nat_of_nat in Hnfo.
 remember Nat.pow as f.
 injection Hnfo; clear Hnfo; intros Hno' Hnf'; subst f.

bbb.
 subst x y; subst P.
 unfold D_of_nat_in_D.
 unfold prod_nat_of_nat.
 unfold D_of_nat_nat_in_D.
 set (i := (Nat.sqrt n - (n - Nat.sqrt n ^ 2))%nat).
 set (j := (n - Nat.sqrt n ^ 2)%nat).
 set (p₂ := fixpoint_of_nat i).
 set (el₂ := not_empty_path_of_nat j).
 set (el₃ := not_empty_path_of_path (path_of_nat i)).
bbb.

Require Import NPeano.
unfold D_of_nat_in_D; simpl.
rewrite Nat.mul_1_r.

unfold D_of_nat_nat_in_D; simpl.

enough (H : p = D_of_nat (nat_of_prod_nat (nf, no))).
bbb.

unfold is_countable, D; simpl.
exists fixpoint_of_nat.
intros p Hp.
unfold D in Hp; simpl in Hp.
destruct Hp as (el & p₁ & Hs & Hn & Hr).
bbb.
SearchAbout FinFun.Surjective.

(* using Cantor_gen, we could prove that ℝ ∖ a countable set contains at
   least one element; if D is countable, ℝ ∖ D countains at least one
   element *)

Theorem equidec_sphere_with_and_without_fixpoints :
  equidecomposable sphere sphere_but_fixpoints.
Proof.
intros.
assert (H : ∃ p₁, p₁ ∈ sphere ∖ D).
 unfold "∈", "∖".
 specialize D_set_is_countable as (f, Hdnc).
 specialize (sphere_set_not_countable f) as (p & Hps & Hp).
 exists p.
 split; [ easy | ].
 intros H; specialize (Hdnc p H) as (n, Hdnc).
 revert Hdnc; apply Hp.

 destruct H as (p₁ & Hp₁s & Hp₁nd).

bbb.

assert (∃ p₁, p₁ ∉ D).
bbb.
assert (∀ p₁, (∀ el p, ¬ (same_orbit p₁ p ∧ norm_list el ≠ [] ∧ fold_right rotate p el = p)) → p₁ ∉ D).
intros p₁ Hf.
apply Classical_Pred_Type.all_not_not_ex; intros el (p, Hp).
revert Hp; apply Hf.
simpl.

bbb.

assert (∃ p₁ θ, ∀ p n, p ∈ D → p ∉ rotate_set p₁ (INR n * θ) D).
bbb.

Theorem Banach_Tarski_paradox :
  equidecomposable sphere (xtransl 3 sphere ∪ xtransl 6 sphere)%S.
Proof.
transitivity sphere_but_fixpoints.
 apply equidec_sphere_with_and_without_fixpoints.

 etransitivity.
  apply Banach_Tarski_paradox_but_fixpoints.

  apply equidec_union.
   apply separated_spheres_without_fixpoints.

   apply separated_spheres.

   apply equidec_transl; symmetry.
   apply equidec_sphere_with_and_without_fixpoints.

   apply equidec_transl; symmetry.
   apply equidec_sphere_with_and_without_fixpoints.
Qed.

Check Banach_Tarski_paradox.
