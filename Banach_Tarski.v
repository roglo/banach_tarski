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
Require Import Countable QCountable RnCountable.

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

(*
Definition neg_point '(P x y z) :=
  if Rlt_dec x 0 then true
  else if Rgt_dec x 0 then false
  else if Rlt_dec y 0 then true
  else if Rgt_dec y 0 then false
  else if Rlt_dec z 0 then true
  else if Rgt_dec z 0 then false
  else true.

Definition select_fixpoint '(P x y z) :=
  if neg_point (P x y z) then P (-x) (-y) (-z)
  else P x y z.
*)

Definition mul_const_vec k '(P x y z) := P (k * x) (k * y) (k * z).

Definition vec_norm '(P x y z) := √ (x² + y² + z²).

Definition rotation_unit_eigenvec (m : matrix) :=
  let x := (a₃₂ m - a₂₃ m)%R in
  let y := (a₁₃ m - a₃₁ m)%R in
  let z := (a₂₁ m - a₁₂ m)%R in
  let r := vec_norm (P x y z) in
  P (x / r) (y / r) (z / r).

Definition rotation_fixpoint (m : matrix) k :=
  mul_const_vec k (rotation_unit_eigenvec m).

Definition mat_of_path el :=
  List.fold_right mat_mul mat_id (map mat_of_elem el).

Definition fixpoint_of_path el :=
  rotation_fixpoint (mat_of_path el) 1.

Definition fixpoint_of_nat n :=
  fixpoint_of_path (path_of_nat n).

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

Theorem matrix_fixpoints_ok : ∀ M V,
  is_rotation_matrix M
  → mat_vec_mul M V = V
  → cos_rot_angle M ≠ 1%R ∧ cos_rot_angle M ≠ -1%R
  → V = mul_const_vec (vec_norm V) (rotation_unit_eigenvec M) ∨
    V = mul_const_vec (- vec_norm V) (rotation_unit_eigenvec M).
Proof.
intros * Hrm Hm (Ha1, Ha2).
remember (rotation_unit_eigenvec M) as ev eqn:Hev.
symmetry in Hev.
destruct ev as (ex, ey, ez).
unfold rotation_unit_eigenvec in Hev.
injection Hev; clear Hev; intros; subst ex ey ez.
remember (a₃₂ M - a₂₃ M)%R as ex eqn:Hex.
remember (a₁₃ M - a₃₁ M)%R as ey eqn:Hey.
remember (a₂₁ M - a₁₂ M)%R as ez eqn:Hez.
fold (vec_norm (P ex ey ez)).
remember (P ex ey ez) as ev eqn:Hev.
remember (vec_norm ev) as re eqn:Hre.
move ey before ex; move ez before ey.
move ev before V.
unfold mul_const_vec.
do 3 rewrite <- Ropp_mult_distr_l.
remember (vec_norm V) as r eqn:Hr.
replace (r * (ex / re))%R with (ex * (r / re))%R by lra.
replace (r * (ey / re))%R with (ey * (r / re))%R by lra.
replace (r * (ez / re))%R with (ez * (r / re))%R by lra.
remember (r / re)%R as k eqn:Hk.
setoid_rewrite Rmult_comm.
unfold cos_rot_angle in Ha1, Ha2.
unfold mat_trace in Ha1, Ha2.
bbb.

Theorem rotate_vec_mul : ∀ el p,
  fold_right rotate p el
  = mat_vec_mul (fold_right mat_mul mat_id (map mat_of_elem el)) p.
Proof.
intros el p.
induction el as [| e]; [ rewrite mat_vec_mul_id; reflexivity | simpl ].
rewrite IHel, mat_vec_mul_assoc; reflexivity.
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

Theorem D_of_nat_prop : ∀ n nf no p p₁ el el₁,
  (nf, no) = prod_nat_of_nat n
  → el₁ = path_of_nat nf
  → p₁ = rotation_fixpoint (mat_of_path el₁) 1
  → el = path_of_nat no
  → p = fold_right rotate p₁ el
  → same_orbit p p₁ ∧ fold_right rotate p₁ el₁ = p₁.
Proof.
intros * Hnfo Hel₁ Hp₁ Hel Hp.
split.
 exists (rev_path el).
 symmetry in Hp; apply rotate_rev_path in Hp; apply Hp.

 apply matrix_fixpoint_ok in Hp₁.
  unfold mat_of_path in Hp₁.
  rewrite <- rotate_vec_mul in Hp₁;
  apply Hp₁.

  apply mat_of_path_is_rotation_matrix.
Qed.

(*
Theorem toto : ∀ (p p₁ : point) (el el₁ : list free_elem),
  norm_list el₁ ≠ []
  → fold_right rotate p₁ el₁ = p₁
  → fold_right rotate p el = p₁
  → p ∈ D.
Proof.
intros * Hnl Hr Hs.
refine
    (@ex_intro (list free_elem)
       (fun el0 : list free_elem =>
        @ex point
          (fun p₁0 : point =>
           and (same_orbit p p₁0)
             (and
                (not
                   (@eq (list free_elem) (norm_list el0)
                      (@Datatypes.nil free_elem)))
                (@eq point
                   (@fold_right point free_elem rotate p₁0 el0) p₁0)))) el₁
       (@ex_intro point
          (fun p₁0 : point =>
           and (same_orbit p p₁0)
             (and
                (not
                   (@eq (list free_elem) (norm_list el₁)
                      (@Datatypes.nil free_elem)))
                (@eq point (@fold_right point free_elem rotate p₁0 el₁) p₁0))) p₁
          (@conj (same_orbit p p₁)
             (and
                (not
                   (@eq (list free_elem) (norm_list el₁)
                      (@Datatypes.nil free_elem)))
                (@eq point (@fold_right point free_elem rotate p₁ el₁) p₁))
             (@ex_intro (list free_elem)
                (fun el0 : list free_elem =>
                 @eq point (@fold_right point free_elem rotate p el0) p₁) el Hs)
             (@conj
                (not
                   (@eq (list free_elem) (norm_list el₁)
                      (@Datatypes.nil free_elem)))
                (@eq point
                   (@fold_right point free_elem rotate p₁ el₁) p₁) Hnl Hr)))).
Defined.

Definition titi p p₁ el el₁ Hr Hnl Hs :=
    (@ex_intro (list free_elem)
       (fun el0 : list free_elem =>
        @ex point
          (fun p₁0 : point =>
           and (same_orbit p p₁0)
             (and
                (not
                   (@eq (list free_elem) (norm_list el0)
                      (@Datatypes.nil free_elem)))
                (@eq point (@fold_right point free_elem rotate p₁0 el0) p₁0))))
       el₁
       (@ex_intro point
          (fun p₁0 : point =>
           and (same_orbit p p₁0)
             (and
                (not
                   (@eq (list free_elem) (norm_list el₁)
                      (@Datatypes.nil free_elem)))
                (@eq point (@fold_right point free_elem rotate p₁0 el₁) p₁0)))
          p₁
          (@conj (same_orbit p p₁)
             (and
                (not
                   (@eq (list free_elem) (norm_list el₁)
                      (@Datatypes.nil free_elem)))
                (@eq point (@fold_right point free_elem rotate p₁ el₁) p₁))
             (@ex_intro (list free_elem)
                (fun el0 : list free_elem =>
                 @eq point (@fold_right point free_elem rotate p el0) p₁) el
                Hs)
             (@conj
                (not
                   (@eq (list free_elem) (norm_list el₁)
                      (@Datatypes.nil free_elem)))
                (@eq point (@fold_right point free_elem rotate p₁ el₁) p₁)
                Hnl Hr)))).
*)

Definition D_of_prod_nat '(nf, no) :=
  let p₁ := fixpoint_of_nat nf in
  let el := path_of_nat no in
  fold_right rotate p₁ el.

Definition D_of_nat n :=
  D_of_prod_nat (prod_nat_of_nat n).

Theorem D_of_nat_nat_in_D : ∀ nf no,
  norm_list (path_of_nat nf) ≠ []
  → D_of_prod_nat (nf, no) ∈ D.
Proof.
intros * Hnl; simpl.
remember (fixpoint_of_nat nf) as p₁ eqn:Hp₁.
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

Theorem D_of_prod_nat_in_D : ∀ nn,
  norm_list (path_of_nat (fst nn)) ≠ []
  → D_of_prod_nat nn ∈ D.
Proof.
intros (nf, no) Hnl.
now apply D_of_nat_nat_in_D.
Defined.

Theorem D_of_nat_in_D : ∀ n, 
  norm_list (path_of_nat (Nat.sqrt n - (n - Nat.sqrt n ^ 2))) ≠ []
  → D_of_nat n ∈ D.
Proof.
intros n Hnl.
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

Theorem surj_prop_prod_nat_surj_prop_nat : ∀ A P,
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

Theorem D_set_is_countable :
  ∃ f : ℕ → point, ∀ p : point, p ∈ D → ∃ n : ℕ, f n = p.
Proof.
apply surj_prop_prod_nat_surj_prop_nat.
exists (λ '(nf, no), fold_right rotate (fixpoint_of_nat nf) (path_of_nat no)).
intros p Hp.
destruct Hp as (el₁ & p₁ & (el & Hs) & Hnl & Hr).
remember (nat_of_path el₁) as nf₁ eqn:Hnf.
remember (nat_of_path (rev_path el)) as no₁ eqn:Hno.
remember (fixpoint_of_nat nf₁) as p₂ eqn:Hp₂.
remember (mat_of_path (path_of_nat nf₁)) as m eqn:Hm.
remember (P (a₃₂ m - a₂₃ m) (a₁₃ m - a₃₁ m) (a₂₁ m - a₁₂ m)) as ev eqn:Hev.
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
 unfold rotation_fixpoint; rewrite <- Hev.
 unfold select_fixpoint.
 rewrite Hev, <- Hev, Hbe.
 remember (neg_point p₁) as b eqn:Hb.
 symmetry in Hb; symmetry.
 destruct b.
  do 3 rewrite Rmult_1_l.
  do 3 rewrite <- Rsqr_neg.
  remember (√ ((a₃₂ m - a₂₃ m)² + (a₁₃ m - a₃₁ m)² + (a₂₁ m - a₁₂ m)²)) as r.
  destruct p₁ as (x₁, y₁, z₁).
  f_equal.

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
