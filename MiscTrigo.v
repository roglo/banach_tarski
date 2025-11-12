(* Banach-Tarski paradox. *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith ZArith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import TrigoWithoutPi.Core.
Require Import a.MiscReals.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.

Definition rngl_atan x :=
  if (x <? 0)%L then (- rngl_asin (rngl_abs x / √(1 + x²)))%A
  else rngl_asin (x / √(1 + x²)).

Arguments rngl_atan x%_L.

Definition rngl_atan' (x y : T) :=
  if (y =? 0)%L then
    match (x ?= 0)%L with
    | Eq => 0%A
    | Lt => (- π/₂)%A
    | Gt => π/₂
    end
  else rngl_atan (x / y).

Definition angle_of_sin_cos s c :=
  if (s <? 0)%L then
    if (c <? 0)%L then (- rngl_acos c)%A else rngl_asin s
  else
    if (c <? 0)%L then rngl_acos c else rngl_asin s.

Theorem angle_lt_sub_lt_add_l_1 :
  ∀ θ1 θ2 θ3 : angle T,
  angle_add_overflow θ2 θ3 = false
  → (θ1 - θ2 < θ3)%A
  → (θ1 < θ2 + θ3)%A.
Proof.
intros * H23 H123.
apply (angle_add_lt_mono_l θ2) in H123; [ | easy ].
rewrite angle_add_comm in H123.
now rewrite angle_sub_add in H123.
Qed.

Theorem rngl_atan_bound :
  rngl_characteristic T ≠ 1 →
  ∀ x, (- π/₂ < rngl_atan x ∨ rngl_atan x < π/₂)%A.
Proof.
destruct_ac.
intros Hc1.
specialize (rngl_1_neq_0 Hc1) as H10.
specialize (rngl_2_neq_0 Hos Hc1 Hor) as H20.
specialize (rngl_integral_or_inv_pdiv_eq_dec_order Hiv Hor) as Hio.
intros.
progress unfold rngl_atan.
remember (x <? 0)%L as xz eqn:Hxz.
symmetry in Hxz.
destruct xz. {
  left.
  apply rngl_ltb_lt in Hxz.
  apply angle_opp_lt_compat_if. {
    intros H.
    progress unfold rngl_asin in H.
    apply -> angle_sub_move_0_r in H.
    symmetry in H.
    progress unfold rngl_acos in H.
    destruct (rngl_leb_dec (∣ x ∣ / √(1 + x²))² 1) as [Hx1| Hx1]. 2: {
      apply eq_angle_eq in H.
      cbn in H.
      now injection H; clear H; intros.
    }
    injection H; clear H; intros H1 H2.
    progress unfold rngl_div in H2.
    rewrite Hiv in H2.
    apply (rngl_eq_mul_0_l Hos Hiq) in H2. {
      apply (eq_rngl_abs_0 Hop) in H2; subst x.
      now apply (rngl_lt_irrefl Hor) in Hxz.
    }
    apply (rngl_inv_neq_0 Hos Hiv).
    intros H.
    apply (eq_rl_sqrt_0 Hos) in H. 2: {
      apply (rngl_le_0_add Hos Hor).
      apply (rngl_0_le_1 Hos Hor).
      apply (rngl_squ_nonneg Hos Hor).
    }
    apply (rngl_eq_add_0 Hor) in H.
    now destruct H as (H, _).
    apply (rngl_0_le_1 Hos Hor).
    apply (rngl_squ_nonneg Hos Hor).
  }
  progress unfold rngl_asin.
  progress unfold rngl_acos.
  destruct (rngl_leb_dec (∣ x ∣ / √(1 + x²))² 1) as [Hx1| Hx1]. 2: {
    apply rngl_leb_nle in Hx1.
    exfalso; apply Hx1; clear Hx1.
    rewrite <- rngl_squ_1.
    apply (rngl_le_le_squ Hop Hor).
    apply (rngl_div_nonneg Hop Hiv Hor).
    apply (rngl_abs_nonneg Hop Hor).
    apply (rl_sqrt_pos Hos Hor).
    rewrite rngl_squ_1.
    apply (rngl_lt_0_add Hor).
    apply (rngl_0_lt_1 Hos Hc1 Hor).
    apply (rngl_squ_nonneg Hos Hor).
    apply (rngl_div_le_1 Hop Hiv Hor).
    rewrite rngl_squ_1.
    intros H.
    apply (eq_rl_sqrt_0 Hos) in H. 2: {
      apply (rngl_le_0_add Hos Hor).
      apply (rngl_0_le_1 Hos Hor).
      apply (rngl_squ_nonneg Hos Hor).
    }
    apply (rngl_eq_add_0 Hor) in H.
    now destruct H as (H, _).
    apply (rngl_0_le_1 Hos Hor).
    apply (rngl_squ_nonneg Hos Hor).
    rewrite rngl_squ_1.
    split; [ apply (rngl_abs_nonneg Hop Hor) | ].
    rewrite <- (rl_sqrt_squ Hop Hor).
    apply (rl_sqrt_le_rl_sqrt Hop Hiq Hor).
    apply (rngl_squ_nonneg Hos Hor).
    apply (rngl_le_add_l Hor).
    apply (rngl_0_le_1 Hos Hor).
  }
  progress unfold angle_sub.
  progress unfold angle_add.
  progress unfold angle_opp.
  progress unfold angle_ltb.
  cbn.
  do 2 rewrite (rngl_mul_0_l Hos).
  do 2 rewrite rngl_mul_1_l.
  rewrite rngl_add_0_r.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_0_l.
  rewrite (rngl_0_leb_1 Hos Hor).
  remember (0 ≤? _)%L as zx eqn:Hzx.
  symmetry in Hzx.
  apply rngl_leb_le in Hx1.
  destruct zx. {
    apply rngl_ltb_lt.
    apply (rl_sqrt_pos Hos Hor).
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_le_neq Hor).
    split; [ easy | ].
    intros H.
    rewrite <- rngl_squ_1 in H at 2.
    apply (eq_rngl_squ_rngl_abs Hop Hor Hii) in H.
    rewrite (rngl_abs_1 Hos Hor) in H.
    progress unfold rngl_abs in H.
    generalize Hxz; intros H1.
    apply (rngl_lt_le_incl Hor) in H1.
    apply rngl_leb_le in H1.
    rewrite H1 in H; clear H1.
    rewrite (rngl_div_opp_l Hop Hiv) in H.
    rewrite (rngl_opp_involutive Hop) in H.
    rewrite (rngl_leb_opp_l Hop Hor) in H.
    rewrite (rngl_opp_0 Hop) in H.
    remember (0 ≤? x / _)%L as zxs eqn:Hzxs.
    symmetry in Hzxs.
    destruct zxs. {
      apply rngl_nle_gt in Hxz.
      apply Hxz; clear Hxz.
      (* lemma *)
      rewrite <- (rngl_div_1_r Hiq) in H; [ | now left ].
      apply (rngl_div_div_mul_mul Hic Hiv) in H; [ | | easy ].
      do 2 rewrite rngl_mul_1_r in H.
      rewrite H.
      apply rl_sqrt_nonneg.
      apply (rngl_le_trans Hor _ 1).
      apply (rngl_0_le_1 Hos Hor).
      apply (rngl_le_add_r Hor).
      apply (rngl_squ_nonneg Hos Hor).
      intros H1.
      apply (eq_rl_sqrt_0 Hos) in H1. 2: {
        apply (rngl_le_0_add Hos Hor).
        apply (rngl_0_le_1 Hos Hor).
        apply (rngl_squ_nonneg Hos Hor).
      }
      apply (rngl_eq_add_0 Hor) in H1.
      now destruct H1 as (H1, _).
      now apply (rngl_0_le_1 Hos Hor).
      now apply (rngl_squ_nonneg Hos Hor).
    }
    rewrite <- (rngl_div_opp_l Hop Hiv) in H.
    rewrite <- (rngl_div_1_r Hiq) in H; [ | now left ].
    apply (rngl_div_div_mul_mul Hic Hiv) in H; [ | | easy ].
    do 2 rewrite rngl_mul_1_r in H.
    apply (f_equal rngl_squ) in H.
    rewrite (rngl_squ_opp Hop) in H.
    rewrite rngl_squ_sqrt in H.
    symmetry in H.
    apply (rngl_add_move_r Hop) in H.
    now rewrite (rngl_sub_diag Hos) in H.
    apply (rngl_le_trans Hor _ 1).
    apply (rngl_0_le_1 Hos Hor).
    apply (rngl_le_add_r Hor).
    apply (rngl_squ_nonneg Hos Hor).
    intros H1.
    apply (eq_rl_sqrt_0 Hos) in H1. 2: {
      apply (rngl_le_0_add Hos Hor).
      apply (rngl_0_le_1 Hos Hor).
      apply (rngl_squ_nonneg Hos Hor).
    }
    apply (rngl_eq_add_0 Hor) in H1.
    now destruct H1 as (H1, _).
    now apply (rngl_0_le_1 Hos Hor).
    now apply (rngl_squ_nonneg Hos Hor).
    rewrite rngl_mul_1_l.
    apply rngl_mul_1_r.
  }
  exfalso.
  apply Bool.not_true_iff_false in Hzx.
  apply Hzx; clear Hzx.
  apply rngl_leb_le.
  apply (rngl_div_nonneg Hop Hiv Hor).
  apply (rngl_abs_nonneg Hop Hor).
  apply (rl_sqrt_pos Hos Hor).
  apply (rngl_lt_le_trans Hor _ 1).
  apply (rngl_0_lt_1 Hos Hc1 Hor).
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hos Hor).
} {
  right.
  apply (rngl_ltb_ge_iff Hor) in Hxz.
  rewrite <- (rngl_abs_nonneg_eq Hop Hor x) at 1; [ | easy ].
  (* presque pareil que ci-dessus *)
  progress unfold rngl_asin.
  progress unfold rngl_acos.
  destruct (rngl_leb_dec (∣ x ∣ / √(1 + x²))² 1) as [Hx1| Hx1]. 2: {
    apply rngl_leb_nle in Hx1.
    exfalso; apply Hx1; clear Hx1.
    rewrite <- rngl_squ_1.
    apply (rngl_le_le_squ Hop Hor).
    apply (rngl_div_nonneg Hop Hiv Hor).
    apply (rngl_abs_nonneg Hop Hor).
    apply (rl_sqrt_pos Hos Hor).
    rewrite rngl_squ_1.
    apply (rngl_lt_0_add Hor).
    apply (rngl_0_lt_1 Hos Hc1 Hor).
    apply (rngl_squ_nonneg Hos Hor).
    apply (rngl_div_le_1 Hop Hiv Hor).
    rewrite rngl_squ_1.
    intros H.
    apply (eq_rl_sqrt_0 Hos) in H. 2: {
      apply (rngl_le_0_add Hos Hor).
      apply (rngl_0_le_1 Hos Hor).
      apply (rngl_squ_nonneg Hos Hor).
    }
    apply (rngl_eq_add_0 Hor) in H.
    now destruct H as (H, _).
    apply (rngl_0_le_1 Hos Hor).
    apply (rngl_squ_nonneg Hos Hor).
    rewrite rngl_squ_1.
    split; [ apply (rngl_abs_nonneg Hop Hor) | ].
    rewrite <- (rl_sqrt_squ Hop Hor).
    apply (rl_sqrt_le_rl_sqrt Hop Hiq Hor).
    apply (rngl_squ_nonneg Hos Hor).
    apply (rngl_le_add_l Hor).
    apply (rngl_0_le_1 Hos Hor).
  }
  progress unfold angle_sub.
  progress unfold angle_add.
  progress unfold angle_opp.
  progress unfold angle_ltb.
  cbn.
  apply rngl_leb_le in Hx1.
  do 2 rewrite (rngl_mul_0_l Hos).
  do 2 rewrite rngl_mul_1_l.
  rewrite rngl_add_0_r.
  rewrite (rngl_sub_opp_r Hop).
  rewrite rngl_add_0_l.
  rewrite (rngl_0_leb_1 Hos Hor).
  remember (0 ≤? _)%L as zx eqn:Hzx.
  symmetry in Hzx.
  destruct zx. {
    apply rngl_ltb_lt.
    apply (rl_sqrt_pos Hos Hor).
    apply (rngl_lt_0_sub Hop Hor).
    apply (rngl_le_neq Hor).
    split; [ easy | ].
    intros H.
    rewrite <- rngl_squ_1 in H at 2.
    apply (eq_rngl_squ_rngl_abs Hop Hor Hii) in H.
    rewrite (rngl_abs_1 Hos Hor) in H.
    progress unfold rngl_abs in H.
    remember (x ≤? 0)%L as xz eqn:Hxz'.
    symmetry in Hxz'.
    destruct xz. {
      apply rngl_leb_le in Hxz'.
      apply (rngl_le_antisymm Hor) in Hxz; [ | easy ].
      clear Hxz'; subst x.
      rewrite (rngl_opp_0 Hop) in H.
      rewrite (rngl_squ_0 Hos) in H.
      rewrite rngl_add_0_r in H.
      rewrite (rl_sqrt_1 Hop Hiq Hor) in H.
      rewrite (rngl_div_1_r Hiq) in H; [ | now left ].
      rewrite (rngl_leb_refl Hor) in H.
      rewrite (rngl_opp_0 Hop) in H.
      now symmetry in H.
    }
    apply (rngl_leb_gt_iff Hor) in Hxz'.
    remember (x / _ ≤? 0)%L as zxs eqn:Hzxs.
    symmetry in Hzxs.
    destruct zxs. {
      apply rngl_leb_le in Hzxs.
      apply rngl_nlt_ge in Hzxs.
      apply Hzxs; clear Hzxs.
      apply (rngl_div_pos Hop Hiv Hor); [ easy | ].
      apply (rl_sqrt_pos Hos Hor).
      apply (rngl_lt_trans Hor _ 1).
      apply (rngl_0_lt_1 Hos Hc1 Hor).
      apply (rngl_lt_add_r Hos Hor).
      apply (rngl_le_neq Hor).
      split; [ apply (rngl_squ_nonneg Hos Hor) | ].
      intros H1; symmetry in H1.
      apply (eq_rngl_squ_0 Hos Hio) in H1; subst x.
      now apply (rngl_lt_irrefl Hor) in Hxz'.
    }
    rewrite <- (rngl_div_1_r Hiq) in H; [ | now left ].
    apply (rngl_div_div_mul_mul Hic Hiv) in H; [ | | easy ].
    do 2 rewrite rngl_mul_1_r in H.
    apply (f_equal rngl_squ) in H.
    rewrite rngl_squ_sqrt in H.
    symmetry in H.
    apply (rngl_add_move_r Hop) in H.
    now rewrite (rngl_sub_diag Hos) in H.
    apply (rngl_le_trans Hor _ 1).
    apply (rngl_0_le_1 Hos Hor).
    apply (rngl_le_add_r Hor).
    apply (rngl_squ_nonneg Hos Hor).
    intros H1.
    apply (eq_rl_sqrt_0 Hos) in H1. 2: {
      apply (rngl_le_0_add Hos Hor).
      apply (rngl_0_le_1 Hos Hor).
      apply (rngl_squ_nonneg Hos Hor).
    }
    apply (rngl_eq_add_0 Hor) in H1.
    now destruct H1 as (H1, _).
    now apply (rngl_0_le_1 Hos Hor).
    now apply (rngl_squ_nonneg Hos Hor).
    rewrite rngl_mul_1_l.
    apply rngl_mul_1_r.
  }
  exfalso.
  apply Bool.not_true_iff_false in Hzx.
  apply Hzx; clear Hzx.
  apply rngl_leb_le.
  apply (rngl_div_nonneg Hop Hiv Hor).
  apply (rngl_abs_nonneg Hop Hor).
  apply (rl_sqrt_pos Hos Hor).
  apply (rngl_lt_le_trans Hor _ 1).
  apply (rngl_0_lt_1 Hos Hc1 Hor).
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hos Hor).
}
Qed.

Theorem rngl_acos_opp :
  ∀ a,
  (-1 ≤ a ≤ 1)%L
  → rngl_acos (-a) = (π - rngl_acos a)%A.
Proof.
destruct_ac.
intros * Ha.
progress unfold rngl_acos.
remember (rngl_leb_dec _ _) as oa1 eqn:Hoa1.
remember (rngl_leb_dec _ _) as a1 eqn:Ha1 in |-*.
symmetry in Hoa1, Ha1.
destruct oa1 as [Hox1| Hox1]. {
  destruct a1 as [Hx1| Hx1]. {
    apply eq_angle_eq; cbn.
    rewrite (rngl_squ_opp Hop).
    clear Hox1 Hoa1 Ha1.
    do 2 rewrite (rngl_mul_0_l Hos).
    rewrite (rngl_sub_0_r Hos).
    rewrite rngl_add_0_l.
    do 2 rewrite (rngl_mul_opp_l Hop).
    do 2 rewrite rngl_mul_1_l.
    now rewrite (rngl_opp_involutive Hop).
  }
  exfalso; clear Hoa1 Ha1.
  rewrite (rngl_squ_opp Hop) in Hox1; try easy.
  congruence.
}
destruct a1 as [Hx1| Hx1]. {
  exfalso; clear Hoa1 Ha1.
  rewrite (rngl_squ_opp Hop) in Hox1.
  congruence.
}
exfalso; clear Hoa1 Ha1.
apply Bool.not_true_iff_false in Hx1.
apply Hx1, rngl_leb_le.
now apply (rngl_squ_le_1_iff Hop Hiq Hor).
Qed.

Theorem rngl_asin_opp :
  ∀ a,
  (-1 ≤ a ≤ 1)%L
  → rngl_asin (-a) = (- rngl_asin a)%A.
Proof.
intros * Ha.
progress unfold rngl_asin.
rewrite rngl_acos_opp; [ | easy ].
rewrite angle_sub_sub_distr.
rewrite angle_opp_sub_distr.
rewrite angle_add_comm.
rewrite <- angle_sub_opp_r.
rewrite angle_opp_sub_distr.
progress f_equal.
apply angle_sub_move_r.
symmetry.
apply angle_right_add_right.
Qed.

Theorem rngl_tan_opp : ∀ θ, rngl_tan (-θ) = (- rngl_tan θ)%L.
Proof.
destruct_ac.
intros.
progress unfold rngl_tan; cbn.
apply (rngl_div_opp_l Hop Hiv).
Qed.

Theorem rngl_lt_0_add_1_squ :
  rngl_has_opp_or_psub T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ a, (0 < 1 + a²)%L.
Proof.
intros Hos Hiq Hc1 Hor *.
apply (rngl_lt_le_trans Hor _ 1).
apply (rngl_0_lt_1 Hos Hc1 Hor).
apply (rngl_le_add_r Hor).
apply (rngl_squ_nonneg Hos Hor).
Qed.

Theorem rl_sqrt_add_1_squ_neq_0 :
   rngl_has_opp_or_psub T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_characteristic T ≠ 1 →
  rngl_is_ordered T = true →
  ∀ a, √(1 + a²) ≠ 0%L.
Proof.
intros Hos Hiq Hc1 Hor * H.
specialize (rngl_lt_0_add_1_squ Hos Hiq Hc1 Hor a) as Hz1a2.
apply (eq_rl_sqrt_0 Hos) in H.
rewrite H in Hz1a2.
now apply (rngl_lt_irrefl Hor) in Hz1a2.
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_div_sqrt_add_1_squ_interval : ∀ a, (-1 ≤ a / √(1 + a²) ≤ 1)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 (-1))%L.
  rewrite (H1 1)%L.
  rewrite (H1 (_ / _))%L.
  split; apply (rngl_le_refl Hor).
}
intros.
specialize (rngl_lt_0_add_1_squ Hos Hiq Hc1 Hor a) as Hz1a2.
specialize (rl_sqrt_add_1_squ_neq_0 Hos Hiq Hc1 Hor a) as Hs1a2.
apply (rngl_squ_le_1_iff Hop Hiq Hor).
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | now apply (rngl_lt_le_incl Hor) ].
apply (rngl_le_div_l Hop Hiv Hor); [ easy | ].
rewrite rngl_mul_1_l.
apply (rngl_le_add_l Hor).
apply (rngl_0_le_1 Hos Hor).
Qed.

Theorem rngl_tan_asin_inv : ∀ a, rngl_tan (rngl_asin (a / √(1 + a²))) = a.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hos Hc1) as H1.
  intros.
  rewrite (H1 a).
  apply H1.
}
intros.
specialize (rngl_lt_0_add_1_squ Hos Hiq Hc1 Hor a) as Hz1a2.
specialize (rl_sqrt_add_1_squ_neq_0 Hos Hiq Hc1 Hor a) as Hs1a2.
assert (H1a2 : (1 + a²)%L ≠ 0%L). {
  intros H.
  rewrite H in Hz1a2.
  now apply (rngl_lt_irrefl Hor) in Hz1a2.
}
assert (H1a1 : (-1 ≤ a / √(1 + a²) ≤ 1)%L). {
  apply (rngl_div_sqrt_add_1_squ_interval).
}
progress unfold rngl_tan.
rewrite rngl_sin_asin; [ | easy ].
rewrite rngl_cos_asin; [ | easy ].
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | now apply (rngl_lt_le_incl Hor) ].
rewrite <- (rngl_div_diag Hiq (1 + a²))%L at 2; [ | easy ].
rewrite <- (rngl_div_sub_distr_r Hop Hiv).
rewrite (rngl_add_sub Hos).
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | | easy ].
rewrite (rl_sqrt_1 Hop Hiq Hor).
rewrite (rngl_div_div_r Hon Hos Hiv); [ | | easy ].
rewrite (rngl_div_1_r Hiq); [ | now left ].
now apply (rngl_div_mul Hon Hiv).
apply (rngl_1_neq_0 Hc1).
apply (rngl_0_le_1 Hos Hor).
Qed.

Theorem rngl_tan_atan : ∀ a, rngl_tan (rngl_atan a) = a.
Proof.
destruct_ac.
intros.
progress unfold rngl_atan.
remember (a <? 0)%L as az eqn:Haz.
symmetry in Haz.
destruct az; [ | apply rngl_tan_asin_inv ].
apply rngl_ltb_lt in Haz.
apply (rngl_lt_le_incl Hor) in Haz.
rewrite rngl_tan_opp.
apply (rngl_opp_inj Hop).
rewrite (rngl_opp_involutive Hop).
rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
rewrite <- (rngl_squ_opp Hop).
apply rngl_tan_asin_inv.
Qed.

Theorem rngl_cos_atan : ∀ x, rngl_cos (rngl_atan x) = (1 / √ (1 + x²))%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros.
  rewrite (H1 (_ / _)%L).
  apply H1.
}
specialize (rngl_integral_or_inv_1_pdiv_eq_dec_order Hon Hiv Hor) as Hio.
intros.
specialize (rl_sqrt_add_1_squ_neq_0 Hos Hiq Hc1 Hor x) as Hs1a2.
assert (Hca : ∀ x, (0 < rngl_cos (rngl_atan x))%L). {
  intros y.
  apply rngl_lt_0_cos.
  specialize (rngl_atan_bound Hc1 y) as H1.
  now destruct H1; [ right | left ].
}
apply (rngl_mul_cancel_r Hi1) with (c := √(1 + x²)); [ easy | ].
rewrite (rngl_div_1_l Hiv).
rewrite (rngl_mul_inv_diag_l Hon Hiv); [ | easy ].
remember (rngl_atan x) as y eqn:Hy.
assert (Hx : x = rngl_tan y) by now subst y; rewrite rngl_tan_atan.
subst x.
specialize (Hca (rngl_tan y)); rewrite <- Hy in Hca.
unfold rngl_tan.
rewrite (rngl_squ_div Hic Hos Hiv). 2: {
  intros H; rewrite H in Hca.
  now apply (rngl_lt_irrefl Hor) in Hca.
}
rewrite <- (rngl_div_diag Hiq (rngl_cos² y)) at 1. 2: {
  intros H.
  apply (eq_rngl_squ_0 Hos Hio) in H.
  rewrite H in Hca.
  now apply (rngl_lt_irrefl Hor) in Hca.
}
rewrite <- (rngl_div_add_distr_r Hiv).
rewrite cos2_sin2_1.
rewrite (rl_sqrt_div Hon Hop Hiv Hor).
rewrite (rl_sqrt_1 Hop Hiq Hor).
rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | now apply (rngl_lt_le_incl Hor) ].
rewrite (rngl_div_1_l Hiv).
apply (rngl_mul_inv_diag_r Hiv).
intros H; rewrite H in Hca.
now apply (rngl_lt_irrefl Hor) in Hca.
apply (rngl_0_le_1 Hos Hor).
apply (rngl_le_neq Hor).
split; [ apply (rngl_squ_nonneg Hos Hor) | ].
intros H; symmetry in H.
apply (eq_rngl_squ_0 Hos Hio) in H.
rewrite H in Hca.
now apply (rngl_lt_irrefl Hor) in Hca.
Qed.

Theorem sin_atan : ∀ x, rngl_sin (rngl_atan x) = (x / √ (1 + x²))%L.
Proof.
destruct_ac.
intros.
progress unfold rngl_atan.
remember (x <? 0)%L as xz eqn:Hxz.
symmetry in Hxz.
destruct xz. {
  apply rngl_ltb_lt in Hxz.
  apply (rngl_lt_le_incl Hor) in Hxz.
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
  specialize (rngl_div_sqrt_add_1_squ_interval (-x))%L as H1.
  rewrite (rngl_squ_opp Hop) in H1.
  rewrite rngl_sin_opp.
  rewrite rngl_sin_asin; [ | easy ].
  rewrite (rngl_div_opp_l Hop Hiv).
  apply (rngl_opp_involutive Hop).
} {
  specialize (rngl_div_sqrt_add_1_squ_interval x) as H1.
  now apply rngl_sin_asin.
}
Qed.

Theorem rngl_sin_cos_asin : ∀ x,
  (-1 ≤ x ≤ 1)%L
  → rngl_sin (rngl_asin x) = x ∧ rngl_cos (rngl_asin x) = √ (1 - x²).
Proof.
intros * Hx.
split; [ now apply rngl_sin_asin | ].
now apply rngl_cos_asin.
Qed.

Theorem rngl_cos_sin_acos : ∀ x,
  (-1 ≤ x ≤ 1)%L
  → rngl_cos (rngl_acos x) = x ∧ rngl_sin (rngl_acos x) = √ (1 - x²).
Proof.
intros * Hx.
split; [ now apply rngl_cos_acos | ].
now apply rngl_sin_acos.
Qed.

Theorem rngl_1_add_squ_tan :
  ∀ θ,
  (rngl_cos θ ≠ 0%L)
  → (1 + (rngl_tan θ)² = 1 / rngl_cos² θ)%L.
Proof.
destruct_ac.
specialize (rngl_integral_or_inv_1_pdiv_eq_dec_order Hon Hiv Hor) as Hio.
intros * Hc.
progress unfold rngl_tan.
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite <- (rngl_div_diag Hiq (rngl_cos² θ)) at 1; [ | ].
rewrite <- (rngl_div_add_distr_r Hiv).
f_equal.
apply cos2_sin2_1.
intros H.
now apply (eq_rngl_squ_0 Hos Hio) in H.
Qed.

Definition rngl_sign' a :=
  match (a ?= 0)%L with
  | Eq => 0%L
  | Lt => (-1)%L
  | Gt => 1%L
  end.

Theorem rngl_div_abs_diag_l :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv T = true →
  rngl_is_ordered T = true →
  ∀ a, a ≠ 0%L → (rngl_abs a / a = rngl_sign' a)%L.
Proof.
intros Hon Hop Hiv Hor.
specialize (rngl_has_eq_dec_or_is_ordered_r Hor) as Heo.
specialize (rngl_has_inv_has_inv_or_pdiv Hiv) as Hiq.
intros * Haz.
progress unfold rngl_abs.
progress unfold rngl_sign'.
remember (a ≤? 0)%L as az eqn:Ha.
remember (a ?= 0)%L as az' eqn:Ha'.
symmetry in Ha, Ha'.
destruct az. {
  apply rngl_leb_le in Ha.
  apply (rngl_compare_le_iff Hor) in Ha.
  destruct az'; [ | | easy ].
  now apply (rngl_compare_eq_iff Heo) in Ha'.
  rewrite (rngl_div_opp_l Hop Hiv).
  progress f_equal.
  now apply (rngl_div_diag Hiq).
}
rewrite (rngl_div_diag Hiq); [ symmetry | easy ].
apply (rngl_leb_gt_iff Hor) in Ha.
destruct az'; [ | | easy ].
now apply (rngl_compare_eq_iff Heo) in Ha'.
apply (rngl_compare_lt_iff Hor) in Ha'.
now apply (rngl_lt_asymm Hor) in Ha'.
Qed.

Theorem rngl_cos_pos_cos_asin_div_tan_sqrt :
  ∀ θ,
  (0 < rngl_cos θ)%L
  → rngl_cos (rngl_asin (rngl_tan θ / √(1 + rngl_tan² θ))) = rngl_cos θ.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hc.
  rewrite (H1 (rngl_cos θ))%L.
  apply H1.
}
specialize (rngl_integral_or_inv_1_pdiv_eq_dec_order Hon Hiv Hor) as Hio.
specialize (rngl_1_neq_0 Hc1) as H10.
specialize (rngl_0_le_1 Hos Hor) as H01.
intros * Haz.
assert (Hcz : (rngl_cos θ ≠ 0)%L). {
  now intros H; rewrite H in Haz; apply (rngl_lt_irrefl Hor) in Haz.
}
assert (Hc2z : (rngl_cos² θ ≠ 0)%L). {
  intros H; apply Hcz.
  now apply (eq_rngl_squ_0 Hos Hio).
}
assert (Hz1t : (0 ≤ 1 + rngl_tan² θ)%L). {
  apply (rngl_le_trans Hor _ 1); [ easy | ].
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hos Hor).
}
assert (Hs1t : √(1 + rngl_tan² θ) ≠ 0%L). {
  intros H; apply (eq_rl_sqrt_0 Hos) in H; [ | easy ].
  apply (rngl_add_move_0_l Hop) in H.
  specialize (rngl_squ_nonneg Hos Hor (rngl_tan θ)) as H1.
  rewrite H in H1.
  apply rngl_nlt_ge in H1.
  apply H1, (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
cbn.
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_l Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_opp_involutive Hop).
rewrite rngl_sin_acos; [ | apply rngl_div_sqrt_add_1_squ_interval ].
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_1_add_squ_tan; [ | easy ].
rewrite (rngl_div_div_r Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_1_r Hiq); [ | now left ].
progress unfold rngl_tan at 1.
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite <- (cos2_sin2_1 θ) at 1.
rewrite (rngl_add_sub Hos).
rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_cos_pos_sin_asin_div_tan_sqrt :
  ∀ θ,
  (0 < rngl_cos θ)%L
  → rngl_sin (rngl_asin (rngl_tan θ / √(1 + rngl_tan² θ))) = rngl_sin θ.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hc.
  rewrite (H1 (rngl_sin θ))%L.
  apply H1.
}
specialize (rngl_integral_or_inv_1_pdiv_eq_dec_order Hon Hiv Hor) as Hio.
specialize (rngl_1_neq_0 Hc1) as H10.
specialize (rngl_0_le_1 Hos Hor) as H01.
intros * Haz.
assert (Hcz : (rngl_cos θ ≠ 0)%L). {
  now intros H; rewrite H in Haz; apply (rngl_lt_irrefl Hor) in Haz.
}
specialize (rngl_lt_le_incl Hor _ _ Haz) as Hcaz.
assert (Hc2z : (rngl_cos² θ ≠ 0)%L). {
  intros H; apply Hcz.
  now apply (eq_rngl_squ_0 Hos Hio).
}
assert (Hzc2 : (0 < rngl_cos² θ)%L). {
  apply (rngl_le_neq Hor).
  split; [ apply (rngl_squ_nonneg Hos Hor) | easy ].
}
assert (Haaz : rngl_abs (rngl_cos θ) ≠ 0%L). {
  now intros H; apply (eq_rngl_abs_0 Hop) in H.
}
cbn.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
rewrite rngl_mul_1_l.
rewrite rngl_cos_acos; [ | apply rngl_div_sqrt_add_1_squ_interval ].
rewrite rngl_1_add_squ_tan; [ | easy ].
progress unfold rngl_tan at 1.
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_squ Hop Hor).
rewrite (rl_sqrt_1 Hop Hiq Hor).
rewrite (rngl_div_div_r Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_1_r Hiq); [ | now left ].
rewrite (rngl_div_mul_mul_div Hic Hiv).
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite (rngl_abs_nonneg_eq Hop Hor); [ | easy ].
rewrite (rngl_div_diag Hiq); [ | easy ].
apply rngl_mul_1_r.
Qed.

Theorem rngl_cos_neg_cos_asin_div_tan_sqrt :
  ∀ θ,
  (rngl_cos θ < 0)%L
  → rngl_cos (rngl_asin (rngl_tan θ / √(1 + rngl_tan² θ))) = (- rngl_cos θ)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hc.
  rewrite (H1 (- rngl_cos θ))%L.
  apply H1.
}
specialize (rngl_integral_or_inv_1_pdiv_eq_dec_order Hon Hiv Hor) as Hio.
specialize (rngl_1_neq_0 Hc1) as H10.
specialize (rngl_0_le_1 Hos Hor) as H01.
intros * Haz.
assert (Hcz : (rngl_cos θ ≠ 0)%L). {
  now intros H; rewrite H in Haz; apply (rngl_lt_irrefl Hor) in Haz.
}
assert (Hc2z : (rngl_cos² θ ≠ 0)%L). {
  intros H; apply Hcz.
  now apply (eq_rngl_squ_0 Hos Hio).
}
assert (Hz1t : (0 ≤ 1 + rngl_tan² θ)%L). {
  apply (rngl_le_trans Hor _ 1); [ easy | ].
  apply (rngl_le_add_r Hor).
  apply (rngl_squ_nonneg Hos Hor).
}
assert (Hs1t : √(1 + rngl_tan² θ) ≠ 0%L). {
  intros H; apply (eq_rl_sqrt_0 Hos) in H; [ | easy ].
  apply (rngl_add_move_0_l Hop) in H.
  specialize (rngl_squ_nonneg Hos Hor (rngl_tan θ)) as H1.
  rewrite H in H1.
  apply rngl_nlt_ge in H1.
  apply H1, (rngl_opp_1_lt_0 Hon Hop Hor Hc1).
}
cbn.
rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_l Hop).
rewrite rngl_mul_1_l.
rewrite (rngl_opp_involutive Hop).
rewrite rngl_sin_acos; [ | apply rngl_div_sqrt_add_1_squ_interval ].
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite rngl_squ_sqrt; [ | easy ].
rewrite rngl_1_add_squ_tan; [ | easy ].
rewrite (rngl_div_div_r Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_1_r Hiq); [ | now left ].
progress unfold rngl_tan at 1.
rewrite (rngl_squ_div Hic Hos Hiv); [ | easy ].
rewrite (rngl_div_mul Hon Hiv); [ | easy ].
rewrite <- (cos2_sin2_1 θ) at 1.
rewrite (rngl_add_sub Hos).
rewrite (rl_sqrt_squ Hop Hor).
rewrite (rngl_abs_nonpos_eq Hop Hor); [ easy | ].
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_cos_neg_sin_asin_div_tan_sqrt :
  ∀ θ,
  (rngl_cos θ < 0)%L
  → rngl_sin (rngl_asin (rngl_tan θ / √(1 + rngl_tan² θ))) = (- rngl_sin θ)%L.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1 Hon Hos Hc1) as H1.
  intros * Hc.
  rewrite (H1 (- rngl_sin θ))%L.
  apply H1.
}
specialize (rngl_integral_or_inv_1_pdiv_eq_dec_order Hon Hiv Hor) as Hio.
specialize (rngl_1_neq_0 Hc1) as H10.
specialize (rngl_0_le_1 Hos Hor) as H01.
intros * Haz.
assert (Hcz : (rngl_cos θ ≠ 0)%L). {
  now intros H; rewrite H in Haz; apply (rngl_lt_irrefl Hor) in Haz.
}
specialize (rngl_lt_le_incl Hor _ _ Haz) as Hcaz.
assert (Hc2z : (rngl_cos² θ ≠ 0)%L). {
  intros H; apply Hcz.
  now apply (eq_rngl_squ_0 Hos Hio).
}
assert (Hzc2 : (0 < rngl_cos² θ)%L). {
  apply (rngl_le_neq Hor).
  split; [ apply (rngl_squ_nonneg Hos Hor) | easy ].
}
assert (Haaz : rngl_abs (rngl_cos θ) ≠ 0%L). {
  now intros H; apply (eq_rngl_abs_0 Hop) in H.
}
cbn.
rewrite (rngl_mul_0_l Hos).
rewrite rngl_add_0_r.
rewrite rngl_mul_1_l.
rewrite rngl_cos_acos; [ | apply rngl_div_sqrt_add_1_squ_interval ].
rewrite rngl_1_add_squ_tan; [ | easy ].
progress unfold rngl_tan at 1.
rewrite (rl_sqrt_div Hon Hop Hiv Hor); [ | easy | easy ].
rewrite (rl_sqrt_squ Hop Hor).
rewrite (rl_sqrt_1 Hop Hiq Hor).
rewrite (rngl_div_div_r Hon Hos Hiv); [ | easy | easy ].
rewrite (rngl_div_1_r Hiq); [ | now left ].
rewrite (rngl_div_mul_mul_div Hic Hiv).
rewrite <- (rngl_mul_div_assoc Hiv).
rewrite (rngl_abs_nonpos_eq Hop Hor); [ | easy ].
rewrite (rngl_div_opp_l Hop Hiv).
rewrite (rngl_div_diag Hiq); [ | easy ].
rewrite (rngl_mul_opp_r Hop).
now rewrite rngl_mul_1_r.
Qed.

Theorem rngl_cos_neg_atan_tan :
  ∀ θ,
  (rngl_cos θ < 0)%L
  → rngl_atan (rngl_tan θ) = (θ + π)%A.
Proof.
destruct_ac.
intros * Hc.
apply eq_angle_eq.
f_equal. {
  rewrite rngl_cos_add_straight_r.
  progress unfold rngl_atan.
  remember (rngl_tan θ <? 0)%L as ta eqn:Hta.
  symmetry in Hta.
  destruct ta; [ | now apply rngl_cos_neg_cos_asin_div_tan_sqrt ].
  apply rngl_ltb_lt in Hta.
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | now apply (rngl_lt_le_incl Hor) ].
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite rngl_asin_opp; [ | apply rngl_div_sqrt_add_1_squ_interval ].
  rewrite angle_opp_involutive.
  now apply rngl_cos_neg_cos_asin_div_tan_sqrt.
} {
  rewrite rngl_sin_add_straight_r.
  progress unfold rngl_atan.
  remember (rngl_tan θ <? 0)%L as ta eqn:Hta.
  symmetry in Hta.
  destruct ta; [ | now apply rngl_cos_neg_sin_asin_div_tan_sqrt ].
  apply rngl_ltb_lt in Hta.
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | now apply (rngl_lt_le_incl Hor) ].
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite rngl_asin_opp; [ | apply rngl_div_sqrt_add_1_squ_interval ].
  rewrite angle_opp_involutive.
  now apply rngl_cos_neg_sin_asin_div_tan_sqrt.
}
Qed.

Theorem rngl_cos_pos_atan_tan :
  ∀ θ,
  (0 < rngl_cos θ)%L
  → rngl_atan (rngl_tan θ) = θ.
Proof.
destruct_ac.
intros * Hc.
apply eq_angle_eq.
f_equal. {
  progress unfold rngl_atan.
  remember (rngl_tan θ <? 0)%L as ta eqn:Hta.
  symmetry in Hta.
  destruct ta; [ | now apply rngl_cos_pos_cos_asin_div_tan_sqrt ].
  apply rngl_ltb_lt in Hta.
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | now apply (rngl_lt_le_incl Hor) ].
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite rngl_asin_opp; [ | apply rngl_div_sqrt_add_1_squ_interval ].
  rewrite angle_opp_involutive.
  now apply rngl_cos_pos_cos_asin_div_tan_sqrt.
} {
  progress unfold rngl_atan.
  remember (rngl_tan θ <? 0)%L as ta eqn:Hta.
  symmetry in Hta.
  destruct ta; [ | now apply rngl_cos_pos_sin_asin_div_tan_sqrt ].
  apply rngl_ltb_lt in Hta.
  rewrite (rngl_abs_nonpos_eq Hop Hor); [ | now apply (rngl_lt_le_incl Hor) ].
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite rngl_asin_opp; [ | apply rngl_div_sqrt_add_1_squ_interval ].
  rewrite angle_opp_involutive.
  now apply rngl_cos_pos_sin_asin_div_tan_sqrt.
}
Qed.

Theorem rngl_cos_0_atan_tan :
  ∀ θ,
  rngl_cos θ = 0%L
  → rngl_atan (rngl_tan θ) =
      if (θ =? angle_right)%A then
        rngl_asin (1 / 0 / √(1 + (1 / 0)²))
      else
        (- rngl_asin (1 / 0 / √(1 + (1 / 0)²)))%A.
Proof.
destruct_ac.
destruct (Nat.eq_dec (rngl_characteristic T) 1) as [Hc1| Hc1]. {
  specialize (rngl_characteristic_1_angle_0 Hc1) as H1.
  intros.
  rewrite H1.
  apply H1.
}
intros * Hcz.
progress unfold rngl_atan.
progress unfold rngl_tan.
rewrite Hcz.
apply eq_rngl_cos_0 in Hcz.
destruct Hcz; subst. {
  cbn.
  rewrite angle_eqb_refl.
  remember (1 / 0 <? 0)%L as ozz eqn:Hozz.
  symmetry in Hozz.
  destruct ozz; [ | easy ].
  apply rngl_ltb_lt in Hozz.
  rewrite (rngl_abs_nonpos_eq Hop Hor).
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite rngl_asin_opp.
  apply angle_opp_involutive.
  apply rngl_div_sqrt_add_1_squ_interval.
  now apply (rngl_lt_le_incl Hor).
} {
  cbn.
  replace (- angle_right =? angle_right)%A with false.
  rewrite (rngl_div_opp_l Hop Hiv).
  rewrite (rngl_ltb_opp_l Hop Hor).
  rewrite (rngl_opp_0 Hop).
  rewrite (rngl_squ_opp Hop).
  remember (0 <? 1 / 0)%L as z1z eqn:Hz1z.
  symmetry in Hz1z.
  destruct z1z. {
    apply rngl_ltb_lt in Hz1z.
    rewrite (rngl_abs_nonpos_eq Hop Hor).
    rewrite (rngl_div_opp_l Hop Hiv).
    rewrite (rngl_div_opp_l Hop Hiv).
    now rewrite (rngl_opp_involutive Hop).
    apply (rngl_opp_nonpos_nonneg Hop Hor).
    now apply (rngl_lt_le_incl Hor).
  }
  rewrite (rngl_div_opp_l Hop Hiv).
  apply rngl_asin_opp.
  apply rngl_div_sqrt_add_1_squ_interval.
  symmetry.
  apply angle_eqb_neq.
  apply neq_angle_neq; cbn.
  intros H; injection H; clear H; intros H.
  rewrite <- (rngl_add_0_l (-1)) in H.
  rewrite (rngl_add_move_r Hop) in H.
  rewrite (rngl_sub_opp_r Hop) in H.
  symmetry in H.
  now apply (rngl_2_neq_0 Hos Hc1 Hor) in H.
}
Qed.

Theorem rngl_atan_tan : ∀ θ,
  rngl_atan (rngl_tan θ) =
    match (rngl_cos θ ?= 0)%L with
    | Eq =>
        if (θ =? angle_right)%A then
          rngl_asin (1 / 0 / √(1 + (1 / 0)²))
        else
          (- rngl_asin (1 / 0 / √(1 + (1 / 0)²)))%A
    | Lt => (θ + π)%A
    | Gt => θ
    end.
Proof.
destruct_ac.
intros.
remember (rngl_cos θ ?= 0)%L as cz eqn:Hcz.
symmetry in Hcz.
destruct cz. {
  apply (rngl_compare_eq_iff Heo) in Hcz.
  now apply rngl_cos_0_atan_tan.
} {
  apply (rngl_compare_lt_iff Hor) in Hcz.
  now apply rngl_cos_neg_atan_tan.
} {
  apply (rngl_compare_gt_iff Hor) in Hcz.
  now apply rngl_cos_pos_atan_tan.
}
Qed.

Theorem rngl_asin_sin :
  ∀ θ, rngl_asin (rngl_sin θ) = if (0 ≤? rngl_cos θ)%L then θ else (π - θ)%A.
Proof.
destruct_ac.
intros.
progress unfold rngl_asin.
progress unfold rngl_acos.
destruct (rngl_leb_dec (rngl_sin² θ) 1) as [Hs1| Hs1]. 2: {
  apply Bool.not_true_iff_false in Hs1.
  exfalso; apply Hs1; clear Hs1.
  apply rngl_leb_le.
  apply (rngl_squ_le_1_iff Hop Hiq Hor).
  apply rngl_sin_bound.
}
apply eq_angle_eq; cbn - [ angle_mul_nat ].
clear Hs1.
do 2 rewrite (rngl_mul_0_l Hos).
rewrite (rngl_sub_0_l Hop).
do 2 rewrite rngl_mul_1_l.
rewrite (rngl_opp_involutive Hop).
rewrite rngl_add_0_r.
rewrite <- (cos2_sin2_1 θ).
rewrite (rngl_add_sub Hos).
rewrite (rl_sqrt_squ Hop Hor).
remember (0 ≤? rngl_cos θ)%L as zc eqn:Hzc.
symmetry in Hzc.
destruct zc. {
  progress f_equal.
  apply (rngl_abs_nonneg_eq Hop Hor).
  now apply rngl_leb_le in Hzc.
}
apply (rngl_leb_gt_iff Hor) in Hzc.
rewrite rngl_cos_sub_straight_l.
rewrite rngl_sin_sub_straight_l.
progress f_equal.
apply (rngl_abs_nonpos_eq Hop Hor).
now apply (rngl_lt_le_incl Hor).
Qed.

Theorem rngl_asin_cos :
  ∀ θ,
  rngl_asin (rngl_cos θ) =
    if (0 ≤? rngl_sin θ)%L then (π/₂ - θ)%A else (π/₂ + θ)%A.
Proof.
destruct_ac.
intros.
rewrite <- rngl_sin_add_right_r.
rewrite rngl_asin_sin.
rewrite rngl_cos_add_right_r.
rewrite (rngl_leb_0_opp Hop Hor).
rewrite angle_sub_add_distr.
rewrite angle_sub_sub_swap.
rewrite angle_straight_sub_right.
remember (0 ≤? rngl_sin θ)%L as zs eqn:Hzs.
remember (rngl_sin θ ≤? 0)%L as sz eqn:Hsz.
symmetry in Hzs, Hsz.
rewrite angle_add_comm.
destruct sz. {
  destruct zs; [ | easy ].
  apply rngl_leb_le in Hzs, Hsz.
  progress unfold angle_sub.
  progress f_equal.
  symmetry.
  apply (rngl_le_antisymm Hor) in Hzs; [ | easy ].
  apply eq_rngl_sin_0 in Hzs.
  destruct Hzs; subst; [ apply angle_opp_0 | ].
  apply angle_opp_straight.
}
destruct zs; [ easy | ].
apply (rngl_leb_gt_iff Hor) in Hzs, Hsz.
now apply (rngl_lt_asymm Hor) in Hzs.
Qed.

Theorem rngl_acos_cos :
  ∀ θ, rngl_acos (rngl_cos θ) = (π/₂ - rngl_asin (rngl_cos θ))%A.
Proof.
intros.
progress unfold rngl_asin.
rewrite angle_sub_sub_distr.
rewrite angle_sub_diag; symmetry.
apply angle_add_0_l.
Qed.

Theorem angle_of_sin_cos_inv : ∀ θ,
  angle_of_sin_cos (rngl_sin θ) (rngl_cos θ) = θ.
Proof.
destruct_ac.
intros.
unfold angle_of_sin_cos.
rewrite rngl_acos_cos.
rewrite rngl_asin_cos.
rewrite rngl_asin_sin.
do 2 rewrite (rngl_ltb_neg_leb Hor).
destruct (0 ≤? rngl_cos θ)%L; cbn.
now destruct (0 ≤? rngl_sin θ)%L.
destruct (0 ≤? rngl_sin θ)%L; cbn. {
  rewrite angle_sub_sub_distr.
  rewrite angle_sub_diag.
  apply angle_add_0_l.
} {
  rewrite angle_sub_add_distr.
  rewrite angle_sub_diag.
  rewrite angle_sub_0_l.
  apply angle_opp_involutive.
}
Qed.

Theorem pre_sin_bound :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ s c, (s² + c² = 1 → -1 ≤ s ≤ 1)%L.
Proof.
intros Hon Hop Hiq Hor.
specialize (rngl_has_opp_has_opp_or_psub Hop) as Hos.
intros s c Hsc.
apply (rngl_squ_le_1_iff Hop Hiq Hor).
rewrite <- Hsc.
apply (rngl_le_add_r Hor).
apply (rngl_squ_nonneg Hos Hor).
Qed.

Theorem pre_cos_bound :
  rngl_has_1 T = true →
  rngl_has_opp T = true →
  rngl_has_inv_or_pdiv T = true →
  rngl_is_ordered T = true →
  ∀ s c, (s² + c² = 1 → -1 ≤ c ≤ 1)%L.
Proof.
intros Hon Hop Hiq Hor.
intros s c Hsc.
rewrite rngl_add_comm in Hsc.
now apply pre_sin_bound in Hsc.
Qed.

Theorem rngl_sin_angle_of_sin_cos : ∀ s c,
  (s² + c² = 1)%L
  → rngl_sin (angle_of_sin_cos s c) = s.
Proof.
destruct_ac.
intros * Hsc.
unfold angle_of_sin_cos.
destruct (rngl_ltb_dec s 0) as [Hs| Hs]; rewrite Hs. {
  destruct (rngl_ltb_dec c 0) as [Hc| Hc]; rewrite Hc. {
    rewrite rngl_sin_opp.
    rewrite rngl_sin_acos; [ | now apply (pre_cos_bound Hon Hop Hiq Hor s) ].
    rewrite <- Hsc.
    rewrite (rngl_add_sub Hos).
    rewrite (rl_sqrt_squ Hop Hor).
    rewrite (rngl_abs_nonpos_eq Hop Hor).
    apply (rngl_opp_involutive Hop).
    apply rngl_ltb_lt in Hs.
    now apply (rngl_lt_le_incl Hor).
  }
  apply rngl_sin_asin.
  now apply (pre_sin_bound Hon Hop Hiq Hor _ c).
}
apply (rngl_ltb_ge_iff Hor) in Hs.
destruct (rngl_ltb_dec c 0) as [Hc| Hc]; rewrite Hc. {
  rewrite rngl_sin_acos; [ | now apply pre_cos_bound in Hsc ].
  rewrite <- Hsc, (rngl_add_sub Hos).
  rewrite (rl_sqrt_squ Hop Hor).
  now apply (rngl_abs_nonneg_eq Hop Hor).
}
apply rngl_sin_asin.
now apply (pre_sin_bound Hon Hop Hiq Hor _ c).
Qed.

Theorem rngl_cos_angle_of_sin_cos : ∀ s c,
  (s² + c² = 1)%L
  → rngl_cos (angle_of_sin_cos s c) = c.
Proof.
destruct_ac.
intros * Hsc.
unfold angle_of_sin_cos.
destruct (rngl_ltb_dec s 0) as [Hs| Hs]; rewrite Hs. {
  destruct (rngl_ltb_dec c 0) as [Hc| Hc]; rewrite Hc. {
    rewrite rngl_cos_opp.
    apply rngl_cos_acos.
    now apply (pre_cos_bound Hon Hop Hiq Hor s).
  }
  apply (rngl_ltb_ge_iff Hor) in Hc.
  rewrite rngl_cos_asin.
  rewrite <- Hsc, rngl_add_comm.
  rewrite (rngl_add_sub Hos).
  rewrite (rl_sqrt_squ Hop Hor).
  now apply (rngl_abs_nonneg_eq Hop Hor).
  now apply (pre_sin_bound Hon Hop Hiq Hor _ c).
}
destruct (rngl_ltb_dec c 0) as [Hc| Hc]; rewrite Hc. {
  apply rngl_cos_acos.
  now apply pre_cos_bound in Hsc.
}
apply (rngl_ltb_ge_iff Hor) in Hc.
rewrite rngl_cos_asin.
rewrite <- Hsc, rngl_add_comm, (rngl_add_sub Hos).
rewrite (rl_sqrt_squ Hop Hor).
now apply (rngl_abs_nonneg_eq Hop Hor).
now apply (pre_sin_bound Hon Hop Hiq Hor _ c).
Qed.

End a.
