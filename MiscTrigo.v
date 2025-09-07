(* Banach-Tarski paradox. *)

Set Nested Proofs Allowed.
From Stdlib Require Import Utf8 Arith ZArith.

Require Import RingLike.Core.
Require Import RingLike.RealLike.
Require Import TrigoWithoutPi.Angle.
Require Import TrigoWithoutPi.TrigoWithoutPiExt.
Require Import TrigoWithoutPi.AngleDiv2.
Require Import TrigoWithoutPi.Angle_order.
Require Import MiscReals.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.
Context {rp : ring_like_prop T}.
Context {rl : real_like_prop T}.
Context {ac : angle_ctx T}.
Context {Hon : rngl_has_1 T = true}.
Context {Hos : rngl_has_opp_or_psub T = true}.
Context {Hiq : rngl_has_inv_or_pdiv T = true}.
Context {Hc1 : rngl_characteristic T ≠ 1}.
Context {Hor : rngl_is_ordered T = true}.

Definition π := angle_straight.

Definition acos := rngl_acos.
Definition asin x := (π /₂ - rngl_acos x)%A.

Arguments acos x%_L.
Arguments asin x%_L.

Definition atan x :=
  if (x <? 0)%L then (- asin (rngl_abs x / √(1 + x²)))%A
  else asin (x / √(1 + x²)).

Arguments atan x%_L.

Definition atan' (x y : T) :=
  if (y =? 0)%L then
    match (x ?= 0)%L with
    | Eq => 0%A
    | Lt => (- π /₂)%A
    | Gt => (π /₂)%A
    end
  else atan (x / y).

Check Rlt_dec.

Definition angle_of_sin_cos s c :=
  if Rlt_dec Hor s 0 then
    if Rlt_dec Hor c 0 then (- acos c)%A else asin s
  else
    if Rlt_dec Hor c 0 then acos c else asin s.

Theorem cos_atan : ∀ x, rngl_cos (atan x) = (1 / √ (1 + x²))%L.
Proof.
intros.
assert (Hs : (√ (1 + x²) ≠ 0)%L). {
  intros H.
  specialize (rngl_squ_nonneg Hon Hos Hiq Hor x) as Hs.
  apply (eq_rl_sqrt_0 Hon Hos) in H. {
    apply (rngl_eq_add_0 Hos Hor) in H.
    now destruct H as (H, _); apply (rngl_1_neq_0 Hon Hc1) in H.
    apply (rngl_0_le_1 Hon Hos Hiq Hor).
    apply (rngl_squ_nonneg Hon Hos Hiq Hor).
  }
  apply (rngl_le_0_add Hos Hor).
  apply (rngl_0_le_1 Hon Hos Hiq Hor).
  apply (rngl_squ_nonneg Hon Hos Hiq Hor).
}
assert (Hca : ∀ x, (0 < rngl_cos (atan x))%L). {
  intros y.
(**)
  apply rngl_lt_0_cos.
  progress unfold atan.
  progress unfold asin.
  remember (y <? 0)%L as yz eqn:Hyz.
  symmetry in Hyz.
  destruct yz. {
    progress unfold π.
    rewrite angle_straight_div_2.
    rewrite angle_opp_sub_distr.
Search (_ - _ < _)%A.
Theorem angle_lt_sub_lt_add_l_1 :
  ∀ θ1 θ2 θ3 : angle T,
  angle_add_overflow θ2 θ3 = false
  → (θ1 - θ2 < θ3)%A
  → (θ1 < θ2 + θ3)%A.
Proof.
intros * H23 H123.
...
apply (angle_add_lt_mono_l θ2) in H123; [ | easy ].
rewrite angle_add_comm in H123.
now rewrite angle_sub_add in H123.
Qed.

Theorem angle_lt_sub_lt_add_l_2 :
  ∀ θ1 θ2 θ3 : angle T,
  angle_add_overflow θ2 θ3 = false
  → (θ1 < θ2 + θ3)%A
  → (θ1 - θ2 < θ3)%A.
Proof.
intros * H23 H123.
apply (angle_add_lt_mono_l (-θ2)) in H123; [ | ].
do 2 rewrite angle_add_opp_l in H123.
rewrite angle_add_comm in H123.
now rewrite angle_add_sub in H123.
rewrite angle_add_comm.
...
apply TrigoWithoutPiExt.angle_add_not_overflow_move_add. 2: {
  rewrite angle_add_opp_l.
  rewrite angle_sub_diag.
  apply TrigoWithoutPiExt.angle_add_overflow_0_l.
}
...
Theorem angle_lt_sub_lt_add_l :
  ∀ a b c : angle T, (a - b < c)%A ↔ (a < b + c)%A.
...
    progress unfold rngl_acos.
    destruct (rngl_le_dec _ _ _) as [Hy1| Hy1]. {
      progress unfold angle_sub.
      progress unfold angle_add.
      cbn.
Search (_ < _)%A.
...
  specialize (atan_bound y) as (Hlta, Halt).
  apply cos_gt_0; [ lra | easy ].
...
atan_bound
     : ∀ x : R, (- PI / 2 < atan x < PI / 2)%R
}
apply Rmult_eq_reg_r with (r := √ (1 + x²)); [ | easy ].
rewrite <- Rinv_div, Rinv_l; [ | easy ].
remember (atan x) as y eqn:Hy.
assert (Hx : x = tan y) by now subst y; rewrite atan_right_inv.
subst x.
specialize (Hca (tan y)); rewrite <- Hy in Hca.
unfold tan.
rewrite Rsqr_div_depr; [ | lra ].
replace (cos y) with (√ (cos y)²) at 1 by (apply sqrt_Rsqr; lra).
rewrite <- sqrt_mult_alt; [ | apply Rle_0_sqr ].
rewrite Rmult_plus_distr_l, Rmult_1_r.
rewrite Rmult_div_r; [ | intros H; apply Rsqr_eq_0 in H; lra ].
rewrite Rplus_comm, sin2_cos2.
apply sqrt_1.
Qed.

Theorem sin_atan : ∀ x, sin (atan x) = x / √ (1 + x²).
Proof.
intros.
unfold Rdiv.
rewrite Rinv_div, <- cos_atan.
remember (atan x) as y eqn:Hy.
assert (Hx : x = tan y) by now subst y; rewrite atan_right_inv.
subst x; unfold tan.
rewrite <- Rmult_div.
unfold Rdiv; rewrite Rmult_assoc.
rewrite Rinv_r; [ lra | ].
intros H; rewrite Hy in H.
rewrite cos_atan in H.
unfold Rdiv in H.
apply Rmult_integral in H.
destruct H; [ lra | ].
apply Rinv_neq_0_compat in H; [ easy | ].
clear H; intros H.
apply sqrt_eq_0 in H. {
  enough (Ht : 0 ≤ (tan y)²) by lra.
  apply Rle_0_sqr.
}
replace 1 with (1 ^ 2) by lra.
rewrite <- Rsqr_pow2.
apply nonneg_plus_sqr.
Qed.

Theorem sin_cos_asin : ∀ x,
  -1 ≤ x ≤ 1
  → sin (asin x) = x ∧ cos (asin x) = √ (1 - x²).
Proof.
intros * Hx.
unfold asin.
unfold atan'.
destruct (Req_dec (√ (1 - x²)) 0) as [Hsx| Hsx]. {
  rewrite Hsx.
  unfold Rsign, Rsignp.
  destruct (Req_dec x 0) as [Hxz| Hxz]. {
    rewrite Hxz in Hsx.
    rewrite Rsqr_0, Rminus_0_r, sqrt_1 in Hsx; lra.
  }
  destruct (Rle_dec 0 x) as [Hxp| Hxn]. {
    rewrite Rmult_1_l.
    rewrite sin_PI2, cos_PI2.
    split; [ | easy ].
    symmetry.
    apply sqrt_diff_sqr_eq_0; [ lra | now rewrite Rsqr_1 ].
  }
  unfold IZR at 1 3; rewrite <- INR_IPR; simpl.
  rewrite <- Ropp_mult_distr_l, Rmult_1_l, Rdiv_opp_l.
  rewrite sin_neg, cos_neg.
  rewrite sin_PI2, cos_PI2.
  split; [ | easy ].
  rewrite <- Ropp_involutive.
  f_equal; symmetry.
  apply sqrt_diff_sqr_eq_0; [ lra | ].
  now rewrite Rsqr_1, <- Rsqr_neg.
}
assert (Hx' : -1 < x < 1). {
  apply Rabs_lt, Rnot_le_lt.
  intros Ha; apply Hsx; clear Hsx.
  apply Rsqr_inj; [ apply sqrt_pos | lra | ].
  rewrite Rsqr_0; unfold Rabs in Ha.
  destruct (Rcase_abs x) as [Hc| Hc]. {
    assert (x = -1) by lra; subst x.
    unfold IZR; rewrite <- INR_IPR; simpl.
    rewrite <- Rsqr_neg, Rsqr_1, Rminus_diag_eq; [ | easy ].
    now rewrite sqrt_0, Rsqr_0.
  }
  assert (x = 1) by lra.
  subst x.
  rewrite Rsqr_1, Rminus_diag_eq; [ | easy ].
  now rewrite sqrt_0, Rsqr_0.
}
clear Hx; rename Hx' into Hx; move Hx before x.
remember (x / √ (1 - x²)) as y eqn:Hy.
rewrite sin_atan, cos_atan.
destruct (Req_dec x 0) as [Hxz| Hxz]. {
  subst x; rewrite Rdiv_0_l in Hy; subst y.
  split; [ now rewrite Rdiv_0_l | ].
  now rewrite Rsqr_0, Rplus_0_r, Rminus_0_r, sqrt_1, Rdiv_1_r.
}
assert (H1x : 0 < 1 - x²). {
  replace 1 with 1² by apply Rsqr_1.
  rewrite <- Rsqr_plus_minus.
  apply Rmult_lt_0_compat; lra.
}
assert (Hsp : 0 < √ (1 - x²)). {
  apply Rsqr_incrst_0; [ | lra | apply sqrt_pos ].
  rewrite Rsqr_sqrt; [ now rewrite Rsqr_0 | lra ].
}
assert (Hyz : y ≠ 0). {
  intros H; apply Hxz; subst y.
  apply Rmult_eq_compat_r with (r := √ (1 - x²)) in H.
  unfold Rdiv in H; rewrite Rmult_assoc, Rmult_0_l in H.
  rewrite Rinv_l in H; lra.
}
assert (Hxy : 0 ≤ x * y). {
  subst y; unfold Rdiv; rewrite <- Rmult_assoc.
  rewrite fold_Rsqr.
  apply Rmult_le_pos; [ apply Rle_0_sqr | ].
  apply Rmult_le_reg_r with (r := √ (1 - x²)); [ lra | ].
  rewrite Rmult_0_l, Rinv_l; lra.
}
apply (f_equal Rsqr) in Hy.
rewrite Rsqr_div_depr in Hy; [ | lra ].
rewrite Rsqr_sqrt in Hy; [ | lra ].
apply Rmult_eq_compat_r with (r := 1 - x²) in Hy.
unfold Rdiv in Hy; rewrite Rmult_assoc in Hy.
rewrite Rinv_l in Hy; [ rewrite Rmult_1_r in Hy | lra ].
rewrite Rmult_minus_distr_l, Rmult_1_r in Hy.
assert (H : y² = x² * (1 + y²)) by lra.
apply Rmult_eq_compat_r with (r := / (1 + y²)) in H.
rewrite Rmult_assoc in H.
assert (H1y : 0 < 1 + y²). {
  apply Rplus_lt_le_0_compat; [ lra | apply Rle_0_sqr ].
}
assert (Hsy : 0 < √ (1 + y²)). {
  apply Rsqr_incrst_0; [ | lra | apply sqrt_pos ].
  rewrite Rsqr_sqrt; [ now rewrite Rsqr_0 | lra ].
}
rewrite Rinv_r in H; [ | lra ].
replace (/ (1 + y²)) with (/ √ (1 + y²))² in H. {
  rewrite <- Rsqr_mult in H.
  rewrite Rmult_1_r in H.
  apply Rsqr_eq in H.
  split. {
    destruct H as [H| H]; [ easy | exfalso ].
    apply Ropp_eq_compat in H.
    rewrite Ropp_involutive in H.
    rewrite <- H in Hxy.
    rewrite <- Ropp_mult_distr_l in Hxy.
    rewrite Rmult_comm, <- Rmult_assoc, fold_Rsqr in Hxy.
    replace 0 with (-0) in Hxy by apply Ropp_0.
    apply Ropp_le_cancel in Hxy.
    apply Rmult_le_compat_r with (r := √ (1 + y²)) in Hxy; [ | lra ].
    rewrite Rmult_assoc, Rmult_0_l in Hxy.
    rewrite Rinv_l in Hxy; [ | lra ].
    rewrite Rmult_1_r in Hxy.
    apply Rle_not_lt in Hxy; apply Hxy.
    now apply Rlt_0_sqr.
  }
  apply Rmult_eq_reg_r with (r := √ (1 + y²)); [ | lra ].
  rewrite <- Rinv_div.
  rewrite Rinv_l; [ | lra ].
  symmetry.
  rewrite <- sqrt_mult; [ | lra | lra ].
  rewrite Rmult_plus_distr_l, Rmult_1_r.
  rewrite Rmult_minus_distr_r, Rmult_1_l.
  rewrite Rmult_comm, Hy.
  now rewrite Rminus_plus, sqrt_1.
}
rewrite Rsqr_inv_depr; [ | lra ].
rewrite Rsqr_sqrt; [ easy | lra ].
Qed.

Theorem cos_sin_acos : ∀ x,
  -1 ≤ x ≤ 1
  → cos (acos x) = x ∧ sin (acos x) = √ (1 - x²).
Proof.
intros * Hx.
unfold acos.
rewrite cos_minus, sin_minus.
rewrite cos_PI2, sin_PI2.
do 2 rewrite Rmult_0_l, Rmult_1_l.
rewrite Rplus_0_l, Rminus_0_r.
now apply sin_cos_asin.
Qed.

Theorem sin_asin : ∀ x, -1 ≤ x ≤ 1 → sin (asin x) = x.
Proof.
intros * Hx.
now apply sin_cos_asin.
Qed.

Theorem sin_acos : ∀ x, -1 ≤ x ≤ 1 → sin (acos x) = √ (1 - x²).
Proof.
intros * Hx.
now apply cos_sin_acos.
Qed.

Theorem cos_asin : ∀ x, -1 ≤ x ≤ 1 → cos (asin x) = √ (1 - x²).
Proof.
intros * Hx.
now apply sin_cos_asin.
Qed.

Theorem cos_acos : ∀ x, -1 ≤ x ≤ 1 → cos (acos x) = x.
Proof.
intros * Hx.
unfold acos; rewrite cos_shift.
now apply sin_asin.
Qed.

Theorem sin_Zperiod : ∀ x k, sin (x + 2 * IZR k * PI) = sin x.
Proof.
intros.
destruct k as [| k| k]. {
  now rewrite Rmult_0_r, Rmult_0_l, Rplus_0_r.
} {
  set (t := 2); unfold IZR; rewrite <- INR_IPR.
  now simpl; rewrite sin_period.
} {
  set (t := 2); unfold IZR; rewrite <- INR_IPR.
  simpl; rewrite <- Ropp_mult_distr_r, <- Ropp_mult_distr_l, fold_Rminus.
  rewrite <- sin_period with (k := Pos.to_nat k).
  now rewrite Rminus_plus.
}
Qed.

Theorem cos_Zperiod : ∀ x k, cos (x + 2 * IZR k * PI) = cos x.
Proof.
intros.
destruct k as [| k| k]. {
  now rewrite Rmult_0_r, Rmult_0_l, Rplus_0_r.
} {
  set (t := 2); unfold IZR; rewrite <- INR_IPR.
  now simpl; rewrite cos_period.
} {
  set (t := 2); unfold IZR; rewrite <- INR_IPR.
  simpl; rewrite <- Ropp_mult_distr_r, <- Ropp_mult_distr_l, fold_Rminus.
  rewrite <- cos_period with (k := Pos.to_nat k).
  now rewrite Rminus_plus.
}
Qed.

Theorem sin_nPI : ∀ n, sin (INR n * PI) = 0.
Proof.
intros.
induction n; [ rewrite Rmult_0_l; apply sin_0 | ].
rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, neg_sin; lra.
Qed.

Theorem cos_nPI : ∀ n, cos (INR n * PI) = (-1) ^ n.
Proof.
intros.
induction n; [ now rewrite Rmult_0_l, cos_0 | ].
rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, neg_cos, IHn.
simpl; lra.
Qed.

Theorem sin_ZPI : ∀ z, sin (IZR z * PI) = 0.
Proof.
intros.
destruct z as [| z| z]; simpl; [ now rewrite Rmult_0_l, sin_0 | | ]. {
  unfold IZR; rewrite <- INR_IPR.
  now rewrite sin_nPI.
} {
  unfold IZR; rewrite <- INR_IPR.
  rewrite <- Ropp_mult_distr_l.
  rewrite sin_neg, sin_nPI; lra.
}
Qed.

Theorem cos_ZPI : ∀ z, cos (IZR z * PI) = (-1) ^ Z.abs_nat z.
Proof.
intros.
destruct z as [| z| z]; simpl; [ now rewrite Rmult_0_l, cos_0 | | ]. {
  unfold IZR; rewrite <- INR_IPR.
  now rewrite cos_nPI.
} {
  unfold IZR; rewrite <- INR_IPR.
  rewrite <- Ropp_mult_distr_l.
  now rewrite cos_neg, cos_nPI.
}
Qed.

Theorem tan_period : ∀ x k, tan (x + INR k * PI) = tan x.
Proof.
intros.
destruct (eq_nat_dec (k mod 2) 0) as [Hk| Hk]. {
  apply Nat.Div0.mod_divides in Hk.
  destruct Hk as (c, Hc); subst k.
  rewrite mult_INR; simpl.
  unfold tan.
  now rewrite sin_period, cos_period.
}
destruct k; [ easy | ].
rewrite S_INR.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l, <- Rplus_assoc.
unfold tan.
rewrite neg_sin, neg_cos.
rewrite sin_plus, cos_plus.
rewrite sin_nPI, cos_nPI.
do 2 rewrite Rmult_0_r.
rewrite Rplus_0_r, Rminus_0_r.
do 2 rewrite Ropp_mult_distr_r.
rewrite Rdiv_mult_simpl_r; [ easy | ].
clear; induction k; simpl; lra.
Qed.

Theorem tan_Zperiod : ∀ x k, tan (x + IZR k * PI) = tan x.
Proof.
intros.
destruct (Z.eq_dec (k mod 2) 0) as [Hk| Hk]. {
  apply Zdiv.Zmod_divides in Hk; [ | easy ].
  destruct Hk as (c, Hc); subst k.
  rewrite mult_IZR; simpl.
  unfold tan.
  now rewrite sin_Zperiod, cos_Zperiod.
}
destruct k as [| k| k]; [ easy | | ]. {
  now unfold IZR; rewrite <- INR_IPR; apply tan_period.
} {
  unfold IZR; rewrite <- INR_IPR.
  simpl; rewrite <- Ropp_mult_distr_l, fold_Rminus.
  rewrite <- tan_period with (k := Pos.to_nat k).
  now rewrite Rminus_plus.
}
Qed.

Theorem tan_ZPI : ∀ k, tan (IZR k * PI) = 0.
Proof.
intros.
specialize (tan_Zperiod 0 k) as H.
now rewrite Rplus_0_l, tan_0 in H.
Qed.

Theorem neg_cos_atan_tan : ∀ x,
  cos x < 0
  → atan (tan x) = x - IZR ((x + PI / 2) // PI) * PI.
Proof.
intros * Hc.
unfold atan.
destruct (pre_atan (tan x)) as (y & Hy & Hyx).
remember ((x + PI / 2) rmod PI - PI / 2) as z eqn:Hz.
assert (Htz : tan z = tan x). {
  subst z.
  unfold Rmod, Rediv_mod, snd.
  destruct (Rcase_abs PI) as [HP| HP]; [ lra | ].
  remember (IZR (Int_part ((x + PI / 2) / PI)) * PI) as t eqn:Ht.
  replace (x + PI / 2 - t - PI / 2) with (x - t) by lra.
  rewrite tan_minus; [ | lra | | | ]. {
    subst t; rewrite tan_ZPI.
    now rewrite Rminus_0_r, Rmult_0_r, Rplus_0_r, Rdiv_1_r.
  } {
    subst t.
    rewrite cos_ZPI.
    apply pow_nonzero; lra.
  } {
    subst t.
    rewrite cos_minus.
    rewrite cos_ZPI, sin_ZPI.
    rewrite Rmult_0_r, Rplus_0_r.
    intros H.
    apply Rmult_integral in H.
    destruct H as [H| H]; [ lra | ].
    apply pow_nonzero in H; lra.
  } {
    subst t.
    rewrite tan_ZPI, Rmult_0_r, Rplus_0_r; lra.
  }
}
assert (Hzi : - PI / 2 < z < PI / 2). {
  rewrite Hz.
  assert (HPP : 0 < PI) by lra.
  specialize (Rmod_interv (x + PI / 2) PI HPP) as H.
  split; [ | lra ].
  enough ((x + PI / 2) rmod PI ≠ 0) by lra.
  intros Hm.
  unfold Rmod, Rediv_mod, snd in Hm.
  destruct (Rcase_abs PI) as [HPQ| HPQ]; [ lra | ].
  fold (Int_part ((x + PI / 2) / PI)) in Hm.
  apply Rminus_diag_uniq in Hm.
  remember (Int_part ((x + PI / 2) / PI)) as k.
  assert (x = IZR k * PI - PI / 2) by lra.
  rewrite H0 in Hc.
  rewrite cos_minus in Hc.
  rewrite cos_ZPI, sin_ZPI in Hc.
  rewrite Rmult_0_l, Rplus_0_r in Hc.
  rewrite cos_PI2, Rmult_0_r in Hc; lra.
}
rewrite <- Htz in Hyx.
specialize (tan_is_inj y z Hy Hzi Hyx) as H.
move H at top; subst z.
rewrite Rmod_from_ediv in Hz; lra.
Qed.

Theorem pos_cos_atan_tan : ∀ x,
  0 < cos x
  → atan (tan x) = x - IZR ((x + PI / 2) // PI) * PI.
Proof.
intros * Hc.
assert (Hcp : cos (x + PI) < 0) by (rewrite neg_cos; lra).
specialize (neg_cos_atan_tan (x + PI) Hcp) as H.
specialize (tan_period x 1) as Ht.
simpl (INR _) in Ht.
rewrite Rmult_1_l in Ht.
rewrite Rplus_shuffle0 in H.
rewrite Rediv_add_1 in H; [ | apply PI_neq0 ].
rewrite plus_IZR in H.
simpl (IZR _) in H.
rewrite Ht in H; lra.
Qed.

Theorem atan_tan : ∀ x,
  cos x ≠ 0
  → atan (tan x) = x - IZR ((x + PI / 2) // PI) * PI.
Proof.
intros * Hxz.
destruct (Rlt_dec (cos x) 0) as [Hx| Hx]. {
  now apply neg_cos_atan_tan.
}
apply pos_cos_atan_tan; lra.
Qed.

Theorem asin_sin : ∀ x,
  asin (sin x) = Rsignp (cos x) * atan' (sin x) (cos x).
Proof.
intros.
unfold asin, atan'.
rewrite <- cos2.
rewrite sqrt_Rsqr_abs.
destruct (Req_dec (cos x) 0) as [Haz| Haz]. {
  rewrite Haz, Rabs_R0.
  rewrite Rsignp_of_pos; [ | lra ].
  destruct (Req_dec 0 0); lra.
}
destruct (Req_dec (Rabs (cos x))) as [Hab| Hab]. {
  now apply Rabs_eq_0 in Hab.
}
unfold Rabs.
destruct (Rcase_abs (cos x)) as [Ha| Ha]. {
  unfold Rdiv.
  rewrite Rsignp_of_neg; [ | easy ].
  destruct (Rle_dec 0 (cos x)); [ lra | ].
  rewrite Rinv_opp.
  rewrite <- Ropp_mult_distr_r.
  rewrite fold_Rdiv.
  fold (tan x); rewrite atan_opp; lra.
}
rewrite Rsignp_of_pos; lra.
Qed.

Theorem cos_plus_PI2 : ∀ x, cos (x + PI / 2) = - sin x.
Proof.
intros.
rewrite cos_plus, cos_PI2, sin_PI2; lra.
Qed.

Theorem asin_cos : ∀ x,
  asin (cos x) =
    if Req_dec (sin x) 0 then Rsign (cos x) * PI / 2
    else - Rsign (sin x) * atan (tan (x + PI / 2)).
Proof.
intros.
rewrite cos_sin, asin_sin.
rewrite Rplus_comm.
unfold atan'.
fold (tan (x + PI / 2)).
rewrite cos_plus_PI2.
unfold Rsignp.
destruct (Req_dec (- sin x) 0) as [H1| H1]. {
  rewrite H1.
  apply (f_equal Ropp) in H1.
  rewrite Ropp_involutive, Ropp_0 in H1.
  rewrite H1.
  destruct (Rle_dec 0 0) as [H| H]; [ clear H | lra ].
  destruct (Req_dec 0 0); lra.
}
destruct (Req_dec (sin x) 0) as [Hs| Hs]; [ lra | clear H1 ].
destruct (Rle_dec 0 (- sin x)) as [H1| H1]. {
  rewrite Rsign_of_neg; lra.
} {
  rewrite Rsign_of_pos; lra.
}
Qed.

Theorem acos_cos : ∀ x, acos (cos x) = PI / 2 - asin (cos x).
Proof. easy. Qed.

Theorem nonneg_sin_interv : ∀ x, 0 ≤ sin x → x rmod (2 * PI) ≤ PI.
Proof.
intros * Hs.
apply Rnot_lt_le; intros Hx.
apply Rle_not_lt in Hs; apply Hs; clear Hs.
enough (H : sin (x rmod (2 * PI)) < 0). {
  rewrite Rmod_from_ediv in H.
  unfold Rminus in H.
  rewrite Ropp_mult_distr_l in H.
  rewrite <- opp_IZR in H.
  rewrite Rmult_comm, Rmult_shuffle0 in H.
  now rewrite sin_Zperiod in H.
}
apply sin_lt_0; [ easy | ].
assert (HP : 0 < 2 * PI) by (specialize PI_RGT_0; lra).
specialize (Rmod_interv x (2 * PI) HP) as H; lra.
Qed.

Theorem pos_sin_interv : ∀ x, 0 < sin x → x rmod (2 * PI) < PI.
Proof.
intros * Hs.
apply Rnot_le_lt; intros Hx.
apply Rlt_not_le in Hs; apply Hs; clear Hs.
enough (H : sin (x rmod (2 * PI)) ≤ 0). {
  rewrite Rmod_from_ediv in H.
  unfold Rminus in H.
  rewrite Ropp_mult_distr_l in H.
  rewrite <- opp_IZR in H.
  rewrite Rmult_comm, Rmult_shuffle0 in H.
  now rewrite sin_Zperiod in H.
}
apply sin_le_0; [ easy | ].
assert (HP : 0 < 2 * PI) by (specialize PI_RGT_0; lra).
specialize (Rmod_interv x (2 * PI) HP) as H; lra.
Qed.

Theorem neg_sin_interv : ∀ x, sin x < 0 → PI < x rmod (2 * PI).
Proof.
intros * Hs.
apply Rnot_le_lt; intros Hx.
apply Rlt_not_le in Hs; apply Hs; clear Hs.
enough (H : 0 ≤ sin (x rmod (2 * PI))). {
  rewrite Rmod_from_ediv in H.
  unfold Rminus in H.
  rewrite Ropp_mult_distr_l in H.
  rewrite <- opp_IZR in H.
  rewrite Rmult_comm, Rmult_shuffle0 in H.
  now rewrite sin_Zperiod in H.
}
apply sin_ge_0; [ | easy ].
assert (HP : 0 < 2 * PI) by (specialize PI_RGT_0; lra).
specialize (Rmod_interv x (2 * PI) HP) as H; lra.
Qed.

Theorem pos_cos_interv : ∀ x,
  0 < cos x
  → x rmod (2 * PI) < PI / 2 ∨ 3 * PI / 2 < x rmod (2 * PI) .
Proof.
intros * Hc.
destruct (Rlt_dec (x rmod (2 * PI)) (PI / 2)) as [Hx| Hx]; [ now left | ].
right.
apply Rlt_not_le in Hc.
apply Rnot_lt_le in Hx.
apply Rnot_le_lt; intros H.
apply Hc; clear Hc.
rewrite Rmod_from_ediv in Hx, H.
remember (x // (2 * PI)) as k eqn:Hk.
rewrite <- cos_Zperiod with (k := (- k)%Z).
apply cos_le_0; rewrite opp_IZR; lra.
Qed.

Theorem neg_cos_interv : ∀ x,
  cos x < 0
  → PI / 2 < x rmod (2 * PI) < 3 * PI / 2.
Proof.
intros * Hc.
split. {
  apply Rnot_le_lt; intros Hx.
  apply Rlt_not_le in Hc; apply Hc; clear Hc.
  enough (H : 0 ≤ cos (x rmod (2 * PI))). {
    rewrite Rmod_from_ediv in H.
    unfold Rminus in H.
    rewrite Ropp_mult_distr_l in H.
    rewrite <- opp_IZR in H.
    rewrite Rmult_comm, Rmult_shuffle0 in H.
    now rewrite cos_Zperiod in H.
  }
  apply cos_ge_0; [ | easy ].
  assert (HP : - (PI / 2) ≤ 0) by (specialize PI_RGT_0; lra).
  eapply Rle_trans; [ apply HP | ].
  apply Rmod_interv.
  specialize PI_RGT_0; lra.
}
apply Rnot_le_lt; intros Hx.
apply Rlt_not_le in Hc; apply Hc; clear Hc.
enough (H : 0 ≤ cos (x rmod (2 * PI))). {
  rewrite Rmod_from_ediv in H.
  unfold Rminus in H.
  rewrite Ropp_mult_distr_l in H.
  rewrite <- opp_IZR in H.
  rewrite Rmult_comm, Rmult_shuffle0 in H.
  now rewrite cos_Zperiod in H.
}
apply cos_ge_0_3PI2; [ lra | ].
apply Rlt_le, Rmod_interv.
specialize PI_RGT_0; lra.
Qed.

Theorem neg_sin_neg_cos_2PI_acos_cos : ∀ x,
  sin x < 0
  → cos x < 0
  → 2 * PI - acos (cos x) = x rmod (2 * PI).
Proof.
intros * Hs Hc.
specialize PI_RGT_0 as HPI_GT_0.
specialize PI_neq0 as HPI_NZ.
rewrite acos_cos, asin_cos.
destruct (Req_dec (sin x) 0) as [| H]; [ lra | clear H ].
rewrite <- Ropp_mult_distr_l, Rminus_opp.
rewrite Rsign_of_neg; [ | easy ].
set (t := 2); unfold IZR; rewrite <- INR_IPR.
rewrite <- Ropp_mult_distr_l, Rmult_1_l.
rewrite fold_Rminus.
rewrite atan_tan; [ | rewrite cos_plus_PI2; lra ].
subst t.
progress replace (x + PI / 2 + PI / 2) with (x + PI) by lra.
rewrite Rediv_add_1; [ | apply PI_neq0 ].
rewrite Rmod_from_ediv.
rewrite plus_IZR; simpl (IZR 1).
remember (IZR (x // PI)) as e eqn:He.
replace ( 2 * PI - (PI / 2 - (x + PI / 2 - (e + 1) * PI))) with
  (x - (e - 1) * PI) by lra; subst e.
rewrite <- Rmult_assoc.
f_equal; f_equal.
enough (IZR (x // PI) = 2 * IZR (x // (2 * PI)) + 1) by lra.
apply neg_sin_interv in Hs.
apply neg_cos_interv in Hc.
rewrite Rmod_from_ediv in Hs, Hc.
remember (x // (2 * PI)) as k eqn:Hk.
replace (IZR k * (2 * PI)) with (2 * IZR k * PI) in Hs, Hc by lra.
assert (Hp : PI < x - 2 * IZR k * PI < 3 * PI / 2) by lra.
clear Hs Hc.
rewrite Rediv_mul_r in Hk.
destruct (Rcase_abs (2 * PI)) as [HP| HP]; [ lra | clear HP ].
rewrite Z.add_0_r in Hk.
unfold Rediv, fst, Rediv_mod.
destruct (Rcase_abs PI) as [HP| HP]; [ lra | clear HP ].
rewrite Rmult_comm in Hk.
rewrite <- Rdiv_div in Hk.
remember (x / PI) as y eqn:Hy.
apply Rmult_eq_compat_r with (r := PI) in Hy.
rewrite Rmult_div_same in Hy; [ | lra ].
subst x; rename y into x.
enough (IZR (Int_part x) = IZR 2 * IZR k + IZR 1) by lra.
rewrite <- mult_IZR, <- plus_IZR; f_equal.
apply Int_part_interv.
do 3 rewrite plus_IZR; rewrite mult_IZR; simpl.
rewrite <- Rmult_minus_distr_r in Hp.
destruct Hp as (H1, H2).
replace PI with (1 * PI) in H1 at 1 by lra.
apply Rmult_lt_reg_r in H1; [ | lra ].
replace (3 * PI / 2) with ((3 / 2) * PI) in H2 by lra.
apply Rmult_lt_reg_r in H2; lra.
Qed.

Theorem neg_sin_pos_cos_asin_sin_2PI : ∀ x,
  sin x < 0
  → 0 ≤ cos x
  → asin (sin x) + 2 * PI = x rmod (2 * PI).
Proof.
intros * Hs Hc.
specialize PI_RGT_0 as HPI_GT_0.
specialize PI_neq0 as HPI_NZ.
destruct (Rlt_dec (sin x) 0) as [H| ]; [ clear H | lra ].
destruct (Rlt_dec (cos x) 0) as [| H]; [ lra | clear H ].
rewrite asin_sin.
rewrite Rsignp_of_pos; [ rewrite Rmult_1_l | easy ].
unfold atan'.
destruct (Req_dec (cos x) 0) as [Hcz| Hcz]. {
  rewrite Rsign_of_neg; [ | easy ].
  set (t := 2); unfold IZR; rewrite <- INR_IPR.
  rewrite <- Ropp_mult_distr_l, Rmult_1_l.
  apply cos_eq_0_0 in Hcz.
  destruct Hcz as (k, Hx).
  apply neg_sin_interv in Hs.
  destruct (Bool.bool_dec (Z.even k) true) as [Hk| Hk]. {
    exfalso.
    apply Zeven_bool_iff, Zeven_ex_iff in Hk.
    destruct Hk as (m, Hm).
    rewrite Hm in Hx; rewrite Hx in Hs.
    rewrite mult_IZR in Hs; simpl in Hs.
    replace (2 * IZR m * PI) with (IZR m * (2 * PI)) in Hs by lra.
    rewrite Rplus_comm in Hs.
    rewrite Rmod_add_Z in Hs; [ | lra ].
    rewrite Rmod_small in Hs; lra.
  }
  rewrite <- Z.negb_odd in Hk.
  apply Bool.not_true_iff_false in Hk.
  apply Bool.negb_false_iff in Hk.
  apply Zodd_bool_iff, Zodd_ex_iff in Hk.
  destruct Hk as (m, Hm).
  rewrite Hx, Hm.
  rewrite plus_IZR, mult_IZR; simpl.
  progress replace ((2 * IZR m + 1) * PI + PI / 2) with
    (3 * PI / 2 + IZR m * (2 * PI)) by lra.
  subst t.
  rewrite Rmod_add_Z; [ | lra ].
  rewrite Rmod_small; lra.
}
progress fold (tan x).
rewrite atan_tan; [ | easy ].
assert (H : 0 < cos x) by lra.
clear Hc Hcz; rename H into Hc.
apply neg_sin_interv in Hs.
apply pos_cos_interv in Hc.
destruct Hc as [Hc| Hc]; [ lra | clear Hs ].
remember (IZR ((x + PI / 2) // PI) * PI) as u eqn:Hu.
replace (x - u + 2 * PI) with (x + PI / 2 - u + 3 * PI / 2) by lra.
subst u; rewrite <- Rmod_from_ediv.
rewrite Rplus_comm; symmetry.
unfold Rmod, snd, Rediv_mod.
destruct (Rcase_abs (2 * PI)) as [| H]; [ lra | clear H ].
destruct (Rcase_abs PI) as [| H]; [ lra | clear H ].
remember (IZR (Int_part ((x + PI / 2) / PI)) * PI) as u eqn:Hu.
replace (3 * PI / 2 + (x + PI / 2 - u)) with (x - (u - 2 * PI)) by lra.
subst u; unfold Rminus.
f_equal; rewrite fold_Rminus.
apply Ropp_eq_compat.
rewrite <- Rmult_minus_distr_r.
replace 2 with (IZR 2) at 4 by easy.
rewrite <- minus_IZR.
rewrite <- Rmult_assoc.
f_equal.
replace ((x + PI / 2) / PI) with ((2 * x + PI) / (2 * PI)). {
  rewrite Rdiv_plus_distr.
  rewrite Rdiv_mult_simpl_l; [ | lra ].
  replace PI with (1 * PI) at 3 by lra.
  rewrite Rdiv_mult_simpl_r; [ | lra ].
  unfold Rmod, snd, Rediv_mod in Hc.
  destruct (Rcase_abs (2 * PI)) as [| H]; [ lra | clear H ].
  replace (2 * PI) with (PI * 2) in Hc at 1 by lra.
  replace (2 * PI) with (PI * 2) by lra.
  rewrite <- Rdiv_div in Hc.
  rewrite <- Rdiv_div.
  remember (x / PI) as y eqn:Hy.
  replace x with (y * PI) in Hc by (subst y; rewrite Rmult_div_same; lra).
  clear x Hy; rename y into x.
  replace (3 * PI / 2) with ((3 / 2) * PI) in Hc by lra.
  rewrite <- Rmult_assoc in Hc.
  rewrite <- Rmult_minus_distr_r in Hc.
  apply Rmult_lt_reg_r in Hc; [ | easy ].
  replace x with ((x / 2) * 2) in Hc at 1 by lra.
  rewrite <- Rmult_minus_distr_r in Hc.
  fold (frac_part (x / 2)) in Hc.
  remember (x / 2) as y eqn:Hy.
  replace x with (2 * y) by lra.
  clear x Hy; rename y into x.
  assert (Hx34 : 3 / 4 < frac_part x) by lra.
  clear Hc.
  destruct (Rlt_dec (frac_part (2 * x)) (1 / 2)) as [Hx12| Hx12]. {
    exfalso.
    rewrite frac_part_double in Hx12.
    destruct (Rlt_dec (frac_part x) (1 / 2)); lra.
  }
  assert (H : frac_part (1 / 2) = 1 / 2) by (apply frac_part_small; lra).
  rewrite plus_Int_part1; [ clear H | lra ].
  rewrite frac_part_double in Hx12; rewrite Int_part_double.
  destruct (Rlt_dec (frac_part x) (1 / 2)) as [| H]; [ lra | clear H ].
  replace 2 with (IZR 2) at 1 by lra.
  rewrite <- mult_IZR; f_equal.
  enough (Int_part (1 / 2) = 0%Z) by lia.
  apply Int_part_small; lra.
}
do 2 rewrite Rdiv_plus_distr.
rewrite Rdiv_mult_simpl_l; [ | lra ].
f_equal.
now rewrite Rdiv_div.
Qed.

Theorem pos_sin_neg_cos_acos_cos : ∀ x,
  0 ≤ sin x
  → cos x < 0
  → acos (cos x) = x rmod (2 * PI).
Proof.
intros * Hs Hc.
specialize PI_RGT_0 as HPI_GT_0.
specialize PI_neq0 as HPI_NZ.
rewrite acos_cos, asin_cos.
destruct (Req_dec (sin x) 0) as [Hsz| Hsnz]. {
  specialize (sin_eq_0_0 _ Hsz) as (k, Hk); subst x.
  rewrite cos_ZPI.
  destruct (Bool.bool_dec (Z.even k) true) as [Hk| Hk]. {
    apply Zeven_bool_iff, Zeven_ex_iff in Hk.
    destruct Hk as (m, Hm).
    rewrite Hm; rewrite Zabs2Nat.inj_mul.
    simpl (Z.abs_nat 2); unfold Pos.to_nat; simpl (Pos.iter_op _ _ _).
    rewrite pow_1_even; rewrite Rsign_of_pos; [ | lra ].
    rewrite Rmult_1_l, mult_IZR; simpl (IZR 2).
    rewrite Rmult_shuffle0, Rmult_comm.
    rewrite Rmod_mul_same; lra.
  }
  rewrite <- Z.negb_odd in Hk.
  apply Bool.not_true_iff_false in Hk.
  apply Bool.negb_false_iff in Hk.
  apply Zodd_bool_iff, Zodd_ex_iff in Hk.
  destruct Hk as (m, Hk).
  rewrite Hk at 1.
  rewrite pow_1_abs_nat_odd.
  rewrite Rsign_of_neg; [ | lra ].
  rewrite Z.add_comm, Z.mul_comm in Hk.
  rewrite Hk, plus_IZR, mult_IZR; simpl.
  rewrite Rmult_plus_distr_r, Rmult_1_l, Rmult_assoc.
  rewrite Rmod_add_Z; [ | lra ].
  rewrite Rmod_small; lra.
}
assert (H : 0 < sin x) by lra; clear Hs Hsnz; rename H into Hs.
move Hs after Hc.
rewrite <- Ropp_mult_distr_l.
rewrite Rminus_opp.
rewrite Rsign_of_pos; [ | easy ].
rewrite Rmult_1_l.
rewrite atan_tan; [ | rewrite cos_plus_PI2; lra ].
replace (x + PI / 2 + PI / 2) with (x + PI) by lra.
rewrite Rediv_add_1; [ | apply PI_neq0 ].
rewrite Rmod_from_ediv.
rewrite plus_IZR; simpl (IZR 1).
remember (IZR (x // PI)) as e eqn:He.
replace (PI / 2 + (x + PI / 2 - (e + 1) * PI)) with (x - e * PI) by lra.
subst e.
rewrite <- Rmult_assoc.
f_equal; f_equal.
apply pos_sin_interv in Hs.
apply neg_cos_interv in Hc.
rewrite Rmod_from_ediv in Hs, Hc.
remember (x // (2 * PI)) as k eqn:Hk.
replace (IZR k * (2 * PI)) with (2 * IZR k * PI) in Hs, Hc by lra.
assert (Hp : PI / 2 < x - 2 * IZR k * PI < PI) by lra.
clear Hs Hc.
rewrite Rediv_mul_r in Hk.
destruct (Rcase_abs (2 * PI)) as [HP| HP]; [ lra | clear HP ].
rewrite Z.add_0_r in Hk.
unfold Rediv, fst, Rediv_mod.
destruct (Rcase_abs PI) as [HP| HP]; [ lra | clear HP ].
rewrite Rmult_comm in Hk.
rewrite <- Rdiv_div in Hk.
remember (x / PI) as y eqn:Hy.
apply Rmult_eq_compat_r with (r := PI) in Hy.
rewrite Rmult_div_same in Hy; [ | lra ].
subst x; rename y into x.
enough (IZR (Int_part x) = IZR 2 * IZR k) by lra.
rewrite <- mult_IZR; f_equal.
apply Int_part_interv.
rewrite plus_IZR; rewrite mult_IZR; simpl.
rewrite <- Rmult_minus_distr_r in Hp.
destruct Hp as (H1, H2).
replace (PI / 2) with (1 / 2 * PI) in H1 at 1 by lra.
apply Rmult_lt_reg_r in H1; [ | lra ].
replace PI with (1 * PI) in H2 at 2 by lra.
apply Rmult_lt_reg_r in H2; lra.
Qed.

Theorem pos_sin_pos_cos_asin_sin : ∀ x,
  0 ≤ sin x
  → 0 ≤ cos x
  → asin (sin x) = x rmod (2 * PI).
Proof.
intros * Hs Hc.
specialize PI_RGT_0 as HPI_GT_0.
specialize PI_neq0 as HPI_NZ.
rewrite asin_sin.
rewrite Rsignp_of_pos; [ rewrite Rmult_1_l | easy ].
unfold atan'.
destruct (Req_dec (cos x) 0) as [Hcz| Hcz]. {
  destruct (Req_dec (sin x) 0) as [Hsz| Hsz]. {
    specialize (sin2_cos2 x) as H.
    rewrite Hsz, Hcz, Rsqr_0 in H; lra.
  }
  assert (H : 0 < sin x) by lra.
  clear Hs Hsz; rename H into Hs.
  move Hs after Hc.
  rewrite Rsign_of_pos; [ | easy ].
  rewrite Rmult_1_l.
  apply cos_eq_0_0 in Hcz.
  destruct Hcz as (k, Hx).
  apply pos_sin_interv in Hs.
  destruct (Bool.bool_dec (Z.even k) true) as [Hk| Hk]. {
    apply Zeven_bool_iff, Zeven_ex_iff in Hk.
    destruct Hk as (m, Hm).
    rewrite Rplus_comm in Hx.
    rewrite Hm in Hx; rewrite Hx.
    rewrite mult_IZR; simpl.
    replace (2 * IZR m * PI) with (IZR m * (2 * PI)) by lra.
    rewrite Rmod_add_Z; [ | lra ].
    rewrite Rmod_small; lra.
  }
  rewrite <- Z.negb_odd in Hk.
  apply Bool.not_true_iff_false in Hk.
  apply Bool.negb_false_iff in Hk.
  apply Zodd_bool_iff, Zodd_ex_iff in Hk.
  destruct Hk as (m, Hm).
  rewrite Rplus_comm in Hx.
  rewrite Z.add_comm in Hm.
  rewrite Hx, Hm in Hs.
  rewrite plus_IZR, mult_IZR in Hs; simpl in Hs.
  rewrite Rmult_plus_distr_r, Rmult_1_l in Hs.
  replace (2 * IZR m * PI) with (IZR m * (2 * PI)) in Hs by lra.
  rewrite <- Rplus_assoc in Hs.
  rewrite Rmod_add_Z in Hs; [ | lra ].
  rewrite Rmod_small in Hs; lra.
}
progress fold (tan x).
rewrite atan_tan; [ | easy ].
assert (H : 0 < cos x) by lra.
clear Hc Hcz; rename H into Hc.
move Hc before Hs.
apply nonneg_sin_interv in Hs.
apply pos_cos_interv in Hc.
destruct Hc as [Hc| Hc]; [ clear Hs | lra ].
unfold Rediv, Rmod, fst, snd, Rediv_mod.
destruct (Rcase_abs (2 * PI)) as [| H]; [ lra | clear H ].
destruct (Rcase_abs PI) as [| H]; [ lra | clear H ].
f_equal.
replace ((x + PI / 2) / PI) with ((2 * x + PI) / (2 * PI)). {
  rewrite Rdiv_plus_distr.
  rewrite Rdiv_mult_simpl_l; [ | lra ].
  replace PI with (1 * PI) at 2 by lra.
  rewrite Rdiv_mult_simpl_r; [ | lra ].
  unfold Rmod, snd, Rediv_mod in Hc.
  destruct (Rcase_abs (2 * PI)) as [| H]; [ lra | clear H ].
  replace (2 * PI) with (PI * 2) in Hc at 1 by lra.
  replace (2 * PI) with (PI * 2) by lra.
  rewrite <- Rdiv_div in Hc.
  rewrite <- Rdiv_div.
  remember (x / PI) as y eqn:Hy.
  replace x with (y * PI) in Hc by (subst y; rewrite Rmult_div_same; lra).
  clear x Hy; rename y into x.
  replace (PI / 2) with ((1 / 2) * PI) in Hc by lra.
  rewrite <- Rmult_assoc in Hc.
  rewrite <- Rmult_minus_distr_r in Hc.
  apply Rmult_lt_reg_r in Hc; [ | easy ].
  replace x with ((x / 2) * 2) in Hc at 1 by lra.
  rewrite <- Rmult_minus_distr_r in Hc.
  fold (frac_part (x / 2)) in Hc.
  remember (x / 2) as y eqn:Hy.
  replace x with (2 * y) by lra.
  clear x Hy; rename y into x.
  rewrite <- Rmult_assoc, Rmult_shuffle0; f_equal.
  replace 2 with (IZR 2) at 3 by lra.
  rewrite <- mult_IZR; f_equal.
  assert (Hx : frac_part x < 1 / 4) by lra; clear Hc.
  destruct (Rlt_dec (frac_part (2 * x)) (1 / 2)) as [Hx12| Hx12]. {
    rewrite plus_Int_part2. {
      rewrite Z.add_comm.
      rewrite Int_part_small; [ | lra ].
      rewrite Z.add_0_l.
      rewrite Int_part_double.
      destruct (Rlt_dec (frac_part x) (1 / 2)); [ lia | lra ].
    }
    rewrite Rplus_comm, frac_part_small; lra.
  }
  rewrite frac_part_double in Hx12.
  apply Rnot_lt_le in Hx12.
  destruct (Rlt_dec (frac_part x) (1 / 2)); lra.
}
do 2 rewrite Rdiv_plus_distr.
rewrite Rdiv_mult_simpl_l; [ | lra ].
f_equal.
now rewrite Rdiv_div.
Qed.

Theorem angle_of_sin_cos_inv : ∀ x,
  angle_of_sin_cos (sin x) (cos x) = x rmod (2 * PI).
Proof.
intros.
unfold angle_of_sin_cos.
destruct (Rlt_dec (sin x) 0) as [Hs| Hs]. {
  destruct (Rlt_dec (cos x) 0) as [Hc| Hc]. {
    now apply neg_sin_neg_cos_2PI_acos_cos.
  }
  apply Rnot_lt_le in Hc.
  now apply neg_sin_pos_cos_asin_sin_2PI.
}
apply Rnot_lt_le in Hs.
destruct (Rlt_dec (cos x) 0) as [Hc| Hc]. {
  now apply pos_sin_neg_cos_acos_cos.
} {
  apply Rnot_lt_le in Hc.
  now apply pos_sin_pos_cos_asin_sin.
}
Qed.

Theorem pre_sin_bound : ∀ s c, s² + c² = 1 → -1 ≤ s ≤ 1.
Proof.
intros s c Hsc.
assert (H : s² ≤ 1). {
  enough (H : s² + 0 ≤ 1) by lra.
  rewrite <- Hsc.
  apply Rplus_le_compat_l, Rle_0_sqr.
}
rewrite <- Rsqr_1 in H.
apply Rsqr_le_abs_0 in H.
rewrite Rabs_R1 in H.
now apply Rabs_le in H.
Qed.

Theorem pre_cos_bound : ∀ s c, s² + c² = 1 → -1 ≤ c ≤ 1.
Proof.
intros s c Hsc.
rewrite Rplus_comm in Hsc.
now apply pre_sin_bound in Hsc.
Qed.

Theorem sin_angle_of_sin_cos : ∀ s c,
  s² + c² = 1
  → sin (angle_of_sin_cos s c) = s.
Proof.
intros * Hsc.
unfold angle_of_sin_cos.
destruct (Rlt_dec s 0) as [Hs| Hs]. {
  destruct (Rlt_dec c 0) as [Hc| Hc]. {
    rewrite sin_minus.
    rewrite cos_2PI, sin_2PI, Rmult_1_l, Rmult_0_l, Rminus_0_l.
    rewrite sin_acos; [ | now apply pre_cos_bound in Hsc ].
    replace (1 - c²) with s² by lra.
    rewrite Rsqr_neg, <- Ropp_involutive; f_equal.
    rewrite sqrt_Rsqr; [ easy | lra ].
  }
  rewrite sin_plus.
  rewrite cos_2PI, sin_2PI, Rmult_1_r, Rmult_0_r, Rplus_0_r.
  rewrite sin_asin; [ easy | now apply pre_sin_bound in Hsc ].
}
destruct (Rlt_dec c 0) as [Hc| Hc]. {
  rewrite sin_acos; [ | now apply pre_cos_bound in Hsc ].
  replace (1 - c²) with s² by lra.
  rewrite sqrt_Rsqr; [ easy | lra ].
}
rewrite sin_asin; [ easy | now apply pre_sin_bound in Hsc ].
Qed.

Theorem cos_angle_of_sin_cos : ∀ s c,
  s² + c² = 1
  → cos (angle_of_sin_cos s c) = c.
Proof.
intros * Hsc.
unfold angle_of_sin_cos.
destruct (Rlt_dec s 0) as [Hs| Hs]. {
  destruct (Rlt_dec c 0) as [Hc| Hc]. {
    rewrite cos_minus.
    rewrite cos_2PI, sin_2PI, Rmult_1_l, Rmult_0_l, Rplus_0_r.
    apply cos_acos.
    now apply pre_cos_bound in Hsc.
  }
  rewrite cos_plus.
  rewrite cos_2PI, sin_2PI, Rmult_1_r, Rmult_0_r, Rminus_0_r.
  rewrite cos_asin; [ | now apply pre_sin_bound in Hsc ].
  replace (1 - s²) with c² by lra.
  apply Rnot_lt_le in Hc.
  now rewrite sqrt_Rsqr.
}
destruct (Rlt_dec c 0) as [Hc| Hc]. {
  rewrite cos_acos; [ easy | ].
  now apply pre_cos_bound in Hsc.
}
rewrite cos_asin; [ | now apply pre_sin_bound in Hsc ].
replace (1 - s²) with c² by lra.
apply Rnot_lt_le in Hc.
now rewrite sqrt_Rsqr.
Qed.
