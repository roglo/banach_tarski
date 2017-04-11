(* Banach-Tarski paradox. *)
(* Coq v8.6 *)

Require Import Utf8 List.
Import ListNotations.
Require Import Reals Psatz.

Require Import MiscReals Words Normalize Reverse Matrix.

Definition rotate_param e '(a, b, c, N) :=
  match e with
  | ạ => ((3 * a)%Z, (b - 2 * c)%Z, (4 * b + c)%Z, S N)
  | ạ⁻¹ => ((3 * a)%Z, (b + 2 * c)%Z, (- 4 * b + c)%Z, S N)
  | ḅ => ((a - 4 * b)%Z, (b + 2 * a)%Z, (3 * c)%Z, S N)
  | ḅ⁻¹ => ((a + 4 * b)%Z, (b - 2 * a)%Z, (3 * c)%Z, S N)
  end.

Arguments Z.mul _ _ : simpl nomatch.

Theorem rotate_param_rotate : ∀ el x y z n a b c N,
  fold_right rotate_param (x, y, z, n) el = (a, b, c, N)
  ↔ fold_right rotate (V (IZR x / 3^n) (IZR y * √2 / 3^n) (IZR z / 3^n)) el =
      V (IZR a / 3^N) (IZR b*√2 / 3^N) (IZR c / 3^N)
    ∧ N = (n + length el)%nat.
Proof.
intros el x y z n a₁ b₁ c₁ N₁.
split.
 intros Hr.
 simpl in Hr; simpl.
 revert a₁ b₁ c₁ N₁ Hr.
 induction el as [| (t, d)]; intros.
  simpl; simpl in Hr; rewrite Nat.add_0_r.
  injection Hr; intros; subst; simpl.
  split; reflexivity.

  simpl in Hr; simpl.
  remember (fold_right rotate_param (x, y, z, n) el) as rp eqn:Hrp.
  symmetry in Hrp.
  destruct rp as (((a, b), c), N).
  pose proof IHel _ _ _ _ (eq_refl _) as H.
  destruct H as (H, HN).
  erewrite H.
  simpl in Hr; simpl; unfold Rdiv.
  destruct t, d; injection Hr; clear Hr; intros; subst a₁ b₁ c₁ N₁ N; simpl.
   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   unfold Rdiv.
   rewrite Rmult5_sqrt2_sqrt5; [ f_equal; lra | lra ].

   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   unfold Rdiv.
   rewrite Rmult5_sqrt2_sqrt5; [ f_equal; lra | lra ].

   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   unfold Rdiv.
   rewrite Rmult5_sqrt2_sqrt5; [ f_equal; lra | lra ].

   split; [ | rewrite Nat.add_succ_r; reflexivity ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   rewrite Rinv_mult_distr; [ | lra | apply pow_nonzero; lra ].
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   unfold Rdiv.
   rewrite Rmult5_sqrt2_sqrt5; [ f_equal; lra | lra ].

 intros Hr.
 revert x y z n a₁ b₁ c₁ N₁ Hr.
 induction el as [| e] using rev_ind; intros.
  simpl in Hr; simpl; rewrite Nat.add_0_r in Hr.
  destruct Hr as (Hr, Hn); subst N₁.
  unfold Rdiv in Hr.
  injection Hr; intros Hz Hy Hx.
  f_equal; f_equal; f_equal.
   apply Rmult_eq_reg_r, eq_IZR in Hx; [ assumption | ].
   apply Rinv_neq_0_compat, pow_nonzero; lra.

   apply Rmult_eq_reg_r in Hy.
    apply Rmult_eq_reg_r in Hy; [ | apply sqrt2_neq_0 ].
    apply eq_IZR; assumption.

    apply Rinv_neq_0_compat, pow_nonzero; lra.

   apply Rmult_eq_reg_r, eq_IZR in Hz; [ assumption | ].
   apply Rinv_neq_0_compat, pow_nonzero; lra.

  simpl in Hr; destruct Hr as (Hr, HN).
  rewrite app_length, Nat.add_1_r in HN.
  rewrite <- Nat.add_succ_comm in HN.
  simpl; destruct e as (t, d).
  rewrite fold_right_app; simpl.
  rewrite fold_right_app in Hr; simpl in Hr.
  destruct t, d.
   apply IHel; split; [ | assumption ].
   rewrite <- Hr; simpl.
   unfold Rdiv.
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
   rewrite plus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   f_equal; f_equal.
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].

   apply IHel; split; [ | assumption ].
   rewrite <- Hr; simpl.
   unfold Rdiv.
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   progress repeat rewrite mult_IZR.
   rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
   rewrite minus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   f_equal; f_equal.
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].

   apply IHel; split; [ | assumption ].
   rewrite <- Hr; simpl.
   unfold Rdiv.
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   progress repeat rewrite mult_IZR.
   rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
   rewrite plus_IZR, minus_IZR.
   progress repeat rewrite mult_IZR.
   f_equal; f_equal.
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].

   apply IHel; split; [ | assumption ].
   rewrite <- Hr; simpl.
   unfold Rdiv.
   progress repeat rewrite Rmult_1_l.
   progress repeat rewrite Rmult_0_l.
   progress repeat rewrite Rplus_0_l.
   progress repeat rewrite Rplus_0_r.
   progress repeat rewrite <- Rmult_assoc.
   progress repeat rewrite mult_IZR.
   rewrite Rmult5_sqrt2_sqrt5; [ | lra ].
   rewrite minus_IZR, plus_IZR.
   progress repeat rewrite mult_IZR.
   f_equal; f_equal.
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
    rewrite Rinv_mult_distr; [ lra | lra | apply pow_nonzero; lra ].
Qed.

Theorem rotate_prop : ∀ p t d el el₁ el₂ e a b c,
  t = lb ∧ p = (1, 0, 0, O)%Z ∨
  t = la ∧ p = (0, 0, 1, O)%Z
  → el₁ = el₂ ++ [FE t d]
  → el = e :: el₁
  → norm_list el = el
  → fold_right rotate_param p el₁ = (a, b, c, length el₁)
  → (b mod 3)%Z ≠ 0%Z
  → match e with
    | ạ => ((b - 2 * c) mod 3)%Z ≠ 0%Z
    | ạ⁻¹ => ((b + 2 * c) mod 3)%Z ≠ 0%Z
    | ḅ => ((b + 2 * a) mod 3)%Z ≠ 0%Z
    | ḅ⁻¹ => ((b - 2 * a) mod 3)%Z ≠ 0%Z
    end.
Proof.
intros p t d el el₁ el₂ e a b c.
intros Htp Hel₁ Hel Hn Hp Hb'.
rewrite Hel₁ in Hp at 2; simpl in Hp.
remember (length el₂) as len eqn:Hlen.
destruct el₂ as [| e₁].
 simpl in Hlen; subst len; simpl in Hel.
 subst el₁; simpl in Hp.
 destruct Htp as [(Ht, Hq)| (Ht, Hq)]; subst t p.
  destruct d; injection Hp; intros; subst.
   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_no_start.

   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_no_start.

  destruct d; injection Hp; intros; subst.
   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_no_start.

   destruct e as (t₁, d₁); destruct t₁, d₁; intros H; try discriminate H.
   revert Hn; apply norm_list_no_start.

 rewrite Hel₁ in Hel; simpl in Hel.
 generalize Hn; intros H₂.
 do 2 rewrite app_comm_cons in Hel.
 rewrite Hel in H₂.
 apply norm_list_app_diag in H₂.
 destruct len; [ discriminate Hlen | ].
 simpl in Hlen; apply eq_add_S in Hlen.
 rewrite Hel₁, fold_right_app in Hp.
 simpl in Hp.
 remember (rotate_param (FE t d) p) as p₁ eqn:Hp₁.
 remember (fold_right rotate_param p₁ el₂) as p' eqn:Hp'.
 symmetry in Hp'.
 destruct p' as (((a', b'), c'), N').
 simpl in Hp.
 destruct e₁ as (t₁, d₁); destruct t₁, d₁.
  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
   remember (b' + 2 * c' + 2 * (-4 * b' + c') + 3 * b' * 3)%Z as x eqn:Hx.
   ring_simplify in Hx; subst x.
   replace 4%Z with (2 * 2)%Z by reflexivity.
   rewrite <- Z.mul_assoc, <- Z.mul_add_distr_l.
   intros H; apply Hb'.
   apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
   apply Z.gauss in H; [ | reflexivity ].
   destruct H as (k, H); rewrite H.
   apply Z.mod_mul; intros; discriminate.

   exfalso; revert Hn; rewrite Hel.
   apply norm_list_no_start.

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   exfalso; revert Hn; rewrite Hel.
   apply norm_list_no_start.

   rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
   remember (b' - 2 * c' - 2 * (4 * b' + c') + 3 * b' * 3)%Z as x eqn:Hx.
   ring_simplify in Hx; subst x.
   replace 4%Z with (2 * 2)%Z by reflexivity.
   rewrite <- Z.mul_assoc, <- Z.mul_sub_distr_l.
   intros H; apply Hb'.
   apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
   apply Z.gauss in H; [ | reflexivity ].
   destruct H as (k, H); rewrite H.
   apply Z.mod_mul; intros; discriminate.

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub at 1; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub at 1; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
   remember (b' - 2 * a' - 2 * (a' + 4 * b') + 3 * b' * 3)%Z as x eqn:Hx.
   ring_simplify in Hx; subst x.
   replace 4%Z with (2 * 2)%Z by reflexivity.
   rewrite <- Z.mul_assoc, <- Z.mul_sub_distr_l.
   intros H; apply Hb'.
   apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
   apply Z.gauss in H; [ | reflexivity ].
   destruct H as (k, H); rewrite H.
   apply Z.mod_mul; intros; discriminate.

   exfalso; revert Hn; rewrite Hel.
   apply norm_list_no_start.

  injection Hp; clear Hp; intros HN Hc Hb Ha; subst a b c N'.
  destruct e as (t₂, d₂); destruct t₂, d₂.
   rewrite Z.mul_assoc, Z.mul_shuffle0.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   rewrite Z.mul_assoc, Z.mul_shuffle0.
   unfold Z.sub; rewrite Zopp_mult_distr_l.
   rewrite Z.mod_add; [ assumption | intros H; discriminate H ].

   exfalso; revert Hn; rewrite Hel.
   apply norm_list_no_start.

   rewrite <- Z.mod_add with (b := (3 * b')%Z); [ | intros; discriminate ].
   remember (b' + 2 * a' + 2 * (a' - 4 * b') + 3 * b' * 3)%Z as x eqn:Hx.
   ring_simplify in Hx; subst x.
   replace 4%Z with (2 * 2)%Z by reflexivity.
   rewrite <- Z.mul_assoc, <- Z.mul_add_distr_l.
   intros H; apply Hb'.
   apply Znumtheory.Zmod_divide in H; [ | intros; discriminate ].
   apply Z.gauss in H; [ | reflexivity ].
   destruct H as (k, H); rewrite H.
   apply Z.mod_mul; intros; discriminate.
Qed.

Theorem rotate_param_b_nonzero : ∀ p t d el el₁ a b c,
  t = lb ∧ p = (1, 0, 0, O)%Z ∨
  t = la ∧ p = (0, 0, 1, O)%Z
  → el = el₁ ++ [FE t d]
  → norm_list el = el
  → fold_right rotate_param p el = (a, b, c, length el)
  → (b mod 3 ≠ 0)%Z.
Proof.
intros p t d el el₁ a b c Htp Hel Hn Hu.
remember (length el₁) as len eqn:Hlen; symmetry in Hlen.
revert el el₁ d a b c Hel Hn Hu Hlen.
induction len as (len, IHlen) using lt_wf_rec; intros.
destruct len.
 apply length_zero_iff_nil in Hlen; subst el₁.
 subst el; simpl in Hu.
 destruct Htp as [(Ht, Hp)| (Ht, Hp)]; subst t p.
  destruct d; injection Hu; intros; subst; intros H; discriminate H.
  destruct d; injection Hu; intros; subst; intros H; discriminate H.

 destruct el₁ as [| e₁]; [ discriminate Hlen | simpl in Hlen ].
 apply eq_add_S in Hlen.
 rewrite <- app_comm_cons in Hel.
 remember (el₁ ++ [FE t d]) as el₂ eqn:Hel₁.
 generalize Hn; intros H₁; rewrite Hel in H₁.
 apply norm_list_cons in H₁.
 rewrite Hel in Hu; simpl in Hu.
 remember (fold_right rotate_param p el₂) as v eqn:Hp.
 symmetry in Hp.
 destruct v as (((a', b'), c'), N').
 assert (Hss : (len < S len)%nat) by apply Nat.lt_succ_diag_r.
 assert (N' = S len); [ | subst N' ].
  destruct e₁ as (t₁, d₁).
  rewrite Hel₁, app_length, Nat.add_1_r in Hu.
  destruct t₁, d₁; simpl in Hu; injection Hu; intros; subst; reflexivity.

  rewrite <- Hlen in Hp.
  replace (S (length el₁)) with (length el₂) in Hp.
   pose proof IHlen _ Hss _ _ _ _ _ _ Hel₁ H₁ Hp Hlen as Hb'; subst len.
   pose proof rotate_prop p t d el el₂ el₁ e₁ a' b' c' Htp Hel₁ Hel Hn Hp Hb'.
   destruct e₁ as (t₁, d₁).
   destruct t₁, d₁; injection Hu; intros; subst; assumption.

   subst; rewrite app_length, Nat.add_1_r; reflexivity.
Qed.

Theorem rotate_0_0_1_b_nonzero : ∀ w el el₁ d,
  el = el₁ ++ [FE la d]
  → norm_list el = el
  → w = (λ p, fold_right rotate p el)
  → ∃ a b c k,
    w (V 0 0 1) = V (IZR a/3^k) (IZR b*√2/3^k) (IZR c/3^k) ∧
    (b mod 3 ≠ 0)%Z.
Proof.
intros w el el₁ d Hel Hn Hw.
subst w.
remember (fold_right rotate_param (0, 0, 1, O)%Z el) as u eqn:Hu.
symmetry in Hu; destruct u as (((a, b), c), len).
generalize Hu; intros Hv.
apply rotate_param_rotate in Hv; simpl in Hv.
rewrite Rmult_0_l, Rdiv_0_l, Rdiv_1_r in Hv.
destruct Hv as (Hv, Hlen).
rewrite Hv.
exists a, b, c, len.
split; [ reflexivity | clear Hv ].
symmetry in Hlen.
rewrite Hel in Hlen; simpl in Hlen.
rewrite app_length, Nat.add_1_r in Hlen.
destruct len; [ discriminate Hlen | ].
apply eq_add_S in Hlen; subst len.
replace (S (length el₁)) with (length el) in Hu.
 eapply rotate_param_b_nonzero; try eassumption.
 right; split; reflexivity.

 subst; rewrite app_length, Nat.add_1_r; reflexivity.
Qed.

(* "we claim that w(1,0,0) has the form (a,b√2,c)/3^k where a,b,c are
    integers and b is not divisible by 3" (Stan Wagon) *)

Theorem rotate_1_0_0_b_nonzero : ∀ w el el₁ d,
  el = el₁ ++ [FE lb d]
  → norm_list el = el
  → w = (λ p, fold_right rotate p el)
  → ∃ a b c k,
    w (V 1 0 0) = V (IZR a/3^k) (IZR b*√2/3^k) (IZR c/3^k) ∧
    (b mod 3 ≠ 0)%Z.
Proof.
intros w el el₁ d Hel Hn Hw.
subst w.
remember (fold_right rotate_param (1, 0, 0, O)%Z el) as u eqn:Hu.
symmetry in Hu; destruct u as (((a, b), c), len).
generalize Hu; intros Hv.
apply rotate_param_rotate in Hv; simpl in Hv.
rewrite Rmult_0_l, Rdiv_0_l, Rdiv_1_r in Hv.
destruct Hv as (Hv, Hlen).
rewrite Hv.
exists a, b, c, len.
split; [ reflexivity | clear Hv ].
symmetry in Hlen.
rewrite Hel in Hlen; simpl in Hlen.
rewrite app_length, Nat.add_1_r in Hlen.
destruct len; [ discriminate Hlen | ].
apply eq_add_S in Hlen; subst len.
replace (S (length el₁)) with (length el) in Hu.
 eapply rotate_param_b_nonzero; try eassumption.
 left; split; reflexivity.

 subst; rewrite app_length, Nat.add_1_r; reflexivity.
Qed.

Theorem rotate_1_0_0_is_diff : ∀ el el₁ d,
  el = el₁ ++ [FE lb d]
  → norm_list el = el
  → fold_right rotate (V 1 0 0) el ≠ V 1 0 0.
Proof.
intros el el₁ d Hel Hn.
remember (λ p, fold_right rotate p el) as w eqn:Hw.
pose proof rotate_1_0_0_b_nonzero w el el₁ d Hel Hn Hw as H.
destruct H as (a, (b, (c, (k, (Hp, Hm))))).
rewrite Hw in Hp.
rewrite Hp; intros H.
injection H; intros Hc Hb Ha.
apply Rmult_integral in Hb.
destruct Hb as [Hb| Hb].
 apply Rmult_integral in Hb.
 destruct Hb as [Hb| Hb].
  apply eq_IZR_R0 in Hb; subst b; apply Hm; reflexivity.

  revert Hb; apply sqrt2_neq_0.

 apply Rmult_eq_compat_r with (r := (3 ^ k)%R) in Hb.
 rewrite Rinv_l in Hb; [ lra | apply pow_nonzero; lra ].
Qed.

Theorem rotate_0_0_1_is_diff : ∀ el el₁ d,
  el = el₁ ++ [FE la d]
  → norm_list el = el
  → fold_right rotate (V 0 0 1) el ≠ V 0 0 1.
Proof.
intros el el₁ d Hel Hn.
remember (λ p, fold_right rotate p el) as w eqn:Hw.
pose proof rotate_0_0_1_b_nonzero w el el₁ d Hel Hn Hw as H.
destruct H as (a, (b, (c, (k, (Hp, Hm))))).
rewrite Hw in Hp.
rewrite Hp; intros H.
injection H; intros Hc Hb Ha.
apply Rmult_integral in Hb.
destruct Hb as [Hb| Hb].
 apply Rmult_integral in Hb.
 destruct Hb as [Hb| Hb].
  apply eq_IZR_R0 in Hb; subst b; apply Hm; reflexivity.

  revert Hb; apply sqrt2_neq_0.

 apply Rmult_eq_compat_r with (r := (3 ^ k)%R) in Hb.
 rewrite Rinv_l in Hb; [ lra | apply pow_nonzero; lra ].
Qed.

Theorem rotate_non_empty_path_is_not_identity : ∀ el,
  norm_list el ≠ []
  → ∃ p, fold_right rotate p el ≠ p.
Proof.
intros * Hn.
remember (rev_path (norm_list el)) as el₁ eqn:Hel₁.
symmetry in Hel₁.
destruct el₁ as [| e₁ el₁]; [ now apply rev_path_is_nil in Hel₁ | ].
apply (f_equal rev_path) in Hel₁.
rewrite rev_path_involutive in Hel₁.
rewrite rev_path_cons, rev_path_single in Hel₁.
destruct e₁ as (t, d).
destruct t.
 apply rotate_0_0_1_is_diff in Hel₁; [ | apply norm_list_idemp ].
 exists (V 0 0 1).
 now rewrite rotate_rotate_norm.

 apply rotate_1_0_0_is_diff in Hel₁; [ | apply norm_list_idemp ].
 exists (V 1 0 0).
 now rewrite rotate_rotate_norm.
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
