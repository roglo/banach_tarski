(* Banach-Tarski paradox. *)

From Stdlib Require Import Utf8 List.
From Stdlib Require Import Reals Nsatz.
Import ListNotations.

Require Import a.Misc a.Words a.Normalize a.Reverse a.Matrix a.Pset a.Orbit.
Require Import a.Partition.

Class sel_model {A} := mkos { os_fun : A → A }.

...

Definition orbit_by_seq_of e {os : sel_model} :=
  mkset (λ p, ∃ n, (mat_of_path (repeat e (S n)) * os_fun p)%vec = p).

Definition D :=
  mkset
    (λ p, ∃ el p₁, same_orbit p p₁
     ∧ norm_list el ≠ [] ∧ (mat_of_path el * p₁)%vec = p₁).

Arguments D : simpl never.

Definition M {os : sel_model} :=
  mkset (λ p, p ∈ ball ∖ D ∧ p = os_fun p).
Definition SS {os : sel_model} e :=
  mkset
    (λ p,
     p ∈ ball ∖ D ∧
     ∃ el el₁,
       norm_list el = e :: el₁ ∧ fold_right rotate (os_fun p) el = p).
Definition G {os : sel_model} :=
  mkset (λ p, p ∈ (ball ∖ D) ∩ orbit_by_seq_of ạ⁻¹).

Opaque M SS G.

Definition rot e (E : set vector) :=
  mkset (λ p, rotate (negf e) p ∈ E).

Theorem empty_set_not_full_set : ∀ f os, os = mkos _ f →
  ∀ e p, p ∈ M → p ∈ SS e → False.
Proof.
intros f os Hos e p He Hs; subst os.
destruct He as (Hinf & He); simpl in He.
destruct Hs as (Hjnf & el & el₁ & Hn & Hs); simpl in Hs.
rewrite rotate_vec_mul in Hs.
rewrite <- He in Hs.
simpl in Hinf.
destruct Hinf as (Hle1 & Hinf).
apply Hinf; clear Hinf.
exists el, p.
now rewrite Hn.
Qed.

Theorem start_with_same : ∀ f os, os = mkos _ f →
  ∀ e₁ e₂ p, p ∈ SS e₁ → p ∈ SS e₂ → e₁ = e₂.
Proof.
intros f os Hos (ti, di) (tj, dj) p Hsi Hsj; subst os.
destruct Hsi as (Hinf & eli & eli₁ & Hni & Hsi); simpl in Hsi.
destruct Hsj as (Hjnf & elj & elj₁ & Hnj & Hsj); simpl in Hsj.
rewrite rotate_vec_mul in Hsi, Hsj.
eapply rotate_rev_path in Hsj.
destruct ti, tj. {
  destruct di, dj; [ easy | exfalso | exfalso | easy ]. {
    eapply not_in_fixpoints_one_path; try eassumption. {
      intros el Hn.
      destruct Hinf as (Hps, Hnpd).
      intros H; apply Hnpd; clear Hnpd.
      rewrite rotate_vec_mul in H.
      now exists el, p.
    } {
      rewrite <- rev_path_norm_list, Hnj.
      now rewrite rev_path_cons, rev_path_single.
    }
    easy.
  }
  eapply not_in_fixpoints_one_path; try eassumption. {
    intros el Hn.
    destruct Hinf as (Hps, Hnpd).
    intros H; apply Hnpd.
    rewrite rotate_vec_mul in H.
    now exists el, p.
  } {
    rewrite <- rev_path_norm_list, Hnj.
    now rewrite rev_path_cons, rev_path_single.
  }
  easy.
} {
  exfalso.
  eapply not_in_fixpoints_one_path; try eassumption. {
    intros el Hn.
    destruct Hinf as (Hps, Hnpd).
    intros H; apply Hnpd.
    rewrite rotate_vec_mul in H.
    now exists el, p.
  } {
    rewrite <- rev_path_norm_list, Hnj.
    now rewrite rev_path_cons, rev_path_single.
  }
  easy.
} {
  exfalso.
  eapply not_in_fixpoints_one_path; try eassumption. {
    intros el Hn.
    destruct Hinf as (Hps, Hnpd).
    intros H; apply Hnpd.
    rewrite rotate_vec_mul in H.
    now exists el, p.
  } {
    rewrite <- rev_path_norm_list, Hnj.
    now rewrite rev_path_cons, rev_path_single.
  }
  easy.
}
destruct di, dj; [ easy | exfalso | exfalso | easy ]. {
  eapply not_in_fixpoints_one_path; try eassumption. {
    intros el Hn.
    destruct Hinf as (Hps, Hnpd).
    intros H; apply Hnpd.
    rewrite rotate_vec_mul in H.
    now exists el, p.
  } {
    rewrite <- rev_path_norm_list, Hnj.
    now rewrite rev_path_cons, rev_path_single.
  }
  easy.
} {
  eapply not_in_fixpoints_one_path; try eassumption. {
    intros el Hn.
    destruct Hinf as (Hps, Hnpd).
    intros H; apply Hnpd.
    rewrite rotate_vec_mul in H.
    now exists el, p.
  } {
    rewrite <- rev_path_norm_list, Hnj.
    now rewrite rev_path_cons, rev_path_single.
  }
  easy.
}
Qed.

Theorem not_start_with_rot :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ e p, p ∈ SS e → p ∈ rot e (SS (negf e)) → False.
Proof.
intros f (Hoe, Ho) os Hos e p Hs Hr; simpl in Hr; subst os.
destruct Hs as (Hnf & el & el₁ & Hn & Hs); simpl in Hs.
destruct Hr as (Hrnf & elr & elr₁ & Hnr & Hsr); simpl in Hsr.
assert (Hr : f p = f (rotate (negf e) p)). {
  apply Hoe.
  exists (negf e :: []).
  now rewrite <- rotate_vec_mul.
}
rewrite <- Hr in Hsr.
rewrite rotate_vec_mul in Hsr.
eapply rotate_rev_path in Hsr.
rewrite <- rotate_vec_mul in Hsr.
rewrite <- fold_right_single, <- fold_right_app in Hsr.
rewrite <- Hsr in Hs.
rewrite <- fold_right_app in Hs.
rewrite rotate_vec_mul in Hs.
rewrite rotate_rotate_norm in Hs.
pose proof is_normal [] el (rev_path elr ++ [negf e]) as H.
do 2 rewrite app_nil_l in H.
rewrite <- H in Hs; clear H.
rewrite <- is_normal in Hs.
rewrite <- rev_path_norm_list in Hs.
rewrite Hnr in Hs.
rewrite <- rotate_rotate_norm in Hs.
rewrite rev_path_cons in Hs.
rewrite rev_path_single in Hs.
rewrite <- app_assoc in Hs.
simpl in Hs.
rewrite negf_involutive in Hs.
rewrite app_assoc in Hs.
rewrite rotate_cancel_in in Hs.
rewrite app_nil_r in Hs.
destruct Hnf as (Hps, Hnpd).
apply Hnpd.
exists (norm_list el ++ rev_path elr₁), p.
split; [ easy | ].
split; [ | easy ].
intros H.
apply norm_list_app_is_nil in H. {
  apply -> rev_path_eq_eq in H.
  rewrite H, Hn in Hnr.
  revert Hnr; apply norm_list_no_start2.
} {
  symmetry; apply norm_list_idemp.
}
rewrite <- rev_path_norm_list; eapply norm_list_is_cons in Hnr.
now rewrite Hnr.
Qed.

Theorem decompose_2a_contrad_case :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ p, p ∈ M ∪ SS ạ ∪ G
  → p ∈ rot ạ (SS ạ⁻¹ ∖ G)
  → False.
Proof.
intros * (Hoe, Ho) * Hos * Hi Hj.
assert (Hfr : f (rotate ạ⁻¹ p) = f p). {
  apply Hoe; exists (ạ :: []); simpl.
  rewrite <- rotate_vec_mul; simpl.
  apply rotate_neg_rotate.
}
destruct Hj as (Hs & Hb); simpl in Hs, Hb; apply Hb; clear Hb.
split; [ now destruct Hs | ].
destruct Hi as [[Hi| Hi] | Hi]. {
  destruct Hs as (Hrnf & el & el₁ & Hn & Hr).
  destruct Hi as (Hnf & Hp); subst os; simpl in Hp.
  exists O; simpl.
  rewrite Hfr, <- Hp.
  apply mat_of_path_single.
} {
  eapply not_start_with_rot in Hi; try eassumption; [ easy | ].
  now split.
} {
  destruct Hi as (Hnf, Hoo).
  destruct Hoo as (n, Hoo).
  unfold orbit_by_seq_of.
  remember S as g; subst os; simpl in Hoo; simpl; subst g.
  rewrite Hfr; simpl.
  exists (S n).
  rewrite mat_of_path_cons, mat_vec_mul_assoc, Hoo.
  rewrite <- mat_of_path_single.
  unfold mat_of_path; simpl.
  now rewrite mat_mul_id_r.
}
Qed.

Theorem r_decomposed_5 :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition (ball ∖ D) [M; SS ạ; SS ạ⁻¹; SS ḅ; SS ḅ⁻¹].
Proof.
intros f (Hoe, Ho) os Hos; subst os.
split. {
  intros p.
  split. {
    intros Hnf.
    unfold set_union_list; simpl; unfold set_union.
    destruct (vec_eq_dec p (f p)) as [H₁| H₁]; [ left; now split | ].
    right.
    pose proof Ho p as H.
    destruct H as (el, Hel).
    remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
    destruct (list_nil_app_dec el₁) as [H₂| (e & el₂ & H₂)]; subst el₁. {
      rewrite rotate_rotate_norm, H₂ in Hel.
      now rewrite mat_vec_mul_id in Hel.
    }
    destruct e as (t, d); destruct t, d. {
      left; split; [ easy | ].
      exists (rev_path el), (rev_path el₂).
      rewrite rotate_vec_mul.
      split; [ | now apply rotate_rev_path ].
      now rewrite <- rev_path_norm_list, H₂, rev_path_app.
    } {
      right; left; split; [ easy | ].
      exists (rev_path el), (rev_path el₂).
      rewrite rotate_vec_mul.
      split; [ | now apply rotate_rev_path ].
      now rewrite <- rev_path_norm_list, H₂, rev_path_app.
    } {
      right; right; left; split; [ easy | ].
      exists (rev_path el), (rev_path el₂).
      rewrite rotate_vec_mul.
      split; [ | now apply rotate_rev_path ].
      now rewrite <- rev_path_norm_list, H₂, rev_path_app.
    } {
      right; right; right; left; split; [ easy | ].
      exists (rev_path el), (rev_path el₂).
      rewrite rotate_vec_mul.
      split; [ | now apply rotate_rev_path ].
      now rewrite <- rev_path_norm_list, H₂, rev_path_app.
    }
  }
  intros Hul.
  unfold set_union_list in Hul; simpl in Hul; unfold set_union in Hul.
  destruct Hul as [Hul| [Hul| [Hul| [Hul| [Hul| Hul]]]]]. {
    destruct Hul as (Hnf, Hul); simpl in Hul.
    now apply Hnf.
  } {
    destruct Hul as (Hnf, Hul); simpl in Hul.
    now apply Hnf.
  } {
    destruct Hul as (Hnf, Hul); simpl in Hul.
    now apply Hnf.
  } {
    destruct Hul as (Hnf, Hul); simpl in Hul.
    now apply Hnf.
  } {
    destruct Hul as (Hnf, Hul); simpl in Hul.
    now apply Hnf.
  }
  easy.
}
intros i j Hij p.
split; [ | easy ].
intros (Hi, Hj).
destruct i; [ simpl in Hi | ]. {
  destruct j; [ exfalso; now apply Hij | clear Hij ].
  destruct Hi as (Hinf & Hi); simpl in Hi.
  destruct j. {
    eapply empty_set_not_full_set; [ easy | | eassumption ].
    easy.
  }
  destruct j. {
    eapply empty_set_not_full_set; [ easy | | eassumption ].
    easy.
  }
  destruct j. {
    eapply empty_set_not_full_set; [ easy | | eassumption ].
    easy.
  }
  destruct j; [ | now destruct j ].
  eapply empty_set_not_full_set; [ easy | | eassumption ].
  easy.
}
destruct i; [ simpl in Hi | ]. {
  destruct j; [ clear Hij | ]. {
    eapply empty_set_not_full_set; [ easy | eassumption | eassumption ].
  }
  destruct j; [ exfalso; now apply Hij | clear Hij ].
  destruct j; [ simpl in Hj | ]. {
    eapply start_with_same in Hi; [ | easy | eassumption ].
    easy.
  }
  destruct j; [ simpl in Hj | ]. {
    eapply start_with_same in Hi; [ | easy | eassumption ].
    easy.
  }
  destruct j; [ simpl in Hj | now destruct j ].
  eapply start_with_same in Hi; [ | easy | eassumption ].
  easy.
}
destruct i; [ simpl in Hi | ]. {
  destruct j; [ clear Hij | ]. {
    eapply empty_set_not_full_set; [ easy | | ]; eassumption.
  }
  destruct j; [ simpl in Hj | ]. {
    eapply start_with_same in Hi; [ | easy | eassumption ].
    easy.
  }
  destruct j; [ exfalso; now apply Hij | clear Hij ].
  destruct j; [ simpl in Hj | ]. {
    eapply start_with_same in Hi; [ | easy | eassumption ].
    easy.
  }
  destruct j; [ simpl in Hj | now destruct j ].
  eapply start_with_same in Hi; [ | easy | eassumption ].
  easy.
}
destruct i; [ simpl in Hi | ]. {
  destruct j; [ clear Hij | ]. {
    eapply empty_set_not_full_set; [ easy | | ]; eassumption.
  }
  destruct j; [ simpl in Hj | ]. {
    eapply start_with_same in Hi; [ | easy | eassumption ].
    easy.
  }
  destruct j; [ simpl in Hj | ]. {
    eapply start_with_same in Hi; [ | easy | eassumption ].
    easy.
  }
  destruct j; [ exfalso; now apply Hij | clear Hij ].
  destruct j; [ simpl in Hj | now destruct j ].
  eapply start_with_same in Hi; [ | easy | eassumption ].
  easy.
}
destruct i; [ simpl in Hi | now destruct i ].
destruct j; [ clear Hij | ]. {
  eapply empty_set_not_full_set; [ easy | | ]; eassumption.
}
destruct j; [ simpl in Hj | ]. {
  eapply start_with_same in Hi; [ | easy | eassumption ].
  easy.
}
destruct j; [ simpl in Hj | ]. {
  eapply start_with_same in Hi; [ | easy | eassumption ].
  easy.
}
destruct j; [ simpl in Hj | ]. {
  eapply start_with_same in Hi; [ | easy | eassumption ].
  easy.
}
destruct j; [ exfalso; now apply Hij | now destruct j ].
Qed.

Theorem r_decomposed_4 :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition (ball ∖ D)
      [M ∪ SS ạ ∪ G; SS ạ⁻¹ ∖ G; SS ḅ; SS ḅ⁻¹].
Proof.
intros f HoeHo os Hos.
pose proof r_decomposed_5 f HoeHo os Hos as H.
destruct HoeHo as (Hoe, Ho).
eapply is_partition_group_first_2_together in H.
apply is_partition_union_sub; [ easy | ].
intros p bm; subst os.
destruct bm as (Ha & n & Hr); remember S as g; simpl in Hr; subst g.
split; [ easy | ].
exists (repeat ạ⁻¹ (S n)), (repeat ạ⁻¹ n).
rewrite rotate_vec_mul.
split; [ apply norm_list_repeat | easy ].
Qed.

Theorem no_fixpoint_after_rotate : ∀ p e, p ∉ D → rotate e p ∉ D.
Proof.
intros * His Hr; apply His; clear His.
unfold D in Hr; simpl in Hr.
unfold D; simpl.
destruct Hr as (el & p₁ & Hso & Hn & Hr).
exists el, p₁.
split; [ | easy ].
destruct Hso as (el₁ & Hso).
exists (el₁ ++ [e]).
now rewrite mat_of_path_app, mat_vec_mul_assoc, mat_of_path_single.
Qed.

Theorem r_decomposed_2 :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → ∀ e,
    is_partition (ball ∖ D) [SS e; rot e (SS (negf e))].
Proof.
intros f (Hoe, Ho) os Hos e; subst os.
split. {
  intros p.
  split. {
    intros Hnf.
    unfold set_union_list; simpl; unfold set_union.
    pose proof Ho p as H.
    apply same_orbit_sym in H.
    destruct H as (el, Hel).
    remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
    destruct el₁ as [| e₁]. {
      rewrite rotate_rotate_norm, Hel₁ in Hel; simpl in Hel.
      rewrite mat_vec_mul_id in Hel.
      clear Hel₁.
      right; left.
      unfold rot.
      split. {
        split. {
          destruct Hnf as (His, _).
          now apply in_ball_after_rotate.
        }
        destruct Hnf as (Hps, Hnpd).
        now apply no_fixpoint_after_rotate.
      }
      exists (negf e :: []), [].
      split; [ easy | simpl ].
      assert (H : f p = f (rotate (negf e) p)). {
        apply Hoe.
        exists (negf e :: []).
        apply mat_of_path_single.
      }
      now rewrite <- H, Hel.
    }
    destruct (free_elem_dec e e₁) as [H₁| H₁]; [ subst e₁ | ]. {
      left; split; [ easy | ].
      exists el, el₁.
      rewrite rotate_vec_mul.
      now split.
    }
    right; left.
    unfold rot.
    split. {
      split. {
        destruct Hnf as (His, _).
        now apply in_ball_after_rotate.
      }
      destruct Hnf.
      now apply no_fixpoint_after_rotate.
    }
    assert (H : f p = f (rotate (negf e) p)). {
      apply Hoe.
      exists (negf e :: []).
      apply mat_of_path_single.
    }
    simpl; rewrite <- H.
    exists (negf e :: el), (e₁ :: el₁); simpl.
    rewrite rotate_vec_mul.
    rewrite Hel₁, Hel.
    destruct (letter_opp_dec (negf e) e₁) as [H₂| H₂]; [ | now split ].
    exfalso.
    apply letter_opp_negf in H₂.
    now apply H₁, negf_eq_eq.
  }
  intros Hul.
  destruct Hul as [(H, _)| [(H, _)| Hul]]; [ easy | | easy ].
  split. {
    destruct H as (His, _).
    apply in_ball_after_rotate with (e := e) in His.
    now rewrite rotate_rotate_neg in His.
  } {
    destruct H as (Hs, Hnp).
    apply no_fixpoint_after_rotate with (e := e) in Hnp.
    now rewrite rotate_rotate_neg in Hnp.
  }
}
intros i j Hij p.
split; [ | easy ].
intros (Hi, Hj).
destruct i; [ simpl in Hi | ]. {
  destruct j; [ exfalso; now apply Hij | clear Hij ].
  destruct j; [ | now destruct j ].
  simpl in Hj.
  eapply not_start_with_rot in Hi; try eassumption; [ | easy ].
  easy.
}
destruct i; [ simpl in Hi | now destruct i ].
destruct j; [ simpl in Hj; clear Hij | ].
eapply not_start_with_rot in Hj; try eassumption; [ | easy ]. {
  easy.
} {
  destruct j; [ now apply Hij | now destruct j ].
}
Qed.

Add Parametric Morphism {A} : (@List.nth (set A))
  with signature eq ==> eq ==> set_eq ==> set_eq
  as nth_set_morph.
Proof.
intros i l a b Hab.
revert i.
induction l as [| y]; intros; [ destruct i; apply Hab | ].
destruct i; simpl; [ easy | apply IHl ].
Qed.

Theorem rev_path_repeat : ∀ e n, rev_path (repeat e n) = repeat (negf e) n.
Proof.
intros e n.
induction n; [ easy | simpl ].
rewrite rev_path_cons, rev_path_single, IHn.
apply app_repeat_diag.
Qed.

Theorem r_decomposed_2_a :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition (ball ∖ D) [M ∪ SS ạ ∪ G; rot ạ (SS ạ⁻¹ ∖ G)].
Proof.
intros f (Hoe, Ho) os Hos.
split. {
  intros p.
  assert (Hfr : f (rotate ạ⁻¹ p) = f p). {
    apply Hoe; exists (ạ :: []).
    rewrite mat_of_path_single.
    apply rotate_neg_rotate.
  }
  split. {
    intros Hnf.
    unfold set_union_list; simpl; unfold set_union.
    pose proof Ho p as H.
    apply same_orbit_sym in H.
    destruct H as (el, Hel).
    remember (norm_list el) as el₁ eqn:Hel₁; symmetry in Hel₁.
    destruct el₁ as [| e₁]. {
      rewrite rotate_rotate_norm, Hel₁ in Hel; simpl in Hel.
      rewrite mat_vec_mul_id in Hel.
      clear el Hel₁.
      left; left; left.
      split; [ easy | subst os; now symmetry ].
    }
    destruct e₁ as (t, d); destruct t. {
      destruct d. {
        destruct (EM (p ∈ G)) as [HB| HB]; [ left; now right | ].
        right; left; simpl.
        split. {
          split. {
            destruct Hnf as (His, Hnf).
            split; [ now apply in_ball_after_rotate | ].
            now apply no_fixpoint_after_rotate.
          }
          subst os; simpl.
          rewrite Hfr.
          exists (ạ⁻¹ :: el), (norm_list el).
          split; [ now simpl; rewrite Hel₁ | ].
          now simpl; rewrite rotate_vec_mul; f_equal.
        }
        simpl; intros (Haf & n & Hoo); apply HB; clear HB.
        split; [ easy | ].
        unfold orbit_by_seq_of in Hoo |-*; simpl.
        remember S as g; subst os; simpl in Hoo |-*; subst g.
        rewrite Hfr in Hoo; simpl in Hoo.
        apply f_equal with (f := rotate (FE la false)) in Hoo.
        rewrite <- rotate_vec_mul in Hoo; simpl in Hoo.
        do 2 rewrite rotate_rotate_neg in Hoo.
        rewrite rotate_vec_mul in Hoo.
        destruct n; [ | now exists n ].
        simpl in Hoo.
        rewrite mat_vec_mul_id in Hoo.
        rewrite Hoo in Hel.
        destruct Hnf as (His & Hoh).
        exfalso; apply Hoh.
        exists el, p.
        now rewrite Hel₁.
      }
      left; left; right.
      split; [ easy | ].
      exists el, el₁; subst os.
      rewrite rotate_vec_mul.
      now split.
    }
    right; left.
    split; simpl. {
      split. {
        destruct Hnf as (His & Hnf).
        split; [ now apply in_ball_after_rotate | ].
        now apply no_fixpoint_after_rotate.
      }
      subst os; simpl; rewrite Hfr.
      exists (ạ⁻¹ :: el), (norm_list el).
      split; [ now simpl; rewrite Hel₁ | ].
      now simpl; rewrite rotate_vec_mul; f_equal.
    }
    intros (Hnf₂, Hoo).
    subst os; simpl in Hoo.
    unfold orbit_by_seq_of in Hoo; simpl in Hoo.
    rewrite Hfr in Hoo.
    destruct Hoo as (n, Hr).
    apply f_equal with (f := rotate (FE la false)) in Hr.
    rewrite <- rotate_vec_mul in Hr; simpl in Hr.
    do 2 rewrite rotate_rotate_neg in Hr.
    rewrite rotate_vec_mul in Hr.
    destruct n. {
      simpl in Hr; rewrite mat_vec_mul_id in Hr.
      rewrite Hr in Hel.
      destruct Hnf as (His, Hoh).
      now apply Hoh; exists el, p; rewrite Hel₁.
    }
    apply rotate_rev_path in Hr.
    rewrite <- Hr in Hel.
    rewrite <- mat_vec_mul_assoc in Hel.
    rewrite <- mat_of_path_app in Hel.
    destruct Hnf as (His, Hoh).
    apply Hoh.
    exists (el ++ rev_path (repeat ạ⁻¹ (S n))), p.
    split; [ easy | ].
    split; [ | easy ].
    replace el with ([] ++ el) by easy.
    rewrite <- app_assoc, <- is_normal, Hel₁, app_nil_l.
    rewrite rev_path_repeat.
    remember norm_list as g; remember S as h; simpl; subst g h.
    rewrite app_of_cons, app_assoc.
    intros H.
    eapply norm_list_app_is_nil in H. {
      simpl in H.
      apply f_equal with (f := rev_path) in H.
      rewrite rev_path_involutive in H.
      rewrite <- app_repeat_diag in H.
      now rewrite rev_path_app in H; simpl in H.
    } {
      unfold app; rewrite <- Hel₁; symmetry.
      apply norm_list_idemp.
    }
    symmetry; apply norm_list_repeat.
  }
  intros HE.
  simpl in HE.
  destruct HE as [[[HE| HE]| HE]| [HE| HE]]; try now destruct HE.
  destruct HE as (((His & Hoo) & HE) & HB).
  split. {
    apply in_ball_after_rotate with (e := ạ) in His.
    now rewrite rotate_rotate_neg in His.
  } {
    apply no_fixpoint_after_rotate with (e := ạ) in Hoo.
    now rewrite rotate_rotate_neg in Hoo.
  }
}
intros i j Hij p.
assert (Hfr : f (rotate ạ⁻¹ p) = f p). {
  apply Hoe; exists (ạ :: []).
  rewrite mat_of_path_single.
  apply rotate_neg_rotate.
}
split; [ | easy ].
intros (Hi, Hj).
destruct i; [ simpl in Hi | ]. {
  destruct j; [ exfalso; now apply Hij | clear Hij ].
  destruct j; [ simpl in Hj | now destruct j ].
  eapply decompose_2a_contrad_case; unfold set_union; try eassumption.
  easy.
}
destruct i; [ simpl in Hi | now destruct i ].
destruct j. {
  eapply decompose_2a_contrad_case; unfold set_union; try eassumption.
  easy.
}
destruct j; [ now apply Hij | now destruct j ].
Qed.

Theorem r_decomposed_2_b :
  ∀ f, orbit_selector f
  → ∀ os, os = mkos _ f
  → is_partition (ball ∖ D) [SS ḅ; rot ḅ (SS ḅ⁻¹)].
Proof.
intros.
eapply r_decomposed_2; eassumption.
Qed.

Theorem rot_set_map_mul : ∀ e E,
  (rot e E = set_map (mat_vec_mul (mat_of_elem e)) E)%S.
Proof.
intros; intros v.
split; intros H. {
  exists (rotate (negf e) v).
  split; [ easy | unfold rotate ].
  rewrite <- mat_vec_mul_assoc.
  now rewrite mat_of_elem_mul_negf_r, mat_vec_mul_id.
}
destruct H as (u & Hu & Hv).
rewrite <- Hv; simpl; unfold rotate.
rewrite <- mat_vec_mul_assoc.
now rewrite mat_of_elem_mul_negf_l, mat_vec_mul_id.
Qed.
