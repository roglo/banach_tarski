(* Cauchy-Schwarz in any dimension *)
(* Compiled with Coq 8.6 *)
Require Import Utf8 List Reals Psatz.
Import ListNotations.

Require Import SummationR.

Theorem fold_Rminus : ∀ x y, (x + - y = x - y)%R.
Proof. intros. now fold (Rminus x y). Qed.

Theorem Rplus_shuffle0 : ∀ n m p : R, (n + m + p)%R = (n + p + m)%R.
Proof.
intros.
rewrite Rplus_comm, <- Rplus_assoc.
f_equal; apply Rplus_comm.
Qed.
