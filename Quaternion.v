(* c'est bien, les quaternions, mais avant, il faut
   que j'utilise ring-like sur les matrices *)

From Stdlib Require Import Utf8.

Require Import RingLike.Core.

Declare Scope vec_scope.
Declare Scope quat_scope.
Delimit Scope vec_scope with vec.
Delimit Scope quat_scope with quat.

Class vector3 T := mk_v { v_x : T; v_y : T; v_z : T }.
Class quaternion T := mk_q { q_re : T; q_im : vector3 T }.

Bind Scope vec_scope with vector3.
Bind Scope quat_scope with quaternion.

Arguments mk_v {T} (v_x v_y v_z)%_L.
Arguments mk_q {T} q_re%_L q_im%_vec.
Arguments v_x {T} v%_vec : rename.
Arguments v_y {T} v%_vec : rename.
Arguments v_z {T} v%_vec : rename.
Arguments q_re {T} q%_quat : rename.
Arguments q_im {T} q%_quat : rename.

Section a.

Context {T : Type}.
Context {ro : ring_like_op T}.

Definition vec3_add a b :=
  mk_v
    (v_x a + v_x b)
    (v_y a + v_y b)
    (v_z a + v_z b).

Definition quat_add a b :=
  mk_q
    (q_re a + q_re b)
    (vec3_add (q_im a) (q_im b)).

Definition quat_mul (u v : quaternion T) :=
  let '(mk_q a (mk_v b c d)) := u in
  let '(mk_q a' (mk_v b' c' d')) := v in
  mk_q
    (a * a' - b * b' - c * c' - d * d')
    (mk_v
      (a * b' + b * a' + c * d' - d * c')
      (a * c' - b * d' + c * a' + d * b')
      (a * d' + b * c' - c * b' + d * a')).

End a.

Notation "a +ℹ b +𝐣 c +𝐤 d" :=
  (mk_q a (mk_v b c d)) (at level 50, b, c, d at level 0) : quat_scope.

Notation "a * b" := (quat_mul a b) : quat_scope.

From Stdlib Require Import ZArith.
Require Import RingLike.Z_algebra.
Open Scope Z_scope.

Compute (
  let i := mk_q 0 (mk_v 1 0 0) in
  let j := mk_q 0 (mk_v 0 1 0) in
  let k := mk_q 0 (mk_v 0 0 1) in
  (j * k)%quat).

