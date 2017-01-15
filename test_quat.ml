(* testing quaternions *)
(*
ocaml -I +camlp5 camlp5r.cma
#use "test_quat.ml";
*)

type matrix =
  { a₁₁ : float; a₁₂ : float; a₁₃ : float;
    a₂₁ : float; a₂₂ : float; a₂₃ : float;
    a₃₁ : float; a₃₂ : float; a₃₃ : float }.

type vector = [ V of float and float and float ].
type quat = { re : float; im : vector }.

value a₁₁ m = m.a₁₁.
value a₁₂ m = m.a₁₂.
value a₁₃ m = m.a₁₃.
value a₂₁ m = m.a₂₁.
value a₂₂ m = m.a₂₂.
value a₂₃ m = m.a₂₃.
value a₃₁ m = m.a₃₁.
value a₃₂ m = m.a₃₂.
value a₃₃ m = m.a₃₃.

value quat a v = {re = a; im = v}.

value mkrmat a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ =
  {a₁₁ = a₁₁; a₁₂ = a₁₂; a₁₃ = a₁₃; 
   a₂₁ = a₂₁; a₂₂ = a₂₂; a₂₃ = a₂₃; 
   a₃₁ = a₃₁; a₃₂ = a₃₂; a₃₃ = a₃₃}.

value mat_trace m = a₁₁ m +. a₂₂ m +. a₃₃ m.

value req_dec (x : float) (y : float) = x = y;
value rlt_dec (x : float) ( y : float) = x < y;

value mat_mul m₁ m₂ =
  mkrmat
    (a₁₁ m₁ *. a₁₁ m₂ +. a₁₂ m₁ *. a₂₁ m₂ +. a₁₃ m₁ *. a₃₁ m₂)
    (a₁₁ m₁ *. a₁₂ m₂ +. a₁₂ m₁ *. a₂₂ m₂ +. a₁₃ m₁ *. a₃₂ m₂)
    (a₁₁ m₁ *. a₁₃ m₂ +. a₁₂ m₁ *. a₂₃ m₂ +. a₁₃ m₁ *. a₃₃ m₂)
    (a₂₁ m₁ *. a₁₁ m₂ +. a₂₂ m₁ *. a₂₁ m₂ +. a₂₃ m₁ *. a₃₁ m₂)
    (a₂₁ m₁ *. a₁₂ m₂ +. a₂₂ m₁ *. a₂₂ m₂ +. a₂₃ m₁ *. a₃₂ m₂)
    (a₂₁ m₁ *. a₁₃ m₂ +. a₂₂ m₁ *. a₂₃ m₂ +. a₂₃ m₁ *. a₃₃ m₂)
    (a₃₁ m₁ *. a₁₁ m₂ +. a₃₂ m₁ *. a₂₁ m₂ +. a₃₃ m₁ *. a₃₁ m₂)
    (a₃₁ m₁ *. a₁₂ m₂ +. a₃₂ m₁ *. a₂₂ m₂ +. a₃₃ m₁ *. a₃₂ m₂)
    (a₃₁ m₁ *. a₁₃ m₂ +. a₃₂ m₁ *. a₂₃ m₂ +. a₃₃ m₁ *. a₃₃ m₂).

value mat_transp m =
  mkrmat
   (a₁₁ m) (a₂₁ m) (a₃₁ m)
   (a₁₂ m) (a₂₂ m) (a₃₂ m)
   (a₁₃ m) (a₂₃ m) (a₃₃ m).

value mat_id =
  mkrmat
    1. 0. 0.
    0. 1. 0.
    0. 0. 1.;

value mat_sym =
  mkrmat
    1. 0.    0.
    0. (-1.) 0.
    0. 0.    (-1.);

value mat_det m =
  a₁₁ m *. (a₂₂ m *. a₃₃ m -. a₃₂ m *. a₂₃ m) +.
  a₁₂ m *. (a₂₃ m *. a₃₁ m -. a₃₃ m *. a₂₁ m) +.
  a₁₃ m *. (a₂₁ m *. a₃₂ m -. a₃₁ m *. a₂₂ m).

value eq_float x y = abs_float (x -. y) <= epsilon_float.

value mat_eq m₁ m₂ =
  eq_float m₁.a₁₁ m₂.a₁₁ && eq_float m₁.a₁₂ m₂.a₁₂ &&
  eq_float m₁.a₁₃ m₂.a₁₃ &&
  eq_float m₁.a₂₁ m₂.a₂₁ && eq_float m₁.a₂₂ m₂.a₂₂ &&
  eq_float m₁.a₂₃ m₂.a₂₃ &&
  eq_float m₁.a₃₁ m₂.a₃₁ && eq_float m₁.a₃₂ m₂.a₃₂ &&
  eq_float m₁.a₃₃ m₂.a₃₃.

value is_rotation_matrix m =
  mat_eq (mat_mul m (mat_transp m)) mat_id &&
  eq_float (mat_det m) 1.0.

value quat_norm {re = a; im = v} =
  match v with
  | V b c d → sqrt (a**2. +. b**2. +. c**2. +. d**2.)
  end.

value quat_unit {re = a; im = v} =
  match v with
  | V b c d →
      let r = sqrt (a**2. +. b**2. +. c**2. +. d**2.) in
      let a = a/.r and b = b/.r and c = c/.r and d = d/.r in
      quat a (V b c d)
  end.

value quat_of_mat m =
  if not (is_rotation_matrix m) then
    invalid_arg "quat_of_mat: not a rotation matrix"
  else if rlt_dec (mat_trace m) 0. then
(*
    if rlt_dec (a₂₂ m) (a₁₁ m) && rlt_dec (a₃₃ m) (a₁₁ m) then
      let s = sqrt (1.0 +. a₁₁ m -. a₂₂ m -. a₃₃ m) *. 2. in
      let x = 1. /. (2. *. s) in
      let y = (a₁₃ m -. a₃₁ m) /. s in
      let z = (a₂₁ m -. a₁₂ m) /. s in
      let w = (a₂₃ m -. a₃₂ m) /. s in
      quat w (V x y z)
    else
*)
      let x₀ = (a₁₁ m -. a₂₂ m -. a₃₃ m) in
      let y₀ = (-. a₁₁ m +. a₂₂ m -. a₃₃ m) in
      let z₀ = (-. a₁₁ m -. a₂₂ m +. a₃₃ m) in
      let x = sqrt (1. +. x₀) /. 2. in
      let y = sqrt (1. +. y₀) /. 2. in
      let z = sqrt (1. +. z₀) /. 2. in
      quat 0. (V x y z)
  else
    let s = sqrt (1. +. mat_trace m) /. 2. in
    let x = (a₃₂ m -. a₂₃ m) /. (4. *. s) in
    let y = (a₁₃ m -. a₃₁ m) /. (4. *. s) in
    let z = (a₂₁ m -. a₁₂ m) /. (4. *. s) in
    quat s (V x y z).

value mat_of_quat h =
  let {re = a; im = v} = quat_unit h in
  match v with
  | V b c d →
      mkrmat
        (a**2. +. b**2. -. c**2. -. d**2.)
          (2. *. b *. c -. 2. *. a *. d)
            (2. *. a *. c +. 2. *. b *. d)
        (2. *. a *. d +. 2. *. b *. c)
          (a**2. -. b**2. +. c**2. -. d**2.)
            (2. *. c *. d -. 2. *. a *. b)
        (2. *. b *. d -. 2. *. a *. c)
          (2. *. a *. b +. 2. *. c *. d)
            (a**2. -. b**2. -. c**2. +. d**2.)
  end.

value rot_x = mkrmat
  1.         0.                 0.
  0.         (1./.3.)           (-.2.*.sqrt 2./.3.)
  0.         (2.*.sqrt 2./.3.)  (1./.3.).

quat_of_mat rot_x;
rot_x.
mat_of_quat (quat_of_mat rot_x);
mat_of_quat (quat_of_mat (mat_of_quat (quat_of_mat rot_x))).

value q₁ = quat (sqrt (2./.3.)) (V (sqrt 3./.3.) 0. 0.).
q₁.
quat_of_mat (mat_of_quat q₁).

value q₂ = quat (-.sqrt (2./.3.)) (V (sqrt 3./.3.) 0. 0.).
q₂.
quat_of_mat (mat_of_quat q₂).

value q₃ = quat (sqrt (2./.3.)) (V (-. sqrt 3./.3.) 0. 0.).
q₃.
quat_of_mat (mat_of_quat q₃).

value q₄ = quat (-.sqrt (2./.3.)) (V (-.sqrt 3./.3.) 0. 0.).
q₄.
quat_of_mat (mat_of_quat q₄).

(* case of quaternion with norm ≠ from 1 *)
value h = quat 0. (V 1. 2. 3.);
h.
quat_of_mat (mat_of_quat h).
