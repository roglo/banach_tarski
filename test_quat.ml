(* testing quaternions *)

type matrix =
  { a₁₁ : float; a₁₂ : float; a₁₃ : float;
    a₂₁ : float; a₂₂ : float; a₂₃ : float;
    a₃₁ : float; a₃₂ : float; a₃₃ : float }.

type point = [ P of float and float and float ].
type quat = [ Quat of float and point ].

value a₁₁ m = m.a₁₁.
value a₁₂ m = m.a₁₂.
value a₁₃ m = m.a₁₃.
value a₂₁ m = m.a₂₁.
value a₂₂ m = m.a₂₂.
value a₂₃ m = m.a₂₃.
value a₃₁ m = m.a₃₁.
value a₃₂ m = m.a₃₂.
value a₃₃ m = m.a₃₃.

value mkrmat a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ =
  {a₁₁ = a₁₁; a₁₂ = a₁₂; a₁₃ = a₁₃; 
   a₂₁ = a₂₁; a₂₂ = a₂₂; a₂₃ = a₂₃; 
   a₃₁ = a₃₁; a₃₂ = a₃₂; a₃₃ = a₃₃}.

value mat_trace m = a₁₁ m +. a₂₂ m +. a₃₃ m.

value req_dec (x : float) (y : float) = x = y;
value rlt_dec (x : float) ( y : float) = x < y;

value quat_of_mat m =
  let s =
    if req_dec (mat_trace m) (-1.) then
      let x₀ = (a₁₁ m -. a₂₂ m -. a₃₃ m) in
      let y₀ = (-. a₁₁ m +. a₂₂ m -. a₃₃ m) in
      let z₀ = (-. a₁₁ m -. a₂₂ m +. a₃₃ m) in
      if rlt_dec x₀ y₀ then
        if rlt_dec y₀ z₀ then (* z is the biggest *)
          ((a₂₁ m -. a₁₂ m) /. (2. *. sqrt (1. +. z₀)))
        else (* y is the biggest *)
          ((a₁₃ m -. a₃₁ m) /. (2. *. sqrt (1. +. y₀)))
      else
        if rlt_dec x₀ z₀ then (* z is the biggest *)
          ((a₂₁ m -. a₁₂ m) /. (2. *. sqrt (1. +. z₀)))
        else (* x is the biggest *)
          ((a₃₂ m -. a₂₃ m) /. (2. *. sqrt (1. +. x₀)))
    else
      (sqrt (1. +. mat_trace m) /. 2.)
  in
  let x = ((a₃₂ m -. a₂₃ m) /. (4. *. s)) in
  let y = ((a₁₃ m -. a₃₁ m) /. (4. *. s)) in
  let z = ((a₂₁ m -. a₁₂ m) /. (4. *. s)) in
  Quat s (P x y z).

value mat_of_quat q =
  match q with
  | Quat a (P b c d) →
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

value quat_norm q =
  match q with
  | Quat a (P b c d) → sqrt (a**2. +. b**2. +. c**2. +. d**2.)
  end.

value rot_x = mkrmat
  1.         0.                 0.
  0.         (1./.3.)           (-.2.*.sqrt 2./.3.)
  0.         (2.*.sqrt 2./.3.)  (1./.3.).

quat_of_mat rot_x;
mat_of_quat (quat_of_mat rot_x);
