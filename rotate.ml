type f2 = [ A | A1 | B | B1 ].

value rec rotate_1_0_0 el =
  match el with
  | [] → (1, 0, 0, 0)
  | [e₁ :: el₁] →
      let (a, b, c, n) = rotate_1_0_0 el₁ in
      match e₁ with
      | A -> (3 * a, b + 2 * c, - 4 * b + c, n + 1)
      | A1 -> (3 * a, b - 2 * c, 4 * b + c, n + 1)
      | B -> (a + 4 * b, - 2 * a + b, 3 * c, n + 1)
      | B1 -> (a - 4 * b, 2 * a + b, 3 * c, n + 1)
      end
  end.
