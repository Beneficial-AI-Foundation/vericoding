-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_matrix_path (n m : Nat) (matrix : List (List Nat)) (s : String) (p q : Nat) : Nat := sorry

theorem solve_matrix_path_nonnegative (n m : Nat) (matrix : List (List Nat)) (s : String) (p q : Nat) :
  solve_matrix_path n m matrix s p q ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_matrix_path_bounded (n m : Nat) (matrix : List (List Nat)) (s : String) (p q : Nat) :
  solve_matrix_path n m matrix s p q ≤ n * m * p + s.length * q := sorry 

theorem solve_matrix_path_consistent (n m : Nat) (matrix : List (List Nat)) (s : String) (p q : Nat) :
  solve_matrix_path n m matrix s p q = solve_matrix_path n m matrix s p q := sorry
-- </vc-theorems>