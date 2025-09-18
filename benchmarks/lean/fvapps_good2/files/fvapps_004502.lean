-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Matrix := List (List Bool)

def solveMatrix (m n a b : Nat) : Option Matrix :=
  sorry

def matrixToStr (m : Matrix) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_matrix_valid_2_2_1_1 :
  ∃ (result : Matrix),
    solveMatrix 2 2 1 1 = some result ∧
    matrixToStr result = "10\n01"
  :=
sorry

theorem solve_matrix_valid_2_2_2_2 :
  ∃ (result : Matrix),
    solveMatrix 2 2 2 2 = some result ∧
    matrixToStr result = "11\n11"
  :=
sorry

theorem solve_matrix_valid_3_6_2_1 :
  ∃ (result : Matrix),
    solveMatrix 3 6 2 1 = some result ∧
    matrixToStr result = "110000\n001100\n000011"
  :=
sorry

theorem solve_matrix_impossible_2_2_2_1 :
  solveMatrix 2 2 2 1 = none :=
sorry

theorem solve_matrix_impossible_3_3_3_1 :
  solveMatrix 3 3 3 1 = none :=
sorry

theorem solve_matrix_impossible_greater_dimensions :
  (∀ m n : Nat, m > 0 → n > 0 →
    (∀ a b : Nat, (a > m ∨ b > n) →
      solveMatrix m n a b = none)) :=
sorry
-- </vc-theorems>