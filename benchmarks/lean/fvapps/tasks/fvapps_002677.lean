-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isTriangular (n : Nat) : Bool := sorry

theorem isTriangular_output_bool (n : Nat) : 
  isTriangular n = true ∨ isTriangular n = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isTriangular_formula (n : Nat) :
  isTriangular n = true → ∃ x : Nat, n = x * (x + 1) / 2 := sorry

theorem isTriangular_known_values : 
  isTriangular 0 = true ∧ 
  isTriangular 1 = true ∧ 
  isTriangular 3 = true ∧ 
  isTriangular 6 = true ∧ 
  isTriangular 10 = true ∧
  isTriangular 15 = true ∧
  isTriangular 21 = true ∧
  isTriangular 28 = true ∧
  isTriangular 36 = true ∧
  isTriangular 45 = true := sorry
-- </vc-theorems>