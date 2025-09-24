-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def triangular_sum (n : Nat) : Bool := sorry

theorem triangular_sum_bool (n : Nat) : 
  triangular_sum n = true ∨ triangular_sum n = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triangular_sum_small_nontriang :
  triangular_sum 2 = false ∧ 
  triangular_sum 3 = false ∧
  triangular_sum 5 = false ∧ 
  triangular_sum 6 = false ∧
  triangular_sum 7 = false ∧
  triangular_sum 8 = false ∧
  triangular_sum 9 = false := sorry

theorem triangular_sum_known_triang :
  triangular_sum 0 = true ∧
  triangular_sum 1 = true ∧
  triangular_sum 3 = true ∧
  triangular_sum 6 = true ∧
  triangular_sum 10 = true ∧
  triangular_sum 15 = true ∧
  triangular_sum 21 = true ∧
  triangular_sum 28 = true ∧
  triangular_sum 36 = true ∧
  triangular_sum 45 = true := sorry
-- </vc-theorems>