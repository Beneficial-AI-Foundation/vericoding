-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_number_of_families (n: Nat) (reserved: List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_reservations {n: Nat} (h: n > 0) :
  max_number_of_families n [] = 2 * n := 
  sorry

theorem result_monotonicity {n: Nat} (reserved: List (Nat × Nat)) (h: n > 0) :
  max_number_of_families n (reserved ++ [(1,5)]) ≤ max_number_of_families n reserved :=
  sorry

theorem basic_bounds {n: Nat} (reserved: List (Nat × Nat)) (h: n > 0) :
  0 ≤ max_number_of_families n reserved ∧ max_number_of_families n reserved ≤ 2 * n :=
  sorry
-- </vc-theorems>