-- <vc-helpers>
-- </vc-helpers>

def distribution_of_candy (candies: List Nat) : Nat × Nat :=
  sorry

theorem distribution_result_type_ranges
  (candies: List Nat) 
  (h: candies.length > 0) :
  let result := distribution_of_candy candies
  -- Result components are natural numbers
  result.1 ≥ 0 ∧ result.2 ≥ 0 :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded