-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_operations_cost (n : Nat) (numbers : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_operations_cost_lower_bound {n : Nat} {numbers : List Nat} 
  (h1: n ≥ 2) (h2: numbers.length = n) : 
  ∃ min_num : Nat, min_num ∈ numbers ∧ min_operations_cost n numbers ≥ min_num * (numbers.length - 1) :=
  sorry

theorem min_operations_cost_non_negative {n : Nat} {numbers : List Nat}
  (h1: n ≥ 2) :
  min_operations_cost n numbers ≥ 0 := 
  sorry

theorem min_operations_cost_preserves_input {n : Nat} {numbers : List Nat}
  (h1: n ≥ 2) :
  min_operations_cost n numbers = min_operations_cost n numbers ∧ numbers = numbers :=
  sorry

theorem min_operations_cost_two_ones :
  min_operations_cost 2 [1, 1] = 1 :=
  sorry

theorem min_operations_cost_same_numbers :
  min_operations_cost 3 [5, 5, 5] = 10 :=
  sorry
-- </vc-theorems>