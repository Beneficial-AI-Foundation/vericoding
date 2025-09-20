-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nth_element (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_positive (n : Nat) (h : n > 0) : 
  find_nth_element n > 0 := sorry

theorem output_increases_in_groups_of_three (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  let group_start := ((n-1) / 3) * 3 + 1
  find_nth_element group_start < find_nth_element (group_start + 1) ∧ 
  find_nth_element (group_start + 1) < find_nth_element (group_start + 2) := sorry

theorem output_ratio_bounds (n : Nat) (h : n > 0) :
  find_nth_element n ≤ 4 * n ∧ 
  find_nth_element n ≥ n / 3 := sorry

theorem binary_length_property (n : Nat) (h : n > 0) :
  Nat.log2 (find_nth_element n) + 1 ≥ (Nat.log2 n + 1) / 2 := sorry

theorem first_few_values :
  find_nth_element 1 = 1 ∧
  find_nth_element 2 = 2 ∧ 
  find_nth_element 3 = 3 ∧
  find_nth_element 4 = 4 := sorry
-- </vc-theorems>