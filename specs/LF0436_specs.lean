-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_least_num_unique_ints (arr : List Int) (k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_bounds (arr : List Int) (k : Nat) (h : arr ≠ []) :
  0 ≤ find_least_num_unique_ints arr k ∧ 
  find_least_num_unique_ints arr k ≤ arr.length := by
  sorry

theorem removing_all_elements (arr : List Int) (h : arr ≠ []) :
  find_least_num_unique_ints arr arr.length = 0 := by
  sorry

theorem removing_none (arr : List Int) (h : arr ≠ []) :
  find_least_num_unique_ints arr 0 = arr.length := by
  sorry

theorem removing_more_than_length (arr : List Int) (k : Nat) (h : arr ≠ []) :
  find_least_num_unique_ints arr (arr.length + k) = 0 := by
  sorry

theorem monotonic_decrease (arr : List Int) (k : Nat) 
  (h1 : arr.length ≥ 2) (h2 : k ≥ 1) (h3 : k < arr.length) :
  find_least_num_unique_ints arr (k + 1) ≤ find_least_num_unique_ints arr k := by
  sorry
-- </vc-theorems>