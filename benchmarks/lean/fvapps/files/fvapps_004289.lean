-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def permutation_average (n : Int) : Int :=
  sorry

def permutation_average_str (s : String) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem permutation_average_returns_integer (n : Int)
  (h : 0 ≤ n ∧ n ≤ 999) :
  ∃ i : Int, permutation_average n = i := by
  sorry

theorem string_int_equivalent (n : Int)
  (h : 0 ≤ n ∧ n ≤ 999) :
  permutation_average n = permutation_average_str (toString n) := by
  sorry

theorem leading_zeros_valid (n : Int)
  (h : 0 ≤ n ∧ n ≤ 99) :
  ∃ i : Int, permutation_average_str ("0" ++ toString n) = i := by
  sorry

theorem result_within_bounds (n : Int)
  (h : 10 ≤ n ∧ n ≤ 999) :
  permutation_average n ≥ 0 ∧ permutation_average n ≤ n := by
  sorry
-- </vc-theorems>