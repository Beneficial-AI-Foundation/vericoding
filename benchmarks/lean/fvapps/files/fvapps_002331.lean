-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_longest_harmonious_subsequence (nums : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_longest_harmonious_subsequence_non_negative (nums : List Int) :
  find_longest_harmonious_subsequence nums ≥ 0 :=
sorry

theorem find_longest_harmonious_subsequence_leq_length (nums : List Int) :
  find_longest_harmonious_subsequence nums ≤ nums.length :=
sorry

theorem find_longest_harmonious_subsequence_empty (nums : List Int) :
  nums = [] → find_longest_harmonious_subsequence nums = 0 :=
sorry
-- </vc-theorems>