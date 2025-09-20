-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_get_zero_sum_subset (a b c d : Int) : String := sorry

theorem zerosum_gives_yes_result {a b c d : Int} (h : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0) : 
  can_get_zero_sum_subset a b c d = "Yes" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem opposite_pairs_give_yes_result {a b c d : Int} 
  (h : a = -b ∨ a = -c ∨ a = -d ∨ b = -c ∨ b = -d ∨ c = -d) :
  can_get_zero_sum_subset a b c d = "Yes" := sorry

theorem all_positive_gives_no_result {a b c d : Int} 
  (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) :
  can_get_zero_sum_subset a b c d = "No" := sorry

theorem all_negative_gives_no_result {a b c d : Int}
  (h : a < 0 ∧ b < 0 ∧ c < 0 ∧ d < 0) :
  can_get_zero_sum_subset a b c d = "No" := sorry

theorem result_is_yes_or_no (a b c d : Int) :
  (can_get_zero_sum_subset a b c d = "Yes") ∨ 
  (can_get_zero_sum_subset a b c d = "No") := sorry

theorem single_zero_gives_yes (x : Int) :
  can_get_zero_sum_subset x 0 (x+1) (x+2) = "Yes" := sorry

theorem opposite_pair_gives_yes (x : Int) :
  can_get_zero_sum_subset x (-x) (x+1) (x+2) = "Yes" := sorry

theorem all_positive_sequence_gives_no (x : Int) (h : x > 0) :
  can_get_zero_sum_subset x (x+1) (x+2) (x+3) = "No" := sorry
-- </vc-theorems>