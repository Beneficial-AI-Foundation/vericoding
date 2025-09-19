-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def contains_duplicate (nums : List Int) : Bool :=
  sorry

def eraseDups (nums : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem contains_duplicate_matches_set_size {nums : List Int} :
  contains_duplicate nums = (nums.length ≠ (eraseDups nums).length) :=
sorry

theorem contains_duplicate_set_membership {nums : List Int} :
  contains_duplicate nums = ∃ i j, i < j ∧ j < nums.length ∧ nums[i]! = nums[j]! :=
sorry

theorem unique_list_returns_false {nums : List Int}
  (h : ∀ i j, i < j → j < nums.length → nums[i]! ≠ nums[j]!) :
  ¬contains_duplicate nums :=
sorry

theorem repeated_element_returns_true {nums : List Int} (h : nums ≠ []) :
  contains_duplicate (nums ++ nums.take 1) :=
sorry
-- </vc-theorems>