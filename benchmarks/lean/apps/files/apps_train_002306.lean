-- <vc-preamble>
def contains_duplicate (nums : List Int) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
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

/-
info: True
-/
-- #guard_msgs in
-- #eval contains_duplicate [1, 2, 3, 1]

/-
info: False
-/
-- #guard_msgs in
-- #eval contains_duplicate [1, 2, 3, 4]

/-
info: True
-/
-- #guard_msgs in
-- #eval contains_duplicate [1, 1, 1, 3, 3, 4, 3, 2, 4, 2]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded