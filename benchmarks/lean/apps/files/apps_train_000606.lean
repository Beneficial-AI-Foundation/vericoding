def sort_numbers (nums : List Int) : List String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def isSorted (l : List Int) : Bool :=
  sorry

theorem sort_numbers_ascending (nums : List Int) :
  let result := sort_numbers nums;
  result.length = nums.length ∧
  isSorted (result.map String.toInt!) := by
  sorry

theorem sort_numbers_idempotent_list (nums : List Int) :
  sort_numbers nums = sort_numbers nums := by
  sorry

theorem sort_numbers_bounds (nums : List Int) (h : nums ≠ []) :
  let result := sort_numbers nums
  let vals := result.map String.toInt!
  vals.head! ≤ vals.getLast! ∧ 
  ∀ x ∈ vals, vals.head! ≤ x ∧ x ≤ vals.getLast! := by
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded