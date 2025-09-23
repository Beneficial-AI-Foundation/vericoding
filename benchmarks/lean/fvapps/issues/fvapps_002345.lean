-- <vc-preamble>
def maxSubArray (nums : List Int) : Int := sorry

def List.sum (l : List Int) : Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.max (l : List Int) : Int := sorry

theorem maxSubArray_geq_max (nums : List Int) (h: nums ≠ []) :
  maxSubArray nums ≥ List.max nums := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxSubArray_all_positive (nums : List Int) (h1: nums ≠ []) 
  (h2: ∀ x ∈ nums, x > 0) :
  maxSubArray nums = List.sum nums := sorry

theorem maxSubArray_geq_elements (nums : List Int) (h: nums ≠ []) :
  ∀ x ∈ nums, maxSubArray nums ≥ x := sorry

theorem maxSubArray_exists_subarray (nums : List Int) (h: nums ≠ []) :
  ∃ i j, i ≤ j ∧ j < nums.length ∧ 
    List.sum (List.take (j - i + 1) (List.drop i nums)) = maxSubArray nums := sorry

theorem maxSubArray_binary (nums : List Int) (h1: nums ≠ [])
  (h2: ∀ x ∈ nums, x ≥ -1 ∧ x ≤ 1) :
  maxSubArray nums = List.max nums ∨ maxSubArray nums > 0 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval maxSubArray #[-2, 1, -3, 4, -1, 2, 1, -5, 4]

/-
info: -1
-/
-- #guard_msgs in
-- #eval maxSubArray #[-1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval maxSubArray #[1, 2, -1, -2, 2, 1, -2, 1]
-- </vc-theorems>