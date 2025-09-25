-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_special_integer (nums : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem special_int_exists (nums : List Int) (h : nums ≠ []) :
  let result := find_special_integer nums
  let count := (nums.filter (· = result)).length 
  count ≥ nums.length / 4 ∨ result = nums.getLast h := by
sorry

theorem result_in_array (nums : List Int) (h : nums ≠ []) :
  let result := find_special_integer nums
  result ∈ nums := by
sorry

theorem all_same_number (nums : List Int) (h1 : nums.length ≥ 4) 
    (h2 : ∀ x ∈ nums, x = nums[0]) :
  find_special_integer nums = nums[0] := by
sorry

theorem binary_array (nums : List Int) (h1 : nums.length ≥ 2)
    (h2 : ∀ x ∈ nums, x = 0 ∨ x = 1) :
  let result := find_special_integer nums
  result = 0 ∨ result = 1 := by
sorry
-- </vc-theorems>