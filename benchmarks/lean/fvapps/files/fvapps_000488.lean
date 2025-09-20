-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_number_operations (nums : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_number_operations_non_negative (nums : List Nat) (h : nums ≠ []) :
  min_number_operations nums ≥ 0 := by
  sorry

theorem min_number_operations_greater_than_first (nums : List Nat) (h : nums ≠ []) :
  min_number_operations nums ≥ nums[0]! := by
  sorry

theorem min_number_operations_greater_than_max (nums : List Nat) (h : nums ≠ []) :
  min_number_operations nums ≥ List.foldl max 0 nums := by
  sorry

theorem min_number_operations_monotonic (nums : List Nat) (h : nums ≠ []) 
  (h2 : ∀ i, i + 1 < nums.length → nums[i]! ≤ nums[i+1]!) :
  min_number_operations nums = nums[nums.length - 1]! := by
  sorry

theorem min_number_operations_constant_list (nums : List Nat) (h : nums ≠ []) 
  (h2 : ∀ i, i < nums.length → nums[i]! = nums[0]!) : 
  min_number_operations nums = nums[0]! := by
  sorry

theorem min_number_operations_sum_differences (nums : List Nat) (h : nums.length ≥ 2) :
  min_number_operations nums = nums[0]! + 
    (List.range (nums.length-1)).foldr 
      (fun i acc => acc + max (nums[i+1]! - nums[i]!) 0) 0 := by
  sorry
-- </vc-theorems>