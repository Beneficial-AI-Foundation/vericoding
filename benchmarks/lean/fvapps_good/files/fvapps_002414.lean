-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_unsorted_subarray (nums : List Int) : Nat := sorry

theorem empty_or_single_element_list 
  (nums : List Int) (h : nums.length ≤ 1) : 
  find_unsorted_subarray nums = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sorted_list_returns_zero 
  (nums : List Int) 
  (h : ∀ (i j : Fin nums.length), i.val < j.val → nums[i] ≤ nums[j]) :
  find_unsorted_subarray nums = 0 := sorry

theorem reverse_sorted_list 
  (nums : List Int) 
  (h1 : nums.length ≥ 2)
  (h2 : ∀ (i j : Fin nums.length), i.val < j.val → nums[i] ≥ nums[j])
  (h3 : ∃ (i j : Fin nums.length), nums[i] > nums[j]) :
  find_unsorted_subarray nums = nums.length := sorry

theorem result_length_bounds
  (nums : List Int) 
  (h : nums.length ≥ 3) :
  0 ≤ find_unsorted_subarray nums ∧ find_unsorted_subarray nums ≤ nums.length := sorry
-- </vc-theorems>