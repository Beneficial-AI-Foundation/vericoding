-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_smaller (nums : List Int) : List Int := sorry

theorem count_smaller_length {nums : List Int} (h : nums ≠ []) :
  (count_smaller nums).length = nums.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_smaller_range {nums : List Int} (h : nums ≠ []) :
  ∀ x ∈ count_smaller nums, 0 ≤ x ∧ x < nums.length := sorry

theorem count_smaller_sorted {nums : List Int} (h : nums ≠ []) :
  (nums.zip (nums.tail?.getD [])).all (fun (a, b) => a ≤ b) → 
  count_smaller nums = List.replicate nums.length 0 := sorry

theorem count_smaller_duplicates {nums : List Int} (h : nums ≠ []) :
  (count_smaller (nums ++ nums)).length = 2 * nums.length := sorry
-- </vc-theorems>