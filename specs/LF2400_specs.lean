-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsNearbyDuplicate (nums : List Int) (k : Nat) : Bool := sorry

theorem single_element_list_no_duplicates {nums : List Int} {k : Nat} (h : nums.length = 1) :
  containsNearbyDuplicate nums k = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem adjacent_identical_elements {nums : List Int} {k : Nat} 
  (h1 : nums.length ≥ 2)
  (h2 : nums[1]! = nums[0]!)
  (h3 : k ≥ 1) :
  containsNearbyDuplicate (nums.take 2) k = true := sorry

theorem unique_elements_no_duplicates {nums : List Int} {k : Nat}
  (h : ∀ i j, i < nums.length → j < nums.length → i ≠ j → nums[i]! ≠ nums[j]!) :
  containsNearbyDuplicate nums k = false := sorry

theorem k_zero_always_false {nums : List Int} :
  containsNearbyDuplicate nums 0 = false := sorry

theorem k_larger_than_list {nums : List Int} {k : Nat}
  (h : k ≥ nums.length) :
  containsNearbyDuplicate nums k = 
    (∃ i j, i < nums.length ∧ j < nums.length ∧ i ≠ j ∧ nums[i]! = nums[j]!) := sorry
-- </vc-theorems>