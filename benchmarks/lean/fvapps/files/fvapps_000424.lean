-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_subarray_ones_after_delete (nums: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longest_subarray_basic_properties {nums : List Nat}
  (h: ∀ x, x ∈ nums → x ≤ 1) : 
  let result := longest_subarray_ones_after_delete nums
  -- Result non-negative
  result ≥ 0 ∧ 
  -- Result not exceeding input length
  result ≤ nums.length :=
sorry

theorem longest_subarray_all_ones {nums : List Nat}
  (h1: nums.length > 0)
  (h2: ∀ x, x ∈ nums → x = 1) :
  longest_subarray_ones_after_delete nums = nums.length - 1 :=
sorry

theorem longest_subarray_concatenation {arr1 arr2 : List Nat}
  (h: ∀ x, (x ∈ arr1 ∨ x ∈ arr2) → x ≤ 1) :
  let result := longest_subarray_ones_after_delete (arr1 ++ arr2)
  result ≥ longest_subarray_ones_after_delete arr1 ∧
  result ≥ longest_subarray_ones_after_delete arr2 :=
sorry
-- </vc-theorems>