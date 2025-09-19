-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numberOfArithmeticSlices (nums : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem number_of_slices_nonnegative (nums : List Int) :
  numberOfArithmeticSlices nums ≥ 0 := by
  sorry

theorem arithmetic_sequence_count (nums : List Int) (n : Nat) (h : nums.length = n) (h2 : n ≥ 3) :
  let d := nums[1]! - nums[0]!
  let isArithmetic := ∀ i, 2 ≤ i → i < n → nums[i]! = nums[i-1]! + d
  isArithmetic →
  numberOfArithmeticSlices nums = (n - 2) * (n - 1) / 2 := by
  sorry

theorem bounded_integers_nonnegative (nums : List Int) 
  (h : ∀ x ∈ nums, -1000 ≤ x ∧ x ≤ 1000) :
  numberOfArithmeticSlices nums ≥ 0 := by
  sorry

theorem short_list_zero_slices (nums : List Int)
  (h : nums.length < 3) :
  numberOfArithmeticSlices nums = 0 := by
  sorry

theorem constant_sequence_count (nums : List Int) (n : Nat) (val : Int)
  (h : nums.length = n)
  (h2 : n ≥ 3)
  (h3 : ∀ i, i < n → nums[i]! = val) :
  numberOfArithmeticSlices nums = (n - 2) * (n - 1) / 2 := by
  sorry
-- </vc-theorems>