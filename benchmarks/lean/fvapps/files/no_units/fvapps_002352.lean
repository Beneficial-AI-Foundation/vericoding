-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def special_array (nums: List Nat) : Int := sorry

theorem special_array_basic_properties {nums : List Nat} :
  let result := special_array nums
  result ≥ -1 ∧ 
  (result ≠ -1 → result ≤ nums.length) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem special_array_count_property {nums : List Nat} :
  let result := special_array nums
  let resultNat := Int.toNat result
  result ≠ -1 →
  (nums.filter (fun x => x ≥ resultNat)).length = resultNat := sorry

theorem special_array_all_zeros {nums : List Nat} :
  (∀ x ∈ nums, x = 0) →
  nums.length > 0 →
  special_array nums = -1 := sorry

theorem special_array_all_large {nums : List Nat} :
  (∀ x ∈ nums, x > nums.length) →
  nums.length > 0 →
  special_array nums = nums.length := sorry
-- </vc-theorems>