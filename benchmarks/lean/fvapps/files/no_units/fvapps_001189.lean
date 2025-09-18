-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_digit_sums (nums : List Nat) : List Nat := sorry

def sumDigits (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_digit_sums_length {nums : List Nat} :
  (calc_digit_sums nums).length = nums.length := sorry

theorem calc_digit_sums_non_negative {nums : List Nat} {i : Nat} :
  i < nums.length →
  ∃ n, (calc_digit_sums nums)[i]? = some n ∧ n ≥ 0 := sorry

theorem calc_digit_sums_order_independent {nums1 nums2 : List Nat} :
  List.Perm nums1 nums2 →
  List.Perm (calc_digit_sums nums1) (calc_digit_sums nums2) := sorry
-- </vc-theorems>