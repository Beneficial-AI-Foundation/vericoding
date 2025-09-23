-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniqueDigitProducts (nums : List Nat) : Nat :=
  sorry

def List.toSet (l : List α) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem uniqueDigitProducts_bounds_nat {nums : List Nat} (h : nums.length > 0) :
  1 ≤ uniqueDigitProducts nums ∧ uniqueDigitProducts nums ≤ nums.length :=
sorry

theorem uniqueDigitProducts_single_digits {nums : List Nat}
  (h1 : nums.length > 0)
  (h2 : ∀ n ∈ nums, n ≤ 9) :
  uniqueDigitProducts nums ≤ (List.toSet nums).length :=
sorry

theorem uniqueDigitProducts_all_zeros {nums : List Nat}
  (h1 : nums.length > 0)
  (h2 : ∀ n ∈ nums, n = 0) :
  uniqueDigitProducts nums = 1 :=
sorry

theorem uniqueDigitProducts_three_digit_no_zeros {nums : List Nat}
  (h1 : nums.length > 0)
  (h2 : ∀ n ∈ nums, 100 ≤ n ∧ n ≤ 999)
  (h3 : ∀ n ∈ nums, ¬ toString n = "0") :
  uniqueDigitProducts nums > 0 :=
sorry

theorem uniqueDigitProducts_permutation {nums : List Nat}
  (h : nums.length > 1) :
  let n := nums[0]
  let nums_with_perm := n :: nums
  uniqueDigitProducts nums_with_perm ≥ uniqueDigitProducts nums :=
sorry
-- </vc-theorems>