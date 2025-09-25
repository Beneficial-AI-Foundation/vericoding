-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def xor_of_pairwise_sums (n : Nat) (arr : List Nat) : Nat := sorry

theorem xor_pairwise_sums_nonnegative (n : Nat) (arr : List Nat) :
  n ≤ arr.length → xor_of_pairwise_sums n arr ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_or_singleton_equals_zero (n : Nat) (arr : List Nat) :
  n ≤ 1 → xor_of_pairwise_sums n arr = 0 := sorry

theorem identical_elements_result_even (n : Nat) (arr : List Nat) (x : Nat) :
  n ≤ arr.length →
  (∀ i, arr.get? i = some x) →
  xor_of_pairwise_sums n arr % 2 = 0 := sorry

theorem two_distinct_elements (arr : List Nat) (h : arr.length = 2) :
  List.get? arr 0 ≠ List.get? arr 1 →
  xor_of_pairwise_sums 2 arr = Option.getD (List.get? arr 0) 0 + Option.getD (List.get? arr 1) 0 := sorry

theorem identical_pair_sum (x : Nat) :
  xor_of_pairwise_sums 2 [x, x] = 2 * x := sorry
-- </vc-theorems>