-- <vc-preamble>
def sumOfSubarray (arr : List Int) (i j : Nat) : Int :=
  (arr.take j).drop i |>.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minSumOfLengths (arr : List Int) (target : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem edge_cases_return_negative_one (target : Int) :
  minSumOfLengths [] target = -1 ∧
  minSumOfLengths [1] (2 : Int) = -1 ∧
  minSumOfLengths [0] (0 : Int) = -1 :=
sorry

theorem valid_result_bounds {arr : List Int} {target : Int}
  (h1 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 100)
  (h2 : 1 ≤ target ∧ target ≤ 1000)
  (h3 : arr ≠ [])
  (h4 : minSumOfLengths arr target ≠ -1) :
  2 ≤ minSumOfLengths arr target ∧ minSumOfLengths arr target ≤ arr.length :=
sorry

theorem negative_result_implies_no_valid_subarrays {arr : List Int} {target : Int}
  (h1 : ∀ x ∈ arr, 0 ≤ x ∧ x ≤ 10)
  (h2 : 0 ≤ target ∧ target ≤ 20)
  (h3 : ¬∃ i j, 0 ≤ i ∧ i < j ∧ j ≤ arr.length ∧
       sumOfSubarray arr i j = target) :
  minSumOfLengths arr target = -1 :=
sorry

theorem negative_one_implies_no_non_overlapping_subarrays {arr : List Int} {target : Int}
  (h1 : ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 10)
  (h2 : 1 ≤ target ∧ target ≤ 20)
  (h3 : arr.length ≥ 4)
  (h4 : minSumOfLengths arr target = -1) :
  ¬∃ i j k l,
    0 ≤ i ∧ i < j ∧ j ≤ k ∧ k < l ∧ l ≤ arr.length ∧
    sumOfSubarray arr i j = target ∧
    sumOfSubarray arr k l = target :=
sorry
-- </vc-theorems>