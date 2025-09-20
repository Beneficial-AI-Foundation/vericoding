-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_of_subarrays (arr : List Int) (k : Nat) (threshold : Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_negative_result (arr : List Int) (k : Nat) (threshold : Int) :
  num_of_subarrays arr k threshold ≥ 0 :=
sorry

theorem empty_result_if_smaller (arr : List Int) (k : Nat) (threshold : Int) :
  arr.length < k → num_of_subarrays arr k threshold = 0 :=
sorry

theorem result_bounded_by_possible_subarrays (arr : List Int) (k : Nat) (threshold : Int) :
  arr.length ≥ k → num_of_subarrays arr k threshold ≤ arr.length - k + 1 :=
sorry

theorem k_equals_one_case (arr : List Int) (threshold : Int) :
  num_of_subarrays arr 1 threshold = (arr.filter (fun x => x ≥ threshold)).length :=
sorry
-- </vc-theorems>