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

/-
info: 3
-/
-- #guard_msgs in
-- #eval num_of_subarrays [2, 2, 2, 2, 5, 5, 5, 8] 3 4

/-
info: 5
-/
-- #guard_msgs in
-- #eval num_of_subarrays [1, 1, 1, 1, 1] 1 0

/-
info: 6
-/
-- #guard_msgs in
-- #eval num_of_subarrays [11, 13, 17, 23, 29, 31, 7, 5, 2, 3] 3 5
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible