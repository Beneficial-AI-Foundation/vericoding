-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkGoodMatrix (n : Nat) (entries : List (Nat × Nat × Nat)) : String := sorry 

theorem check_good_matrix_result_is_yes_or_no (n : Nat) (entries : List (Nat × Nat × Nat)) : 
  let result := checkGoodMatrix n entries
  result = "yes" ∨ result = "no" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_matrix_is_good (n : Nat) :
  checkGoodMatrix n [] = "yes" := sorry

theorem self_zero_entries_valid (n i : Nat) (h : i ≤ n) :
  checkGoodMatrix n [(i, i, 0)] = "yes" := sorry

theorem self_one_entries_invalid (n i : Nat) (h : i ≤ n) :
  checkGoodMatrix n [(i, i, 1)] = "no" := sorry

theorem symmetric_entries_zero_valid (n : Nat) (h : n ≥ 2) :
  checkGoodMatrix n [(1, 2, 0), (2, 1, 0)] = "yes" := sorry

theorem symmetric_entries_one_invalid (n : Nat) (h : n ≥ 2) :
  checkGoodMatrix n [(1, 2, 1), (2, 1, 0)] = "no" := sorry
-- </vc-theorems>