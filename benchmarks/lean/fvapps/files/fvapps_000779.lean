-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_solved_problems (N: Nat) (confidence_matrix: List (List Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_solved_problems_non_negative {N: Nat} {confidence_matrix: List (List Nat)} :
  count_solved_problems N confidence_matrix ≥ 0 :=
sorry

theorem count_solved_problems_upper_bound {N: Nat} {confidence_matrix: List (List Nat)} :
  count_solved_problems N confidence_matrix ≤ confidence_matrix.length :=
sorry

theorem count_solved_problems_matches_confident {N: Nat} {confidence_matrix: List (List Nat)} :
  count_solved_problems N confidence_matrix = 
    (confidence_matrix.filter (fun conf => (conf.foldl (· + ·) 0) ≥ 2)).length :=
sorry

theorem count_solved_problems_empty {N: Nat} :
  count_solved_problems N [] = 0 :=
sorry
-- </vc-theorems>