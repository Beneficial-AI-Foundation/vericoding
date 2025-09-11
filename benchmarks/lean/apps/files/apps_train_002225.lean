-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def WeightList := List Nat

def process_weight_queries (n : Nat) (weights : WeightList) (queries : List (List Nat)) : List String := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem weights_length_matches_n (n : Nat) (weights : WeightList) :
  weights.length ≤ n → True := 
  sorry

theorem query_results_valid_format (n : Nat) (weights : WeightList) (queries : List (List Nat)) 
    (results : List String) :
  results.all (fun r => r = "Yes" ∨ r = "No") := 
  sorry

theorem double_reverse_idempotent (n : Nat) (weights : WeightList) :
  let queries := [[2, 1, weights.length], [2, 1, weights.length]]
  let original := weights
  let _ := process_weight_queries n weights queries
  weights = original :=
  sorry

theorem sum_bounds (n : Nat) (weights : WeightList) : 
  let total := weights.foldl (· + ·) 0
  let queries := [[3, 1, weights.length, total + 1]]
  let results := process_weight_queries n weights queries
  results = ["No"] :=
  sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval process_weight_queries 5 [1, 2, 3, 5, 6] [[3, 2, 3, 3], [3, 2, 3, 4], [3, 2, 3, 5], [2, 2, 5], [3, 2, 4, 8], [1, 2, 1], [3, 2, 4, 8], [2, 1, 4], [3, 2, 4, 3], [3, 1, 5, 7]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval process_weight_queries 3 [2013, 2015, 2017] [[3, 1, 3, 4030], [1, 1, 111], [3, 1, 3, 4030], [3, 1, 2, 111]]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded