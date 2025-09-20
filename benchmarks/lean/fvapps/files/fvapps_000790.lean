-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_mountain_queries (n : Nat) (mountains : List Nat) (queries : List (List Nat)) : List Nat :=
  sorry

-- Results length matches number of type 1 queries
-- </vc-definitions>

-- <vc-theorems>
theorem results_length_matches_type_1_queries (n : Nat) (mountains : List Nat) (queries : List (List Nat)) 
  (h1 : n ≥ 2) (h2 : mountains.length = n) :
  (solve_mountain_queries n mountains queries).length = 
    (queries.filter (fun q => q.get? 0 = some 1)).length := 
  sorry

-- All results are either -1 or higher than queried mountain 

theorem results_valid_height (n : Nat) (mountains : List Nat) (queries : List (List Nat)) 
  (h1 : n ≥ 2) (h2 : mountains.length = n)
  (i : Nat) (h3 : i < (solve_mountain_queries n mountains queries).length)
  (h4 : i < (queries.filter (fun q => q.get? 0 = some 1)).length) :
  let result := (solve_mountain_queries n mountains queries)[i]'h3
  let type1Queries := queries.filter (fun q => q.get? 0 = some 1)
  let mountainIdx := (type1Queries[i]?.bind (λ q => q.get? 1)).getD 0
  result = 0 ∨ result > mountains[mountainIdx]?.getD 0 :=
  sorry

-- Update query changes mountain height

theorem update_query_changes_height (n : Nat) (mountains : List Nat) (new_height : Nat)
  (h1 : n ≥ 2) (h2 : mountains.length = n) :
  let update_idx := min 1 (n-1)
  let queries1 := [[0, update_idx, new_height], [1, update_idx]]
  let queries2 := [[1, update_idx]]
  let new_mountains := mountains.set update_idx new_height
  solve_mountain_queries n mountains queries1 = 
    solve_mountain_queries n new_mountains queries2 :=
  sorry
-- </vc-theorems>