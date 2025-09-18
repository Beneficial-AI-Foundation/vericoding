-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_rich_substrings (s : String) (queries : List (Nat × Nat)) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_queries_give_empty_result (s : String) :
  solve_rich_substrings s [] = [] :=
  sorry

theorem too_short_range_always_no (s : String) (queries : List (Nat × Nat)) :
  (∀ q ∈ queries, q.1 = 1 ∧ q.2 = 2) →
  ∀ r ∈ solve_rich_substrings s queries, r = "NO" :=
  sorry 

theorem result_length_matches_queries (s : String) (queries : List (Nat × Nat)) :
  (∀ q ∈ queries, q.1 < q.2 ∧ q.2 ≤ s.length) →
  (solve_rich_substrings s queries).length = queries.length :=
  sorry

theorem results_only_yes_or_no (s : String) (queries : List (Nat × Nat)) :
  (∀ q ∈ queries, q.1 < q.2 ∧ q.2 ≤ s.length) →
  ∀ r ∈ solve_rich_substrings s queries, r = "YES" ∨ r = "NO" :=
  sorry
-- </vc-theorems>