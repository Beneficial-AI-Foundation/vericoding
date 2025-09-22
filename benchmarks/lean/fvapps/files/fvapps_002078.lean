-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def paper_folding_queries (n: Nat) (queries: List (Nat × Nat × Nat)) : List Nat := sorry

theorem empty_queries_return_empty (n: Nat) :
  n > 0 → paper_folding_queries n [] = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_query_returns_single_result (n: Nat) :
  n > 0 → n ≤ 20 →
  let query := [(2, 0, min 1 (n-1))]
  List.length (paper_folding_queries n query) = 1 := sorry
-- </vc-theorems>