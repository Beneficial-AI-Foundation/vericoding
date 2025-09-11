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

/-
info: [4, 3]
-/
-- #guard_msgs in
-- #eval paper_folding_queries 7 [[1, 3], [1, 2], [2, 0, 1], [2, 1, 2]]

/-
info: [7, 2, 10, 4, 5]
-/
-- #guard_msgs in
-- #eval paper_folding_queries 10 [[2, 2, 9], [1, 1], [2, 0, 1], [1, 8], [2, 0, 8], [1, 2], [2, 1, 3], [1, 4], [2, 2, 4]]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval paper_folding_queries 1 [[2, 0, 1]]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded