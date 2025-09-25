-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_witch_prevent_finish (n: Nat) (d: Nat) (distances: List Nat) (queries: List Nat) : List Answer :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_length_matches_queries 
  (n d: Nat) (distances queries: List Nat) 
  (h1: n > 0) (h2: d > 0) 
  (h3: distances.length = n)
  (h4: queries.length > 0)
  (h5: ∀ q ∈ queries, q ≤ n)
  (h6: ∀ x ∈ distances, x > 0) :
  (can_witch_prevent_finish n d distances queries).length = queries.length := by
  sorry

theorem results_are_yes_or_no
  (n d: Nat) (distances queries: List Nat)
  (h1: n > 0) (h2: d > 0)
  (h3: distances.length = n)
  (h4: queries.length > 0)
  (h5: ∀ q ∈ queries, q ≤ n)
  (h6: ∀ x ∈ distances, x > 0) :
  ∀ x ∈ can_witch_prevent_finish n d distances queries, x = Answer.YES ∨ x = Answer.NO := by
  sorry

theorem query_order_independence
  (n d: Nat) (distances queries: List Nat)
  (h1: n > 0) (h2: d > 0)
  (h3: distances.length = n)
  (h4: queries.length > 0)
  (h5: ∀ q ∈ queries, q ≤ n)
  (h6: ∀ x ∈ distances, x > 0) :
  can_witch_prevent_finish n d distances queries =
  List.reverse (can_witch_prevent_finish n d distances (List.reverse queries)) := by
  sorry

theorem single_query_consistency
  (n d: Nat) (distances queries: List Nat)
  (h1: n > 0) (h2: d > 0)
  (h3: distances.length = n)
  (h4: queries.length > 0)
  (h5: ∀ q ∈ queries, q ≤ n)
  (h6: ∀ x ∈ distances, x > 0) :
  ∀ i, i < queries.length →
    (can_witch_prevent_finish n d distances [queries[i]!]).get! 0 =
    (can_witch_prevent_finish n d distances queries).get! i := by
  sorry

/-
info: ['NO', 'YES']
-/
-- #guard_msgs in
-- #eval can_witch_prevent_finish 4 10 [3, 4, 3, 3] [4, 3]

/-
info: ['YES', 'YES', 'YES', 'YES', 'YES']
-/
-- #guard_msgs in
-- #eval can_witch_prevent_finish 5 9 [4, 4, 2, 3, 2] [1, 4, 2, 3, 5]

/-
info: ['NO', 'NO', 'YES', 'NO', 'NO', 'YES']
-/
-- #guard_msgs in
-- #eval can_witch_prevent_finish 6 15 [4, 3, 5, 4, 2, 1] [1, 2, 3, 4, 5, 6]
-- </vc-theorems>