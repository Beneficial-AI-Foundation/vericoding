-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_free_time (n k : Nat) (queries : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_free_time_positive
  (n k : Nat) (queries : List Nat)
  (h1 : n > 0)
  (h2 : k > 0)
  (h3 : queries.length = n) :
  solve_free_time n k queries > 0 :=
sorry

theorem solve_free_time_bounded
  (n k : Nat) (queries : List Nat)
  (h1 : n > 0)
  (h2 : k > 0)
  (h3 : queries.length = n) :
  1 ≤ solve_free_time n k queries ∧ 
  solve_free_time n k queries ≤ n + (queries.foldl (· + ·) 0)/k + 1 :=
sorry

theorem solve_free_time_all_zeros
  (n k : Nat) (queries : List Nat)
  (h1 : n > 0)
  (h2 : k > 0)
  (h3 : queries.length = n)
  (h4 : ∀ q ∈ queries, q = 0) :
  solve_free_time n k queries = 1 :=
sorry

theorem solve_free_time_first_below_k
  (n k : Nat) (queries : List Nat)
  (h1 : n > 0)
  (h2 : k > 0) 
  (h3 : queries.length = n)
  (h4 : ∃ i < queries.length,
    (List.take i queries).foldl (· + ·) 0 + queries[i]! < k ∧
    ∀ j < i, queries[j]! = 0) :
  solve_free_time n k queries = i + 1 :=
sorry

theorem solve_free_time_edge_cases :
  solve_free_time 1 1 [0] = 1 ∧
  solve_free_time 1 5 [10] = 3 ∧
  solve_free_time 2 3 [3,3] = 2 :=
sorry
-- </vc-theorems>