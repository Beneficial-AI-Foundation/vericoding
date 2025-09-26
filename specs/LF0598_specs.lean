-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_bill_queries (n q : Nat) (bills : List Nat) (queries : List (Nat × Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_bill_queries_results_length 
  (n q : Nat) (bills : List Nat) (queries : List (Nat × Nat))
  (h1 : bills.length > 0) (h2 : queries.length > 0) :
  (solve_bill_queries n q bills queries).length = queries.length :=
sorry

theorem solve_bill_queries_results_bounded
  (n q : Nat) (bills : List Nat) (queries : List (Nat × Nat))
  (h1 : bills.length > 0) (h2 : queries.length > 0) :
  ∀ x, x ∈ solve_bill_queries n q bills queries → x < 10^9 :=
sorry

theorem solve_bill_queries_matches_sum_mod
  (n q : Nat) (bills : List Nat) (queries : List (Nat × Nat))
  (h1 : bills.length > 0) (h2 : queries.length > 0)
  (h3 : ∀ p ∈ queries, (p.1 ≤ p.2 ∧ p.2 ≤ n))
  (i : Nat) (hi : i < queries.length) :
  let query := queries[i]'hi
  let sublist := (bills.take query.2).drop (query.1 - 1)
  (solve_bill_queries n q bills queries)[i]'(by rw [solve_bill_queries_results_length n q bills queries h1 h2]; exact hi) = 
    sublist.foldl (fun acc x => acc + x) 0 % (10^9) :=
sorry

theorem solve_bill_queries_whole_array
  (bills : List Nat) (h : bills.length > 0) :
  solve_bill_queries (bills.length) 1 bills [(1, bills.length)] = 
    [bills.foldl (fun acc x => acc + x) 0 % (10^9)] :=
sorry
-- </vc-theorems>