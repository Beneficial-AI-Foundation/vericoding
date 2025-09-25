-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_list_pattern (n : Nat) (a b c : Nat) (queries : List Nat) : List Nat :=
sorry

/- Output list length matches query list length -/
-- </vc-definitions>

-- <vc-theorems>
theorem solve_list_pattern_length {n a b c : Nat} {queries : List Nat} 
  (h1 : n ≥ 1) (h2 : n ≤ 10^9)
  (h3 : a ≥ 1) (h4 : a ≤ 100)
  (h5 : b ≥ 1) (h6 : b ≤ 100) 
  (h7 : c ≥ 1) (h8 : c ≤ 100)
  (h9 : queries.length ≥ 1) (h10 : queries.length ≤ 100)
  (h11 : ∀ q ∈ queries, q ≥ 0 ∧ q ≤ 100) :
  (solve_list_pattern n a b c queries).length = queries.length :=
sorry

/- All output values are single digits except possibly first -/

theorem solve_list_pattern_range {n a b c : Nat} {queries : List Nat}
  (h1 : n ≥ 1) (h2 : n ≤ 10^9)
  (h3 : a ≥ 1) (h4 : a ≤ 100)
  (h5 : b ≥ 1) (h6 : b ≤ 100)
  (h7 : c ≥ 1) (h8 : c ≤ 100)
  (h9 : queries.length ≥ 1) (h10 : queries.length ≤ 100)
  (h11 : ∀ q ∈ queries, q ≥ 0 ∧ q ≤ 100) :
  ∀ i ∈ (solve_list_pattern n a b c queries).tail, i ≤ 9 :=
sorry

/- First query at index 0 returns initial n -/

theorem solve_list_pattern_init {n a b c : Nat} {queries : List Nat}
  (h1 : n ≥ 1) (h2 : n ≤ 10^9)
  (h3 : a ≥ 1) (h4 : a ≤ 100)
  (h5 : b ≥ 1) (h6 : b ≤ 100)
  (h7 : c ≥ 1) (h8 : c ≤ 100)
  (h9 : queries.length ≥ 1) (h10 : queries.length ≤ 100)
  (h11 : ∀ q ∈ queries, q ≥ 0 ∧ q ≤ 100)
  (h12 : 0 ∈ queries) :
  (solve_list_pattern n a b c queries)[queries.indexOf 0]? = some n :=
sorry

/- Function is idempotent (same inputs produce same outputs) -/

theorem solve_list_pattern_idempotent {n a b c : Nat} {queries : List Nat}
  (h1 : n ≥ 1) (h2 : n ≤ 10^9)
  (h3 : a ≥ 1) (h4 : a ≤ 100)
  (h5 : b ≥ 1) (h6 : b ≤ 100)
  (h7 : c ≥ 1) (h8 : c ≤ 100)
  (h9 : queries.length ≥ 1) (h10 : queries.length ≤ 100)
  (h11 : ∀ q ∈ queries, q ≥ 0 ∧ q ≤ 100) :
  solve_list_pattern n a b c queries = solve_list_pattern n a b c queries :=
sorry

/-
info: [56, 6, 2, 2]
-/
-- #guard_msgs in
-- #eval solve_list_pattern 56 3 5 7 [0, 1, 2, 3]
-- </vc-theorems>