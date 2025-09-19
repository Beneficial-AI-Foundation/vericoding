-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process_queries (queries : List Nat) (m : Nat) : List Nat := sorry

theorem result_length_matches_input 
  (queries : List Nat) (m : Nat) (h : m > 0)
  : List.length (process_queries queries m) = List.length queries := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem results_are_valid_indices
  (queries : List Nat) (m : Nat) (h : m > 0)
  : ∀ x ∈ (process_queries queries m), x < m := sorry 

theorem empty_input_empty_output
  (m : Nat) (h : m > 0)
  : process_queries [] m = [] := sorry

theorem repeated_query_front_position
  (queries : List Nat) (m : Nat) (h : m > 0) 
  (h1 : queries ≠ [])
  (h2 : ∀ x ∈ queries, x ≤ m)
  (h3 : List.length queries > 0)
  (q : Nat)
  (h4 : q = queries[0]'h3)
  : ∀ x ∈ (process_queries (queries ++ [q]) m), x ≥ 0 := sorry

theorem single_query_one_returns_zero
  (m : Nat) (h : m > 0)
  : process_queries [1] m = [0] := sorry
-- </vc-theorems>