-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_nyc_roads (events : List (Nat × Nat × Nat × Nat)) : List Nat := sorry

-- The output length matches number of queries
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_correct {events : List (Nat × Nat × Nat × Nat)} :
  List.length (solve_nyc_roads events) = 
  List.length (List.filter (fun e => e.1 == 2) events) := sorry

-- The result list contains only natural numbers

theorem result_type_correct {events : List (Nat × Nat × Nat × Nat)} :
  ∀ x ∈ solve_nyc_roads events, Nat.le 0 x := sorry

-- If only queries are provided with no rules, result is all zeros

theorem queries_only_gives_zeros {events : List (Nat × Nat × Nat × Nat)} 
  (h : ∀ e ∈ events, e.1 = 2) :
  ∀ x ∈ solve_nyc_roads events, x = 0 := sorry

-- All results are non-negative

theorem results_non_negative {events : List (Nat × Nat × Nat × Nat)} :
  ∀ x ∈ solve_nyc_roads events, Nat.le 0 x := sorry
-- </vc-theorems>