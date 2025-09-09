-- <vc-helpers>
-- </vc-helpers>

def solve_sandglass_wrapped (X K : Nat) (r : List Nat) (Q : Nat) (queries : List (Nat × Nat)) : List Nat := sorry

theorem sandglass_results_length_matches_queries (X K : Nat) (r : List Nat) (Q : Nat) (queries : List (Nat × Nat)) :
  queries.length = Q → (solve_sandglass_wrapped X K r Q queries).length = Q := sorry

theorem sandglass_results_within_bounds (X K : Nat) (r : List Nat) (Q : Nat) (queries : List (Nat × Nat)) 
  (result : Nat) : 
  result ∈ solve_sandglass_wrapped X K r Q queries → result ≤ X ∧ result ≥ 0 := sorry

theorem sandglass_each_result_valid (X K : Nat) (r : List Nat) (Q : Nat) 
  (queries : List (Nat × Nat)) (t a : Nat) :
  (t, a) ∈ queries → 
  ∃ result, result ∈ solve_sandglass_wrapped X K r Q queries ∧ result ≤ X ∧ result ≥ 0 := sorry

/-
info: [60, 1, 120]
-/
-- #guard_msgs in
-- #eval solve_sandglass 180 3 [60, 120, 180] 3 [(30, 90), (61, 1), (180, 180)]

/-
info: [100, 10, 0, 0]
-/
-- #guard_msgs in
-- #eval solve_sandglass 100 1 [100000] 4 [(0, 100), (90, 100), (100, 100), (101, 100)]

/-
info: [19, 52, 91, 10, 58, 42, 100]
-/
-- #guard_msgs in
-- #eval solve_sandglass 100 5 [48, 141, 231, 314, 425] 7 [(0, 19), (50, 98), (143, 30), (231, 55), (342, 0), (365, 100), (600, 10)]

-- Apps difficulty: competition
-- Assurance level: unguarded