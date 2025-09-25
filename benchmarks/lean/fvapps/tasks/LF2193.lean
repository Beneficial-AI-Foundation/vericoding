-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_colored_balls (n : Nat) (pairs : List (List Nat)) : Nat := sorry

theorem solve_colored_balls_non_negative (n : Nat) (pairs : List (List Nat)) : 
  solve_colored_balls n pairs ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_colored_balls_max_bound (n : Nat) (pairs : List (List Nat)) :
  solve_colored_balls n pairs ≤ (10^9 - 1) * (10^9 - 1) := sorry

theorem solve_colored_balls_reverse_invariant (n : Nat) (pairs : List (List Nat)) 
  (h₁ : ∀ p ∈ pairs, p.length = 2) :
  solve_colored_balls n pairs = 
  solve_colored_balls n (pairs.map (fun p => [p.get ⟨1, sorry⟩, p.get ⟨0, sorry⟩])) := sorry

theorem solve_colored_balls_identical_pairs (n : Nat) :
  solve_colored_balls n (List.replicate n [1,1]) = 0 := sorry

theorem solve_colored_balls_edge_case :
  solve_colored_balls 2 [[1,1], [1000000000,1000000000]] = 
  (1000000000-1) * (1000000000-1) := sorry
-- </vc-theorems>