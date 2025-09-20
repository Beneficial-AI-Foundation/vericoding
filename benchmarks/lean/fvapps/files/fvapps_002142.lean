-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def solve (N : Nat) (coords : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_within_bounds (N : Nat) (coords : List (Nat × Nat)) : 
  solve N coords < MOD :=
  sorry

theorem solve_result_nonneg (N : Nat) (coords : List (Nat × Nat)) :
  solve N coords ≥ 0 :=
  sorry

theorem solve_empty_coords (N : Nat) :
  solve N [] < MOD ∧ solve N [] ≥ 0 :=
  sorry

theorem solve_valid_coords (N : Nat) (coords : List (Nat × Nat)) 
  (h1 : N ≥ 1)
  (h2 : N ≤ 4) 
  (h3 : ∀ c ∈ coords, c.1 ≥ 1 ∧ c.1 ≤ N ∧ c.2 ≥ 1 ∧ c.2 ≤ N)
  (h4 : coords.length ≥ N)
  (h5 : coords.length ≤ 2*N) :
  solve N coords < MOD ∧ solve N coords ≥ 0 :=
  sorry
-- </vc-theorems>