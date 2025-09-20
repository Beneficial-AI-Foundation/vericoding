-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def spinning_rings (inner_max outer_max : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem spinning_rings_always_positive (inner_max outer_max : Nat) 
  (h1 : inner_max > 0) (h2 : outer_max > 0) :
  spinning_rings inner_max outer_max > 0 :=
sorry

theorem spinning_rings_same_size_bound (n : Nat) (h : n > 0) :
  spinning_rings n n ≤ n + 1 :=
sorry

theorem spinning_rings_edge_cases :
  spinning_rings 1 1 = 1 ∧
  (spinning_rings 1 2 = 1 ∨ spinning_rings 1 2 = 2 ∨ spinning_rings 1 2 = 3) :=
sorry
-- </vc-theorems>