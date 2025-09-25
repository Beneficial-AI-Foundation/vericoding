-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def plant_doubling (n : Nat) : Nat := sorry

theorem plant_doubling_output_range (n : Nat) (h : n > 0) :
  1 ≤ plant_doubling n ∧ plant_doubling n ≤ n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem plant_doubling_edge_cases :
  plant_doubling 1 = 1 ∧
  plant_doubling 2 = 1 ∧  
  plant_doubling 3 = 2 := sorry
-- </vc-theorems>