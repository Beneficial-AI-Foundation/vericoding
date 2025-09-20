-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_square_side (n : Nat) : Nat := sorry

theorem min_square_side_positive (n : Nat) (h : n ≥ 3) : 
  min_square_side n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_square_side_monotone (n : Nat) (h : n ≥ 3) :
  min_square_side n ≤ min_square_side (n + 1) := sorry
-- </vc-theorems>