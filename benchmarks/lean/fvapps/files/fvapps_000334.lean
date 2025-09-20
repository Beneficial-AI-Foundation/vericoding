-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat := sorry

def numSquares (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numSquares_bounds (n : Nat) (h : n ≥ 1) : 
  1 ≤ numSquares n ∧ numSquares n ≤ 4 := sorry

theorem numSquares_four_pattern (k m : Nat) (h : 4^k * (8*m + 7) > 0) :
  numSquares (4^k * (8*m + 7)) = 4 := sorry
-- </vc-theorems>