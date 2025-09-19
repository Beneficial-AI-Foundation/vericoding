-- <vc-preamble>
def solve (n : Nat) : Nat := sorry

def is_composite (n : Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isDigitIn (d : Char) (n : Nat) : Bool := sorry

theorem solve_positive (n : Nat) : 
  solve n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_monotonic {n : Nat} (h : n > 0) :
  solve n > solve (n-1) := sorry

theorem solve_deterministic (n : Nat) :
  solve n = solve n := sorry

theorem solve_zero :
  solve 0 = 1 := sorry
-- </vc-theorems>