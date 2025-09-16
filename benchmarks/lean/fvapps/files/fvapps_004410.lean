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

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve 0

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve 2

/-
info: 44
-/
-- #guard_msgs in
-- #eval solve 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible