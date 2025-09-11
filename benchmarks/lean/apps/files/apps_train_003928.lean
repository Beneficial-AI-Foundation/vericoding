-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x y : Nat) : Nat := sorry

def isSpecialPrime (n : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_range_properties (x y : Nat) (hx : x ≤ 1000000) (hy : y ≤ 1000000) :
  solve x y ≥ 0 := sorry

theorem solve_empty_range (x : Nat) (hx : x ≤ 1000000) :
  solve x x = 0 := sorry

theorem solve_monotonicity (x y z : Nat) 
  (hxy : x ≤ y) (hyz : y ≤ z) (hxz : x ≤ z) :
  solve x y ≤ solve x z := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve 0 10

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve 0 15

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve 100 1000
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible