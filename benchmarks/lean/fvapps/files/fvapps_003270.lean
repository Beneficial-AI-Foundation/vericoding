-- <vc-preamble>
def solve (sum gcd : Nat) : Option (Nat × Nat) :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat :=
  sorry

-- For any x,y > 0:
-- If solve returns None, then sum not divisible by gcd
-- If solve returns Some (a,b), then:
--   a + b = sum, gcd(a,b) = gcd, a ≤ b
-- </vc-definitions>

-- <vc-theorems>
theorem solve_properties (x y : Nat) (h1: x > 0) (h2: y > 0) :
  let s := x + y
  let g := gcd x y
  match solve s g with
  | none => s % g ≠ 0 
  | some (a, b) => a + b = s ∧ gcd a b = g ∧ a ≤ b
  := sorry

-- For any x > 0:
-- solve(2x, x) = (x,x)

theorem solve_same_number (x : Nat) (h: x > 0) :
  solve (2*x) x = some (x, x) := sorry

/-
info: [3, 3]
-/
-- #guard_msgs in
-- #eval solve 6 3

/-
info: [2, 6]
-/
-- #guard_msgs in
-- #eval solve 8 2

/-
info: [4, 8]
-/
-- #guard_msgs in
-- #eval solve 12 4
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded