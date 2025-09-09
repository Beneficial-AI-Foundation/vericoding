-- <vc-helpers>
-- </vc-helpers>

def solve (n : Nat) : Int := sorry

def isPerfectSquare (n : Int) : Bool := sorry

theorem solve_output_nonnegative_or_minus_one (n : Nat) :
  let result := solve n
  result ≥ -1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve 3

/-
info: 36
-/
-- #guard_msgs in
-- #eval solve 13

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve 4

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible