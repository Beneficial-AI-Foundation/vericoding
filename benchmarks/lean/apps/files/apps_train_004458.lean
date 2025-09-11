-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lucasnum (n : Int) : Int := sorry

-- Base cases
-- </vc-definitions>

-- <vc-theorems>
theorem lucas_zero : lucasnum 0 = 2 := sorry

theorem lucas_one : lucasnum 1 = 1 := sorry

-- Alternating signs for negative indices

theorem lucas_negative (n : Int) : 
  n < 0 → lucasnum n = (if n % 2 = 0 then 1 else -1) * lucasnum (-n) := sorry

-- Signs symmetry property

theorem lucas_symmetry (n : Int) :
  n < 0 → lucasnum n = (if n % 2 = 0 then 1 else -1) * lucasnum (-n) := sorry

/-
info: 123
-/
-- #guard_msgs in
-- #eval lucasnum -10

/-
info: 2
-/
-- #guard_msgs in
-- #eval lucasnum 0

/-
info: 11
-/
-- #guard_msgs in
-- #eval lucasnum 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded