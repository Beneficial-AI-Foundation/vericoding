-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def egcd (a b : Int) : Int × Int × Int := sorry

def inverseMod (a m : Int) : Option Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem egcd_basic_properties {a b : Int} (h : ¬(a = 0 ∧ b = 0)) :
  let (g, x, y) := egcd (Int.natAbs a) (Int.natAbs b)
  (Int.natAbs a) * x + (Int.natAbs b) * y = g ∧ 
  g > 0 ∧
  (a ≠ 0 → Int.natAbs a % g = 0) ∧
  (b ≠ 0 → Int.natAbs b % g = 0) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval inverseMod 2 5

/-
info: 40
-/
-- #guard_msgs in
-- #eval inverseMod 48 101

/-
info: 419
-/
-- #guard_msgs in
-- #eval inverseMod 7 733
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible