-- <vc-helpers>
-- </vc-helpers>

def quadratic (x1 x2 : Int) : Int × Int × Int :=
  sorry

theorem first_coeff_one (x1 x2 : Int) :
  let (a, b, c) := quadratic x1 x2
  a = 1 := sorry

theorem vieta_formulas (x1 x2 : Int) :
  let (a, b, c) := quadratic x1 x2
  (-b = x1 + x2) ∧ (c = x1 * x2) := sorry

/-
info: (1, -1, 0)
-/
-- #guard_msgs in
-- #eval quadratic 0 1

/-
info: (1, -13, 36)
-/
-- #guard_msgs in
-- #eval quadratic 4 9

/-
info: (1, 9, 20)
-/
-- #guard_msgs in
-- #eval quadratic -5 -4

-- Apps difficulty: introductory
-- Assurance level: unguarded