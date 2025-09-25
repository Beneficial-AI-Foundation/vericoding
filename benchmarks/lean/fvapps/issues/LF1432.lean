-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_atomic_weight (f : ChemicalFormula) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem atomic_weight_positive (f : ChemicalFormula) :
  solve_atomic_weight f > 0 := by
  sorry

theorem atomic_weight_consistent (f : ChemicalFormula) :
  solve_atomic_weight f = solve_atomic_weight f := by
  sorry

theorem atomic_weight_x :
  solve_atomic_weight ⟨"x"⟩ = 2 := by
  sorry

theorem atomic_weight_y :
  solve_atomic_weight ⟨"y"⟩ = 4 := by
  sorry

theorem atomic_weight_z :
  solve_atomic_weight ⟨"z"⟩ = 10 := by
  sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval solve_atomic_weight "(xy)2"

/-
info: 46
-/
-- #guard_msgs in
-- #eval solve_atomic_weight "x(x2y)3(z)2"

/-
info: 16
-/
-- #guard_msgs in
-- #eval solve_atomic_weight "xyz"
-- </vc-theorems>