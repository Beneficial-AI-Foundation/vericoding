-- <vc-helpers>
-- </vc-helpers>

def wrap_mystery (n : Nat) : Int :=
  sorry

theorem wrap_mystery_17 : wrap_mystery 17 = -1 := by
  sorry

theorem wrap_mystery_1 : wrap_mystery 1 = 0 := by
  sorry

theorem wrap_mystery_13 : wrap_mystery 13 = 0 := by
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval wrap_mystery 1

/-
info: -1
-/
-- #guard_msgs in
-- #eval wrap_mystery 17

/-
info: 65
-/
-- #guard_msgs in
-- #eval wrap_mystery 7

-- Apps difficulty: introductory
-- Assurance level: guarded