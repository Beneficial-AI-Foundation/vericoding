def get_weight (s : String) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def swapcase (c : Char) : Nat :=
  sorry

theorem get_weight_nonnegative (s : String) :
  get_weight s ≥ 0 :=
  sorry

/-
info: 254
-/
-- #guard_msgs in
-- #eval get_weight "Joe"

/-
info: 1275
-/
-- #guard_msgs in
-- #eval get_weight "George Washington"

/-
info: 214
-/
-- #guard_msgs in
-- #eval get_weight "R2D2"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible