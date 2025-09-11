-- <vc-preamble>
def get_weight (s : String) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swapcase (c : Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible