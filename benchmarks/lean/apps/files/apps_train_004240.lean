-- <vc-helpers>
-- </vc-helpers>

def start_smoking (bars : Nat) (boxes : Nat) : Nat :=
sorry

theorem start_smoking_nonnegative (bars boxes : Nat) :
  start_smoking bars boxes ≥ 0 := sorry

/-
info: 22
-/
-- #guard_msgs in
-- #eval start_smoking 0 1

/-
info: 224
-/
-- #guard_msgs in
-- #eval start_smoking 1 0

/-
info: 247
-/
-- #guard_msgs in
-- #eval start_smoking 1 1

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible