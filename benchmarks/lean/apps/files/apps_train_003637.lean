-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def angle (n : Nat) : Nat := sorry

theorem angle_monotonic_increasing {n : Nat} (h : n ≥ 3) :
  angle n > angle (n-1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem angle_properties {n : Nat} (h : n ≥ 3) :
  angle n % 180 = 0 ∧ angle n ≥ 180 := sorry

/-
info: 180
-/
-- #guard_msgs in
-- #eval angle 3

/-
info: 360
-/
-- #guard_msgs in
-- #eval angle 4

/-
info: 540
-/
-- #guard_msgs in
-- #eval angle 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible