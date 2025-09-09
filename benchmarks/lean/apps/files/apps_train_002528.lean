-- <vc-helpers>
-- </vc-helpers>

def last_chair (n : Nat) : Nat :=
  sorry

theorem last_chair_range {n : Nat} (h : n ≥ 3) :
  1 ≤ last_chair n ∧ last_chair n ≤ n := by
  sorry

theorem last_chair_value {n : Nat} (h : n ≥ 3) :
  last_chair n = n - 1 := by
  sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval last_chair 10

/-
info: 4
-/
-- #guard_msgs in
-- #eval last_chair 5

/-
info: 2
-/
-- #guard_msgs in
-- #eval last_chair 3

-- Apps difficulty: introductory
-- Assurance level: guarded