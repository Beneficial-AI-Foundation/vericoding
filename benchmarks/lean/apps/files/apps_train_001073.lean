-- <vc-helpers>
-- </vc-helpers>

def min_modifications (arr : List Nat) : Nat := sorry

theorem min_modifications_non_negative (arr : List Nat) :
  min_modifications arr ≥ 0 := sorry

theorem min_modifications_upper_bound (arr : List Nat) :
  min_modifications arr ≤ arr.length * arr.length := sorry

theorem min_modifications_empty :
  min_modifications [] = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_modifications [1, 4, 1, 2, 2]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_modifications [2, 3, 2, 3]

-- Apps difficulty: interview
-- Assurance level: unguarded