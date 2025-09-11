-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_safest_position (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem safest_position_in_range (n : Nat) (h : n > 0) :
  let pos := find_safest_position n
  1 ≤ pos ∧ pos ≤ n :=
sorry

theorem safest_position_consistent (n : Nat) :
  find_safest_position n = find_safest_position n :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_safest_position 9

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_safest_position 5

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_safest_position 7
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded