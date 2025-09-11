-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_cost (n: Nat) (arr: List Int) (x: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_cost_nonnegative (n: Nat) (arr: List Int) (x: Nat) :
  find_min_cost n arr x ≥ 0 :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_min_cost 3 [-1, -2, -3] 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_min_cost 4 [-1, 0, 2, -3] 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_min_cost 2 [1, 2] 5
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible