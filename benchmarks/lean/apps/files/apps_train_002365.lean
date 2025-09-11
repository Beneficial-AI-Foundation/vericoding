-- <vc-preamble>
def min_cost_to_move_chips (positions: List Nat) : Nat :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_even (positions: List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_upper_bound (positions: List Nat) (h: positions ≠ []) :
  min_cost_to_move_chips positions ≤ positions.length :=
sorry

theorem min_cost_non_negative (positions: List Nat) :
  min_cost_to_move_chips positions ≥ 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_cost_to_move_chips [1, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_cost_to_move_chips [2, 2, 2, 3, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_cost_to_move_chips [1, 1000000000]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible