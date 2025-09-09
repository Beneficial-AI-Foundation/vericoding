-- <vc-helpers>
-- </vc-helpers>

def solve_sokka_journey (n: Nat) : Nat :=
  sorry

theorem solve_sokka_journey_non_negative (n: Nat) (h: n ≥ 2) : 
  solve_sokka_journey n ≥ 0 := sorry

theorem solve_sokka_journey_less_than_modulo (n: Nat) (h: n ≥ 2) :
  solve_sokka_journey n < 1000000007 := sorry

theorem solve_sokka_journey_minimum_input :
  solve_sokka_journey 2 = 0 := sorry

theorem solve_sokka_journey_three_input :
  solve_sokka_journey 3 = 333333336 := sorry

/-
info: 200000002
-/
-- #guard_msgs in
-- #eval solve_sokka_journey 5

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_sokka_journey 2

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible