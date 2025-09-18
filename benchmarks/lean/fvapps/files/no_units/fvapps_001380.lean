-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_sokka_journey (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_sokka_journey_non_negative (n: Nat) (h: n ≥ 2) : 
  solve_sokka_journey n ≥ 0 := sorry

theorem solve_sokka_journey_less_than_modulo (n: Nat) (h: n ≥ 2) :
  solve_sokka_journey n < 1000000007 := sorry

theorem solve_sokka_journey_minimum_input :
  solve_sokka_journey 2 = 0 := sorry

theorem solve_sokka_journey_three_input :
  solve_sokka_journey 3 = 333333336 := sorry
-- </vc-theorems>