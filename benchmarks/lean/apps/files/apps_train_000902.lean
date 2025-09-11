-- <vc-preamble>
def solve_bulb_fluctuations (n: Nat) : Nat :=
  sorry

def sqrt (n: Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countSquaresNotDiv3 (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_non_negative (n: Nat) :
  solve_bulb_fluctuations n ≥ 0 :=
  sorry

theorem output_less_than_input (n: Nat) :
  solve_bulb_fluctuations n ≤ n :=
  sorry

theorem matches_edge_cases_0 :
  solve_bulb_fluctuations 0 = 0 :=
  sorry

theorem matches_edge_cases_1 :
  solve_bulb_fluctuations 1 = 1 :=
  sorry

theorem matches_edge_cases_2 :
  solve_bulb_fluctuations 2 = 1 :=
  sorry

theorem matches_edge_cases_3 :
  solve_bulb_fluctuations 3 = 1 :=
  sorry

theorem matches_edge_cases_9 :
  solve_bulb_fluctuations 9 = 2 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_bulb_fluctuations 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_bulb_fluctuations 20

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_bulb_fluctuations 100
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible