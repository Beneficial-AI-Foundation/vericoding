-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_colored_parentheses (n: Nat) : Nat := sorry

def MOD : Nat := 1000000007
-- </vc-definitions>

-- <vc-theorems>
theorem result_in_valid_range (n: Nat) :
  solve_colored_parentheses n ≥ 0 ∧ solve_colored_parentheses n < MOD := sorry

theorem result_deterministic (n: Nat) :
  solve_colored_parentheses n = solve_colored_parentheses n := sorry

theorem base_cases :
  solve_colored_parentheses 0 = 1 ∧
  solve_colored_parentheses 1 = 1 := sorry

theorem known_sequence_values :
  solve_colored_parentheses 1 = 1 ∧
  solve_colored_parentheses 2 = 6 ∧
  solve_colored_parentheses 3 = 90 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_colored_parentheses 1

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_colored_parentheses 2

/-
info: 90
-/
-- #guard_msgs in
-- #eval solve_colored_parentheses 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded