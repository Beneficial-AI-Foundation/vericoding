-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD := 1000000007

def solve_feast (N K : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_feast_base_case : 
  solve_feast 2 1 = 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_feast 2 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_feast 3 3

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_feast 2 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible