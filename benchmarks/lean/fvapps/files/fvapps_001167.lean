-- <vc-preamble>
def MOD := 1000000007

def solve_f_n (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def direct_calc (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem base_cases :
  solve_f_n 1 = 1 ∧ 
  solve_f_n 2 = 2 ∧ 
  solve_f_n 3 = 12 :=
sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval solve_f_n 3

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_f_n 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_f_n 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible