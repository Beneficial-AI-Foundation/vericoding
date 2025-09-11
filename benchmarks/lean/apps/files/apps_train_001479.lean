-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_division (a : String) (b : String) (l : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem division_by_zero :
  ∀ l : Nat, solve_division "1" "0" l = 0 ∨ solve_division "1" "0" l = 0 :=
sorry

theorem zero_numerator
  (l : Nat)
  (h : 1 ≤ l ∧ l ≤ 5) :
  solve_division "0" "1" l = 0 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_division "21" "5" 10

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_division "202" "13" 1

/-
info: 13
-/
-- #guard_msgs in
-- #eval solve_division "202" "13" 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible