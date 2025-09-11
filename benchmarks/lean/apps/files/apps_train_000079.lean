-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_broken_calc (l r : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem same_value (x : Nat) (h : 0 < x) (h' : x ≤ 10^6) :
  solve_broken_calc x x = 0 :=
sorry

theorem consecutive_valid (x : Nat) (h : 0 < x) (h' : x < 10^6) :
  solve_broken_calc x (x + 1) ≥ 0 :=
sorry

theorem range_validity {l r : Nat} (h₁ : 0 < l) (h₂ : 0 < r) 
    (h₃ : l ≤ 10^6) (h₄ : r ≤ 10^6) :
  solve_broken_calc (min l r) (max l r) ≥ 0 :=
sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_broken_calc 1 4

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_broken_calc 323 323

/-
info: 3439863766
-/
-- #guard_msgs in
-- #eval solve_broken_calc 1 1000000
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded