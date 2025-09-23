-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate (input : String) : CalcResult := sorry

theorem calculate_empty_expr : 
  calculate "" = CalcResult.Number 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_returns_float (expr : String) :
  ∃ (n : Float), calculate expr = CalcResult.Number n ∨ calculate expr = CalcResult.Error := sorry

theorem calculate_single_number (n : Float) (h : -1000 ≤ n ∧ n ≤ 1000) :
  calculate (toString n) = CalcResult.Number n := sorry

theorem calculate_addition (a b : Float) (h : -1000 ≤ a ∧ a ≤ 1000 ∧ -1000 ≤ b ∧ b ≤ 1000) :
  calculate (toString a ++ " " ++ toString b ++ " +") = CalcResult.Number (a + b) := sorry

theorem calculate_multiplication (a b : Float) (h : -1000 ≤ a ∧ a ≤ 1000 ∧ -1000 ≤ b ∧ b ≤ 1000) :
  calculate (toString a ++ " " ++ toString b ++ " *") = CalcResult.Number (a * b) := sorry

theorem calculate_division (a b : Float) (h₁ : -1000 ≤ a ∧ a ≤ 1000 ∧ -1000 ≤ b ∧ b ≤ 1000) (h₂ : b ≠ 0) :
  calculate (toString a ++ " " ++ toString b ++ " /") = CalcResult.Number (a / b) := sorry

theorem calculate_subtraction (a b : Float) (h : -1000 ≤ a ∧ a ≤ 1000 ∧ -1000 ≤ b ∧ b ≤ 1000) :
  calculate (toString a ++ " " ++ toString b ++ " -") = CalcResult.Number (a - b) := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval calc ""

/-
info: 4
-/
-- #guard_msgs in
-- #eval calc "1 3 +"

/-
info: 14
-/
-- #guard_msgs in
-- #eval calc "5 1 2 + 4 * + 3 -"
-- </vc-theorems>