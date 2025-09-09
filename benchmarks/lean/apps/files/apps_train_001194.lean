-- <vc-helpers>
-- </vc-helpers>

def find_max_profit_transformations (dollars cents cost : Nat) : Nat :=
sorry

theorem max_profit_non_negative (dollars cents cost : Nat) :
  find_max_profit_transformations dollars cents cost ≥ 0 := by
  sorry

theorem max_profit_bounded (dollars cents cost : Nat) :
  find_max_profit_transformations dollars cents cost ≤ 10000 := by
  sorry

theorem max_profit_insufficient_funds (dollars cents cost : Nat) :
  dollars * 100 + cents < cost →
  find_max_profit_transformations dollars cents cost = 0 := by
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_max_profit_transformations 9 77 69

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_max_profit_transformations 98 99 69

-- Apps difficulty: interview
-- Assurance level: guarded