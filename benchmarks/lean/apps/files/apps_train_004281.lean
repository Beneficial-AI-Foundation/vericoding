-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiple (n : Int) : String := sorry 

theorem multiple_output_valid (x : Int) : 
  multiple x = "Bang" ∨ multiple x = "Boom" ∨ multiple x = "BangBoom" ∨ multiple x = "Miss" := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiple_divisible_by_both (x : Int) : 
  x % 3 = 0 ∧ x % 5 = 0 → multiple x = "BangBoom" :=
sorry

theorem multiple_divisible_by_3 (x : Int) :
  x % 3 = 0 ∧ x % 5 ≠ 0 → multiple x = "Bang" :=
sorry

theorem multiple_divisible_by_5 (x : Int) :
  x % 3 ≠ 0 ∧ x % 5 = 0 → multiple x = "Boom" :=
sorry

theorem multiple_not_divisible (x : Int) :
  x % 3 ≠ 0 ∧ x % 5 ≠ 0 → multiple x = "Miss" :=
sorry

theorem multiple_deterministic (x : Int) :
  multiple x = multiple x :=
sorry

theorem multiple_modulo_equivalence (x y : Int) :
  x % 3 = y % 3 → x % 5 = y % 5 → multiple x = multiple y :=
sorry

/-
info: 'BangBoom'
-/
-- #guard_msgs in
-- #eval multiple 30

/-
info: 'Bang'
-/
-- #guard_msgs in
-- #eval multiple 9

/-
info: 'Miss'
-/
-- #guard_msgs in
-- #eval multiple 98
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded