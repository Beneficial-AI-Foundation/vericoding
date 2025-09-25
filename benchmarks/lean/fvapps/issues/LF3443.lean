-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arithmetic (a b : Int) (op : Op) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arithmetic_add (a b : Int) : 
  arithmetic a b Op.add = a + b := sorry

theorem arithmetic_subtract (a b : Int) :
  arithmetic a b Op.subtract = a - b := sorry

theorem arithmetic_multiply (a b : Int) :
  arithmetic a b Op.multiply = a * b := sorry

theorem arithmetic_divide (a b : Int) (h : b ≠ 0) :
  arithmetic a b Op.divide = a / b := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval arithmetic 1 2 "add"

/-
info: 6
-/
-- #guard_msgs in
-- #eval arithmetic 8 2 "subtract"

/-
info: 10
-/
-- #guard_msgs in
-- #eval arithmetic 5 2 "multiply"
-- </vc-theorems>