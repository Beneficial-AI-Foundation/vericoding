-- <vc-preamble>
def is_negative_zero (x : Float) : Bool := sorry

/- Helper function to emulate sign behavior -/

def getSign (x : Float) : Float := sorry

theorem is_negative_zero_main (x : Float) :
  is_negative_zero x = true ↔ (getSign x < 0 ∧ x = 0) := sorry

def posInf : Float := sorry
def negInf : Float := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nanFloat : Float := sorry

theorem is_negative_zero_special_cases :
  is_negative_zero posInf = false ∧
  is_negative_zero negInf = false ∧
  is_negative_zero nanFloat = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_negative_zero_integers (n : Int) :
  is_negative_zero (Float.ofInt n) = false := sorry

/- Constants for special float values -/

/-
info: True
-/
-- #guard_msgs in
-- #eval is_negative_zero -0.0

/-
info: False
-/
-- #guard_msgs in
-- #eval is_negative_zero 0.0

/-
info: False
-/
-- #guard_msgs in
-- #eval is_negative_zero -5.0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded