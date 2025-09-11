-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def toBool (b : Bool) : Bool := b

def negation_value (s : String) (value : Bool) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem double_negation (value : Bool) :
  negation_value "!!" value = value := sorry

theorem basic_negation (value : Bool) :
  negation_value "!" value = !value := sorry

theorem empty_negation (value : Bool) : 
  negation_value "" value = value := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval negation_value "!" False

/-
info: False
-/
-- #guard_msgs in
-- #eval negation_value "!" True

/-
info: True
-/
-- #guard_msgs in
-- #eval negation_value "!!!" []
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded