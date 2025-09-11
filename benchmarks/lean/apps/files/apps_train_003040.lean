-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greet (name : Option String) : Option String := sorry

theorem greet_with_name (name : String) :
  greet (some name) = some s!"hello {name}!" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greet_with_none :
  greet none = none := sorry

/-
info: 'hello Niks!'
-/
-- #guard_msgs in
-- #eval greet "Niks"

/-
info: None
-/
-- #guard_msgs in
-- #eval greet ""

/-
info: None
-/
-- #guard_msgs in
-- #eval greet None
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded