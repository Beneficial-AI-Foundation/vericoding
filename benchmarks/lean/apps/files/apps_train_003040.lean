-- <vc-helpers>
-- </vc-helpers>

def greet (name : Option String) : Option String := sorry

theorem greet_with_name (name : String) :
  greet (some name) = some s!"hello {name}!" := sorry

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

-- Apps difficulty: introductory
-- Assurance level: unguarded