/-
Each test case will generate a variable whose value is 777. Find the name of the variable.
-/

-- <vc-helpers>
-- </vc-helpers>

def find_variable_with_777 : String := sorry

theorem no_777_variable
  (h : find_variable_with_777.isEmpty = true) :
  ¬ (∃ x : String, find_variable_with_777 = x) := sorry

theorem wrong_value
  (name : String)
  (val : Int)
  (h1 : name.length > 0)
  (h2 : val ≠ 777) :
  ¬ (∃ x : String, find_variable_with_777 = x) := sorry

/-
info: 'secret_var'
-/
-- #guard_msgs in
-- #eval find_variable_with_777 

/-
info: 'magic_number'
-/
-- #guard_msgs in
-- #eval find_variable_with_777

-- Apps difficulty: introductory
-- Assurance level: unguarded