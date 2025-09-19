-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_variable_with_777 : String := sorry

theorem no_777_variable
  (h : find_variable_with_777.isEmpty = true) :
  ¬ (∃ x : String, find_variable_with_777 = x) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wrong_value
  (name : String)
  (val : Int)
  (h1 : name.length > 0)
  (h2 : val ≠ 777) :
  ¬ (∃ x : String, find_variable_with_777 = x) := sorry
-- </vc-theorems>