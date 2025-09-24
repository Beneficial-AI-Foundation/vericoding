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
-- </vc-theorems>