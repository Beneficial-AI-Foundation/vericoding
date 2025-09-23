-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def search_substr (text pattern : String) (case_sensitive : Bool := true) : Nat := sorry

theorem empty_inputs_return_zero (text pattern : String) : 
  text = "" ∨ pattern = "" → 
  search_substr text pattern = 0 ∧ 
  search_substr text pattern false = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem substring_length_property (text pattern : String) : 
  text ≠ "" → pattern ≠ "" →
  (search_substr text pattern false) * (pattern.length) ≤ text.length := sorry
-- </vc-theorems>