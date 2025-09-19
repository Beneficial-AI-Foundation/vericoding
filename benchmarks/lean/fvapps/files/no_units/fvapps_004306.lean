-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidHexColor (color : String) : Bool := sorry

def shadesOfGrey (n : Int) : List String := sorry

/- Each output is a valid list of strings where each string is a valid hex color -/
-- </vc-definitions>

-- <vc-theorems>
theorem shadesOfGrey_outputs_valid_list (n : Int) : 
  ∀ x ∈ shadesOfGrey n, isValidHexColor x := sorry
-- </vc-theorems>