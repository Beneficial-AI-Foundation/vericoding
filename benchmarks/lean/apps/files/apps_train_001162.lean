def isUpper (c : Char) : Bool := sorry
def isDigit (c : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def isSpace (c : Char) : Bool := sorry

def count_elements (s : String) : Nat × Nat × Nat := sorry

theorem count_elements_totals (s : String) :
  let (uppers, digits, spaces) := count_elements s
  let total := uppers + digits + spaces
  total ≤ s.length := 
sorry

theorem empty_string :
  count_elements "" = (0, 0, 0) :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible