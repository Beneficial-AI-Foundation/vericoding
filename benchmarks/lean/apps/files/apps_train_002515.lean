def isAlnum (c : Char) : Bool := sorry
def isAlpha (c : Char) : Bool := sorry  

def isDigit (c : Char) : Bool := sorry
def isLower (c : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def isUpper (c : Char) : Bool := sorry

def check_string_properties (s : String) : List Bool := sorry

theorem check_string_properties_bool (s : String) :
  ∀ x ∈ check_string_properties s, x = true ∨ x = false := sorry

theorem alpha_implies_alnum (s : String) :
  (check_string_properties s).get! 1 = true → (check_string_properties s).get! 0 = true := sorry

theorem digit_implies_alnum (s : String) :
  (check_string_properties s).get! 2 = true → (check_string_properties s).get! 0 = true := sorry

theorem case_implies_alpha (s : String) :
  ((check_string_properties s).get! 3 = true ∨ (check_string_properties s).get! 4 = true) →
  (check_string_properties s).get! 1 = true := sorry

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible