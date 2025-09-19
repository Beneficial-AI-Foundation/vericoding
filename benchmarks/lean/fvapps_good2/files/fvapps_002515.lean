-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAlnum (c : Char) : Bool :=
sorry

def isAlpha (c : Char) : Bool :=
sorry

def isDigit (c : Char) : Bool :=
sorry

def isLower (c : Char) : Bool :=
sorry

def isUpper (c : Char) : Bool :=
sorry

def check_string_properties (s : String) : List Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_string_properties_bool (s : String) :
  ∀ x ∈ check_string_properties s, x = true ∨ x = false :=
sorry

theorem alpha_implies_alnum (s : String) :
  (check_string_properties s).get! 1 = true → (check_string_properties s).get! 0 = true :=
sorry

theorem digit_implies_alnum (s : String) :
  (check_string_properties s).get! 2 = true → (check_string_properties s).get! 0 = true :=
sorry

theorem case_implies_alpha (s : String) :
  ((check_string_properties s).get! 3 = true ∨ (check_string_properties s).get! 4 = true) →
  (check_string_properties s).get! 1 = true :=
sorry
-- </vc-theorems>