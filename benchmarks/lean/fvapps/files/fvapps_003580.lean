-- <vc-preamble>
def YES : String := "In with a chance"

def NO : String := "Plenty more fish in the sea"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validateNumber (phone : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_number_format (phone : String) (h1 : String.length phone > 0) :
  validateNumber phone = YES ∨ validateNumber phone = NO :=
sorry

theorem valid_uk_mobile (phone : String) (h1 : String.startsWith phone "+44" ∨ String.startsWith phone "0")
    (h2 : String.length (String.replace phone "[^0-9]" "") = 11) :
  validateNumber phone = YES :=
sorry

theorem invalid_number_wrong_prefix (phone : String)
    (h1 : ¬String.startsWith phone "+44" ∧ ¬String.startsWith phone "0") :
  validateNumber phone = NO :=
sorry

theorem invalid_number_wrong_length (phone : String)
    (h1 : String.length (String.replace phone "[^0-9]" "") ≠ 11) :
  validateNumber phone = NO :=
sorry

theorem validates_with_dashes (phone : String)
    (h1 : String.contains phone '-')
    (h2 : String.startsWith (String.replace phone "-" "") "+44" ∨
          String.startsWith (String.replace phone "-" "") "0")
    (h3 : String.length (String.replace phone "[^0-9]" "") = 11) :
  validateNumber phone = YES :=
sorry
-- </vc-theorems>