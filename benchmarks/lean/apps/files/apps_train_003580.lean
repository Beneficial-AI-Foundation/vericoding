-- <vc-preamble>
def validateNumber (phone : String) : String := sorry

def YES : String := "In with a chance"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def NO : String := "Plenty more fish in the sea"

theorem valid_number_format (phone : String) (h1 : String.length phone > 0) : 
  validateNumber phone = YES ∨ validateNumber phone = NO :=
sorry
-- </vc-definitions>

-- <vc-theorems>
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

/-
info: 'In with a chance'
-/
-- #guard_msgs in
-- #eval validate_number "07454876120"

/-
info: 'In with a chance'
-/
-- #guard_msgs in
-- #eval validate_number "0745--487-61-20"

/-
info: 'In with a chance'
-/
-- #guard_msgs in
-- #eval validate_number "+447535514555"

/-
info: 'Plenty more fish in the sea'
-/
-- #guard_msgs in
-- #eval validate_number "0754876120"

/-
info: 'Plenty more fish in the sea'
-/
-- #guard_msgs in
-- #eval validate_number "+337535512555"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded