-- <vc-preamble>
def Email := String
def validate_emails (emails : List Email) : List Email := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidEmailFormat (e : Email) : Bool := sorry

/- For a list of valid email addresses, all should be returned unchanged -/
-- </vc-definitions>

-- <vc-theorems>
theorem validate_valid_emails (emails : List Email) 
  (h : ∀ e ∈ emails, isValidEmailFormat e) :
  validate_emails emails = emails :=
sorry
-- </vc-theorems>