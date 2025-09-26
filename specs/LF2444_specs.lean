-- <vc-preamble>
def Email := String
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validate_emails (emails : List Email) : List Email :=
sorry

def isValidEmailFormat (e : Email) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem validate_valid_emails (emails : List Email)
  (h : ∀ e ∈ emails, isValidEmailFormat e) :
  validate_emails emails = emails :=
sorry

theorem validate_invalid_emails (emails : List Email)
  (h : ∀ e ∈ emails, ¬ isValidEmailFormat e) :
  validate_emails emails = [] :=
sorry

theorem validate_mixed_emails (emails : List Email)
  (valid : List Email := emails.filter isValidEmailFormat) :
  validate_emails emails = valid :=
sorry

theorem validate_arbitrary_input (inputs : List String) :
  ∃ result, validate_emails inputs = result :=
sorry
-- </vc-theorems>