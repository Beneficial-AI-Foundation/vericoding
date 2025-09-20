-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidHKPhoneNumber (s : String) : Bool :=
sorry

def hasValidHKPhoneNumber (s : String) : Bool :=
sorry

def isValidDigitStr (s : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_number_is_accepted {d1 d2 : String} :
  isValidDigitStr d1 → isValidDigitStr d2 →
  isValidHKPhoneNumber (d1 ++ " " ++ d2) ∧
  hasValidHKPhoneNumber (d1 ++ " " ++ d2) :=
sorry

theorem invalid_numbers_are_rejected {s : String} :
  (∃ i, String.get? s i = some ' ') →
  (∃ i n, String.get? s i = some n ∧ (n < '0' ∨ n > '9')) →
  ¬isValidHKPhoneNumber s :=
sorry

theorem has_valid_number_with_text {d1 d2 pre suf : String} :
  isValidDigitStr d1 → isValidDigitStr d2 →
  hasValidHKPhoneNumber (pre ++ d1 ++ " " ++ d2 ++ suf) ∧
  ¬isValidHKPhoneNumber (pre ++ d1 ++ " " ++ d2 ++ suf) :=
sorry
-- </vc-theorems>