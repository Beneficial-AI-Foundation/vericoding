-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isLower (c : Char) : Bool :=
  sorry

def isUpper (c : Char) : Bool :=
  sorry

def isDigit (c : Char) : Bool :=
  sorry

def is_valid_password (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_password_conditions (s : String) :
  (s.length ≥ 8) →
  (∃ c, c ∈ s.data ∧ isLower c) →
  (∃ c, c ∈ s.data ∧ isUpper c) →
  (∃ c, c ∈ s.data ∧ isDigit c) →
  is_valid_password s = true :=
sorry

theorem invalid_password_too_short (s : String) :
  s.length < 8 →
  is_valid_password s = false :=
sorry

theorem invalid_password_no_upper (s : String) :
  s.length ≥ 8 →
  (¬∃ c, c ∈ s.data ∧ isUpper c) →
  is_valid_password s = false :=
sorry

theorem invalid_password_no_lower (s : String) :
  s.length ≥ 8 →
  (¬∃ c, c ∈ s.data ∧ isLower c) →
  is_valid_password s = false :=
sorry

theorem invalid_password_no_digit (s : String) :
  s.length ≥ 8 →
  (¬∃ c, c ∈ s.data ∧ isDigit c) →
  is_valid_password s = false :=
sorry

theorem empty_password_invalid :
  is_valid_password "" = false :=
sorry

theorem short_password_invalid :
  is_valid_password "aA1" = false :=
sorry

theorem valid_min_length_password :
  is_valid_password "aaaaA111" = true :=
sorry
-- </vc-theorems>