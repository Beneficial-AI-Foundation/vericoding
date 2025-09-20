-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_password (s : String) : String :=
  sorry

def is_special_char (c : Char) : Bool :=
  sorry

def has_lowercase (s : String) : Bool :=
  sorry

def has_uppercase (s : String) : Bool :=
  sorry

def has_digit (s : String) : Bool :=
  sorry

def has_special (s : String) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem password_too_short {s : String} (h : s.length < 8) :
  check_password s = "not valid" :=
sorry

theorem password_too_long {s : String} (h : s.length > 20) :
  check_password s = "not valid" :=
sorry

theorem password_invalid_chars {s : String} (h : ∃ c ∈ s.data,
  ¬(c.isLower ∨ c.isUpper ∨ c.isDigit ∨ is_special_char c)) :
  check_password s = "not valid" :=
sorry

theorem password_missing_required_chars {s : String}
  (h1 : s.length ≥ 8)
  (h2 : s.length ≤ 20)
  (h3 : ∀ c ∈ s.data, (c.isLower ∨ c.isUpper ∨ c.isDigit ∨ is_special_char c))
  (h4 : ¬(has_lowercase s ∧ has_uppercase s ∧ has_digit s ∧ has_special s)) :
  check_password s = "not valid" :=
sorry
-- </vc-theorems>