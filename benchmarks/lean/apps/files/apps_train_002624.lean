/-
Your users passwords were all stole in the Yahoo! hack, and it turns out they have been lax in creating secure passwords.  Create a function that checks their new password (passed as a string) to make sure it meets the following requirements:

Between 8 - 20 characters

Contains only the following characters: (and at least one character from each category): uppercase letters, lowercase letters, digits, and the special characters !@#$%^&*?

Return "valid" if passed or else "not valid"
-/

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

-- <vc-helpers>
-- </vc-helpers>

def has_special (s : String) : Bool :=
  sorry

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

/-
info: 'not valid'
-/
-- #guard_msgs in
-- #eval check_password ""

/-
info: 'not valid'
-/
-- #guard_msgs in
-- #eval check_password "Password123"

/-
info: 'valid'
-/
-- #guard_msgs in
-- #eval check_password "P@ssw0rd123"

-- Apps difficulty: introductory
-- Assurance level: unguarded