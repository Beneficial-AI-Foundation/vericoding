-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validate_usr (username : String) : Bool := sorry

theorem valid_username_accepted 
  (username : String)
  (h1 : username.length ≥ 4)
  (h2 : username.length ≤ 16) 
  (h3 : ∀ c ∈ username.data, c.isLower ∨ c.isDigit ∨ c = '_') :
  validate_usr username = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_chars_rejected
  (username : String)
  (h1 : username.length ≥ 4)
  (h2 : username.length ≤ 16)
  (h3 : ∃ c ∈ username.data, ¬(c.isLower ∨ c.isDigit ∨ c = '_')) :
  validate_usr username = false := sorry

theorem invalid_length_rejected
  (username : String)
  (h : username.length < 4 ∨ username.length > 16) :
  validate_usr username = false := sorry

theorem edge_cases :
  validate_usr "" = false ∧
  validate_usr "abc" = false ∧
  validate_usr "aaaaaaaaaaaaaaaaa" = false := sorry
-- </vc-theorems>