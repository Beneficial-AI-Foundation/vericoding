-- <vc-helpers>
-- </vc-helpers>

def validate_usr (username : String) : Bool := sorry

theorem valid_username_accepted 
  (username : String)
  (h1 : username.length ≥ 4)
  (h2 : username.length ≤ 16) 
  (h3 : ∀ c ∈ username.data, c.isLower ∨ c.isDigit ∨ c = '_') :
  validate_usr username = true := sorry

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

/-
info: True
-/
-- #guard_msgs in
-- #eval validate_usr "asddsa"

/-
info: True
-/
-- #guard_msgs in
-- #eval validate_usr "____"

/-
info: False
-/
-- #guard_msgs in
-- #eval validate_usr "Hass"

-- Apps difficulty: introductory
-- Assurance level: unguarded