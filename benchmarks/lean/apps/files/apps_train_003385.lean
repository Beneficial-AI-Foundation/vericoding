-- <vc-helpers>
-- </vc-helpers>

def isLucky (s : String) : Bool := sorry

def sumDigits (s : String) : Nat := sorry

theorem valid_ticket_behavior (ticket : String) 
  (h1 : ticket.length = 6) 
  (h2 : ∀ c ∈ ticket.data, c.isDigit) :
  isLucky ticket = (sumDigits (ticket.take 3) = sumDigits (ticket.drop 3)) := sorry

theorem invalid_ticket_length (ticket : String)
  (h : ticket.length ≠ 6) :
  isLucky ticket = false := sorry

theorem invalid_ticket_chars (ticket : String)
  (h : ∃ c ∈ ticket.data, ¬c.isDigit) :
  isLucky ticket = false := sorry

theorem edge_cases :
  isLucky "000000" = true ∧
  isLucky "" = false ∧ 
  isLucky "12345" = false ∧
  isLucky "1234567" = false ∧
  isLucky "abcdef" = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_lucky "123321"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_lucky "12341234"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_lucky "000000"

-- Apps difficulty: introductory
-- Assurance level: unguarded