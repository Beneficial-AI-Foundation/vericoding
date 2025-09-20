-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def valid_card (s : String) : Bool := sorry

def make_valid_number (digits : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_format_raises {s : String} 
  (h : ¬ ∀ c, c ∈ s.data → c = ' ' ∨ ('0' ≤ c ∧ c ≤ '9')) :
  valid_card s = false :=
sorry

theorem valid_card_with_valid_number {digits : List Nat}
  (h1 : digits.length = 16) 
  (h2 : ∀ d ∈ digits, 0 ≤ d ∧ d ≤ 9) :
  let card := make_valid_number (String.join (digits.map toString))
  valid_card card = true ∧
  valid_card (card.take 4 ++ " " ++ card.drop 4) = true ∧ 
  valid_card (String.join [(card.take 4), " ", (card.drop 4).take 4, " ", 
                          (card.drop 8).take 4, " ", (card.drop 12).take 4]) = true :=
sorry

theorem invalid_card_remains_invalid {digits : List Nat}
  (h1 : digits.length = 15)
  (h2 : ∀ d ∈ digits, 0 ≤ d ∧ d ≤ 9) :
  let card := String.join (digits.map toString) ++ "0"
  ¬valid_card card →
  ¬valid_card card ∧
  ¬valid_card (String.join [(card.take 4), " ", (card.drop 4).take 4, " ",
                           (card.drop 8).take 4, " ", (card.drop 12).take 4]) :=
sorry
-- </vc-theorems>