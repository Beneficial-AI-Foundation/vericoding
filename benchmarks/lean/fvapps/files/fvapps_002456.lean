-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Result := String
def validate_credit_cards : List String → List Result := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem validate_returns_valid_or_invalid (cards : List String) 
  (h : cards.length > 0) : 
  let results := validate_credit_cards cards
  results.length = cards.length ∧ 
  ∀ r ∈ results, r = "Valid" ∨ r = "Invalid"
  := sorry

theorem consecutive_digits_invalid (card : String)
  (h : card ∈ ["4444444444444444", "5444-4444-4444-4444", "6444444444444444"]) :
  validate_credit_cards [card] = ["Invalid"] := sorry

theorem invalid_format_cards (card : String)
  (h : card ∈ ["1234567890123456", "7234567890123456", "4123-456-789-0123", "4123-4567-8901"]) :
  validate_credit_cards [card] = ["Invalid"] := sorry

theorem valid_format_cards (card : String) 
  (h : card ∈ ["4123456789123456", "5123-4567-8912-3456"]) :
  validate_credit_cards [card] = ["Valid"] := sorry

theorem empty_list :
  validate_credit_cards [] = [] := sorry

theorem whitespace_handling :
  validate_credit_cards [" 4123456789123456 "] = ["Valid"] := sorry
-- </vc-theorems>