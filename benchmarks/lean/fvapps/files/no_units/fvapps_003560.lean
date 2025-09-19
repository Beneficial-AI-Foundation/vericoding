-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.isAlphaNum (c : Char) : Bool := sorry

def countLettersAndDigits (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_letters_and_digits_non_negative (s : String) :
  countLettersAndDigits s ≥ 0 := sorry

theorem count_letters_and_digits_bounded (s : String) :
  countLettersAndDigits s ≤ s.length := sorry

theorem count_letters_and_digits_equals_alphanums (s : String) :
  countLettersAndDigits s = (s.data.filter String.isAlphaNum).length := sorry

theorem count_letters_and_digits_non_string :
  countLettersAndDigits "" = 0 := sorry

theorem count_letters_and_digits_only_alphanumeric (s : String) 
  (h : ∀ c ∈ s.data, String.isAlphaNum c = true) :
  countLettersAndDigits s = s.length := sorry

theorem count_letters_and_digits_only_special (s : String)
  (h : ∀ c ∈ s.data, String.isAlphaNum c = false) :
  countLettersAndDigits s = 0 := sorry
-- </vc-theorems>