-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encrypt (text: String) (key: String) : String := sorry

theorem single_letter_padded {key: String} 
  (h1: key.length = 4) 
  (h2: ∀ c ∈ key.data, c.isLower) : 
  ∀ text: String, text = "A" → (encrypt text key).length = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encrypt_output_is_uppercase_alpha {key: String}
  (h1: key.length = 4)
  (h2: ∀ c ∈ key.data, c.isLower) :
  ∀ text: String, 
  ∀ c ∈ (encrypt text key).data,
  c.isUpper ∧ c.isAlpha := sorry

theorem encrypt_output_length_is_even {key: String}
  (h1: key.length = 4)
  (h2: ∀ c ∈ key.data, c.isLower) :
  ∀ text: String,
  (encrypt text key).length > 0 →
  (encrypt text key).length % 2 = 0 := sorry

theorem encrypt_preserves_alpha_count {key: String}
  (h1: key.length = 4)
  (h2: ∀ c ∈ key.data, c.isLower) :
  ∀ text: String,
  let alpha_count := (text.data.filter Char.isAlpha).length
  if alpha_count % 2 = 1 
  then (encrypt text key).length = alpha_count + 1
  else (encrypt text key).length = alpha_count := sorry

theorem empty_string_encrypt {key: String}
  (h: key = "hill") :
  encrypt "" key = "" := sorry

theorem non_alpha_stripped {key: String}
  (h1: key.length = 4)
  (h2: ∀ c ∈ key.data, c.isLower) :
  ∀ text: String,
  (∀ c ∈ text.data, c.isDigit ∨ c = ' ' ∨ c = '.' ∨ c = ',' ∨ c = '!' ∨ c = '?') →
  encrypt text key = "" := sorry
-- </vc-theorems>