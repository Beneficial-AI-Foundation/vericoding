-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def letter_check (input : List String) : Bool := sorry

theorem letter_check_empty_second_string 
  (s₁ : String) : 
  letter_check [s₁, ""] = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem letter_check_identical_strings
  (s : String) :
  letter_check [s, s] = true := sorry

theorem letter_check_case_insensitive
  (s₁ s₂ : String) :
  letter_check [s₁, s₂] = letter_check [s₁.toUpper, s₂.toLower] := sorry

theorem letter_check_true_implies_chars_exist
  (s₁ s₂ : String) :
  letter_check [s₁, s₂] = true →
  ∀ c ∈ s₂.data, c.toLower ∈ (s₁.map Char.toLower).data := sorry

theorem letter_check_self_subset
  (s : String) :
  letter_check [s, s] = true := sorry
-- </vc-theorems>