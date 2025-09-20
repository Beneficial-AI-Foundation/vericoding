-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_acronym (s : String) : String := sorry

theorem empty_string_returns_empty :
  make_acronym "" = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_letter_strings_returns_not_letters (s : String) :
  (∃ c ∈ s.data, ¬c.isAlpha ∧ ¬c.isWhitespace) →
  make_acronym s = "Not letters" := sorry

theorem valid_input_produces_uppercase_first_letters (words : List String) : 
  (words.length > 0) →
  (∀ w ∈ words, w.length > 0 ∧ (∀ c ∈ w.data, c.isAlpha)) →
  make_acronym (" ".intercalate words) = 
    String.mk (words.map (λ w => w.data.head!.toUpper)) := sorry
-- </vc-theorems>