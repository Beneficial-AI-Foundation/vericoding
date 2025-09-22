-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def capitalize_word (s : String) : String := sorry

theorem capitalize_word_length (word : String) (h : word.length > 0) :
  (capitalize_word word).length = word.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem capitalize_word_case (word : String) (h : word.length > 0) :
  ∃ first rest, word = String.mk (first :: rest) → 
  capitalize_word word = String.mk (first.toUpper :: rest.map Char.toLower) := sorry

theorem capitalize_word_idempotent (word : String) (h : word.length > 0) :
  capitalize_word (capitalize_word word) = capitalize_word word := sorry

theorem capitalize_word_empty :
  capitalize_word "" = "" := sorry
-- </vc-theorems>