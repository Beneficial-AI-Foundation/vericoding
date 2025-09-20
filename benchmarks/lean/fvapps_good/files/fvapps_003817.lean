-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def high (s : String) : String := sorry

def wordScore (word : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem high_gives_highest_score_word (text : String) : 
  text ≠ "" → (∀ c ∈ text.data, c = ' ' ∨ (97 ≤ c.val ∧ c.val ≤ 122)) →
  let words := text.split (· = ' ')
  words.length > 0 →
  ∀ w ∈ words, w ≠ "" →
  let result := high text
  result ∈ words ∧ 
  ∀ w ∈ words, wordScore result ≥ wordScore w := by
  sorry

theorem high_single_word (word : String) :
  word ≠ "" →
  (∀ c ∈ word.data, 97 ≤ c.val ∧ c.val ≤ 122) →
  high word = word := by
  sorry

theorem high_only_spaces (text : String) :
  text ≠ "" →
  (∀ c ∈ text.data, c = ' ') →
  ¬∃ result, result = high text := by
  sorry
-- </vc-theorems>