-- <vc-helpers>
-- </vc-helpers>

def lengthLex (s₁ s₂ : String) : Bool := sorry

def longest_word (words : List String) : String := sorry

theorem longest_word_prefixes_exist (words : List String) 
  (h : words ≠ []) : 
  let result := longest_word words
  ∀ i, 1 ≤ i → i < result.length → 
  ∃ w ∈ words, result.take i = w :=
sorry

theorem longest_word_is_maximal (words : List String)
  (h : words ≠ []) :
  let result := longest_word words
  ∀ word ∈ words,
    (word.length > result.length → 
      ∃ i, 1 ≤ i ∧ i < word.length ∧ 
      (∀ w ∈ words, word.take i ≠ w)) ∧
    (word.length = result.length ∧ lengthLex word result → 
      ∃ i, 1 ≤ i ∧ i < word.length ∧
      (∀ w ∈ words, word.take i ≠ w)) :=
sorry

/-
info: 'world'
-/
-- #guard_msgs in
-- #eval longest_word ["w", "wo", "wor", "worl", "world"]

/-
info: 'apple'
-/
-- #guard_msgs in
-- #eval longest_word ["a", "banana", "app", "appl", "ap", "apply", "apple"]

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval longest_word ["a", "b", "c"]

-- Apps difficulty: introductory
-- Assurance level: unguarded