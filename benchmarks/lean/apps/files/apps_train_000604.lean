-- <vc-preamble>
def isInfixOf (sub str : String) : Bool := sorry 
def substr (s : String) (i len : Nat) : String := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_stem (words : List String) : String := sorry

theorem stem_exists_in_all_words (words : List String) :
  let stem := find_stem words
  ∀ word ∈ words, isInfixOf stem word := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stem_is_substring_of_first_word (words : List String) (h : words.length > 0) :
  let stem := find_stem words
  isInfixOf stem (words.get ⟨0, h⟩) := sorry

theorem stem_length_consistency (words : List String) (h : words.length > 0) :
  let stem := find_stem words
  let first := words.get ⟨0, h⟩
  ∀ i j, i < j → j ≤ first.length →
    let substring := substr first i (j-i)
    (∀ word ∈ words, isInfixOf substring word) →
    substring.length ≤ stem.length ∨ 
    (substring.length = stem.length ∧ stem ≤ substring) := sorry

/-
info: 'grace'
-/
-- #guard_msgs in
-- #eval find_stem ["grace", "graceful", "disgraceful", "gracefully"]

/-
info: 'cat'
-/
-- #guard_msgs in
-- #eval find_stem ["cat", "catch", "cathedral"]

/-
info: 'python'
-/
-- #guard_msgs in
-- #eval find_stem ["python", "pythonic", "pythoness"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded