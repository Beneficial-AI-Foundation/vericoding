-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def removeEqualExclamations (s : String) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem word_count_preserved (words : List String) (h : words ≠ []) :
  let text := String.intercalate " " words
  let result := removeEqualExclamations text
  List.length (text.split (· = ' ')) = List.length (result.split (· = ' '))
  := by sorry

theorem preserves_no_exclamation_text (s : String) (h : ∀ c ∈ s.data, c ≠ '!') : 
  removeEqualExclamations s = s := by sorry

/-
info: 'Hi'
-/
-- #guard_msgs in
-- #eval remove_equal_exclamations "Hi!"

/-
info: '!Hi! Hi'
-/
-- #guard_msgs in
-- #eval remove_equal_exclamations "!Hi! Hi!"

/-
info: '!Hi! !Hi!'
-/
-- #guard_msgs in
-- #eval remove_equal_exclamations "!!Hi! !Hi!!"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded