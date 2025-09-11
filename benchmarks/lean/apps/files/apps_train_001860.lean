-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_num_valid_words (words: List String) (puzzles: List String) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_puzzles {words: List String} {puzzles: List String}
  (h1: words.length > 0)
  (h2: puzzles.length > 0)
  (h3: ∀ p ∈ puzzles, p.length = 7)
  : (find_num_valid_words words puzzles).length = puzzles.length := by
  sorry

theorem outputs_are_non_negative {words: List String} {puzzles: List String} 
  (h1: words.length > 0)
  (h2: puzzles.length > 0)
  (h3: ∀ p ∈ puzzles, p.length = 7)
  : ∀ x ∈ (find_num_valid_words words puzzles), x ≥ 0 := by
  sorry

theorem empty_puzzles {words: List String}
  (h1: words.length > 0) :
  find_num_valid_words words [] = [] := by
  sorry

theorem empty_words {puzzles: List String}
  (h1: puzzles.length > 0)
  (h2: ∀ p ∈ puzzles, p.length = 7)
  : ∀ x ∈ (find_num_valid_words [] puzzles), x = 0 := by
  sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval find_num_valid_words ["aaaa", "asas", "able", "ability", "actt", "actor", "access"] ["aboveyz", "abrodyz", "abslute", "absoryz", "actresz", "gaswxyz"]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval find_num_valid_words ["apple", "pleas", "please"] ["aelwxyz", "aelpxyz", "aelpsxy", "saelpxy"]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval find_num_valid_words ["a"] ["abcdefg"]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded