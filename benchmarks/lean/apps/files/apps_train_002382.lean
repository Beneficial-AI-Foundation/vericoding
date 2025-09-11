-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAlienSorted (words : List String) (order : String) : Bool := sorry

theorem single_word_always_sorted (w : String) (order : String) 
  (h : ∀ c, c ∈ w.data → c ∈ order.data) :
  isAlienSorted [w] order := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_words_sorted (w : String) (order : String) 
  (h : ∀ c, c ∈ w.data → c ∈ order.data) :
  isAlienSorted [w, w] order := sorry

theorem prefix_property (w longer : String) (order : String)
  (h₁ : ∀ c, c ∈ w.data → c ∈ order.data)
  (h₂ : ∀ c, c ∈ longer.data → c ∈ order.data)
  (h₃ : ∃ s, longer = w.append s) :
  (¬ isAlienSorted [longer, w] order) ∧ 
  isAlienSorted [w, longer] order := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_alien_sorted ["hello", "leetcode"] "hlabcdefgijkmnopqrstuvwxyz"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_alien_sorted ["word", "world", "row"] "worldabcefghijkmnpqstuvxyz"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_alien_sorted ["apple", "app"] "abcdefghijklmnopqrstuvwxyz"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded