-- <vc-helpers>
-- </vc-helpers>

def remove_vowels (s : String) : String := sorry

def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'

theorem remove_vowels_no_vowels (s : String) :
  ∀ c, c ∈ (remove_vowels s).data → ¬isVowel c := sorry

theorem remove_vowels_length (s : String) :
  (remove_vowels s).length ≤ s.length := sorry

theorem remove_vowels_preserves_nonvowels (s : String) :
  remove_vowels s = String.mk (s.data.filter (λ c => ¬isVowel c)) := sorry

theorem remove_vowels_identity (s : String) :
  (∀ c ∈ s.data, ¬isVowel c) → remove_vowels s = s := sorry

/-
info: 'drk'
-/
-- #guard_msgs in
-- #eval remove_vowels "drake"

/-
info: 'schlrstm'
-/
-- #guard_msgs in
-- #eval remove_vowels "scholarstem"

/-
info: 'hgh fvs!'
-/
-- #guard_msgs in
-- #eval remove_vowels "high fives!"

-- Apps difficulty: introductory
-- Assurance level: unguarded