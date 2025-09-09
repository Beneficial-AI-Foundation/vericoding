def reverse_vowels (s : String) : String := sorry

def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
  c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'

-- <vc-helpers>
-- </vc-helpers>

def count_char (s : String) (c : Char) : Nat := 
  s.toList.filter (· == c) |>.length

theorem reverse_vowels_length_unchanged (s : String) :
  (reverse_vowels s).length = s.length := sorry

theorem reverse_vowels_consonants_unchanged (s : String) (i : String.Pos) :
  ¬isVowel (s.get i) → (reverse_vowels s).get i = s.get i := sorry 

theorem reverse_vowels_idempotent (s : String) :
  reverse_vowels (reverse_vowels s) = s := sorry

theorem reverse_vowels_preserves_count (s : String) (c : Char) :
  isVowel c → count_char (reverse_vowels s) c = count_char s c := sorry

theorem reverse_vowels_no_vowels (s : String) :
  (∀ i : String.Pos, ¬isVowel (s.get i)) → reverse_vowels s = s := sorry

/-
info: 'holle'
-/
-- #guard_msgs in
-- #eval reverse_vowels "hello"

/-
info: 'leotcede'
-/
-- #guard_msgs in
-- #eval reverse_vowels "leetcode"

/-
info: 'Aa'
-/
-- #guard_msgs in
-- #eval reverse_vowels "aA"

-- Apps difficulty: introductory
-- Assurance level: unguarded