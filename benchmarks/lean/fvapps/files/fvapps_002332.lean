-- <vc-preamble>
def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' ||
  c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'

def count_char (s : String) (c : Char) : Nat :=
  s.toList.filter (· == c) |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_vowels (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_vowels_length_unchanged (s : String) :
  (reverse_vowels s).length = s.length :=
sorry

theorem reverse_vowels_consonants_unchanged (s : String) (i : String.Pos) :
  ¬isVowel (s.get i) → (reverse_vowels s).get i = s.get i :=
sorry

theorem reverse_vowels_idempotent (s : String) :
  reverse_vowels (reverse_vowels s) = s :=
sorry

theorem reverse_vowels_preserves_count (s : String) (c : Char) :
  isVowel c → count_char (reverse_vowels s) c = count_char s c :=
sorry

theorem reverse_vowels_no_vowels (s : String) :
  (∀ i : String.Pos, ¬isVowel (s.get i)) → reverse_vowels s = s :=
sorry
-- </vc-theorems>