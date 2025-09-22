-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_vowels (s : String) : String := sorry

def isVowel (c : Char) : Bool :=
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
-- </vc-definitions>

-- <vc-theorems>
theorem remove_vowels_no_vowels (s : String) :
  ∀ c, c ∈ (remove_vowels s).data → ¬isVowel c := sorry

theorem remove_vowels_length (s : String) :
  (remove_vowels s).length ≤ s.length := sorry

theorem remove_vowels_preserves_nonvowels (s : String) :
  remove_vowels s = String.mk (s.data.filter (λ c => ¬isVowel c)) := sorry

theorem remove_vowels_identity (s : String) :
  (∀ c ∈ s.data, ¬isVowel c) → remove_vowels s = s := sorry
-- </vc-theorems>