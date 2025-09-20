-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binaryStringToDecimal (s : String) : Nat :=
sorry

def isVowel (c : Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_in_valid_range (s : String) (h : s.length > 0) :
  binaryStringToDecimal s < 10^9 + 7 ∧ binaryStringToDecimal s ≥ 0 :=
sorry

theorem all_vowels_max_value (s : String) (h : s.length > 0)
  (h2 : ∀ c ∈ s.data, isVowel c) :
  binaryStringToDecimal s = (2^s.length - 1) % (10^9 + 7) :=
sorry

theorem all_consonants_zero (s : String) (h : s.length > 0)
  (h2 : ∀ c ∈ s.data, ¬isVowel c) :
  binaryStringToDecimal s = 0 :=
sorry

theorem same_vowel_positions_equal (s1 s2 : String)
  (h1 : s1.length > 0)
  (h2 : s1.length = s2.length)
  (h3 : ∀ (i : String.Pos), isVowel (s1.get i) = isVowel (s2.get i)) :
  binaryStringToDecimal s1 = binaryStringToDecimal s2 :=
sorry
-- </vc-theorems>