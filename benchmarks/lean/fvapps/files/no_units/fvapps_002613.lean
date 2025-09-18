-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Char.isVowel : Char → Bool := sorry

def check_vowel : String → Int → Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_vowel_bounds {s : String} {i : Int} :
  (i < 0 ∨ i ≥ s.length) → check_vowel s i = false := sorry

theorem check_vowel_is_vowel {s : String} {i : Int} :
  check_vowel s i = true → 
  ∃ p : String.Pos, (p.byteIdx = i.toNat) ∧ (s.get p).toLower.isVowel := sorry

theorem check_vowel_case_insensitive {s : String} {i : Int} :
  0 ≤ i ∧ i < s.length →
  check_vowel s.toLower i = check_vowel s.toUpper i := sorry

theorem check_vowel_non_letters {s : String} {i : Int} : 
  (∀ c ∈ s.data, ¬c.isAlpha) → 
  check_vowel s i = false := sorry

theorem check_vowel_all_vowels {s : String} {i : Int} :
  (∀ c ∈ s.data, c.isVowel) →
  0 ≤ i → i < s.length →
  check_vowel s i = true := sorry
-- </vc-theorems>