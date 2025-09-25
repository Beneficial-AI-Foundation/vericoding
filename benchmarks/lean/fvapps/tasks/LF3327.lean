-- <vc-preamble>
def isVowel (c : Char) : Bool := 
  let lc := c.toLower
  lc == 'a' ∨ lc == 'e' ∨ lc == 'i' ∨ lc == 'o' ∨ lc == 'u' ∨ lc == 'y'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vowel_indices (s : String) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vowel_indices_in_bounds (s : String) :
  ∀ i ∈ vowel_indices s, 0 < i ∧ i ≤ s.length :=
sorry

theorem vowel_indices_ascending (s : String) (i j : Nat) :
  i < j → 
  i ∈ vowel_indices s →
  j ∈ vowel_indices s →
  i < j :=
sorry

theorem vowel_indices_points_to_vowels (s : String) (i : Nat) :
  i ∈ vowel_indices s → 
  i > 0 →
  i ≤ s.length →
  isVowel (s.data.get! (i-1)) :=
sorry

theorem vowel_indices_finds_all_vowels (s : String) :
  (vowel_indices s).length = (s.data.filter isVowel).length :=
sorry

theorem vowel_indices_unique (s : String) (i j : Nat) :
  i ∈ vowel_indices s →
  j ∈ vowel_indices s →
  i = j ∨ i ≠ j :=
sorry
-- </vc-theorems>