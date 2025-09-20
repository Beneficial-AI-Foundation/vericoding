-- <vc-preamble>
def is_vowel (c : Char) : Bool :=
  c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u'

def count_chars (s : String) : Nat := s.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def move_vowels (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem move_vowels_length_preserved (s : String) :
  count_chars (move_vowels s) = count_chars s :=
sorry

theorem move_vowels_preserves_characters (s : String) :
  (s.data : List Char) = ((move_vowels s).data : List Char) :=
sorry

theorem move_vowels_splits_correctly (s : String) :
  let result := move_vowels s
  ∃ i : Nat, i ≤ result.length ∧
    (∀ j : String.Pos, j.1 < i → ¬is_vowel (result.get j)) ∧
    (∀ j : String.Pos, i ≤ j.1 ∧ j.1 < result.length → is_vowel (result.get j)) :=
sorry

theorem move_vowels_empty :
  move_vowels "" = "" :=
sorry
-- </vc-theorems>