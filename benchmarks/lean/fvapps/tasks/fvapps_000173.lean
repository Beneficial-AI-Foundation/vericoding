-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isScramble (s1 s2 : String) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equal_strings_are_scramble (s : String) :
  isScramble s s = true :=
sorry

theorem different_lengths_not_scramble (s : String) :
  isScramble s (s ++ "a") = false :=
sorry

theorem different_chars_not_scramble (s : String) (h : s.length > 0) :
  ∀ (s2 : String), s.length = s2.length → (∃ c, s.contains c ≠ s2.contains c) →
  isScramble s s2 = false :=
sorry

theorem length_two_strings_scramble (s1 s2 : String) :
  s1.length = 2 → s2.length = 2 → (∀ c, s1.contains c = s2.contains c) →
  isScramble s1 s2 = true :=
sorry

theorem scramble_symmetric (s1 s2 : String) :
  isScramble s1 s2 = isScramble s2 s1 :=
sorry

theorem empty_strings_are_scramble :
  isScramble "" "" = true :=
sorry
-- </vc-theorems>