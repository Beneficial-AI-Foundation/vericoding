-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isScramble (s1 s2 : String) : Bool := sorry

theorem equal_strings_are_scramble (s : String) : 
  isScramble s s = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem different_lengths_not_scramble (s : String) :
  isScramble s (s ++ "a") = false := sorry
-- </vc-theorems>