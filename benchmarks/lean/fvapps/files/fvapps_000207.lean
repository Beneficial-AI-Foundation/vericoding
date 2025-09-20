-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxUniqueSplit (s: String) : Nat := sorry

theorem maxUniqueSplit_single_char (s: String) (h: s.length = 1) :
  maxUniqueSplit s = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxUniqueSplit_aa : 
  maxUniqueSplit "aa" = 1 := sorry

theorem maxUniqueSplit_aba :
  maxUniqueSplit "aba" = 2 := sorry
-- </vc-theorems>